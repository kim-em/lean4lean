import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaPacket
import Lean4Lean.Theory.Typing.AnchoredNativePlanInterpretation
import Lean4Lean.Theory.Typing.NativeTerminalSoundness
import Lean4Lean.Theory.Typing.SourceConstantProvenance
import Lean4Lean.Theory.Typing.EquationControls
import Lean4Lean.Theory.Typing.EquationStratifiedFuel

/-! Canonical native opening from pointwise final registration. Unlike the
old native declaration-origin consumer, both equation proofs and the actual
recursor header formation live in the one source selected by the target's
equation stratification. No common declaration-history hypothesis is used.
This does not yet port the native capture interpreter to rich controlled F. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv OriginalClosureMeasure AnchoredProfiles AnchoredSemantics OriginalRecordSource
open InductiveSignature NativeRecursorData EquationStratifiedFuel
open private selected_head from Lean4Lean.Theory.Typing.NativeTerminalSoundness
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- A finite native plan always reaches an actual selected singleton rule;
there is no inhabited native query whose computational head has no equation. -/
theorem NativePlan.selectedProgram
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    (plan : NativePlan env U registry target signature
      arguments demand footprint) :
    ∃ (arguments : List VExpr) (program : SaturatedProgram data),
      data.saturatedProgram levels arguments = some program := by
  match plan with
  | .terminal program selected .. => exact ⟨_, program, selected⟩
  | .binder _ _ _ body _ _ => exact body.selectedProgram
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

structure CanonicalNativeOpening (env : VEnv) (registry : CanonicalHead.Registry)
    (strata : EquationStratification env) (name : Name) where
  data : NativeRecursorData
  lookup : registry.natives name = some data
  notDefinition : registry.definitions name = none
  nameEq : data.name = name
  registered : NativeRecursorRegistered env data
  levels : List VLevel
  arguments : List VExpr
  program : SaturatedProgram data
  programSelected : data.saturatedProgram levels arguments = some program

namespace CanonicalNativeOpening
variable {env : VEnv} {registry : CanonicalHead.Registry} {strata : EquationStratification env} {name : Name}

theorem singleton
    (opening : CanonicalNativeOpening env registry strata name) :
    opening.data.singletonEquation = some opening.program.equation :=
  (saturatedProgram_spec opening.programSelected).2.2.2.2.2.2.2.2.1

noncomputable def selected
    (opening : CanonicalNativeOpening env registry strata name) :
    strata.Selected opening.program.equation :=
  strata.select (opening.registered.singletonEquation opening.singleton)

theorem headOrdinal_eq (opening : CanonicalNativeOpening env registry strata name) :
    strata.headOrdinal registry name = opening.selected.ordinal :=
  strata.headOrdinal_native opening.notDefinition opening.lookup opening.singleton
    (opening.registered.singletonEquation opening.singleton)

theorem sourceCutoff (opening : CanonicalNativeOpening env registry strata name) :
    strata.SourceCutoff opening.selected.origin.source (opening.selected.ordinal - 1) :=
  opening.selected.sourceCutoff

private theorem constants_head {expression : VExpr}
    (known : expression.ConstantsIn source) : expression.getAppFnArgs.1.ConstantsIn source := by
  induction expression with
  | app fn arg ih _ => simpa only [getAppFnArgs_app] using ih known.1
  | _ => exact known

/-- The canonical equation LHS itself contains the native recursor. Thus its
checking source contains the exact registered header, even when that source
has additional constants absent from the caller. -/
theorem signatureLookup (opening : CanonicalNativeOpening env registry strata name)
    (signature : NativeConstantSignature opening.data requestedLevels) :
    opening.selected.origin.source.constants opening.data.name =
      some { uvars := opening.data.uvars, type := signature.type } := by
  have closedBody := opening.selected.origin.strong.1.constantsIn.1
  have extracted := (saturatedProgram_spec opening.programSelected).2.2.2.2.2.2.2.2.2.1
  rw [← (CaseSchema.EquationBody.extract_sound extracted).1] at closedBody
  have bodyKnown := closedBody.wrapLams.2
  have headKnown := constants_head bodyKnown
  rw [selected_head opening.programSelected] at headKnown
  obtain ⟨actual, lookup⟩ := headKnown
  have same := Option.some.inj
    ((opening.selected.origin.sourceBelow.constants lookup).symm.trans
      (opening.registered.recursorType signature.typeOrigin))
  simpa only [same] using lookup

/-- The header proof is recovered from the canonical equation source, not
from an independently supplied native declaration history. -/
theorem signatureFormation (opening : CanonicalNativeOpening env registry strata name)
    (signature : NativeConstantSignature opening.data requestedLevels)
    (levelsWF : ∀ level ∈ requestedLevels, level.WF U) :
    ∃ level, opening.selected.origin.source.IsDefEqStrong U []
      (signature.type.instL requestedLevels) (signature.type.instL requestedLevels) (.sort level) := by
  obtain ⟨level, formation⟩ := opening.selected.origin.ordered.constWF (opening.signatureLookup signature)
  exact ⟨level.inst requestedLevels,
    (formation.strong opening.selected.origin.ordered (Γ := []) trivial).instL levelsWF⟩

/-- The original equation packet consumed by native capture replay is
constructed from the SAME canonical source as the signature formation. -/
noncomputable def originalEquation (opening : CanonicalNativeOpening env registry strata name)
    (levelsWF : ∀ level ∈ requestedLevels, level.WF U) :
    NativeOriginalEquation opening.selected.origin.source U requestedLevels opening.program.equation := by
  let pair := opening.selected.origin.strong
  have left := pair.1.instL levelsWF
  have right := pair.2.instL levelsWF
  let formation := right.isType' opening.selected.origin.ordered
    opening.selected.origin.ordered.strong (by trivial)
  exact {
    leftStructural := true
    rightStructural := true
    level := formation.choose
    left := left.hasType'.1
    right := right.hasType'.1
    formation := formation.choose_spec }

/-- Canonical native source entry has the same installed-or-missing strict
decrease as canonical delta, with the actual native head selector. -/
theorem openingDecrease (opening : CanonicalNativeOpening env registry strata name)
    (cutoff : Nat) (cutoffBound : cutoff ≤ strata.rules.length) (fuel children : Nat → Nat)
    (bounded : WithinAbove cutoff fuel
      (headDepth (strata.headOrdinal registry name) children))
    (callerConstants callerSchedule childSchedule : Nat) :
    EquationControlMeasure.Less
      (EquationControlMeasure.key strata.rules.length (opening.selected.ordinal - 1) children
        opening.selected.origin.ordered.constantCount childSchedule)
      (EquationControlMeasure.key strata.rules.length cutoff fuel callerConstants callerSchedule) := by
  rw [opening.headOrdinal_eq] at bounded
  exact EquationStratifiedFuel.openingDecrease opening.selected.ordinal_pos
    opening.selected.ordinal_le cutoffBound bounded callerConstants callerSchedule
    opening.selected.origin.ordered.constantCount childSchedule

end CanonicalNativeOpening

/-- Actual native syntax chooses the canonical rule deterministically from
its finite plan; pointwise registry registration is the only provenance input. -/
theorem NativePlan.canonicalOpening
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {data : NativeRecursorData} {levels : List VLevel} {name : Name}
    {signature : NativeConstantSignature data levels}
    (strata : EquationStratification env)
    (plan : NativePlan env U registry target signature
      arguments demand footprint)
    (lookup : registry.natives name = some data)
    (notDefinition : registry.definitions name = none)
    (nameEq : data.name = name) (registered : NativeRecursorRegistered env data) :
    ∃ opening : CanonicalNativeOpening env registry strata name, opening.data = data := by
  obtain ⟨arguments, program, selected⟩ := plan.selectedProgram
  exact ⟨⟨data, lookup, notDefinition, nameEq, registered, levels, arguments, program, selected⟩, rfl⟩

end Lean4Lean.AnchoredSource.Adapted
