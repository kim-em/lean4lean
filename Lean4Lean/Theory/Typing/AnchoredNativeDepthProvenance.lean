import Lean4Lean.Theory.Typing.DefinitionRegistryPrefix
import Lean4Lean.Theory.Typing.AnchoredNativeSourceProvenance
import Lean4Lean.Theory.Typing.AnchoredNativeDepth

/-! An observer over earlier source syntax cannot acquire newer source-native
heads through target guards, grade changes, or reconstructed certificates.
Every native child is checked against the ORIGINAL declaration in the actual
earlier registry prefix. No semantic interpretation or returned-size bound is
assumed. This supplies the missing budget bound for newly built old-stage
native observations, rather than only observations retained by constDF. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false
variable {base env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {before declarations : List VDecl} {old : Name → Option NativeRecursorData}
  {first : NativeRegistryHistory base before old}
  {last : NativeRegistryHistory env declarations registry.natives}
  (continuation : NativeRegistryHistory.Prefix first last)
  (current : Name → Bool)
  (quiet : ∀ name value, base.constants name = some value → current name = false)

private theorem constants_wrapForalls
    (known : (wrapForalls domains body).ConstantsIn base) :
    ∀ domain ∈ domains, domain.ConstantsIn base := by
  induction domains with
  | nil => simp
  | cons domain domains ih =>
    intro d member
    rcases List.mem_cons.mp member with rfl | member
    · exact known.1
    · exact ih known.2 d member

private theorem constants_wrapForalls_result
    (known : (wrapForalls domains body).ConstantsIn base) : body.ConstantsIn base := by
  induction domains with
  | nil => exact known
  | cons domain domains ih => exact ih known.2

include continuation quiet in
mutual
theorem Obs.nativeDepth_of_constants
    (observation : Obs env U registry target locals σ expression demand footprint)
    (known : expression.ConstantsIn base) : observation.nativeDepth current = 0 := by
  match observation with
  | .delta (name := name) (seedLevels := seedLevels) lookup nameEq registered seedWF seedLength levelsWF equivalent
      bodyClosed typeClosed certificate typed body =>
    obtain ⟨constant, present⟩ := known
    have finalLookup := last.history.definitionLookup registered
    rw [nameEq] at finalLookup
    obtain ⟨origin⟩ := first.history.definitionOrigin (continuation.previous_definition present finalLookup)
    have bodyKnown := (origin.bodyConstants.mono origin.header_le).instL seedLevels
    have typeKnown := (origin.bodyStrong.typeConstantsIn.mono origin.header_le).instL seedLevels
    simp only [Obs.nativeDepth, body.nativeDepth_of_constants bodyKnown,
      certificate.nativeDepth_of_constants typeKnown, quiet name constant present,
      Bool.false_eq_true, ↓reduceIte, Nat.max_self, Nat.add_zero]
  | .native (name := name) (seedLevels := seedLevels) lookup notDefinition nameEq registered seedWF levelsWF equivalent
      signature typeClosed certificate typed tree =>
    obtain ⟨value, present⟩ := known
    obtain ⟨_, ⟨origin⟩⟩ := first.origin (continuation.previous_lookup present lookup)
    have typeKnown := (origin.typeConstants signature.typeOrigin).instL seedLevels
    simp only [Obs.nativeDepth, tree.nativeDepth_of_origin origin,
      certificate.nativeDepth_of_constants typeKnown,
      quiet name value present, Bool.false_eq_true, ↓reduceIte, Nat.max_self, Nat.add_zero]
  | .family (name := name) (seedLevels := seedLevels) lookup notDefinition notNative notQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    obtain ⟨value, present⟩ := known
    have same := Option.some.inj ((continuation.le.constants present).symm.trans lookup)
    subst value
    have ordered := (show base.WF from ⟨before, first.history⟩).ordered
    obtain ⟨_, formation⟩ := ordered.constWF present
    have typeKnown := ((formation.strong ordered (show OnCtx [] (base.IsType _) from trivial)).constantsIn.1).instL seedLevels
    simp only [Obs.nativeDepth, tree.nativeDepth_of_constants typeKnown,
      certificate.nativeDepth_of_constants typeKnown, Nat.max_self]
  | .constructor (name := name) (seedLevels := seedLevels) lookup notDefinition notNative notQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    obtain ⟨value, present⟩ := known
    have same := Option.some.inj ((continuation.le.constants present).symm.trans lookup)
    subst value
    have ordered := (show base.WF from ⟨before, first.history⟩).ordered
    obtain ⟨_, formation⟩ := ordered.constWF present
    have typeKnown := ((formation.strong ordered (show OnCtx [] (base.IsType _) from trivial)).constantsIn.1).instL seedLevels
    simp only [Obs.nativeDepth, tree.nativeDepth_of_constants typeKnown,
      certificate.nativeDepth_of_constants typeKnown, Nat.max_self]
  | .var .. | .empty | .sort .. => simp only [Obs.nativeDepth]
  | .app fn arg adapter admitted =>
    simp only [Obs.nativeDepth,
      fn.nativeDepth_of_constants known.1,
      arg.nativeDepth_of_constants known.2, Nat.max_self]
  | .lam domain guard body pack covered =>
    simp only [Obs.nativeDepth,
      domain.nativeDepth_of_constants known.1,
      body.nativeDepth_of_constants known.2, Nat.max_self]
  | .pi domain guard bodies =>
    simp only [Obs.nativeDepth,
      domain.nativeDepth_of_constants known.1,
      bodies.nativeDepth_of_constants known.2, Nat.max_self]
  | .union left right =>
    simp only [Obs.nativeDepth,
      left.nativeDepth_of_constants known,
      right.nativeDepth_of_constants known, Nat.max_self]
  | .view child _ | .pad child | .unpad child | .rowShift child =>
    simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using child.nativeDepth_of_constants known
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

theorem CodeCert.nativeDepth_of_constants
    (certificate : CodeCert env U registry target locals σ expression demand footprint)
    (known : expression.ConstantsIn base) : certificate.nativeDepth current = 0 := by
  match certificate with
  | .seed child _ => simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using child.nativeDepth_of_constants known
  | .union left right =>
    simp only [CodeCert.nativeDepth,
      left.nativeDepth_of_constants known,
      right.nativeDepth_of_constants known, Nat.max_self]
  | .pad child | .familyPad child | .unpad child | .down child | .map _ child | .select child _ | .focusMinimal child _ _ =>
    simpa only [Obs.nativeDepth, CodeCert.nativeDepth] using child.nativeDepth_of_constants known
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; omega

theorem PiRows.nativeDepth_of_constants
    (rows : PiRows env U registry target locals σ A B ambient rowList footprint)
    (known : B.ConstantsIn base) : rows.nativeDepth current = 0 := by
  match rows with
  | .nil => simp only [PiRows.nativeDepth]
  | .cons guard body pack covered tail =>
    simp only [PiRows.nativeDepth,
      body.nativeDepth_of_constants known,
      tail.nativeDepth_of_constants known, Nat.max_self]
termination_by sizeOf rows
decreasing_by all_goals simp_wf; omega

theorem NativeCaptures.nativeDepth_of_origin {data : NativeRecursorData}
    {program : SaturatedProgram data}
    (captures : NativeCaptures env U registry target program witnesses index required outside)
    (origin : NativeDeclarationOrigin base before data) : captures.nativeDepth current = 0 := by
  match captures with
  | .prefix _ => simp only [NativeCaptures.nativeDepth]
  | .index (templates := templates) natural _ declared _ _ _ _ _ _ _ _ _ previous =>
    have known := origin.indexConstants templates
    simp only [NativeCaptures.nativeDepth,
      natural.nativeDepth_of_constants known.1,
      declared.nativeDepth_of_constants known.2,
      previous.nativeDepth_of_origin origin, Nat.max_self]
  | .proof _ _ _ _ _ _ previous =>
    simpa only [NativeCaptures.nativeDepth] using previous.nativeDepth_of_origin origin
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

theorem NativePlan.nativeDepth_of_origin {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels}
    (plan : NativePlan env U registry target signature arguments demand footprint)
    (origin : NativeDeclarationOrigin base before data) : plan.nativeDepth current = 0 := by
  match plan with
  | .terminal program selected _ _ _ _ _ _ _ _ _ _ body captures =>
    have known := ((origin.programConstants selected).2).instL levels
    simp only [NativePlan.nativeDepth,
      body.nativeDepth_of_constants known,
      captures.nativeDepth_of_origin origin, Nat.max_self]
  | .binder member domain guard body pack covered =>
    have known := origin.signatureDomainConstants signature member
    simp only [NativePlan.nativeDepth,
      domain.nativeDepth_of_constants known,
      body.nativeDepth_of_origin origin, Nat.max_self]
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

theorem FamilyCaptures.nativeDepth_of_constants
    (captures : FamilyCaptures env U registry target source locals σ expressions keys footprint)
    (known : ∀ expression ∈ expressions, expression.ConstantsIn base) :
    captures.nativeDepth current = 0 := by
  match captures with
  | .nil => simp only [FamilyCaptures.nativeDepth]
  | .cons lookup value adapter alignment anchor tail =>
    simp only [FamilyCaptures.nativeDepth,
      value.nativeDepth_of_constants (known _ List.mem_cons_self),
      tail.nativeDepth_of_constants (fun e member => known e (List.mem_cons_of_mem _ member)),
      Nat.max_self]
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

theorem FamilyPlan.nativeDepth_of_constants
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    (plan : FamilyPlan env U registry target name levels signature arguments demand footprint)
    (known : declaredType.ConstantsIn base) : plan.nativeDepth current = 0 := by
  match plan with
  | .terminal saturated resultSort relevance captures =>
    simp only [FamilyPlan.nativeDepth]
    apply captures.nativeDepth_of_constants
    intro expression member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    trivial
  | .binder origin domain guard body pack covered =>
    have domainKnown := constants_wrapForalls (signature.type_eq ▸ known) _ (List.mem_of_getElem? origin)
    simp only [FamilyPlan.nativeDepth,
      domain.nativeDepth_of_constants domainKnown,
      body.nativeDepth_of_constants known, Nat.max_self]
  | .view source view | .pad source =>
    simpa only [FamilyPlan.nativeDepth] using source.nativeDepth_of_constants known
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega
theorem ConstructorPlan.nativeDepth_of_constants
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType}
    (plan : ConstructorPlan env U registry target name levels signature arguments demand footprint)
    (known : declaredType.ConstantsIn base) : plan.nativeDepth current = 0 := by
  match plan with
  | .terminal saturated resultShape relevance captures resultCode =>
    have captureDepth := captures.nativeDepth_of_constants (fun expression member => by
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      trivial)
    have resultKnown := constants_wrapForalls_result (signature.type_eq ▸ known)
    simp only [ConstructorPlan.nativeDepth, captureDepth,
      resultCode.nativeDepth_of_constants resultKnown, Nat.max_self]
  | .binder origin domain guard body pack covered =>
    have domainKnown := constants_wrapForalls (signature.type_eq ▸ known) _ (List.mem_of_getElem? origin)
    simp only [ConstructorPlan.nativeDepth,
      domain.nativeDepth_of_constants domainKnown,
      body.nativeDepth_of_constants known, Nat.max_self]
  | .view source view | .pad source =>
    simpa only [ConstructorPlan.nativeDepth] using source.nativeDepth_of_constants known
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

end

include continuation quiet

/-- The source fact comes from the given original derivation, while the
observer is arbitrary and may have been newly constructed by factorization. -/
theorem Obs.nativeDepth_of_original
    (observation : Obs env U registry target locals σ expression demand footprint)
    (original : base.IsDefEqStrong sourceU source expression right type) :
    observation.nativeDepth current = 0 :=
  observation.nativeDepth_of_constants continuation current quiet original.constantsIn.1

theorem CodeCert.nativeDepth_of_original
    (certificate : CodeCert env U registry target locals σ expression demand footprint)
    (original : base.IsDefEqStrong sourceU source expression right type) :
    certificate.nativeDepth current = 0 :=
  certificate.nativeDepth_of_constants continuation current quiet original.constantsIn.1

end Lean4Lean.AnchoredSource.Adapted

namespace Lean4Lean.VInductBlock.TypingStages
open VEnv

/-- Freshness comes from the real recursor installation, even though types,
constructors, and projection metadata have already been installed. -/
theorem currentNames_old {base installed : VEnv} {block : VInductBlock}
    (stages : TypingStages base block installed)
    (present : base.constants name = some value) :
    block.recursors.any (fun recursor => recursor.name == name) = false := by
  cases selected : block.recursors.any (fun recursor => recursor.name == name) with
  | false => rfl
  | true =>
    obtain ⟨recursor, member, equal⟩ := List.any_eq_true.mp selected
    have fresh := VEnv.addConstVals_names_fresh stages.addRecursors recursor member
    have below : base ≤ stages.constructors.addProjections block.projections :=
      (VEnv.addConstVals_le stages.addTypes).trans
        ((VEnv.addConstVals_le stages.addConstructors).trans VEnv.addProjections_le)
    have contradiction := below.constants present
    have same : recursor.name = name := by simpa only [beq_iff_eq] using equal
    rw [← same, fresh] at contradiction
    cases contradiction

end Lean4Lean.VInductBlock.TypingStages

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles
variable {base env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
  {before declarations : List VDecl} {old : Name → Option InductiveSignature.NativeRecursorData}
  {first : NativeRegistryHistory base before old}
  {last : NativeRegistryHistory env declarations registry.natives}

theorem Obs.nativeDepth_beforeBlock
    (continuation : NativeRegistryHistory.Prefix first last)
    (stages : VInductBlock.TypingStages base block installed)
    (observation : Obs env U registry target locals σ expression demand footprint)
    (original : base.IsDefEqStrong sourceU source expression right type) :
    observation.nativeDepth (fun name => block.recursors.any (fun value => value.name == name)) = 0 :=
  observation.nativeDepth_of_original continuation _
    (fun _ _ present => stages.currentNames_old present) original

theorem CodeCert.nativeDepth_beforeBlock
    (continuation : NativeRegistryHistory.Prefix first last)
    (stages : VInductBlock.TypingStages base block installed)
    (certificate : CodeCert env U registry target locals σ expression demand footprint)
    (original : base.IsDefEqStrong sourceU source expression right type) :
    certificate.nativeDepth (fun name => block.recursors.any (fun value => value.name == name)) = 0 :=
  certificate.nativeDepth_of_original continuation _
    (fun _ _ present => stages.currentNames_old present) original

end Lean4Lean.AnchoredSource.Adapted
