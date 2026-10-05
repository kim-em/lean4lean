import Lean4Lean.Theory.Typing.AnchoredOriginalStagedLowerCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeAction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorPlanResult

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1200000

/-- Independently retained headers of the same actual constant are compared
at the same seed. The returned certificate uses the destination's original
header and its exact empty resource table; no metadata proof is opened. -/
theorem StagedOriginalLowerCallBank.closedCodeReindex
    {leftEnv rightEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {name : Name} {info : VConstant}
    (henv : env.Ordered)
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (leftOrigin : ConstantHeaderOrigin leftEnv name info)
    (rightOrigin : ConstantHeaderOrigin rightEnv name info)
    (leftOrdered : leftEnv.Ordered) (rightOrdered : rightEnv.Ordered)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftStage : SourceAtStage stage leftEnv) (rightStage : SourceAtStage stage rightEnv)
    {levels : List VLevel} (levelsWF : ∀ level ∈ levels, level.WF U)
    {target : List VExpr} {σ : Subst} {n : Nat} {profile : Profile n}
    (certificate : RichCert leftOrigin.source env U registry target
      (.ref (leftOrigin.familyHeader levelsWF).reference) [] σ relevant profile []) :
    ∃ footprint, Nonempty (RichCert rightOrigin.source env U registry target
      (.ref (rightOrigin.familyHeader levelsWF).reference) [] σ relevant profile footprint) ∧
      footprint.Available (fun _ => []) := by
  let callStage := max leftOrigin.ordered.constantCount rightOrigin.ordered.constantCount
  let rightFrame := OriginalRichFrame.nil (sourceEnv := rightOrigin.source) (env := env)
    (U := U) (registry := registry) (target := target) (locals := [])
    (σ := σ) (τ := σ) (available := fun _ => [])
  let base := rightFrame.captureBase (.nil : Ctx.SubstEq env U target σ σ [])
  let rightProvenance : EndpointProvenance (ContextDerivation.nil (env := rightOrigin.source))
      (.ref (rightOrigin.familyHeader levelsWF).reference) :=
    .ofLocation (.here (root := (rightOrigin.familyHeader levelsWF).reference)) .nil
  let right := OriginalNestedDisplay.identity base
    (.ref (rightOrigin.familyHeader levelsWF).reference) rightProvenance
  let left : OriginalNestedDisplay U [] (info.type.instL levels)
      (.sort (leftOrigin.familyHeader levelsWF).level) := {
    sourceEnv := leftOrigin.source
    source := []
    sourceExpression := info.type.instL levels
    sourceType := .sort (leftOrigin.familyHeader levelsWF).level
    context := .nil
    node := .ref (leftOrigin.familyHeader levelsWF).reference
    provenance := .ofLocation (.here (root := (leftOrigin.familyHeader levelsWF).reference)) .nil
    raw := .id
    graph := .empty []
    expression_eq := subst_id.symm
    type_eq := subst_id.symm }
  let leftFrame : OriginalCaptureRealization left.graph env registry target [] σ σ
      (fun _ => []) := ⟨.nil, .nil⟩
  have leftGenerated : SourceCaptureGenerated (SourceAtStage callStage) base base.initialCaps
      σ σ left.graph leftFrame.frame.raw :=
    .empty [] σ σ (leftOrigin.sourceBelow.trans leftBelow)
      (fun _ => Nat.le_max_left _ _)
  have rightAmbient : rightFrame.Ambient := by
    change RawOriginalRichFrame.Ambient (.nil (sourceEnv := rightOrigin.source) (env := env))
    rw [RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨rightOrigin.sourceBelow.trans rightBelow, trivial⟩
  have rightSources : rightFrame.raw.AllSources (SourceAtStage callStage) := by
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨fun _ => Nat.le_max_right _ _, trivial⟩
  have rightGenerated : SourceCaptureGenerated (SourceAtStage callStage) base base.initialCaps
      σ σ right.graph base.identityRealization.frame.raw := .identity rightAmbient rightSources
  have closed : Valuation.AtomClosed (fun _ => []) := by intro _ _ member; cases member
  have lower : callStage < stage := Nat.max_lt.mpr
    ⟨originalHeader_stage_lt leftOrigin leftOrdered leftStage,
      originalHeader_stage_lt rightOrigin rightOrdered rightStage⟩
  obtain ⟨reply⟩ := bank.observation callStage base base.initialCaps left right σ σ
    leftOrigin.ordered rightOrigin.ordered leftFrame leftGenerated closed
    base.identityRealization rightGenerated closed (.left _ _ lower)
    (.code certificate) (by intro _ _ member; cases member)
  exact reply.answer.freezeBase.code henv certificate.formed

/-- A concrete nullary constructor is rebuilt at an independently retained
original constant endpoint. Its seed and complete family descriptor stay
unchanged; only the actual closed header certificate is reindexed. -/
theorem StagedOriginalLowerCallBank.nullaryConstructorReindex
    {leftEnv rightEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {name : Name} {info : VConstant}
    (henv : env.Ordered)
    (bank : StagedOriginalLowerCallBank env U registry stage limit)
    (leftOrigin : ConstantHeaderOrigin leftEnv name info)
    (rightOrigin : ConstantHeaderOrigin rightEnv name info)
    (leftOrdered : leftEnv.Ordered) (rightOrdered : rightEnv.Ordered)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (leftStage : SourceAtStage stage leftEnv) (rightStage : SourceAtStage stage rightEnv)
    {seedLevels levels : List VLevel}
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (seedLength : seedLevels.length = info.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none)
    (notQuotient : name ≠ ``Quot.lift)
    {target : List VExpr} {σ : Subst} {n : Nat}
    {family : FamilyData (Profile n)} (relevant : family.relevant = true)
    {familyLevels : List VLevel} {familyArguments : List VExpr}
    (resultShape : info.type.instL seedLevels =
      mkApps (.const family.name familyLevels) familyArguments)
    {typeSupport : Profile (n + 1)}
    (certificate : RichCert leftOrigin.source env U registry target
      (.ref (leftOrigin.familyHeader seedWF).reference) [] σ true typeSupport [])
    (typed : (Profile.singleton (n := n + 1)
      (.ctor ⟨name, seedLevels, [], family, relevant⟩)).HasType typeSupport)
    {source : List VExpr} {assigned : VExpr}
    {node : EndpointState rightEnv U source (.const name levels) assigned}
    {locals : List Nat} {realization : Subst} :
    Nonempty (RichObs rightEnv env U registry target node locals realization
      (Profile.singleton (n := n + 1) (.ctor ⟨name, seedLevels, [], family, relevant⟩)) []) := by
  have familyCertificate := RichCert.select certificate typed.ctor_family_mem
  obtain ⟨footprint, ⟨moved⟩, resources⟩ := bank.closedCodeReindex henv
    leftOrigin rightOrigin leftOrdered rightOrdered leftBelow rightBelow leftStage rightStage
    seedWF familyCertificate
  have empty : footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry member
    exact List.not_mem_nil (resources entry.1 entry.2 member)
  subst footprint
  let signature : ConstantTelescope (info.type.instL seedLevels) := ⟨[], _, rfl⟩
  let answer := RichConstructorPlanResult.terminal
    (header := (rightOrigin.familyHeader seedWF).reference)
    (signature := signature) (name := name) (levels := seedLevels)
    (context := .nil) (σ := σ) (arguments := [])
    (available := fun _ => []) rfl resultShape relevant
    (.here (root := (rightOrigin.familyHeader seedWF).reference)) rfl
    FamilyCaptures.nil moved
    (by intro _ _ member; cases member) resources
  exact ⟨.constructor rightOrigin
    (rightBelow.constants rightOrigin.constant) notDefinition notNative notQuotient
    seedWF seedLength levelsWF equivalent signature
    (henv.closedC (rightBelow.constants rightOrigin.constant))
    moved answer.typed answer.plan⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
