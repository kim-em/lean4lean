import Lean4Lean.Theory.Typing.AnchoredOriginalStagedConstructorSpineReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 2000000

private def undoExpressionCast
    {node : EndpointState sourceEnv U source expression assigned}
    (same : expression = next)
    (certificate : RichCert sourceEnv env U registry target (node.cast same rfl)
      locals σ relevant profile footprint) :
    RichCert sourceEnv env U registry target node locals σ relevant profile footprint := by
  cases same
  exact certificate

/-- Full constructor-query reconstruction at an independently retained
original constant occurrence. The destination header spine and every
selected frame are computed. Record metadata and raw projection origins
travel unchanged, even if absent from the destination source environment. -/
theorem StagedOriginalLowerCallBank.constructorReindex
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
    {target : List VExpr} {σ : Subst} {demand : Profile n}
    {signature : ConstantTelescope (info.type.instL seedLevels)}
    (plan : RichConstructorPlan env U registry target
      (leftOrigin.familyHeader seedWF).reference name seedLevels signature .nil σ [] demand [])
    {source : List VExpr} {assigned : VExpr}
    {node : EndpointState rightEnv U source (.const name levels) assigned}
    {locals : List Nat} {realization : Subst} :
    Nonempty (RichObs rightEnv env U registry target node locals realization demand []) := by
  let callStage := max leftOrigin.ordered.constantCount rightOrigin.ordered.constantCount
  let rightFrame := OriginalRichFrame.nil (sourceEnv := rightOrigin.source) (env := env)
    (U := U) (registry := registry) (target := target) (locals := [])
    (σ := σ) (τ := σ) (available := fun _ => [])
  let base := rightFrame.captureBase (.nil : Ctx.SubstEq env U target σ σ [])
  let leftGraph : OriginalCaptureMap (common := [])
      (ContextDerivation.nil (env := leftOrigin.source) (U := U)) Subst.id := .empty []
  let rightGraph : OriginalCaptureMap (common := [])
      (ContextDerivation.nil (env := rightOrigin.source) (U := U)) Subst.id := .identity .nil
  let leftFrame : OriginalCaptureRealization leftGraph env registry target [] σ σ
      (fun _ => []) := ⟨.nil, .nil⟩
  have leftGenerated : SourceCaptureGenerated (SourceAtStage callStage) base base.initialCaps
      σ σ leftGraph leftFrame.frame.raw :=
    .empty [] σ σ (leftOrigin.sourceBelow.trans leftBelow) (fun _ => Nat.le_max_left _ _)
  have rightAmbient : rightFrame.Ambient := by
    change RawOriginalRichFrame.Ambient (.nil (sourceEnv := rightOrigin.source) (env := env))
    rw [RawOriginalRichFrame.Ambient.eq_def]
    exact ⟨rightOrigin.sourceBelow.trans rightBelow, trivial⟩
  have rightSources : rightFrame.raw.AllSources (SourceAtStage callStage) := by
    rw [RawOriginalRichFrame.AllSources.eq_def]
    exact ⟨fun _ => Nat.le_max_right _ _, trivial⟩
  have rightGenerated : SourceCaptureGenerated (SourceAtStage callStage) base base.initialCaps
      σ σ rightGraph base.identityRealization.frame.raw := .identity rightAmbient rightSources
  have closed : Valuation.AtomClosed (fun _ => []) := by intro _ _ member; cases member
  have lower : callStage < stage := Nat.max_lt.mpr
    ⟨originalHeader_stage_lt leftOrigin leftOrdered leftStage,
      originalHeader_stage_lt rightOrigin rightOrdered rightStage⟩
  let destination := (EndpointState.ref (rightOrigin.familyHeader seedWF).reference).cast signature.type_eq rfl
  let location : Located (rightOrigin.familyHeader seedWF).reference destination :=
    Located.here.castExpression signature.type_eq
  have lineage : location.contextDerivation .nil = .nil := by
    change (Located.here.castExpression signature.type_eq).contextDerivation .nil = _
    rw [Located.castExpression_contextDerivation]
    rfl
  obtain ⟨spine⟩ := originalConstructorSpine location lineage
  obtain ⟨answer⟩ := plan.reindexSpine (footprint := []) (arguments := []) henv bank lower leftOrigin.ordered rightOrigin.ordered
    (leftOrigin.sourceBelow.trans leftBelow) (rightOrigin.sourceBelow.trans rightBelow)
    leftFrame leftGenerated closed base.identityRealization rightGenerated closed
    (by intro _ _ member; cases member) rfl spine (by intro _ _ member; cases member)
  have availableEmpty : ∀ index need, need ∈ answer.nextAvailable index → False := by
    intro index need member
    exact List.not_mem_nil (answer.generation.capped.availableBound index need member)
  have footprintEmpty : answer.result.footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry member
    exact availableEmpty entry.1 entry.2 (answer.result.resources entry.1 entry.2 member)
  have typeFootprintEmpty : answer.result.typeFootprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry member
    exact availableEmpty entry.1 entry.2 (answer.result.typeResources entry.1 entry.2 member)
  have finalPlan : RichConstructorPlan env U registry target
      (rightOrigin.familyHeader seedWF).reference name seedLevels signature .nil σ [] demand [] :=
    footprintEmpty ▸ answer.result.plan
  have finalCode : RichCert rightOrigin.source env U registry target
      (.ref (rightOrigin.familyHeader seedWF).reference) [] σ true answer.result.support [] :=
    typeFootprintEmpty ▸ undoExpressionCast signature.type_eq answer.result.certificate
  exact ⟨.constructor rightOrigin (rightBelow.constants rightOrigin.constant)
    notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature
    (henv.closedC (rightBelow.constants rightOrigin.constant)) finalCode answer.result.typed finalPlan⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
