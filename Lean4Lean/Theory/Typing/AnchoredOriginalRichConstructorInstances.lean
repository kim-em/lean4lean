import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstructorPlanInterpretation
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSubstitution
import Lean4Lean.Theory.Typing.AnchoredLevels
import Lean4Lean.Theory.Typing.AnchoredLiveInterpretation

/-! A native family plan keeps its original seed header and all rich
declared-domain children when the displayed universe packet changes. Only
the target semantic relation moves between equivalent universe instances. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1600000

/-- The output observer retains the same original seed certificate and
plan. Its assigned-type certificate is deliberately not relabelled: that
separate channel must follow the actual displayed header/ambient origins. -/
theorem RichConstructorPlan.transferInstances
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceOrdered : sourceEnv.Ordered)
    (sourceBelow : sourceEnv ≤ env)
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (seedWF : ∀ level ∈ seedLevels, level.WF U) (seedCount : seedLevels.length = info.uvars)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (seedLeft : List.Forall₂ (· ≈ ·) seedLevels leftLevels)
    (seedRight : List.Forall₂ (· ≈ ·) seedLevels rightLevels)
    (typeClosed : info.type.Closed) (formed : OnCtx target (env.IsType U))
    (certificate : RichCert origin.source env U registry target
      (.ref (origin.familyHeader seedWF).reference) [] typeRealization true support [])
    (typed : demand.HasType support)
    (plan : RichConstructorPlan env U registry target (origin.familyHeader seedWF).reference
      name seedLevels signature .nil planRealization [] demand [])
    (bank : OriginalLowerCallBank env U registry limit)
    (headerBound : richSchedule .fundamental
      (Closure.close ((origin.familyHeader seedWF).reference.dependencyOrigin origin.ordered) []).cost < limit)
    {right : EndpointState sourceEnv U source (.const name rightLevels) assigned}
    {locals : List Nat} {τ : Subst} {available : Valuation} :
    TypeRelated env U registry target (info.type.instL leftLevels) (info.type.instL leftLevels) support ∧
      Related env U registry target (.const name leftLevels) (.const name rightLevels)
        (info.type.instL leftLevels) demand support ∧
      Nonempty (RichGradedResult sourceEnv env U registry target right locals τ available demand) := by
  have emptyClosed : Valuation.AtomClosed (fun _ => []) := by intro _ _ member; cases member
  have ambient : (OriginalRichFrame.nil (sourceEnv := origin.source) (U := U)
      (locals := []) (σ := typeRealization) (τ := typeRealization)
      (available := fun _ => []) (env := env) (registry := registry) (target := target)).Ambient :=
    by
      change (RawOriginalRichFrame.nil : RawOriginalRichFrame origin.source env U registry target
        .nil [] typeRealization typeRealization (fun _ => [])).Ambient
      rw [RawOriginalRichFrame.Ambient.eq_def]
      exact ⟨origin.sourceBelow.trans sourceBelow, trivial⟩
  obtain ⟨computed⟩ := bank.computational origin.ordered (origin.sourceBelow.trans sourceBelow)
    .nil (.here (root := (origin.familyHeader seedWF).reference)) target [] typeRealization typeRealization
    (fun _ => []) .nil ambient headerBound emptyClosed formed .nil (.code certificate)
    (fun _ _ member => nomatch member)
  obtain ⟨answer⟩ := computed.code henv hscoped formed certificate.formed
  have seedCode : TypeRelated env U registry target (info.type.instL seedLevels)
      (info.type.instL seedLevels) support := by
    simpa only [typeClosed.instL.subst_eq (σ := typeRealization) .zero] using answer.related
  have seedRelated := plan.bareSupported henv hscoped origin.ordered (origin.sourceBelow.trans sourceBelow)
    bank headerBound lookup seedWF seedCount notDefinition notNative notQuotient typeClosed formed typed seedCode
  have seedSelf : List.Forall₂ (· ≈ ·) seedLevels seedLevels :=
    Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl)
  have typeSelf := EqUpToLevels.instL_expr info.type seedWF seedWF seedSelf
  have typeLeft := EqUpToLevels.instL_expr info.type seedWF leftWF seedLeft
  have code := seedCode.levels henv typeLeft typeLeft
  have bridge := seedCode.levels henv typeSelf typeLeft
  have related := (seedRelated.levels henv (.const seedWF leftWF seedLeft)
    (.const seedWF rightWF seedRight)).convert henv typed bridge
  refine ⟨code, related, ⟨{
    rank := _
    bound := Nat.le_refl _
    raw := demand
    footprint := []
    observation := .constructor origin lookup notDefinition notNative notQuotient seedWF seedCount
      rightWF seedRight signature typeClosed certificate typed plan
    adapter := ?_
    resources := fun _ _ member => nomatch member
    live := related.live henv hscoped formed }⟩⟩
  simpa only [raiseProfile_self] using
    (show GeneralNormalProfileAdapter env U registry target demand demand from .refl _)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
