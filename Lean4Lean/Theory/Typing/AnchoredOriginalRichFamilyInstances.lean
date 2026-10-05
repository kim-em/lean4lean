import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanInterpretation
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

/-- The output observer retains the same original seed certificate and
plan. Its assigned-type certificate is deliberately not relabelled: that
separate channel must follow the actual displayed header/ambient origins. -/
theorem RichFamilyPlan.transferInstances
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
    (plan : RichFamilyPlan env U registry target (origin.familyHeader seedWF).reference
      name seedLevels signature .nil planRealization [] demand [])
    (headerF : origin.ordered.constantCount < sourceOrdered.constantCount →
      RichCert origin.source env U registry target (.ref (origin.familyHeader seedWF).reference)
        [] typeRealization true support [] →
      Nonempty (RichCodeTransferResult env U registry target
        (.ref (origin.familyHeader seedWF).reference) (.ref (origin.familyHeader seedWF).reference)
        [] typeRealization typeRealization (fun _ => []) true support))
    {right : EndpointState sourceEnv U source (.const name rightLevels) assigned}
    {locals : List Nat} {τ : Subst} {available : Valuation} :
    TypeRelated env U registry target (info.type.instL leftLevels) (info.type.instL leftLevels) support ∧
      Related env U registry target (.const name leftLevels) (.const name rightLevels)
        (info.type.instL leftLevels) demand support ∧
      Nonempty (RichGradedResult sourceEnv env U registry target right locals τ available demand) := by
  obtain ⟨answer⟩ := headerF (origin.count_lt sourceOrdered) certificate
  have seedCode : TypeRelated env U registry target (info.type.instL seedLevels)
      (info.type.instL seedLevels) support := by
    simpa only [typeClosed.instL.subst_eq (σ := typeRealization) .zero] using answer.related
  have seedRelated := plan.bareSupported henv hscoped (origin.sourceBelow.trans sourceBelow)
    (.const lookup seedWF seedCount) notDefinition notNative notQuotient typeClosed.instL formed typed seedCode
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
    observation := .family origin lookup notDefinition notNative notQuotient seedWF seedCount
      rightWF seedRight signature typeClosed certificate typed plan
    adapter := ?_
    resources := fun _ _ member => nomatch member
    live := related.live henv hscoped formed }⟩⟩
  simpa only [raiseProfile_self] using
    (show GeneralNormalProfileAdapter env U registry target demand demand from .refl _)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
