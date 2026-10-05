import Lean4Lean.Theory.Typing.AnchoredSortableBudgetResults
import Lean4Lean.Theory.Typing.AnchoredSortableSortResult

/-! Exact formation results keep source sort relevance separate from the
requested formation flag, with the same caller bounds on the finite code. -/
namespace Lean4Lean.AnchoredSource.Adapted.HereditaryBudgeted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

structure SortResult (budgets : Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (σ τ : Subst) (available : Valuation)
    (left right : VExpr) (requestedFlag actualFlag : Bool) (profile : Profile n)
    extends SortableSortResult env U registry target locals σ τ available
      left right requestedFlag actualFlag profile where
  bounded : Within budgets certificate.nativeDepth

theorem Result.atSort
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (result : Result budgets env U registry target locals σ τ available left right (.sort level) profile)
    (requested : profile.HasType (.sort requestedFlag)) (actual : Relevant level actualFlag) :
    Nonempty (SortResult budgets env U registry target locals σ τ available
      left right requestedFlag actualFlag profile) := by
  obtain ⟨footprint, certificate, resources, depth⟩ := result.toSortableGradedResult.code_allDepth henv closed requested
  exact ⟨{
    footprint := footprint, certificate := certificate, available := resources
    related := (result.requestedRelated henv hTarget).code_of_sortable henv hscoped hTarget requested
    sorted := TypeRelated.sort_typed hTarget actual
      (result.typeCode.lower henv result.bound) result.requestedTyped
    bounded := fun current fuel member => Nat.le_trans (depth current) (result.observationBound current fuel member) }⟩

noncomputable def SortResult.computational
    (henv : env.Ordered)
    (result : SortResult budgets env U registry target locals σ τ available left right requestedFlag actualFlag profile)
    (levelWF : level.WF U) (actual : Relevant level actualFlag) :
    Result budgets env U registry target locals σ τ available left right (.sort level) profile where
  toSortableComputationalTransferResult := result.toSortableSortResult.computational henv levelWF actual
  observationBound := by
    intro current fuel member
    simpa only [SortableSortResult.computational, SortableObs.nativeDepth] using result.bounded current fuel member
  certificateBound := by
    intro current fuel member
    simp only [SortableSortResult.computational, SortableCert.nativeDepth, Obs.nativeDepth]
    exact Nat.zero_le _

end Lean4Lean.AnchoredSource.Adapted.HereditaryBudgeted
