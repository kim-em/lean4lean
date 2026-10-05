import Lean4Lean.Theory.Typing.AnchoredOriginalSortableEtaData
import Lean4Lean.Theory.Typing.AnchoredSortableBudgetPiExtraction
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

structure BudgetEtaExpansionResult (budgets : HereditaryBudgeted.Budgets) (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat)
    (σ τ : Subst) (available : Valuation) (A B f : VExpr) (demand : Profile n)
    extends SortableEtaExpansionResult env U registry target locals σ τ available A B f demand where
  observationBound : HereditaryBudgeted.Within budgets observation.nativeDepth
  certificateBound : HereditaryBudgeted.Within budgets certificate.nativeDepth

def BudgetEtaExpansionResult.empty :
    BudgetEtaExpansionResult budgets env U registry target locals σ τ available A B f (Profile.empty (n := n)) where
  toSortableEtaExpansionResult := .empty
  observationBound := by intro current fuel member; simp only [SortableEtaExpansionResult.empty, SortableObs.nativeDepth, Obs.nativeDepth]; exact Nat.zero_le _
  certificateBound := by intro current fuel member; simp only [SortableEtaExpansionResult.empty, SortableCert.nativeDepth, Obs.nativeDepth]; exact Nat.zero_le _

noncomputable def BudgetEtaExpansionResult.union
    (henv : env.Ordered)
    (a : BudgetEtaExpansionResult budgets env U registry target locals σ τ available A B f (p : Profile n))
    (b : BudgetEtaExpansionResult budgets env U registry target locals σ τ available A B f (q : Profile n)) :
    BudgetEtaExpansionResult budgets env U registry target locals σ τ available A B f (p.union q) where
  toSortableEtaExpansionResult := a.toSortableEtaExpansionResult.union henv b.toSortableEtaExpansionResult
  observationBound := by
    intro current fuel member
    simp only [SortableEtaExpansionResult.union, SortableObs.nativeDepth]
    exact Nat.max_le.mpr ⟨a.observationBound current fuel member, b.observationBound current fuel member⟩
  certificateBound := by
    intro current fuel member
    simp only [SortableEtaExpansionResult.union, SortableCert.nativeDepth]
    exact Nat.max_le.mpr ⟨a.certificateBound current fuel member, b.certificateBound current fuel member⟩

end Lean4Lean.AnchoredSource.Adapted
