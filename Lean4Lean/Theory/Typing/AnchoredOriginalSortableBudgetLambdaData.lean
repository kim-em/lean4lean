import Lean4Lean.Theory.Typing.AnchoredOriginalSortableLambdaData
import Lean4Lean.Theory.Typing.AnchoredSortableBudgetJoint
import Lean4Lean.Theory.Typing.AnchoredSortableTailDepthFuture
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
structure BudgetLambdaTypeResult (budgets : HereditaryBudgeted.Budgets) (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (realization : Subst) (available : Valuation)
    (localNeeds : List Need) (A B body other : VExpr) (key : Key n) (output : Atom n) (domain : Profile n)
    extends SortableLambdaTypeResult env U registry target locals realization available localNeeds A B body other key output domain where
  bodyBound : HereditaryBudgeted.Within budgets bodyCertificate.nativeDepth
  certificateBound : HereditaryBudgeted.Within budgets certificate.nativeDepth

noncomputable def BudgetLambdaTypeResult.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) {target future : List VExpr} {ρ : Lift}
    (insertion : FutureInsertion env U target future ρ)
    {locals : List Nat} {realization : Subst} {available : Valuation}
    {inputFootprint : Footprint} {A B body other : VExpr}
    {key : Key n} {output : Atom n} {domain : Profile n}
    (fixed : BudgetLambdaTypeResult budgets env U registry target locals realization available
      (inputFootprint.localNeeds ++ inputFootprint.localNeeds.flatMap Need.singletons) A B body other key output domain) :
    BudgetLambdaTypeResult budgets env U registry future locals (realization.lift_r ρ)
      (Valuation.rename ρ available) ((Footprint.rename ρ inputFootprint).localNeeds ++
        (Footprint.rename ρ inputFootprint).localNeeds.flatMap Need.singletons)
      A B body other (key.rename ρ) (output.rename ρ) (domain.rename ρ) := by
  let old := fixed.toSortableLambdaTypeResult.future henv insertion
  have bodyDepth : ∀ current, old.bodyCertificate.nativeDepth current = fixed.bodyCertificate.nativeDepth current := by
    intro current
    simp only [old, SortableLambdaTypeResult.future, SortableCert.nativeDepth_future, id_eq, SortableCert.nativeDepth_mp, subst_cons_future, Key.rename, Profile.pi, Profile.rename_singleton, Atom.rename_pi, Rows.rename, List.map_cons, List.map_nil, lift'_subst, ← Subst.lift_r_lift]
  have certificateDepth : ∀ current, old.certificate.nativeDepth current = fixed.certificate.nativeDepth current := by
    intro current
    simp only [old, SortableLambdaTypeResult.future, SortableCert.nativeDepth_future, id_eq, SortableCert.nativeDepth_mp, subst_cons_future, Key.rename, Profile.pi, Profile.rename_singleton, Atom.rename_pi, Rows.rename, List.map_cons, List.map_nil, lift'_subst, ← Subst.lift_r_lift]
  exact {
    toSortableLambdaTypeResult := old
    bodyBound := by intro current fuel member; change old.bodyCertificate.nativeDepth current ≤ fuel; rw [bodyDepth]; exact fixed.bodyBound current fuel member
    certificateBound := by intro current fuel member; change old.certificate.nativeDepth current ≤ fuel; rw [certificateDepth]; exact fixed.certificateBound current fuel member }

end Lean4Lean.AnchoredSource.Adapted
