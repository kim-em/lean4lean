import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceGradedFundamental
import Lean4Lean.Theory.Typing.AnchoredSortAdequacy

/-! The sort-correctness part of the joint motive follows uniformly from
the actual certificate and assigned-type capability of graded transfer. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

theorem GradedTransfer.sortCorrect
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {left right sourceType : VExpr}
    (original : GradedTransfer env U registry target locals σ τ
      available left right sourceType) :
    SortCorrect env U registry target locals σ available left sourceType := by
  intro level relevant he flag n demand footprint observation resources
  subst sourceType
  obtain ⟨result⟩ := original observation resources
  have code := TypeRelated.lower henv result.bound result.typeCode
  exact TypeRelated.sort_typed hTarget flag code result.requestedTyped

theorem GradedJoint.of_transfers
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered)
    {source : List VExpr} {left right sourceType : VExpr}
    (original : ∀ target locals σ τ available,
      available.AtomClosed → OnCtx target (env.IsType U) →
      Ctx.SubstEq env U target σ τ source →
      PairedFits env U registry source target locals σ τ available →
        GradedTransfer env U registry target locals σ τ available left right sourceType ∧
        GradedTransfer env U registry target locals σ τ available right left sourceType) :
    GradedJoint env U registry source left right sourceType := by
  intro target locals σ τ available closed hTarget substitutions fits
  obtain ⟨forward, backward⟩ := original target locals σ τ available
    closed hTarget substitutions fits
  exact ⟨forward, backward, forward.sortCorrect henv hTarget,
    backward.sortCorrect henv hTarget⟩

end Lean4Lean.AnchoredSource.Adapted
