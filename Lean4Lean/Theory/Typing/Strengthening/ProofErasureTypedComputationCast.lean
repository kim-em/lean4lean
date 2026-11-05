import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationEqPrefix

/-! # Cast computation from chains of types

A cast retains the genuine computational comparison between its endpoint types.
Once that comparison is a typed chain, canonical Eq computation removes the cast
at any actual source assignment, including an opaque equality witness.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}

/-- A chain between the endpoint types computes a canonical cast. Ordinary type
equality alone is not a premise of this computation theorem. -/
theorem TypedComputationEq.typeCast
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (VExpr.typeCast u X Y q x) T)
    (HXY : TypedComputationEq D Γ X Y (.sort u)) :
    TypedComputationEq D Γ (VExpr.typeCast u X Y q x) x T :=
  TypedComputationEq.eq_rec heq hs hΓ ht HXY

end Lean4Lean.VEnv.Strengthening
