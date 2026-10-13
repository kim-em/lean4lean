import Lean4Lean.Theory.Typing.Strengthening.HybridNormal

/-! # Changing a lambda annotation by typed eta expansion

A chosen function typing supplies the new domain. Eta expansion followed by one
beta contraction changes only the lambda annotation. This can repair comparisons
which no finite beta-only development can repair; it does not supply a common
function typing when only the enclosing application has one.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Eta expansion at a chosen function type, then beta contraction under the new
binder, reannotates a lambda while retaining its literal body. -/
theorem lambda_reannotation
    (h : HasType Params.env univs Γ (.lam D b) (.forallE A B)) :
    FullReduction Γ (.lam D b) (.lam A b) := by
  refine .tail (.tail .rfl (.funEta h)) (.core (.lam .rfl ?_))
  have hb : ParRed (A :: Γ) (.app (.lam D.lift (b.liftN 1 1)) (.bvar 0))
      ((b.liftN 1 1).inst (.bvar 0)) := .beta .rfl .rfl
  simpa only [lift, liftN, inst_liftN_bvar] using hb

/-- Lambdas with the same body and a common function typing have a literal common
full reduct, even when their displayed domains have no recursive certificate. -/
theorem same_body_reannotation_join
    (h₁ : HasType Params.env univs Γ (.lam D b) (.forallE A B))
    (h₂ : HasType Params.env univs Γ (.lam E b) (.forallE A B)) :
    FullReduction Γ (.lam D b) (.lam A b) ∧ FullReduction Γ (.lam E b) (.lam A b) :=
  ⟨lambda_reannotation h₁, lambda_reannotation h₂⟩

end Lean4Lean.VEnv.Strengthening
