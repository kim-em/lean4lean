import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContext

/-! # Erasing a residual lambda telescope

Each annotation is erased in its source prefix context. A non-proof wrapped
term retains the entire telescope and the body at the fully extended context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

namespace ProofShape
/-- Wrap raw binders in outermost-first order. -/
def wrapLams (domains : List ProofShape) (body : ProofShape) : ProofShape :=
  domains.foldr .lam body
end ProofShape

variable [Params]

/-- Erase each residual annotation beneath all preceding residual binders. -/
noncomputable def proofEraseDomains (Γ : List VExpr) : List VExpr → List ProofShape
  | [] => []
  | A :: domains => proofErase Γ A :: proofEraseDomains (A :: Γ) domains

/-- Annotation erasure preserves the exact residual arity. -/
theorem proofEraseDomains_length : (proofEraseDomains Γ domains).length = domains.length := by
  induction domains generalizing Γ with
  | nil => rfl
  | cons A domains ih => simp only [proofEraseDomains, List.length_cons, ih]

/-- The erased opened context is precisely the raw telescope extension. -/
theorem proofEraseDomains_context :
    proofEraseCtx (domains.reverse ++ Γ) = (proofEraseDomains Γ domains).reverse ++ proofEraseCtx Γ := by
  induction domains generalizing Γ with
  | nil => rfl
  | cons A domains ih =>
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
      proofEraseDomains, proofEraseCtx] using ih (Γ := A :: Γ)

/-- A non-proof lambda telescope retains all annotations and its erased body.
No typing of a replacement body or conversion of endpoint types is assumed. -/
theorem proofErase_wrapLams_nonproof
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType univs))
    (hn : ¬ IsProof Γ (VExpr.wrapLams domains body)) :
    proofErase Γ (VExpr.wrapLams domains body) =
      ProofShape.wrapLams (proofEraseDomains Γ domains)
        (proofErase (domains.reverse ++ Γ) body) := by
  induction domains generalizing Γ with
  | nil => rfl
  | cons A domains ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hctx ⊢
    obtain ⟨hΓ, u, hA⟩ := OnCtx.of_append hctx
    have hnb : ¬ IsProof (A :: Γ) (VExpr.wrapLams domains body) :=
      fun hp => hn (hp.lam hΓ hA)
    change proofErase Γ (.lam A (VExpr.wrapLams domains body)) = _
    rw [show proofErase Γ (.lam A (VExpr.wrapLams domains body)) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) (VExpr.wrapLams domains body)) from if_neg hn,
      ih hctx hnb]
    rfl

end Lean4Lean.VEnv.Strengthening
