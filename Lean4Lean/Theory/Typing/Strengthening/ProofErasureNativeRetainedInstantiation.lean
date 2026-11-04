import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeImages

/-! # Native images only for retained arguments

A proof argument cannot be the image of a retained fresh variable. Its
instantiation therefore needs no native recovery certificate for `.proof`.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeImageTransport
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Single instantiation demands native recovery only when the argument is
retained by erasure. This includes arbitrary proofs without recovering a type
from the proof marker. -/
theorem Images.inst_retained
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p T)
    (H : ¬ IsProof Γ p → ScopedTypeRecovery ImageStep (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ T)) :
    Images ImageStep (T :: Γ) Γ (ProofShape.Subst.one (proofErase Γ p)) := by
  obtain ⟨u, hT⟩ := hp.isType henv hΓ
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := T)).substEq hΓT hp
  intro i A hl hn
  cases hl with
  | zero =>
    have hb : env.HasType univs (T :: Γ) (.bvar 0) T.lift := .bvar .zero
    have hnp : ¬ IsProof Γ p := by
      intro hpp
      apply hn
      apply (isProof_subst hΓ W hb).1
      simpa only [VExpr.subst, VExpr.Subst.one, VExpr.Subst.liftN, VExpr.Subst.cons] using hpp
    simpa only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.Subst.cons] using H hnp
  | succ hl =>
    simp only [proofEraseCtx, contextOracle, TypeOracle.cons, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id]
    exact .bvar

/-- A proof argument supplies every required native image vacuously at the
fresh slot; the remaining variables recover from the unchanged context. -/
theorem Images.inst_proof
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p T)
    (hproof : IsProof Γ p) :
    Images ImageStep (T :: Γ) Γ (ProofShape.Subst.one (proofErase Γ p)) :=
  Images.inst_retained hΓ hp (fun hn => (hn hproof).elim)

end Lean4Lean.VEnv.Strengthening.NativeImageTransport
