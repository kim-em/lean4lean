import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedCoverage

/-! # Typed application support for context-indexed guards -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- An inferred function certificate applies to the same typed argument.
The common result type synchronizes whole-proof collapse. -/
theorem proofErase_scoped_apply_inferred (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  classical
  have hfX := HasType.app hf hx
  have hgX := HasType.app hg hx
  by_cases hp : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 (isProof_of_common_type hΓ hfX hgX hp)]
    exact .refl
  · have hp' : ¬ IsProof Γ (.app g x) := fun h => hp (isProof_of_common_type hΓ hgX hfX h)
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
      show proofErase Γ (.app g x) = .app _ _ from if_neg hp']
    exact .app H .refl

/-- Erased computation of a function extends to the same typed argument.
Both function endpoints have the supplied Pi type, so their applications have
identical proof classification even when their bodies erase completely. -/
theorem proofErase_scoped_compute_apply_same (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A)
    (R : ProofShape.ScopedCompute Step Δ (proofErase Γ f) (proofErase Γ g)) :
    ProofShape.ScopedCompute Step Δ (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  classical
  have hfX := HasType.app hf hx
  have hgX := HasType.app hg hx
  by_cases hp : IsProof Γ (.app f x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 (isProof_of_common_type hΓ hfX hgX hp)]
    exact .refl
  · have hp' : ¬ IsProof Γ (.app g x) := fun h => hp (isProof_of_common_type hΓ hgX hfX h)
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hp,
      show proofErase Γ (.app g x) = .app _ _ from if_neg hp']
    exact .app R .refl

/-- Apply a common lambda-body certificate despite distinct displayed domains.
Common function typing aligns those domains before ordinary typed substitution. -/
theorem proofErase_scoped_apply_lams
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam D b) (.forallE A B))
    (hg : env.HasType univs Γ (.lam D' b') (.forallE A B)) (hx : env.HasType univs Γ x A)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx (D :: Γ)) true
      (proofErase (D :: Γ) b) (proofErase (D' :: Γ) b')) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app (.lam D b) x)) (proofErase Γ (.app (.lam D' b') x)) := by
  obtain ⟨⟨u, hD⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨_, hD'⟩, C', hb'⟩ := hg.lam_inv henv hΓ
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have hPi := (hf.uniqU henv hΓ (HasType.lam hD hb)).symm.trans henv hΓ
    (hg.uniqU henv hΓ (HasType.lam hD' hb'))
  obtain ⟨⟨_, HDD⟩, _⟩ := hPi.forallE_inv henv hΓ
  have hctx := IsDefEqCtx.succ .zero HDD.symm
  have Eb := proofErase_defeqCtx (Γ₁ := D' :: Γ) ⟨hΓ, _, hD'⟩ hctx hb'
  rw [Eb] at H
  have hxD := argument_at_displayed_domain hΓ hf (HasType.lam hD hb) hx
  have HC := proofErase_scoped_compare_instN hsubst hΓD hxD Ctx.InstN.zero hb
    (hb'.defeqDFC henv hctx) H
  exact .compute (.beta (proofErase_beta_forward hΓ (HasType.app hf hx) .beta))
    (.beta (proofErase_beta_forward hΓ (HasType.app hg hx) .beta)) HC

/-- A recursive eta-body comparison applies to a typed argument by one beta
step on the long endpoint. No promotion to inferred function mode is used. -/
theorem proofErase_scoped_apply_eta_body
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hD : env.HasType univs Γ D (.sort u))
    (hb : env.HasType univs (D :: Γ) b C) (hf : env.HasType univs Γ f (.forallE D C))
    (hx : env.HasType univs Γ x D)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx (D :: Γ)) true
      (proofErase (D :: Γ) b) (proofErase (D :: Γ) (.app f.lift (.bvar 0)))) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.app (.lam D b) x)) (proofErase Γ (.app f x)) := by
  have hΓD : OnCtx (D :: Γ) (env.IsType univs) := ⟨hΓ, u, hD⟩
  have hη : env.HasType univs (D :: Γ) (.app f.lift (.bvar 0)) C := by
    simpa only [lift, liftN, inst_liftN_bvar] using HasType.app (hf.weak henv (B := D)) (.bvar .zero)
  have HC := proofErase_scoped_compare_instN hsubst hΓD hx Ctx.InstN.zero hb hη H
  simp only [inst, instVar_zero, inst_lift] at HC
  exact .compute (.beta (proofErase_beta_forward hΓ (HasType.app (HasType.lam hD hb) hx) .beta)) .refl HC

end Lean4Lean.VEnv.Strengthening
