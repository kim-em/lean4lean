import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageSubstitution

/-! # Forward beta simulation by annotated proof erasure

Typed original beta paths erase to actual beta paths, including reduction of
retained binder annotations. Paths whose entire source is a proof collapse to
the empty path. Combined with exact beta replay, this covers both directions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

private theorem beta_forward_modes (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.IsDefEq univs Γ e out T)
    (core : ¬ IsProof Γ e → ¬ IsProof Γ out →
      ProofShape.BetaRed (proofErase Γ e) (proofErase Γ out)) :
    ProofShape.BetaRed (proofErase Γ e) (proofErase Γ out) := by
  by_cases hp : IsProof Γ e
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ H).1 hp)]
    exact .refl
  · exact core hp (mt (isProof_congr hΓ H).2 hp)

/-- Every typed original beta computation erases forwards, without normalization
or a fixed bound on the number of created redexes. -/
theorem proofErase_beta_forward (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e T) (R : VExpr.BetaRed e out) :
    ProofShape.BetaRed (proofErase Γ e) (proofErase Γ out) := by
  induction R generalizing Γ T with
  | refl => exact .refl
  | trans R1 R2 ih1 ih2 =>
    exact (ih1 hΓ ht).trans (ih2 hΓ (beta_eq hΓ ht R1).hasType.2)
  | app Rf Ra ihf iha =>
    apply beta_forward_modes hΓ (beta_eq hΓ ht (.app Rf Ra))
    intro hn hn'
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    simp only [proofErase, if_neg hn, if_neg hn']
    exact .app (ihf hΓ hf) (iha hΓ ha)
  | proj Rm ihm =>
    apply beta_forward_modes hΓ (beta_eq hΓ ht (.proj Rm))
    intro hn hn'
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    simp only [proofErase, if_neg hn, if_neg hn']
    exact .proj (ihm hΓ hm.hasType.2)
  | lam RA Rb ihA ihb =>
    apply beta_forward_modes hΓ (beta_eq hΓ ht (.lam RA Rb))
    intro hn hn'
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HAA := beta_eq hΓ hA RA
    have Hbb := beta_eq hΓA hb Rb
    have Eb := proofErase_defeqCtx hΓA (.succ .zero HAA) Hbb.hasType.2
    simp only [proofErase, if_neg hn, if_neg hn', ← Eb]
    exact .lam (ihA hΓ hA) (ihb hΓA hb)
  | forallE RA RB ihA ihB =>
    apply beta_forward_modes hΓ (beta_eq hΓ ht (.forallE RA RB))
    intro hn hn'
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HAA := beta_eq hΓ hA RA
    have HBB := beta_eq hΓA hB RB
    have EB := proofErase_defeqCtx hΓA (.succ .zero HAA) HBB.hasType.2
    simp only [proofErase, if_neg hn, if_neg hn', ← EB]
    exact .forallE (ihA hΓ hA) (ihB hΓA hB)
  | beta =>
    apply beta_forward_modes hΓ (beta_eq hΓ ht .beta)
    intro hn _
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨⟨u, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨⟨_, hDA⟩, _⟩ := (hf.uniqU henv hΓ (HasType.lam hA hb)).forallE_inv henv hΓ
    have haA := hDA.defeq ha
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hnf := not_isProof_fn hΓ hf ha hn
    rw [proofErase_instN hΓA haA .zero hb]
    simp only [proofErase, if_neg hn, if_neg hnf]
    exact .beta

/-- Beta reduction is already represented at every erased computation stage. -/
theorem proofErase_K_beta (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e T) (R : VExpr.BetaRed e out) :
    ProofShape.Compute (ErasedKStage D stage) (proofErase Γ e) (proofErase Γ out) :=
  .beta (proofErase_beta_forward hΓ ht R)

end Lean4Lean.VEnv.Strengthening
