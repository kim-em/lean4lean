import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParallelBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaForward

/-! # Exact typed replay of parallel beta developments

The existing original ComputePar relation with empty declarations is pure
parallel beta. Typed erasure preserves and reflects one such development,
including changed binder annotations and erased proof arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv beta_eq beta_not_proof
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- One raw parallel beta development of a typed erasure replays as one
original parallel development with exactly the specified raw endpoint. -/
theorem proofErase_parallel_beta_replay (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e T) (R : ProofShape.BetaPar (proofErase Γ e) out) :
    ∃ e', ComputePar .empty e e' ∧ proofErase Γ e' = out := by
  generalize hsrc : proofErase Γ e = source at R
  induction R generalizing Γ e T with
  | proof | bvar | sort | const => exact ⟨e, .refl e, hsrc⟩
  | app Rf Ra ihf iha =>
    obtain ⟨f, a, rfl, hn, Hf, Ha⟩ := erase_app_inv hsrc
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    obtain ⟨f', Rf', Hf'⟩ := ihf hΓ hf Hf
    obtain ⟨a', Ra', Ha'⟩ := iha hΓ ha Ha
    have R' := ComputePar.app Rf' Ra'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (beta_not_proof hΓ he R'.toCompute.to_beta hn), Hf', Ha']
  | @proj m₁ m₂ s i Rm ihm =>
    obtain ⟨m, rfl, hn, Hm⟩ := erase_proj_inv hsrc
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    obtain ⟨m', Rm', Hm'⟩ := ihm hΓ hm.hasType.2 Hm
    have R' := ComputePar.proj (s := s) (i := i) Rm'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (beta_not_proof hΓ he R'.toCompute.to_beta hn), Hm']
  | lam RA Rb ihA ihb =>
    obtain ⟨A, b, rfl, hn, HA, Hb⟩ := erase_lam_inv hsrc
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨A', RA', HA'⟩ := ihA hΓ hA HA
    obtain ⟨b', Rb', Hb'⟩ := ihb hΓA hb Hb
    have hAA := beta_eq hΓ hA RA'.toCompute.to_beta
    have hb' := (beta_eq hΓA hb Rb'.toCompute.to_beta).hasType.2
    have Hb'' := (proofErase_defeqCtx hΓA (.succ .zero hAA) hb').symm.trans Hb'
    have R' := ComputePar.lam RA' Rb'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (beta_not_proof hΓ he R'.toCompute.to_beta hn), HA', Hb'']
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, hn, HA, HB⟩ := erase_forallE_inv hsrc
    obtain ⟨⟨u, hA⟩, _, hB⟩ := he.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨A', RA', HA'⟩ := ihA hΓ hA HA
    obtain ⟨B', RB', HB'⟩ := ihB hΓA hB HB
    have hAA := beta_eq hΓ hA RA'.toCompute.to_beta
    have hB' := (beta_eq hΓA hB RB'.toCompute.to_beta).hasType.2
    have HB'' := (proofErase_defeqCtx hΓA (.succ .zero hAA) hB').symm.trans HB'
    have R' := ComputePar.forallE RA' RB'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (beta_not_proof hΓ he R'.toCompute.to_beta hn), HA', HB'']
  | beta Rb Ra ihb iha =>
    obtain ⟨f, a, rfl, _, Hf, Ha⟩ := erase_app_inv hsrc
    obtain ⟨A, b, rfl, _, HA, Hb⟩ := erase_lam_inv Hf
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    obtain ⟨⟨u, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨⟨_, hDA⟩, _⟩ := (hf.uniqU henv hΓ (HasType.lam hA hb)).forallE_inv henv hΓ
    have haA := hDA.defeq ha
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨b', RB, EB⟩ := ihb hΓA hb Hb
    obtain ⟨a', RA, EA⟩ := iha hΓ haA Ha
    have hb' := (beta_eq hΓA hb RB.toCompute.to_beta).hasType.2
    have ha' := (beta_eq hΓ haA RA.toCompute.to_beta).hasType.2
    refine ⟨b'.inst a', .beta RB RA, ?_⟩
    rw [proofErase_instN hΓA ha' .zero hb', EB, EA]

private theorem parallel_forward_modes (hΓ : OnCtx Γ (env.IsType univs))
    (H : env.IsDefEq univs Γ e out T)
    (core : ¬ IsProof Γ e → ¬ IsProof Γ out →
      ProofShape.BetaPar (proofErase Γ e) (proofErase Γ out)) :
    ProofShape.BetaPar (proofErase Γ e) (proofErase Γ out) := by
  by_cases hp : IsProof Γ e
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ H).1 hp)]
    exact .refl _
  · exact core hp (mt (isProof_congr hΓ H).2 hp)

/-- A typed original parallel beta development erases to one raw parallel
step. Whole-proof developments become the reflexive proof-marker step. -/
theorem proofErase_parallel_beta_forward (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ e T) (R : ComputePar .empty e out) :
    ProofShape.BetaPar (proofErase Γ e) (proofErase Γ out) := by
  induction R generalizing Γ T with
  | bvar | sort | const => exact .refl _
  | delta H => exact H.elim
  | app Rf Ra ihf iha =>
    apply parallel_forward_modes hΓ (beta_eq hΓ ht ((ComputePar.app Rf Ra).toCompute.to_beta))
    intro hn hn'
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    simp only [proofErase, if_neg hn, if_neg hn']
    exact .app (ihf hΓ hf) (iha hΓ ha)
  | proj Rm ihm =>
    apply parallel_forward_modes hΓ (beta_eq hΓ ht ((ComputePar.proj Rm).toCompute.to_beta))
    intro hn hn'
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    simp only [proofErase, if_neg hn, if_neg hn']
    exact .proj (ihm hΓ hm.hasType.2)
  | lam RA Rb ihA ihb =>
    apply parallel_forward_modes hΓ (beta_eq hΓ ht ((ComputePar.lam RA Rb).toCompute.to_beta))
    intro hn hn'
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HAA := beta_eq hΓ hA RA.toCompute.to_beta
    have Hbb := beta_eq hΓA hb Rb.toCompute.to_beta
    have Eb := proofErase_defeqCtx hΓA (.succ .zero HAA) Hbb.hasType.2
    simp only [proofErase, if_neg hn, if_neg hn', ← Eb]
    exact .lam (ihA hΓ hA) (ihb hΓA hb)
  | forallE RA RB ihA ihB =>
    apply parallel_forward_modes hΓ (beta_eq hΓ ht ((ComputePar.forallE RA RB).toCompute.to_beta))
    intro hn hn'
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HAA := beta_eq hΓ hA RA.toCompute.to_beta
    have HBB := beta_eq hΓA hB RB.toCompute.to_beta
    have EB := proofErase_defeqCtx hΓA (.succ .zero HAA) HBB.hasType.2
    simp only [proofErase, if_neg hn, if_neg hn', ← EB]
    exact .forallE (ihA hΓ hA) (ihB hΓA hB)
  | beta Rb Ra ihb iha =>
    apply parallel_forward_modes hΓ (beta_eq hΓ ht (ComputePar.beta Rb Ra).toCompute.to_beta)
    intro hn _
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    obtain ⟨⟨u, hA⟩, _, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨⟨_, hDA⟩, _⟩ := (hf.uniqU henv hΓ (HasType.lam hA hb)).forallE_inv henv hΓ
    have haA := hDA.defeq ha
    have hΓA : OnCtx (_ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hb' := (beta_eq hΓA hb Rb.toCompute.to_beta).hasType.2
    have ha' := (beta_eq hΓ haA Ra.toCompute.to_beta).hasType.2
    have hnf := not_isProof_fn hΓ hf ha hn
    rw [proofErase_instN hΓA ha' .zero hb']
    simp only [proofErase, if_neg hn, if_neg hnf]
    exact .beta (ihb hΓA hb) (iha hΓ haA)

end Lean4Lean.VEnv.Strengthening
