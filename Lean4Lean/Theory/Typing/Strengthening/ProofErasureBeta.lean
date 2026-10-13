import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSubstitution

/-! # Replaying beta reduction of annotated proof erasures

Every finite erased beta reduction starting from a typed original can be replayed
by a finite beta reduction of that original. The produced endpoint has exactly the
specified erasure; its typing follows from subject reduction in the same context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

namespace ProofShape
/-- Finite compatible beta reduction, including inside retained annotations. -/
inductive BetaRed : ProofShape → ProofShape → Prop where
  | refl : BetaRed e e
  | trans : BetaRed a b → BetaRed b c → BetaRed a c
  | app : BetaRed f f' → BetaRed a a' → BetaRed (.app f a) (.app f' a')
  | proj : BetaRed m m' → BetaRed (.proj s i m) (.proj s i m')
  | lam : BetaRed A A' → BetaRed b b' → BetaRed (.lam A b) (.lam A' b')
  | forallE : BetaRed A A' → BetaRed B B' → BetaRed (.forallE A B) (.forallE A' B')
  | beta : BetaRed (.app (.lam A b) a) (b.inst a)
end ProofShape

variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

private theorem erase_app_inv (H : proofErase Γ e = .app f a) :
    ∃ f₀ a₀, e = .app f₀ a₀ ∧ ¬ IsProof Γ e ∧ proofErase Γ f₀ = f ∧ proofErase Γ a₀ = a := by
  cases e <;> simp only [proofErase] at H <;> split at H <;> simp_all
  exact ⟨_, _, ⟨rfl, rfl⟩, H⟩

private theorem erase_proj_inv (H : proofErase Γ e = .proj s i m) :
    ∃ m₀, e = .proj s i m₀ ∧ ¬ IsProof Γ e ∧ proofErase Γ m₀ = m := by
  cases e <;> simp only [proofErase] at H <;> split at H <;> simp_all

private theorem erase_lam_inv (H : proofErase Γ e = .lam A b) :
    ∃ A₀ b₀, e = .lam A₀ b₀ ∧ ¬ IsProof Γ e ∧
      proofErase Γ A₀ = A ∧ proofErase (A₀ :: Γ) b₀ = b := by
  cases e <;> simp only [proofErase] at H <;> split at H <;> simp_all
  exact ⟨_, _, ⟨rfl, rfl⟩, H⟩

private theorem erase_forallE_inv (H : proofErase Γ e = .forallE A B) :
    ∃ A₀ B₀, e = .forallE A₀ B₀ ∧ ¬ IsProof Γ e ∧
      proofErase Γ A₀ = A ∧ proofErase (A₀ :: Γ) B₀ = B := by
  cases e <;> simp only [proofErase] at H <;> split at H <;> simp_all
  exact ⟨_, _, ⟨rfl, rfl⟩, H⟩

private theorem beta_eq (hΓ : OnCtx Γ (Params.env.IsType univs)) (he : Γ ⊢ e : T)
    (R : VExpr.BetaRed e e') : IsDefEq Params.env univs Γ e e' T :=
  R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ T he

private theorem beta_not_proof (hΓ : OnCtx Γ (Params.env.IsType univs))
    (he : Γ ⊢ e : T) (R : VExpr.BetaRed e e') (hn : ¬ IsProof Γ e) : ¬ IsProof Γ e' := by
  rintro ⟨P, heP, hP⟩
  exact hn ⟨P, ((show IsDefEqU Params.env univs Γ e' e from ⟨_, (beta_eq hΓ he R).symm⟩).of_l
    henv hΓ heP).hasType.2, hP⟩

/-- Replay an arbitrary finite erased beta reduction from a typed source. This
includes reductions inside lambda annotations and proof-erased arguments. -/
theorem proofErase_beta_replay (hΓ : OnCtx Γ (Params.env.IsType univs))
    (he : Γ ⊢ e : T) (R : ProofShape.BetaRed (proofErase Γ e) out) :
    ∃ e', VExpr.BetaRed e e' ∧ proofErase Γ e' = out := by
  generalize hsrc : proofErase Γ e = source at R
  induction R generalizing Γ e T with
  | refl => exact ⟨e, .refl, hsrc⟩
  | trans R1 R2 ih1 ih2 =>
    obtain ⟨e1, Re1, H1⟩ := ih1 hΓ he hsrc
    obtain ⟨e2, Re2, H2⟩ := ih2 hΓ (beta_eq hΓ he Re1).hasType.2 H1
    exact ⟨e2, Re1.trans Re2, H2⟩
  | app Rf Ra ihf iha =>
    obtain ⟨f, a, rfl, hn, Hf, Ha⟩ := erase_app_inv hsrc
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    obtain ⟨f', Rf', Hf'⟩ := ihf hΓ hf Hf
    obtain ⟨a', Ra', Ha'⟩ := iha hΓ ha Ha
    have R' := VExpr.BetaRed.app Rf' Ra'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (beta_not_proof hΓ he R' hn), Hf', Ha']
  | @proj m₁ m₂ s i Rm ihm =>
    obtain ⟨m, rfl, hn, Hm⟩ := erase_proj_inv hsrc
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    obtain ⟨m', Rm', Hm'⟩ := ihm hΓ hm.hasType.2 Hm
    have R' := VExpr.BetaRed.proj (n := s) (i := i) Rm'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (beta_not_proof hΓ he R' hn), Hm']
  | lam RA Rb ihA ihb =>
    obtain ⟨A, b, rfl, hn, HA, Hb⟩ := erase_lam_inv hsrc
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨A', RA', HA'⟩ := ihA hΓ hA HA
    obtain ⟨b', Rb', Hb'⟩ := ihb hΓA hb Hb
    have hAA := beta_eq hΓ hA RA'
    have hb' := (beta_eq hΓA hb Rb').hasType.2
    have Hb'' := (proofErase_defeqCtx hΓA (.succ .zero hAA) hb').symm.trans Hb'
    have R' := VExpr.BetaRed.lam RA' Rb'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (beta_not_proof hΓ he R' hn), HA', Hb'']
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, hn, HA, HB⟩ := erase_forallE_inv hsrc
    obtain ⟨⟨u, hA⟩, _, hB⟩ := he.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨A', RA', HA'⟩ := ihA hΓ hA HA
    obtain ⟨B', RB', HB'⟩ := ihB hΓA hB HB
    have hAA := beta_eq hΓ hA RA'
    have hB' := (beta_eq hΓA hB RB').hasType.2
    have HB'' := (proofErase_defeqCtx hΓA (.succ .zero hAA) hB').symm.trans HB'
    have R' := VExpr.BetaRed.forallE RA' RB'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (beta_not_proof hΓ he R' hn), HA', HB'']
  | beta =>
    obtain ⟨f, a, rfl, _, Hf, Ha⟩ := erase_app_inv hsrc
    obtain ⟨D, b, rfl, _, HD, Hb⟩ := erase_lam_inv Hf
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    obtain ⟨⟨u, hD⟩, _, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨⟨_, hAD⟩, _⟩ := (hf.uniqU henv hΓ (HasType.lam hD hb)).forallE_inv henv hΓ
    have haD := hAD.defeq ha
    refine ⟨_, .beta, ?_⟩
    rw [proofErase_instN (Γ₁ := D :: Γ) ⟨hΓ, u, hD⟩ haD .zero hb, Hb, Ha]

omit [Params] in
/-- Finite beta reduction of a lifted term is itself a lifted finite reduction.
This is purely syntactic and does not require typings of intermediate terms. -/
theorem betaRed_lift_inv (R : VExpr.BetaRed (e.lift' ρ) out) :
    ∃ e', VExpr.BetaRed e e' ∧ out = e'.lift' ρ := by
  generalize hsrc : e.lift' ρ = source at R
  induction R generalizing e ρ with
  | refl => exact ⟨e, .refl, hsrc.symm⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e1, R1, h1⟩ := ih1 hsrc
    obtain ⟨e2, R2, h2⟩ := ih2 h1.symm
    exact ⟨e2, R1.trans R2, h2⟩
  | app _ _ ihf iha =>
    obtain ⟨f, a, rfl, rfl, rfl⟩ := lift'_eq_app hsrc
    obtain ⟨f', Rf, rfl⟩ := ihf rfl
    obtain ⟨a', Ra, rfl⟩ := iha rfl
    exact ⟨_, .app Rf Ra, rfl⟩
  | proj _ ihm =>
    obtain ⟨m, rfl, rfl⟩ := lift'_eq_proj hsrc
    obtain ⟨m', Rm, rfl⟩ := ihm rfl
    exact ⟨_, .proj Rm, rfl⟩
  | lam _ _ ihA ihb =>
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hsrc
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨b', Rb, rfl⟩ := ihb rfl
    exact ⟨_, .lam RA Rb, rfl⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, B, rfl, rfl, rfl⟩ := lift'_eq_forallE hsrc
    obtain ⟨A', RA, rfl⟩ := ihA rfl
    obtain ⟨B', RB, rfl⟩ := ihB rfl
    exact ⟨_, .forallE RA RB, rfl⟩
  | beta =>
    obtain ⟨f, a, rfl, hf, rfl⟩ := lift'_eq_app hsrc
    obtain ⟨A, b, rfl, rfl, rfl⟩ := lift'_eq_lam hf.symm
    exact ⟨_, .beta, (lift'_inst_hi b a ρ).symm⟩

/-- A beta join of annotated erasures reflects as original definitional equality
at a common type. No normalization assumption and no erased intermediate typings
are needed: replay supplies typed originals for the complete finite paths. -/
theorem proofErase_beta_join_reflect (hΓ : OnCtx Γ (Params.env.IsType univs))
    (ha : Γ ⊢ a : T) (hb : Γ ⊢ b : T)
    (Ra : ProofShape.BetaRed (proofErase Γ a) out)
    (Rb : ProofShape.BetaRed (proofErase Γ b) out) : IsDefEq Params.env univs Γ a b T := by
  obtain ⟨a', Ra', Ha⟩ := proofErase_beta_replay hΓ ha Ra
  obtain ⟨b', Rb', Hb⟩ := proofErase_beta_replay hΓ hb Rb
  have hAA := beta_eq hΓ ha Ra'
  have hBB := beta_eq hΓ hb Rb'
  obtain ⟨_, hT⟩ := ha.isType henv hΓ
  obtain ⟨_, HC⟩ := (proofErase_reflect hΓ hAA.hasType.2 hBB.hasType.2 (Ha.trans Hb.symm)).1 ⟨_, hT⟩
  exact hAA.trans (((HC.defeq hΓ).of_l henv hΓ hAA.hasType.2).trans hBB.symm)

/-- An erased beta join of lifted terms descends at a common original type.
Replay and syntactic beta descent produce the smaller-context intermediate typings;
these are proved rather than assumed. This covers beta joins only. -/
theorem proofErase_beta_join_descend (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hΓ' : OnCtx Γ' (Params.env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (ha : Γ ⊢ a : T) (hb : Γ ⊢ b : T)
    (Ra : ProofShape.BetaRed (proofErase Γ' (a.liftN n k)) out)
    (Rb : ProofShape.BetaRed (proofErase Γ' (b.liftN n k)) out) :
    IsDefEq Params.env univs Γ a b T := by
  obtain ⟨a', Ra', Ha⟩ := proofErase_beta_replay hΓ' (ha.weakN henv W) Ra
  obtain ⟨b', Rb', Hb⟩ := proofErase_beta_replay hΓ' (hb.weakN henv W) Rb
  rw [← lift'_consN_skipN] at Ra' Rb'
  obtain ⟨a₀, RA, rfl⟩ := betaRed_lift_inv Ra'
  obtain ⟨b₀, RB, rfl⟩ := betaRed_lift_inv Rb'
  rw [lift'_consN_skipN] at Ha Hb
  have hAA := beta_eq hΓ ha RA
  have hBB := beta_eq hΓ hb RB
  obtain ⟨_, hT⟩ := ha.isType henv hΓ
  obtain ⟨_, HC⟩ := (proofErase_lift_reflect hΓ hΓ' W hAA.hasType.2 hBB.hasType.2
    (Ha.trans Hb.symm)).1 ⟨_, hT⟩
  exact hAA.trans (((HC.defeq hΓ).of_l henv hΓ hAA.hasType.2).trans hBB.symm)

end Lean4Lean.VEnv.Strengthening
