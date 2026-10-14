import Lean4Lean.Theory.Typing.Strengthening.CanonicalEqPrefixReplay
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPrefixStages

/-! # Exact operational replay of finite scoped prefix computation

Each scoped path from a typed erasure has an original path using the actual
registered singleton prefixes. This is stronger than declarative replay; no
forward erasure or confluence of the general prefix presentation is asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions PrefixCompute)
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A

/-- Reconstruct an actual original prefix-computation path from each typed
source of a scoped primitive, with its exact erased target. -/
def ErasedScopedPrefixReplay (D : Definitions)
    (Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ e T out}, OnCtx Γ (env.IsType univs) → (Γ ⊢ e : T) →
    Step (proofEraseCtx Γ) (proofErase Γ e) out →
    ∃ e', PrefixCompute D Γ e e' ∧ proofErase Γ e' = out

private theorem compute_eq (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (he : Γ ⊢ e : T) (R : PrefixCompute D Γ e e') : env.IsDefEq univs Γ e e' T :=
  R.simAt hs hΓ T he

private theorem compute_not_proof (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (he : Γ ⊢ e : T) (R : PrefixCompute D Γ e e') (hn : ¬ IsProof Γ e) : ¬ IsProof Γ e' := by
  rintro ⟨P, heP, hP⟩
  exact hn ⟨P, ((show env.IsDefEqU univs Γ e' e from ⟨_, (compute_eq hs hΓ he R).symm⟩).of_l
    henv hΓ heP).hasType.2, hP⟩

/-- Primitive replay extends through every compatible finite erased computation. -/
theorem proofErase_scoped_prefix_replay (hs : D.Sound env univs) (hstep : ErasedScopedPrefixReplay D Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (he : Γ ⊢ e : T)
    (hΔ : proofEraseCtx Γ = Δ)
    (R : ProofShape.ScopedCompute Step Δ (proofErase Γ e) out) :
    ∃ e', PrefixCompute D Γ e e' ∧ proofErase Γ e' = out := by
  generalize hsrc : proofErase Γ e = source at R
  induction R generalizing Γ e T with
  | base R => exact hstep hΓ he (hΔ ▸ hsrc ▸ R)
  | beta R =>
    obtain ⟨e', R', H⟩ := proofErase_beta_replay hΓ he (hsrc ▸ R)
    exact ⟨e', .base (.base (.base (.of_beta R'))), H⟩
  | trans R1 R2 ih1 ih2 =>
    obtain ⟨e1, Re1, H1⟩ := ih1 hΓ he hΔ hsrc
    obtain ⟨e2, Re2, H2⟩ := ih2 hΓ (compute_eq hs hΓ he Re1).hasType.2 hΔ H1
    exact ⟨e2, Re1.trans Re2, H2⟩
  | app Rf Ra ihf iha =>
    obtain ⟨f, a, rfl, hn, Hf, Ha⟩ := erase_app_inv hsrc
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv hΓ
    obtain ⟨f', Rf', Hf'⟩ := ihf hΓ hf hΔ Hf
    obtain ⟨a', Ra', Ha'⟩ := iha hΓ ha hΔ Ha
    have R' := PrefixCompute.app Rf' Ra'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (compute_not_proof hs hΓ he R' hn), Hf', Ha']
  | @proj Δ m₁ m₂ s i Rm ihm =>
    obtain ⟨m, rfl, hn, Hm⟩ := erase_proj_inv hsrc
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv hΓ
    obtain ⟨m', Rm', Hm'⟩ := ihm hΓ hm.hasType.2 hΔ Hm
    have R' := PrefixCompute.proj (s := s) (i := i) Rm'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (compute_not_proof hs hΓ he R' hn), Hm']
  | lam RA Rb ihA ihb =>
    obtain ⟨A, b, rfl, hn, HA, Hb⟩ := erase_lam_inv hsrc
    obtain ⟨⟨u, hA⟩, _, hb⟩ := he.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨A', RA', HA'⟩ := ihA hΓ hA hΔ HA
    obtain ⟨b', Rb', Hb'⟩ := ihb hΓA hb (by simp only [proofEraseCtx, HA, hΔ]) Hb
    have hAA := compute_eq hs hΓ hA RA'
    have hb' := (compute_eq hs hΓA hb Rb').hasType.2
    have Hb'' := (proofErase_defeqCtx hΓA (.succ .zero hAA) hb').symm.trans Hb'
    have R' := PrefixCompute.lam RA' Rb'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (compute_not_proof hs hΓ he R' hn), HA', Hb'']
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, hn, HA, HB⟩ := erase_forallE_inv hsrc
    obtain ⟨⟨u, hA⟩, _, hB⟩ := he.forallE_inv henv
    have hΓA : OnCtx (A :: Γ) (Params.env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨A', RA', HA'⟩ := ihA hΓ hA hΔ HA
    obtain ⟨B', RB', HB'⟩ := ihB hΓA hB (by simp only [proofEraseCtx, HA, hΔ]) HB
    have hAA := compute_eq hs hΓ hA RA'
    have hB' := (compute_eq hs hΓA hB RB').hasType.2
    have HB'' := (proofErase_defeqCtx hΓA (.succ .zero hAA) hB').symm.trans HB'
    have R' := PrefixCompute.forallE RA' RB'
    refine ⟨_, R', ?_⟩
    simp only [proofErase, if_neg (compute_not_proof hs hΓ he R' hn), HA', HB'']

/-- A scoped K primitive replays through the actual canonical prefix rule.
The selected presentation must use the environment's Eq.rec registry entry. -/
theorem erased_scoped_K_prefix_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hstep : ErasedScopedPrimitiveDescent Step)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ErasedScopedPrefixReplay D (ProofShape.ScopedPrefixKPrimitive Step) := by
  intro Γ e T out hΓ ht R
  generalize hsrc : proofErase Γ e = source at R
  cases R with
  | @intro a b v w α M m HC =>
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Hα, Ha, HM, Hm, Hb⟩ := proofErase_eqRecBeforeMajor_inv hsrc
    rw [← Ha, ← Hb] at HC
    obtain ⟨_, hw, hα, ha, _, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have hab := (proofErase_scoped_compare_reflect hstep hΓ ha hb HC).1 ⟨_, hα⟩
    have HP : PrefixUnfold env univs recursorData Γ ``Eq.rec [v, w]
        [α₀, a₀, M₀, m₀, b₀] (.lam (eqApp w α₀ a₀ b₀) m₀.lift) := by
      obtain ⟨data, hl, hr, hn, _⟩ := heq.recursorRegistration henv
      exact eqRecBeforeMajor_prefix_registered henv heq hΓ hr hn
        (hregistry.trans hl) ⟨_, ht⟩ hab
    have HR : PrefixCompute D Γ (eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀)
        (.lam (eqApp w α₀ a₀ b₀) m₀.lift) := .singleton HP
    have HH := HR.simAt hs hΓ T ht
    have hn : ¬ IsProof Γ (eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀) := by
      intro hp
      rw [proofErase_eq_proof.2 hp] at hsrc
      cases hsrc
    have hn' := mt (isProof_congr hΓ HH).2 hn
    have hE := HasType.eqApp heq hw hα ha hb
    have hΓE : OnCtx (eqApp w α₀ a₀ b₀ :: Γ) (env.IsType univs) := ⟨hΓ, _, hE⟩
    refine ⟨_, HR, ?_⟩
    rw [show proofErase Γ (.lam (eqApp w α₀ a₀ b₀) m₀.lift) =
      .lam (proofErase Γ (eqApp w α₀ a₀ b₀))
        (proofErase (eqApp w α₀ a₀ b₀ :: Γ) m₀.lift) from if_neg hn',
      proofErase_eqProofType heq hw hΓ hα ha hb,
      proofErase_liftN hΓ hΓE Ctx.LiftN.one hm, Hα, Ha, Hb, Hm]

/-- Every finite stage's primitives have exact operational replay, including
recursively scoped endpoint guards. No raw-stage confluence is assumed. -/
theorem erased_scoped_stage_prefix_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    ∀ stage, ErasedScopedPrefixReplay D (ErasedScopedPrefixStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ e T out hΓ ht R
    obtain ⟨e', HR, HE⟩ := erased_iota_replay hs hΓ ht R
    exact ⟨e', .base HR, HE⟩
  | succ stage ih =>
    intro Γ e T out hΓ ht R
    rcases R with R | R
    · exact ih hΓ ht R
    · exact erased_scoped_K_prefix_replay heq hs
        (erased_scoped_prefix_stage_descent heq hs stage) hregistry hΓ ht R

/-- A complete finite scoped-stage path from a typed erasure replays as an
actual original prefix-computation path, preserving the exact erased output. -/
theorem proofErase_scoped_stage_operational_replay (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ)
      (proofErase Γ e) out) :
    ∃ e', PrefixCompute D Γ e e' ∧ env.HasType univs Γ e' T ∧ proofErase Γ e' = out := by
  obtain ⟨e', HR, HE⟩ := proofErase_scoped_prefix_replay hs
    (erased_scoped_stage_prefix_replay heq hs hregistry stage) hΓ ht rfl R
  exact ⟨e', HR, (HR.simAt hs hΓ T ht).hasType.2, HE⟩

end Lean4Lean.VEnv.Strengthening
