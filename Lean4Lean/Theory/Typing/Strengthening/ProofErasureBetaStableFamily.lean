import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableFamilyBeta

/-! # Family certificates retaining future beta and substitution paths

Both endpoints may undergo further beta reduction after any interpreted typed
substitution. Composition keeps this property attached to a particular family
guard; no closure of the whole underlying comparison relation is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- An actual family comparison at all beta reducts of its endpoints, retaining
that same property after every interpreted context substitution. The first
component also covers raw contexts without a chosen typed realization. -/
def BetaStableFamily (Cmp : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  (∀ {p q}, ProofShape.BetaRed a p → ProofShape.BetaRed b q → Cmp Δ p q) ∧
  ∀ {Δ' τ p q}, ContextSubstitution Δ Δ' τ →
    ProofShape.BetaRed (a.subst τ) p → ProofShape.BetaRed (b.subst τ) q → Cmp Δ' p q

/-- Forgetting future paths gives an actual underlying comparison. -/
theorem BetaStableFamily.base (H : BetaStableFamily Cmp Δ a b) : Cmp Δ a b :=
  H.1 .refl .refl

/-- Further endpoint beta reductions preserve all future certificates by
composing their substituted paths with the new reductions. -/
theorem BetaStableFamily.beta (H : BetaStableFamily Cmp Δ a b)
    (RA : ProofShape.BetaRed a a') (RB : ProofShape.BetaRed b b') :
    BetaStableFamily Cmp Δ a' b' := by
  refine ⟨fun PA PB => H.1 (RA.trans PA) (RB.trans PB), ?_⟩
  intro Δ' τ p q W PA PB
  exact H.2 W (RA.subst.trans PA) (RB.subst.trans PB)

/-- Substitution preserves the certificate by composition of interpreted
substitutions, even when the next beta paths contract newly created redexes. -/
theorem BetaStableFamily.subst (H : BetaStableFamily Cmp Δ a b)
    (W : ContextSubstitution Δ Δ' τ) : BetaStableFamily Cmp Δ' (a.subst τ) (b.subst τ) := by
  refine ⟨fun PA PB => H.2 W PA PB, ?_⟩
  intro Δ'' υ p q V PA PB
  rw [ProofShape.subst_subst] at PA PB
  exact H.2 (W.comp V) PA PB

/-- Certified family comparisons inherit typed descent by forgetting paths. -/
theorem beta_stable_family_descent (hcmp : ErasedFamilyDescent Cmp) :
    ErasedFamilyDescent (BetaStableFamily Cmp) :=
  fun hΓ hΓ' W hP hQ H => hcmp hΓ hΓ' W hP hQ H.base

/-- The enriched family relation transports to itself under typed proposition
substitution, retaining its certificates for further beta and substitutions. -/
theorem beta_stable_family_substitution :
    ErasedFamilySubstitution (BetaStableFamily Cmp) (BetaStableFamily Cmp) := by
  intro Γ Γ₀ σ P Q hΓ₀ W hP hQ H
  have E : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
  rw [proofErase_subst_with hΓ₀ W hP E, proofErase_subst_with hΓ₀ W hQ E]
  exact H.subst (ContextSubstitution.of_typed hΓ₀ W E)

/-- Family beta reduction and converted residual contexts preserve the enriched
relation itself. This uses only the certificate of the given guard. -/
theorem beta_stable_family_transport :
    ErasedFamilyContextBetaTransport (BetaStableFamily Cmp) (BetaStableFamily Cmp) := by
  intro Γ Γ₁ Γ₂ P Q P' Q' hΓ W hP hQ H RP RQ
  have hΓ₁ : OnCtx Γ₁ (env.IsType univs) := by
    clear hP hQ H
    induction W with
    | zero => exact hΓ
    | succ _ hA ih => exact ⟨ih, _, hA.hasType.1⟩
  have HS := (H.beta (proofErase_beta_forward hΓ₁ hP RP)
    (proofErase_beta_forward hΓ₁ hQ RQ)).subst (ContextSubstitution.of_defeqCtx hΓ W)
  simp only [ProofShape.subst_id] at HS
  rwa [proofErase_defeqCtx hΓ₁ W (beta_eq hΓ₁ hP RP).hasType.2,
    proofErase_defeqCtx hΓ₁ W (beta_eq hΓ₁ hQ RQ).hasType.2] at HS

/-- Lower-source-stage beta transport supplies the stronger certificate at
arbitrary beta reducts. Every future substitution and beta path is handled
using the original guard at that same finite source stage. -/
theorem JointPropBetaTransport.beta_stable_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) Target)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q))
    (RP : ProofShape.BetaRed (proofErase Γ P) p) (RQ : ProofShape.BetaRed (proofErase Γ Q) q) :
    BetaStableFamily (fun Δ => JointCompare Target Δ true) (proofEraseCtx Γ) p q := by
  refine ⟨fun PA PB => Hbeta hΓ hP hQ H (RP.trans PA) (RQ.trans PB), ?_⟩
  intro Δ' τ p' q' W PA PB
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  rw [← EΓ₀]
  apply Hbeta.subst_beta_stage heq hs hΓ₀ WS hP hQ H
  · rw [proofErase_subst_with hΓ₀ WS hP ES]
    exact RP.subst.trans PA
  · rw [proofErase_subst_with hΓ₀ WS hQ ES]
    exact RQ.subst.trans PB

/-- The original lower-stage guard can be replaced by a certificate retaining
future beta and substitutions when the singleton residual telescope changes. -/
theorem JointPropBetaTransport.beta_stable_family_transport
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) Target) :
    ErasedFamilyContextBetaTransport (fun Δ => JointCompare (ErasedJointStage D stage) Δ true)
      (BetaStableFamily (fun Δ => JointCompare Target Δ true)) := by
  intro Γ Γ₁ Γ₂ P Q P' Q' hΓ W hP hQ H RP RQ
  have hΓ₁ : OnCtx Γ₁ (env.IsType univs) := by
    clear hP hQ H
    induction W with
    | zero => exact hΓ
    | succ _ hA ih => exact ⟨ih, _, hA.hasType.1⟩
  have HS := Hbeta.beta_stable_stage heq hs hΓ₁ hP hQ H
    (proofErase_beta_forward hΓ₁ hP RP) (proofErase_beta_forward hΓ₁ hQ RQ)
  have HS := HS.subst (ContextSubstitution.of_defeqCtx hΓ W)
  simp only [ProofShape.subst_id] at HS
  rwa [proofErase_defeqCtx hΓ₁ W (beta_eq hΓ₁ hP RP).hasType.2,
    proofErase_defeqCtx hΓ₁ W (beta_eq hΓ₁ hQ RQ).hasType.2] at HS

end Lean4Lean.VEnv.Strengthening
