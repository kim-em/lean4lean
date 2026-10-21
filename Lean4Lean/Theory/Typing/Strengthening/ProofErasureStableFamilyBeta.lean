import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStablePrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointSingletonBeta

/-! # Retaining lower-stage family origins through beta and substitution

The original finite-stage guard supplies all future substituted comparisons in
one invocation of lower-stage beta transport. No transported target guard is
fed back into that hypothesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Beta residuals of finite-stage proposition comparisons retain all future
typed substitutions, using transport only at the original source stage. -/
theorem JointPropBetaTransport.stable_beta_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) Target)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) (hQ : env.HasType univs Γ Q (.sort .zero))
    (H : JointCompare (ErasedJointStage D stage) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q))
    (RP : ProofShape.BetaRed (proofErase Γ P) p) (RQ : ProofShape.BetaRed (proofErase Γ Q) q) :
    SubstitutionStablePrimitive (fun Δ => JointCompare Target Δ true) (proofEraseCtx Γ) p q := by
  refine ⟨Hbeta hΓ hP hQ H RP RQ, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  rw [← EΓ₀]
  apply Hbeta.subst_beta_stage heq hs hΓ₀ WS hP hQ H
  · rw [proofErase_subst_with hΓ₀ WS hP ES]
    exact RP.subst
  · rw [proofErase_subst_with hΓ₀ WS hQ ES]
    exact RQ.subst

/-- Context conversion preserves the future-substitution certificate of each
beta-reduced family guard by composition with the interpreted identity. -/
theorem JointPropBetaTransport.stable_family_transport
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) Target) :
    ErasedFamilyContextBetaTransport (fun Δ => JointCompare (ErasedJointStage D stage) Δ true)
      (SubstitutionStablePrimitive (fun Δ => JointCompare Target Δ true)) := by
  intro Γ Γ₁ Γ₂ P Q P' Q' hΓ W hP hQ H RP RQ
  have hΓ₁ : OnCtx Γ₁ (env.IsType univs) := by
    clear hP hQ H
    induction W with
    | zero => exact hΓ
    | succ _ hA ih => exact ⟨ih, _, hA.hasType.1⟩
  have HS := Hbeta.stable_beta_stage heq hs hΓ₁ hP hQ H
    (proofErase_beta_forward hΓ₁ hP RP) (proofErase_beta_forward hΓ₁ hQ RQ)
  have HS := HS.subst (ContextSubstitution.of_defeqCtx hΓ W)
  simp only [ProofShape.subst_id] at HS
  rwa [proofErase_defeqCtx hΓ₁ W (beta_eq hΓ₁ hP RP).hasType.2,
    proofErase_defeqCtx hΓ₁ W (beta_eq hΓ₁ hQ RQ).hasType.2] at HS

/-- A certified comparator inherits family descent from its underlying
comparison. Its extra substitution certificate contributes no new equality. -/
theorem substitution_stable_family_descent (hcmp : ErasedFamilyDescent Cmp) :
    ErasedFamilyDescent (SubstitutionStablePrimitive Cmp) :=
  fun hΓ hΓ' W hP hQ H => hcmp hΓ hΓ' W hP hQ H.1

/-- The retained certificate supplies typed family substitution without any
closure assumption on arbitrary underlying target comparisons. -/
theorem substitution_stable_family_substitution :
    ErasedFamilySubstitution (SubstitutionStablePrimitive Cmp) Cmp := by
  intro Γ Γ₀ σ P Q hΓ₀ W hP hQ H
  have E : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
  rw [proofErase_subst_with hΓ₀ W hP E, proofErase_subst_with hΓ₀ W hQ E]
  exact H.2 (ContextSubstitution.of_typed hΓ₀ W E)

/-- A general singleton with a substitution-certified union guard is itself
an actual union primitive stable under every future typed substitution. -/
theorem singleton_with_stable_guard
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ a)
    (H : SingletonPrimitiveWith
      (SubstitutionStablePrimitive (fun Δ => JointCompare (ErasedJointUnion D) Δ true)) Δ a b) :
    SubstitutionStablePrimitive (ErasedJointUnion D) Δ a b := by
  have hcmp : ErasedFamilyDescent (fun Δ => JointCompare (ErasedJointUnion D) Δ true) :=
    erased_joint_family_descent (erased_joint_union_descent heq hs)
  refine ⟨erased_joint_union_iff.2 (.inr (.inl ⟨HT, H.mono (fun H => H.1)⟩)), ?_⟩
  intro Δ' τ W
  have HT' := HT.subst W
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ EΓ
  have HR : SingletonPrimitiveWith
      (SubstitutionStablePrimitive (fun Δ => JointCompare (ErasedJointUnion D) Δ true))
      (proofEraseCtx Γ) (proofErase Γ e) b := by
    rw [EΓ, Ee]
    exact H
  have HR := proofErase_singleton_subst_with heq (substitution_stable_family_descent hcmp)
    hcmp substitution_stable_family_substitution hΓ₀ WS ES ht HR
  rw [EΓ₀, Ee] at HR
  exact erased_joint_union_iff.2 (.inr (.inl ⟨HT', HR⟩))

end Lean4Lean.VEnv.Strengthening
