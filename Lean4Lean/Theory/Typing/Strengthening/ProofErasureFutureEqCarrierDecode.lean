import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureEqCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqCarrierDecode

/-! # Lossless future Eq encoding at substitution-closed primitives

Future Eq comparison can be decoded at every independent carrier and endpoint
beta residual, including after interpreted substitution. Actual typed Eq
sources are replayed before using the native carrier decoder. This requires
primitive substitution closure; the certified relation provides it, whereas
no such premise is silently discharged for the full union.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem decode_future_at
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (HF : ∀ {p q}, ProofShape.BetaRed (proofErase Γ (eqApp u α z a)) p →
      ProofShape.BetaRed (proofErase Γ (eqApp u α z b)) q →
      JointCompare Step (proofEraseCtx Γ) true p q)
    (RC : ProofShape.BetaRed (proofErase Γ α) C)
    (RA : ProofShape.BetaRed (proofErase Γ a) a')
    (RB : ProofShape.BetaRed (proofErase Γ b) b') :
    JointCarrierGuard Step (proofEraseCtx Γ) C a' b' := by
  have hP := HasType.eqApp heq hu hα hz ha
  have hQ := HasType.eqApp heq hu hα hz hb
  have RP : ProofShape.BetaRed (proofErase Γ (eqApp u α z a))
      (eqProofType u C (proofErase Γ z) a') := by
    rw [proofErase_eqProofType heq hu hΓ hα hz ha]
    exact .app (.app (.app .refl RC) .refl) RA
  have RQ : ProofShape.BetaRed (proofErase Γ (eqApp u α z b))
      (eqProofType u C (proofErase Γ z) b') := by
    rw [proofErase_eqProofType heq hu hΓ hα hz hb]
    exact .app (.app (.app .refl RC) .refl) RB
  obtain ⟨P', HP, EP⟩ := proofErase_scoped_compute_realize hstep hΓ hP rfl rfl (.beta RP)
  obtain ⟨Q', HQ, EQ⟩ := proofErase_scoped_compute_realize hstep hΓ hQ rfl rfl (.beta RQ)
  have HI : JointCompare Step (proofEraseCtx Γ) false
      (eqProofType u C (proofErase Γ z) a') (eqProofType u C (proofErase Γ z) b') := by
    rw [← EP, ← EQ]
    apply proofErase_joint_types_inferred hstep hΓ HP.hasType.2 HQ.hasType.2
    rw [EP, EQ]
    exact HF RP RQ
  exact HI.eq_carrier_decode heq hstep hhead hsubst hinert
    ⟨Γ, P', .sort .zero, hΓ, rfl, HP.hasType.2, EP⟩
    ⟨Γ, Q', .sort .zero, hΓ, rfl, HQ.hasType.2, EQ⟩ .refl .refl

/-- A future comparison of typed Eq propositions decodes to a full future
carrier certificate, including independent carrier reduction. The primitive
relation must preserve interpreted substitution and the Eq constant head. -/
theorem proofErase_future_eq_carrier_decode
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (HF : BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b))) :
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ α) (proofErase Γ a) (proofErase Γ b) := by
  refine ⟨fun RC RA RB => decode_future_at heq hu hstep hhead hsubst hinert
    hΓ hα hz ha hb HF.1 RC RA RB, ?_⟩
  intro Δ' τ C p q W RC RA RB
  have HS := HF.subst W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have hP := HasType.eqApp heq hu hα hz ha
  have hQ := HasType.eqApp heq hu hα hz hb
  rw [← proofErase_subst_with hΓ₀ WS hP ES,
    ← proofErase_subst_with hΓ₀ WS hQ ES, ← EΓ₀] at HS
  rw [← proofErase_subst_with hΓ₀ WS hα ES] at RC
  rw [← proofErase_subst_with hΓ₀ WS ha ES] at RA
  rw [← proofErase_subst_with hΓ₀ WS hb ES] at RB
  rw [← EΓ₀]
  simp only [eqApp, VExpr.subst] at HS
  exact decode_future_at heq hu hstep hhead hsubst hinert hΓ₀
    (hα.subst henv WS) (hz.subst henv WS) (ha.subst henv WS) (hb.subst henv WS) HS.1 RC RA RB

/-- At substitution-closed sound primitives, Eq proposition encoding preserves
and reflects the complete future carrier certificate. No forward endpoint
computation or certificate-composition law is assumed. -/
theorem proofErase_future_carrier_eq_iff
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hinert : ∀ {Δ ls args out}, ¬ Step Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b)) ↔
    BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ α) (proofErase Γ a) (proofErase Γ b) :=
  ⟨proofErase_future_eq_carrier_decode heq hu hstep hhead hsubst hinert hΓ hα hz ha hb,
    proofErase_future_carrier_eq_family heq hu hΓ hα hz ha hb⟩

/-- Certified computation satisfies every decoder premise. Consequently its
future Eq family guards and future supplied-carrier certificates are equivalent
at all typed occurrences, without an additional transport obligation. -/
theorem proofErase_certified_future_carrier_eq_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α) :
    BetaStableFamily (fun Δ => JointCompare (ErasedBetaStableJoint D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b)) ↔
    BetaStableCarrier (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ α) (proofErase Γ a) (proofErase Γ b) := by
  apply proofErase_future_carrier_eq_iff heq hu
    (erased_beta_stable_joint_descent heq hs) erased_beta_stable_joint_head
    (erased_beta_stable_joint_subst heq hs) ?_ hΓ hα hz ha hb
  intro Δ ls args out H
  exact erased_joint_union_no_rigid heq (heq.rigid henv) hEq
    (erased_beta_stable_joint_into_union H) (constHead_mkApps _ _)

end Lean4Lean.VEnv.Strengthening
