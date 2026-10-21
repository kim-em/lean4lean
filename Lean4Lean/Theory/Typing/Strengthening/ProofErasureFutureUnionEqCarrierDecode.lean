import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnionEqDecode
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureEqCarrier

/-! # Full-union equivalence of future Eq and carrier certificates

Every typed occurrence, including after interpreted substitution, uses the
unconditional union Eq decoder. Independent carrier beta paths are retained;
no global substitution or forward computation transport law is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem decode_future_at
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hs : D.Sound env univs)
    (hinert : ∀ {Δ ls args out}, ¬ (ErasedJointUnion D) Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (HF : ∀ {p q}, ProofShape.BetaRed (proofErase Γ (eqApp u α z a)) p →
      ProofShape.BetaRed (proofErase Γ (eqApp u α z b)) q →
      JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true p q)
    (RC : ProofShape.BetaRed (proofErase Γ α) C)
    (RA : ProofShape.BetaRed (proofErase Γ a) a')
    (RB : ProofShape.BetaRed (proofErase Γ b) b') :
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ) C a' b' := by
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
  obtain ⟨P', HP, EP⟩ := proofErase_scoped_compute_realize (erased_joint_union_descent heq hs) hΓ hP rfl rfl (.beta RP)
  obtain ⟨Q', HQ, EQ⟩ := proofErase_scoped_compute_realize (erased_joint_union_descent heq hs) hΓ hQ rfl rfl (.beta RQ)
  have HI : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false
      (eqProofType u C (proofErase Γ z) a') (eqProofType u C (proofErase Γ z) b') := by
    rw [← EP, ← EQ]
    apply proofErase_joint_types_inferred (erased_joint_union_descent heq hs) hΓ HP.hasType.2 HQ.hasType.2
    rw [EP, EQ]
    exact HF RP RQ
  exact HI.union_eq_carrier_decode heq hs hinert
    ⟨Γ, P', .sort .zero, hΓ, rfl, HP.hasType.2, EP⟩
    ⟨Γ, Q', .sort .zero, hΓ, rfl, HQ.hasType.2, EQ⟩ .refl .refl

/-- A future comparison of typed Eq propositions decodes to a full future
carrier certificate, including independent carrier reduction. Eq heads must remain inert. Each substituted occurrence is decoded afresh;
no primitive substitution closure is used. -/
theorem proofErase_union_future_eq_carrier_decode
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hs : D.Sound env univs)
    (hinert : ∀ {Δ ls args out}, ¬ (ErasedJointUnion D) Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (HF : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b))) :
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ α) (proofErase Γ a) (proofErase Γ b) := by
  refine ⟨fun RC RA RB => decode_future_at heq hu hs hinert
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
  exact decode_future_at heq hu hs hinert hΓ₀
    (hα.subst henv WS) (hz.subst henv WS) (ha.subst henv WS) (hb.subst henv WS) HS.1 RC RA RB

/-- In the full union, Eq proposition encoding preserves and reflects the
complete future carrier certificate whenever Eq heads remain inert. No forward endpoint
computation or certificate-composition law is assumed. -/
theorem proofErase_union_future_carrier_eq_iff_of_inert
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hs : D.Sound env univs)
    (hinert : ∀ {Δ ls args out}, ¬ (ErasedJointUnion D) Δ (ProofShape.mkApps (.const ``Eq ls) args) out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b)) ↔
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ α) (proofErase Γ a) (proofErase Γ b) :=
  ⟨proofErase_union_future_eq_carrier_decode heq hu hs hinert hΓ hα hz ha hb,
    proofErase_future_carrier_eq_family heq hu hΓ hα hz ha hb⟩

/-- Under canonical Eq, sound definitions that do not unfold Eq give the
full future Eq/carrier equivalence in the entire union. No anchor recovery,
primitive substitution, beta transport or forward guard-persistence law is
an additional premise. -/
theorem proofErase_union_future_carrier_eq_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b)) ↔
    BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ α) (proofErase Γ a) (proofErase Γ b) := by
  apply proofErase_union_future_carrier_eq_iff_of_inert heq hu hs ?_ hΓ hα hz ha hb
  intro Δ ls args out H
  exact erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _)

/-- A full future Eq guard is independent of its repeated typed anchor.
The old and new anchors need not compare or compute to one another: both
encodings express the same future carrier check on the final endpoints. -/
theorem proofErase_union_future_eq_anchor_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (hw : env.HasType univs Γ w α)
    (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b)) ↔
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α w a)) (proofErase Γ (eqApp u α w b)) :=
  (proofErase_union_future_carrier_eq_iff heq hs hEq hu hΓ hα hz ha hb).trans
    (proofErase_union_future_carrier_eq_iff heq hs hEq hu hΓ hα hw ha hb).symm

/-- Any repeated typed anchor can certify the actual canonical Eq prefix.
Decoding its full future family guard and re-encoding at the prefix's own
anchor constructs the existing certified primitive with its exact output. -/
theorem proofErase_union_future_eq_family_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (hz : env.HasType univs Γ z α)
    (HF : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp w α z a)) (proofErase Γ (eqApp w α z b))) :
    ErasedBetaStableJoint D (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have HC := (proofErase_union_future_carrier_eq_iff heq hs hEq hw hΓ hα hz ha hb).1 HF
  exact proofErase_future_carrier_eq_prefix heq hs hregistry hΓ ht hn HC

end Lean4Lean.VEnv.Strengthening
