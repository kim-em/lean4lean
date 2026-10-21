import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointStageCertification
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCheckingOracleBeta

/-! # Joint checking that retains future context and carrier transport

The certified primitive relation supports exact substitution and finite beta
commutation internally. Recovery and the full checking induction therefore
transport back into that same relation. Finite-stage source certificates can
enter it using only strictly lower-stage proposition beta transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private recovery_oracle_beta
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointOracleBetaTransport
variable [Params]

/-- Certified recovery survives oracle beta with a certified output recovery.
Its selected type may beta-reduce; the expression remains fixed. No beta law
for arbitrary union proposition comparisons is needed. -/
theorem proofErase_beta_stable_joint_recovery_oracle_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : ContextOracleBeta (proofEraseCtx Γ) Δ')
    (R : ScopedTypeRecovery (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (ErasedBetaStableJoint D) Δ' (proofErase Γ e) out' ∧
      ProofShape.BetaRed out out' :=
  recovery_oracle_beta (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs)
    (proofErase_beta_stable_joint_beta_commute heq hs)
    R hΓ ht rfl rfl W.interpretation W.entries

/-- All certified comparison and carrier constructors transport to the same
certified relation. This closes context-oracle and carrier-type beta transport
under iteration without a new proposition stability premise at the target. -/
theorem proofErase_beta_stable_joint_oracle_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : JointCheck (ErasedBetaStableJoint D) Δ kind sa sb) :
    JointOracleBetaResult (ErasedBetaStableJoint D) Δ kind sa sb := by
  apply H.oracle_beta (erased_beta_stable_joint_descent heq hs)
  · intro Γ Δ Δ' e T source out R hΓ ht EΓ Ee W
    simpa only [ProofShape.subst_id] using
      R.subst (erased_beta_stable_joint_subst heq hs) W.interpretation
  · intro Γ Δ' e T out reduced hΓ ht R B W
    obtain ⟨shared, BS, RS⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ ht R B
    have RS := RS.subst (erased_beta_stable_joint_subst heq hs) W.interpretation
    simp only [ProofShape.subst_id] at RS
    exact ⟨shared, BS, RS⟩
  · intro Γ Δ' e T out hΓ ht R W
    exact proofErase_beta_stable_joint_recovery_oracle_beta heq hs hΓ ht W R

/-- Source-stage checking transports with all future primitive certificates
retained. The new target can itself undergo further context and carrier beta
transport by the preceding theorem, without invoking the lower-stage premise
on any enlarged target guard. Expression endpoints stay fixed. -/
theorem proofErase_joint_stage_certified_oracle_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (H : JointCheck (ErasedJointStage D (stage + 1)) Δ kind sa sb) :
    JointOracleBetaResult (ErasedBetaStableJoint D) Δ kind sa sb := by
  apply H.oracle_beta (erased_joint_stage_descent heq hs (stage + 1))
  · intro Γ Δ Δ' e T source out R hΓ ht EΓ Ee W
    simpa only [ProofShape.subst_id] using R.subst_typed
      (erased_joint_stage_descent heq hs (stage + 1))
      (erased_joint_stage_certified_subst_of_lower_beta heq hs hregistry Hbeta)
      hΓ ht EΓ Ee W.interpretation
  · intro Γ Δ' e T out reduced hΓ ht R B W
    obtain ⟨shared, BS, RS⟩ := proofErase_joint_stage_beta_commute_of_lower_beta
      heq hs hregistry Hbeta hΓ ht R B
    have RS := RS.subst (erased_beta_stable_joint_subst heq hs) W.interpretation
    simp only [ProofShape.subst_id] at RS
    exact ⟨shared, BS, RS⟩
  · intro Γ Δ' e T out hΓ ht R W
    exact proofErase_joint_recovery_oracle_beta_of_lower_beta heq hs hregistry Hbeta
      hΓ ht W.interpretation W.entries R

/-- At source stage zero the stronger certified checking output needs no
proposition beta assumption. It retains closure under future context and
carrier changes, rather than forgetting certificates into the union. -/
theorem proofErase_joint_zero_certified_oracle_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : JointCheck (ErasedJointStage D 0) Δ kind sa sb) :
    JointOracleBetaResult (ErasedBetaStableJoint D) Δ kind sa sb := by
  apply H.oracle_beta (erased_joint_stage_descent heq hs 0)
  · intro Γ Δ Δ' e T source out R hΓ ht EΓ Ee W
    have RS := R.subst (fun H _ => erased_iota_primitive_subst H) W.interpretation
    simp only [ProofShape.subst_id] at RS
    exact RS.mono (fun H => .inl H)
  · intro Γ Δ' e T out reduced hΓ ht R B W
    obtain ⟨shared, BS, RS⟩ := proofErase_joint_zero_beta_commute heq hs hΓ ht R B
    have RS := RS.subst (erased_beta_stable_joint_subst heq hs) W.interpretation
    simp only [ProofShape.subst_id] at RS
    exact ⟨shared, BS, RS⟩
  · intro Γ Δ' e T out hΓ ht R W
    exact proofErase_joint_zero_recovery_oracle_beta heq hs hΓ ht W.interpretation W.entries R

/-- A typed stage-n+1 comparison can be certified with its original context,
mode and endpoints. Native recovery inside the certificate may change to a
beta-reduced type; its carrier subderivation adapts constructively. -/
theorem proofErase_joint_compare_certify_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCompare (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b) := by
  have W : ContextOracleBeta (proofEraseCtx Γ) (proofEraseCtx Γ) :=
    ⟨ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ)), fun _ => .refl⟩
  exact proofErase_joint_stage_certified_oracle_beta heq hs hregistry Hbeta H hΓ ha hb rfl rfl rfl W

/-- A typed stage-n+1 carrier guard can be certified without changing its
carrier or endpoints. This retains the type-indexed checking information that
general common-mode endpoint beta transport would incorrectly discard. -/
theorem proofErase_joint_carrier_certify_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCarrierGuard (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) := by
  have W : ContextOracleBeta (proofEraseCtx Γ) (proofEraseCtx Γ) :=
    ⟨ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ)), fun _ => .refl⟩
  exact proofErase_joint_stage_certified_oracle_beta heq hs hregistry Hbeta H
    hΓ ha hb rfl rfl rfl rfl W _ .refl

/-- The remaining proposition endpoint-beta law can be restricted to certified
source comparisons. Induction on the original finite stage then recovers the
whole union law. Conversely the union law handles certified inputs by
inclusion. This is an equivalence, not a strictly smaller sufficient front;
its benefit is a source relation with proved internal transport operations. -/
theorem joint_prop_beta_transport_certified_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec) :
    JointPropBetaTransport (ErasedBetaStableJoint D) (ErasedJointUnion D) ↔
      JointPropBetaStability (ErasedJointUnion D) := by
  constructor
  · intro HC
    apply joint_prop_beta_transport_stages_iff.1
    intro stage
    induction stage with
    | zero =>
      intro Γ P Q p q hΓ hP hQ H RP RQ
      have W : ContextOracleBeta (proofEraseCtx Γ) (proofEraseCtx Γ) :=
        ⟨ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ)), fun _ => .refl⟩
      have H' := proofErase_joint_zero_certified_oracle_beta heq hs H hΓ hP hQ rfl rfl rfl W
      exact HC hΓ hP hQ H' RP RQ
    | succ stage ih =>
      intro Γ P Q p q hΓ hP hQ H RP RQ
      exact HC hΓ hP hQ
        (proofErase_joint_compare_certify_of_lower_beta heq hs hregistry ih hΓ hP hQ H) RP RQ
  · intro HU Γ P Q p q hΓ hP hQ H RP RQ
    exact HU.forward hΓ hP hQ (H.mono erased_beta_stable_joint_into_union) RP RQ

end Lean4Lean.VEnv.Strengthening
