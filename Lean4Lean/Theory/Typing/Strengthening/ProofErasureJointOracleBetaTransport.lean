import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDependentCarrierBeta

/-! # Recovery through beta reduction of context oracles

The expression stays fixed. Its selected recovered type may beta-reduce while
the context oracle beta-reduces. Conversion forks use lower-stage computation
commutation and the certified target's context substitution closure; arbitrary
joint confluence and exact output preservation are not assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_forallE_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

omit [Params] in
private theorem oracle_cons_beta
    (HO : ∀ i, ProofShape.BetaRed (contextOracle Δ i) (contextOracle Δ' i)) :
    ∀ i, ProofShape.BetaRed (contextOracle (A :: Δ) i) (contextOracle (A :: Δ') i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (HO i).liftN

private theorem identity_cons (W : ContextSubstitution Δ Δ' ProofShape.Subst.id) :
    ContextSubstitution (A :: Δ) (A :: Δ') ProofShape.Subst.id := by
  have E : ProofShape.Subst.id.lift = ProofShape.Subst.id := by
    funext i
    cases i <;> simp [ProofShape.Subst.lift, ProofShape.Subst.id, ProofShape.liftN]
  intro Γ hΓ EΓ
  simpa only [ProofShape.subst_id, E] using W.cons (A := A) hΓ EΓ

private theorem recovery_oracle_beta
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hsubst : ∀ {Δ Δ' a b τ}, Target Δ a b → ContextSubstitution Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (commute : ∀ {Γ e T out reduced}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e) out →
      ProofShape.BetaRed (proofErase Γ e) reduced →
      ∃ shared, ProofShape.BetaRed out shared ∧ ScopedCompute Target (proofEraseCtx Γ) reduced shared)
    (R : ScopedTypeRecovery Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : ContextSubstitution Δ Δ' ProofShape.Subst.id)
    (HO : ∀ i, ProofShape.BetaRed (contextOracle Δ i) (contextOracle Δ' i)) :
    ∃ out', ScopedTypeRecovery Target Δ' source out' ∧ ProofShape.BetaRed out out' := by
  induction R generalizing Γ e T Δ' with
  | bvar => exact ⟨_, .bvar, HO _⟩
  | sort hu => exact ⟨_, .sort hu, .refl⟩
  | const hc hw hn => exact ⟨_, .const hc hw hn, .refl⟩
  | lam R ih =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb
      (by simp only [proofEraseCtx, EA, EΓ]) Eb (identity_cons W) (oracle_cons_beta HO)
    exact ⟨_, .lam HR, .forallE .refl HB⟩
  | app R ih =>
    obtain ⟨f, a, rfl, _, Ef, Ea⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, _⟩ := ht.app_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hf EΓ Ef W HO
    obtain ⟨A', B', rfl, _, HB⟩ := beta_forallE_parts HB
    exact ⟨_, .app HR, by simpa only [ProofShape.inst_eq_subst] using HB.subst⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨outA, HA, BA⟩ := ihA hΓ hA EΓ EA W HO
    have EA' := (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := Δ') BA).sort_fixed (fun H => H.elim)
    subst outA
    obtain ⟨outB, HB, BB⟩ := ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB
      (by simp only [proofEraseCtx, EA, EΓ]) EB (identity_cons W) (oracle_cons_beta HO)
    have EB' := (ScopedCompute.beta (Step := fun _ _ _ => False) (Δ := Δ') BB).sort_fixed (fun H => H.elim)
    subst outB
    exact ⟨_, .forallE HA HB, .refl⟩
  | proj hi HT hj hlen R ih =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨out', HR, HB⟩ := ih hΓ hm.hasType.2 EΓ Em W HO
    obtain ⟨args', rfl, Hargs⟩ := HB.const_spine
    exact ⟨_, .proj hi HT hj (Hargs.length_eq.symm.trans hlen) HR, projectionType_beta Hargs .refl⟩
  | @convert Δ₀ e₀ A₀ B₀ R RC ih =>
    obtain ⟨out', HR, HB⟩ := ih hΓ ht EΓ Ee W HO
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ ht
      (by simpa only [EΓ, Ee] using R)
    obtain ⟨u, hA⟩ := heA.isType henv hΓ
    have RC' : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ A) B₀ := by
      simpa only [EΓ, EA] using RC
    have HB' : ProofShape.BetaRed (proofErase Γ A) out' := by rw [EA]; exact HB
    obtain ⟨shared, BS, CS⟩ := commute hΓ hA RC' HB'
    have CS : ScopedCompute Target Δ₀ out' shared := EΓ ▸ CS
    have CS' := CS.subst hsubst W
    simp only [ProofShape.subst_id] at CS'
    exact ⟨shared, HR.convert CS', BS⟩

/-- Type recovery at stage n+1 survives an interpreted identity context change
whose oracle entries beta-reduce, using proposition transport only at stage n.
The expression is unchanged and its old selected type has a pure beta path to
the new selected type. No beta closure of arbitrary recovery outputs is assumed. -/
theorem proofErase_joint_recovery_oracle_beta_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : ContextSubstitution (proofEraseCtx Γ) Δ' ProofShape.Subst.id)
    (HO : ∀ i, ProofShape.BetaRed (contextOracle (proofEraseCtx Γ) i) (contextOracle Δ' i))
    (R : ScopedTypeRecovery (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (ErasedBetaStableJoint D) Δ' (proofErase Γ e) out' ∧
      ProofShape.BetaRed out out' :=
  recovery_oracle_beta (erased_joint_stage_descent heq hs (stage + 1))
    (erased_beta_stable_joint_subst heq hs)
    (proofErase_joint_stage_beta_commute_of_lower_beta heq hs hregistry Hbeta)
    R hΓ ht rfl rfl W HO

/-- The same forward oracle transport for stage-zero recovery is unconditional
on proposition beta transport. The certified target may use later union steps. -/
theorem proofErase_joint_zero_recovery_oracle_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (W : ContextSubstitution (proofEraseCtx Γ) Δ' ProofShape.Subst.id)
    (HO : ∀ i, ProofShape.BetaRed (contextOracle (proofEraseCtx Γ) i) (contextOracle Δ' i))
    (R : ScopedTypeRecovery (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (ErasedBetaStableJoint D) Δ' (proofErase Γ e) out' ∧
      ProofShape.BetaRed out out' :=
  recovery_oracle_beta (erased_joint_stage_descent heq hs 0) (erased_beta_stable_joint_subst heq hs)
    (proofErase_joint_zero_beta_commute heq hs) R hΓ ht rfl rfl W HO

/-- Reducing a typed binder domain transports recovery of every typed body to
that actual new context. The old selected type only beta-reduces; the original
expression and its erasure through context conversion are preserved. -/
theorem proofErase_joint_recovery_domain_beta_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (RA : VExpr.BetaRed A B) (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedJointStage D (stage + 1))
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) e) out) :
    ∃ out', ScopedTypeRecovery (ErasedBetaStableJoint D) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out' ∧ ProofShape.BetaRed out out' := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have HE := beta_eq hΓ hA RA
  have W : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ)) ProofShape.Subst.id :=
    ContextSubstitution.of_defeqCtx hΓ (.succ .zero HE)
  have HO : ∀ i, ProofShape.BetaRed (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (B :: Γ)) i) := by
    intro i
    cases i with
    | zero => exact (proofErase_beta_forward hΓ hA RA).liftN
    | succ i => exact .refl
  obtain ⟨out', HR, HB⟩ := proofErase_joint_recovery_oracle_beta_of_lower_beta
    heq hs hregistry Hbeta hΓA ht W HO R
  rw [proofErase_defeqCtx hΓA (.succ .zero HE) ht] at HR
  exact ⟨out', HR, HB⟩

end Lean4Lean.VEnv.Strengthening
