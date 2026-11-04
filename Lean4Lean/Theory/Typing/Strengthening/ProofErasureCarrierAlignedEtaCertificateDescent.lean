import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionCertificateDescent

/-! # Retaining eta-aware certificates through unused binder insertion

The recovered Pi annotation descends together with its native certificate.
Consequently the lower eta expansion has its own guard at the original stage,
not merely a declarative equality witnessing its output.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- A recovered upper Pi descends with its exact lower native certificate and
both component erasures. The result does not merely reconstruct a typing. -/
theorem proofErase_recovered_pi_certificate_descend
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hf : env.HasType univs Γ f T)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ')
      ((proofErase Γ f).liftN n k) (.forallE A B)) :
    ∃ D C, env.HasType univs Γ f (.forallE D C) ∧
      ScopedTypeRecovery Target (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D) (proofErase (D :: Γ) C)) ∧
      (proofErase Γ D).liftN n k = A ∧ (proofErase (D :: Γ) C).liftN n (k+1) = B := by
  obtain ⟨F, hfF, RF, EF⟩ := proofErase_scoped_recovery_certificate_descend hstep hΓ hΓ' W hf rfl R
  obtain ⟨X, Y, Es, EA, EB⟩ := ProofShape.liftN_forallE_inv EF
  obtain ⟨D, C, rfl, _, ED, EC⟩ := erase_forallE_inv Es
  refine ⟨D, C, hfF, ?_, ?_, ?_⟩
  · simpa only [Es, ← ED, ← EC] using RF
  · simpa only [← ED] using EA
  · simpa only [← EC] using EB

/-- Native eta expansion descends as a primitive certificate. The recovered
lower Pi and its realized sort supply precisely the lower eta guard. -/
theorem erased_nativeEtaExpansion_certificate_descent
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveCertificateDescent (NativeEtaExpansion Step)
      (NativeEtaExpansion Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro R S =>
    obtain ⟨A, B, he, RN, EA, _⟩ := proofErase_recovered_pi_certificate_descend hstep hΓ hΓ' W ht R
    obtain ⟨_, hPi⟩ := he.isType henv hΓ
    obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
    have hA := (EA ▸ S).descend hΓ hΓ' W hA
    have hn : ¬ IsProof Γ e := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
    refine ⟨_, (IsDefEq.eta he).symm.toU.of_l henv hΓ ht, ?_, ?_⟩
    · rw [proofErase_nativeEtaExpansion hΓ hA he hn]
      exact .base (.intro RN (DomainSort.of_typed hΓ hA))
    · rw [proofErase_nativeEtaExpansion hΓ hA he hn]
      simp only [ProofShape.liftN, etaArgument_liftN, EA]
      rw [ProofShape.liftN_comm _ n 1 k 0 (Nat.zero_le _)]

/-- Every finite eta-expanded stage retains its exact lower certificates,
including the native guards of eta and identity expansion. -/
theorem erased_eta_expansion_stage_certificate_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveCertificateDescent (ErasedEtaExpansionStage D stage)
      (ErasedEtaExpansionStage D stage) := by
  intro stage
  induction stage with
  | zero => exact erased_expansion_stage_certificate_descent heq hs 0
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H | H | H
    · obtain ⟨e', HE, R, E⟩ := ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inl H), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_carrier_recovered_singleton_certificate_descent heq ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inl H)), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_computed_joint_prefix_certificate_descent heq ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inr (.inl H))), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_nativeIdentityExpansion_certificate_descent ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inr (.inr (.inl H)))), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_nativeEtaExpansion_certificate_descent ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inr (.inr (.inr H)))), E⟩

/-- Removing an unused binder block retains a certificate over the whole
eta-expanded union, with no new native-coverage premise. -/
theorem erased_eta_expansion_union_certificate_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveCertificateDescent (ErasedEtaExpansionUnion D) (ErasedEtaExpansionUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht ⟨stage, H⟩
  obtain ⟨e', HE, R, E⟩ := erased_eta_expansion_stage_certificate_descent heq hs stage hΓ hΓ' W ht H
  exact ⟨e', HE, R.mono (fun H => ⟨stage, H⟩), E⟩

/-- Actual typed computation certificates reflect through inserted binders at
the unchanged eta stage whenever both raw endpoints are prescribed lifts. -/
theorem proofErase_eta_stage_compute_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ScopedCompute (ErasedEtaExpansionStage D stage) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ScopedCompute (ErasedEtaExpansionStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨e', _, R, E⟩ := proofErase_scoped_compute_certificate_descend
      (erased_eta_expansion_stage_certificate_descent heq hs stage) hΓ hΓ' W ht rfl H
    exact ProofShape.liftN_inj.1 E ▸ R
  · intro H
    have R := H.rename (erased_eta_expansion_stage_rename heq hs stage)
      (ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [subst_bvar_liftN] using R

/-- Native recovery certificates at exact lifted outputs likewise reflect
without changing the stage or assuming general assigned-type coverage. -/
theorem proofErase_eta_stage_recovery_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ScopedTypeRecovery (ErasedEtaExpansionStage D stage) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ScopedTypeRecovery (ErasedEtaExpansionStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨A, _, R, E⟩ := proofErase_scoped_recovery_certificate_descend
      (erased_eta_expansion_stage_certificate_descent heq hs stage) hΓ hΓ' W ht rfl H
    exact ProofShape.liftN_inj.1 E ▸ R
  · intro H
    have R := H.rename (erased_eta_expansion_stage_rename heq hs stage)
      (ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [subst_bvar_liftN] using R

end Lean4Lean.VEnv.Strengthening
