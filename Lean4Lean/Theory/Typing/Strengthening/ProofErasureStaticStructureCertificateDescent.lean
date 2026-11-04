import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureEtaStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaCertificateDescent

/-! # Certificate descent with full masked structure eta

Native family certificates and the exact closed field mask descend together.
This retains a lower primitive path, not merely a declarative equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Structure eta descends with its own native family certificate. All field
masks remain fixed, and all occurrence parameters are recovered below insertion. -/
theorem erased_nativeMaskedStructureExpansion_certificate_descent
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveCertificateDescent (NativeMaskedStructureExpansion Step)
      (NativeMaskedStructureExpansion Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro hi hx ha hp RN =>
    rename_i family info ls rawPs
    obtain ⟨A, heA, RL, EA⟩ := proofErase_scoped_recovery_certificate_descend hstep hΓ hΓ' W ht rfl RN
    obtain ⟨rawPs, Es, Eps⟩ := ProofShape.liftN_const_spine_inv EA
    obtain ⟨ps, rfl, rfl⟩ := proofErase_const_spine_inv Es
    have hps : ps.length = info.nparams := by
      have H := congrArg List.length Eps
      simp only [List.length_map] at H
      omega
    have hc := (StructureReplay.expansion_typed_iff henv hΓ hi hps hx heA).2 ha
    have HE := (IsDefEq.structEta hi hps hx heA hc).symm
    have hn : ¬ IsProof Γ e := fun H => RL.ne_proof (proofErase_eq_proof.2 H)
    have hnc : ¬ IsProof Γ (structExpand family info ls ps e) :=
      fun H => hn ((isProof_congr hΓ HE).2 H)
    refine ⟨structExpand family info ls ps e, HE.toU.of_l henv hΓ ht, ?_, ?_⟩
    · rw [proofErase_nativeStructureOutput hΓ hi hps hc hnc]
      exact .base (.intro hi hx ha (by simpa only [List.length_map] using hps) (by simpa only [Es] using RL))
    · rw [proofErase_nativeStructureOutput hΓ hi hps hc hnc, nativeStructureOutput_liftN, ← Eps]

/-- Every finite eta-expanded stage retains its exact lower certificates,
including the native guards of eta and identity expansion. -/
theorem erased_static_structure_eta_expansion_stage_certificate_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveCertificateDescent (ErasedStaticStructureEtaExpansionStage D stage)
      (ErasedStaticStructureEtaExpansionStage D stage) := by
  intro stage
  induction stage with
  | zero => exact erased_expansion_stage_certificate_descent heq hs 0
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H | H | H | H
    · obtain ⟨e', HE, R, E⟩ := ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inl H), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_carrier_recovered_singleton_certificate_descent heq ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inl H)), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_computed_joint_prefix_certificate_descent heq ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inr (.inl H))), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_nativeIdentityExpansion_certificate_descent ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inr (.inr (.inl H)))), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_nativeEtaExpansion_certificate_descent ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inr (.inr (.inr (.inl H))))), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_nativeMaskedStructureExpansion_certificate_descent ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inr (.inr (.inr (.inr H))))), E⟩

/-- Removing an unused binder block retains a certificate over the whole
eta-expanded union, with no new native-coverage premise. -/
theorem erased_static_structure_eta_expansion_union_certificate_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveCertificateDescent (ErasedStaticStructureEtaExpansionUnion D) (ErasedStaticStructureEtaExpansionUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht ⟨stage, H⟩
  obtain ⟨e', HE, R, E⟩ := erased_static_structure_eta_expansion_stage_certificate_descent heq hs stage hΓ hΓ' W ht H
  exact ⟨e', HE, R.mono (fun H => ⟨stage, H⟩), E⟩

/-- Actual typed computation certificates reflect through inserted binders at
the unchanged eta stage whenever both raw endpoints are prescribed lifts. -/
theorem proofErase_static_structure_stage_compute_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨e', _, R, E⟩ := proofErase_scoped_compute_certificate_descend
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs stage) hΓ hΓ' W ht rfl H
    exact ProofShape.liftN_inj.1 E ▸ R
  · intro H
    have R := H.rename (erased_static_structure_eta_expansion_stage_rename heq hs stage)
      (ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [subst_bvar_liftN] using R

/-- Native recovery certificates at exact lifted outputs likewise reflect
without changing the stage or assuming general assigned-type coverage. -/
theorem proofErase_static_structure_stage_recovery_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨A, _, R, E⟩ := proofErase_scoped_recovery_certificate_descend
      (erased_static_structure_eta_expansion_stage_certificate_descent heq hs stage) hΓ hΓ' W ht rfl H
    exact ProofShape.liftN_inj.1 E ▸ R
  · intro H
    have R := H.rename (erased_static_structure_eta_expansion_stage_rename heq hs stage)
      (ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [subst_bvar_liftN] using R

end Lean4Lean.VEnv.Strengthening
