import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperPivotTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeEtaDiamond

/-! # Native pivot transfer under fresh binders and eta frames

Certificate descent recovers every native output of a lifted typed source in
the original context. Transfer there and typed weakening recover exactly the
same output at the lifted pivot. Eta frames consequently preserve all native
outputs, even when their current source no longer recovers their original guard.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Exact output transfer lifts under any typed fresh binder. Only the source
needs an ordinary representative; the paired pivot may be raw syntax. -/
theorem NativeOutputTransfer.lift
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : WrapperTypeWitness Γ source T)
    (SD : DomainSort (proofEraseCtx Γ) A u)
    (H : NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) source pivot) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (A :: proofEraseCtx Γ)
      (source.liftN 1) (pivot.liftN 1) := by
  obtain ⟨e, T₀, ht, rfl, _⟩ := HT
  obtain ⟨A₀, hA, rfl⟩ := SD.realize hΓ
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  intro out RN
  obtain ⟨C, _, RN₀, EC⟩ := proofErase_scoped_recovery_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓA Ctx.LiftN.one ht rfl RN
  have RP := H _ RN₀
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨n, R⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n R W⟩
  have RL := RP.rename hrename (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
  simpa only [subst_bvar_liftN, proofEraseCtx, EC] using RL

/-- With a fixed annotation, transfer of all body outputs transfers all
lambda outputs, including arbitrary conversions after forming the Pi. -/
theorem NativeOutputTransfer.lambda_body
    (H : NativeOutputTransfer Step (A :: Δ) b d) :
    NativeOutputTransfer Step Δ (.lam A b) (.lam A d) := by
  intro out RN
  obtain ⟨B, RB, RT⟩ := RN.lam_compute
  exact (ScopedTypeRecovery.lam (H _ RB)).convert RT

/-- The same raw application argument may occur below the fresh binder on
both sides. It can already have computed away from the original eta variable. -/
theorem NativeOutputTransfer.eta_body
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : WrapperTypeWitness Γ source T)
    (SD : DomainSort (proofEraseCtx Γ) A u)
    (H : NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) source pivot)
    (argument : ProofShape) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.lam A (.app (source.liftN 1) argument))
      (.lam A (.app (pivot.liftN 1) argument)) :=
  ((H.lift heq hs hΓ HT SD).app argument).lambda_body

/-- A paired eta frame preserves native output transfer under its fresh
binder. Neither source nor pivot must still recover the frame's original Pi. -/
theorem NativeOutputTransfer.eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : WrapperTypeWitness Γ source T)
    (SD : DomainSort (proofEraseCtx Γ) A u)
    (H : NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) source pivot) :
    NativeOutputTransfer (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.lam A (.app (source.liftN 1) (etaArgument u)))
      (.lam A (.app (pivot.liftN 1) (etaArgument u))) :=
  ((H.lift heq hs hΓ HT SD).app (etaArgument u)).lambda_body

/-- An eta frame keeps ordinary function typing and the sort of its selected
domain. Later argument and annotation computations need no renewed native Pi. -/
def EtaFrameWitness (Γ : List VExpr) (source A : ProofShape) (u : VLevel) : Prop :=
  ∃ f L M, env.HasType univs Γ f (.forallE L M) ∧
    env.HasType univs Γ L (.sort u) ∧ proofErase Γ f = source ∧ proofErase Γ L = A

/-- The native eta guard supplies its persistent ordinary frame witness. -/
theorem EtaFrameWitness.of_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HT : WrapperTypeWitness Γ source T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      source (.forallE A B)) (SD : DomainSort (proofEraseCtx Γ) A u) :
    EtaFrameWitness Γ source A u := by
  obtain ⟨f, T₀, ht, rfl, _⟩ := HT
  obtain ⟨L, M, hf, hL, EL, _⟩ := proofErase_native_eta_domain_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht RN SD
  exact ⟨f, L, M, hf, hL, rfl, EL⟩

/-- The stored selected domain supplies its typed raw binder. -/
theorem EtaFrameWitness.domain
    (hΓ : OnCtx Γ (env.IsType univs)) (H : EtaFrameWitness Γ source A u) :
    DomainSort (proofEraseCtx Γ) A u := by
  obtain ⟨_, L, _, _, hL, _, EL⟩ := H
  exact ⟨Γ, L, hΓ, rfl, hL, EL⟩

/-- An ordinary eta frame still has a typed retained realization after its
creation guard has been lost by the enclosed function. -/
theorem EtaFrameWitness.source_witness
    (hΓ : OnCtx Γ (env.IsType univs)) (H : EtaFrameWitness Γ source A u)
    (hn : source ≠ .proof) :
    ∃ T, WrapperTypeWitness Γ (.lam A (.app (source.liftN 1) (etaArgument u))) T := by
  obtain ⟨f, L, M, hf, hL, rfl, rfl⟩ := H
  have hnf : ¬ IsProof Γ f := fun hp => hn (proofErase_eq_proof.2 hp)
  exact ⟨_, _, _, (IsDefEq.eta hf).hasType.1, proofErase_nativeEtaExpansion hΓ hL hf hnf, rfl⟩

/-- Scoped computation preserves a realized domain's sort by ordinary replay. -/
theorem ProofShape.DomainSort.scoped_compute
    (hstep : ErasedScopedPrimitiveDescent Step) (SD : DomainSort Δ A u)
    (R : ScopedCompute Step Δ A A') : DomainSort Δ A' u := by
  obtain ⟨Γ, L, hΓ, EΓ, hL, EL⟩ := SD
  obtain ⟨L', HE, EL'⟩ := proofErase_scoped_compute_realize hstep hΓ hL EΓ EL R
  exact ⟨Γ, L', hΓ, EΓ, HE.hasType.2, EL'⟩

/-- Computation of the enclosed raw term lifts through the typed eta frame. -/
theorem static_structure_eta_frame_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (SD : DomainSort Δ A u)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source target) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ
      (.lam A (.app (source.liftN 1) argument))
      (.lam A (.app (target.liftN 1) argument)) :=
  .lam .refl (.app (static_structure_compute_under_domain heq hs SD R) .refl)

end Lean4Lean.VEnv.Strengthening
