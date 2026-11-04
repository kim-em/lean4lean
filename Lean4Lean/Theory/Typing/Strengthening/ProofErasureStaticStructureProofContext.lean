import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeBinder

/-! # Exact native transport across proof binders

Changing a proof binder needs no domain computation or native coverage: its
lookup cannot occur in a retained term. All other identity images recover
directly from the unchanged tail. The full structure/function-eta computation
language therefore transports with the same finite stage and selected output.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Converting an erased proof binder supplies exact native identity images
for any image relation. This uses only ordinary context equality; neither
binder annotation has to compute to the other one. -/
theorem NativeImageTransport.proof_context
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (hp : IsProof (A :: Γ) (.bvar 0)) :
    ImageSubstitution ImageStep (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ)) ProofShape.Subst.id := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HC : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have W : Ctx.SubstEq env univs (B :: Γ) VExpr.Subst.id VExpr.Subst.id (A :: Γ) :=
    substEq_source_convert hΓB (HC.symm henv.ordered) (Ctx.SubstEq.id henv.ordered hΓB)
  have ES : ErasedSubstAgreement (A :: Γ) (B :: Γ) VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    have hn' : ¬ IsProof (B :: Γ) (.bvar i) := mt (isProof_defeqCtx HC).2 hn
    simp only [VExpr.Subst.id, proofErase, if_neg hn', ProofShape.Subst.id]
  apply ImageSubstitution.of_typed hΓB W ES
  intro i T hl hn
  cases hl with
  | zero => exact (hn hp).elim
  | succ hl =>
    simp only [ProofShape.subst_id, proofEraseCtx, contextOracle, TypeOracle.cons]
    exact .bvar

/-- Computation transports exactly across a converted proof binder without
increasing its guard depth. Interpreted images extend through all nested binders. -/
theorem proofErase_static_structure_compute_proof_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (hp : IsProof (A :: Γ) (.bvar 0))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have W : StaticStructureEtaNativeSubstitution.ImageSubstitution D 0
      (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ)) ProofShape.Subst.id :=
    NativeImageTransport.proof_context hΓ HAB hp
  have HR := StaticStructureEtaNativeSubstitution.compute heq hs R hΓA ht rfl rfl W
  simp only [Nat.add_zero, ProofShape.subst_id] at HR
  have EE := proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HAB) ht
  simpa only [EE] using HR

/-- Every selected native type survives conversion of a proof binder exactly,
at its original finite stage. No confluence or forward-binder premise is used. -/
theorem proofErase_static_structure_recovery_proof_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (hp : IsProof (A :: Γ) (.bvar 0))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have W : StaticStructureEtaNativeSubstitution.ImageSubstitution D 0
      (proofEraseCtx (A :: Γ)) (proofEraseCtx (B :: Γ)) ProofShape.Subst.id :=
    NativeImageTransport.proof_context hΓ HAB hp
  have HR := StaticStructureEtaNativeSubstitution.recovery heq hs R hΓA ht rfl rfl W
  simp only [Nat.add_zero, ProofShape.subst_id] at HR
  have EE := proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HAB) ht
  simpa only [EE] using HR

/-- Exact computation transport also holds for the union of all finite stages. -/
theorem proofErase_static_structure_union_compute_proof_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (hp : IsProof (A :: Γ) (.bvar 0))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out := by
  obtain ⟨n, R⟩ := R.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  exact (proofErase_static_structure_compute_proof_context heq hs hΓ HAB hp ht R).mono (fun H => ⟨n, H⟩)

/-- Exact recovery transport also holds for the union of all finite stages. -/
theorem proofErase_static_structure_union_recovery_proof_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (hp : IsProof (A :: Γ) (.bvar 0))
    (ht : env.HasType univs (A :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out := by
  obtain ⟨n, R⟩ := R.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  exact (proofErase_static_structure_recovery_proof_context heq hs hΓ HAB hp ht R).mono (fun H => ⟨n, H⟩)

/-- The still-open forward-binder obligation restricted to retained variables.
The proof-variable case is established above, so this restriction removes a
proved branch rather than assuming a new coverage or confluence theorem. -/
def NativeRetainedForwardBinder (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ A C u e T out}, OnCtx Γ (env.IsType univs) →
    env.IsDefEq univs Γ A C (.sort u) →
    ¬ IsProof (A :: Γ) (.bvar 0) →
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C) →
    env.HasType univs (A :: Γ) e T →
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out →
    ∃ native, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
        (proofErase (C :: Γ) e) native ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ)) out native

/-- Proof binders add no obligation to forward transport. The retained case
is still unproved and already entails all typed type-fork joins via the
function-to-sort test; this is not a smaller sufficient front for strengthening. -/
theorem native_forward_binder_iff_retained
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    NativeForwardBinder D ↔ NativeRetainedForwardBinder D := by
  constructor
  · intro H Γ A C u e T out hΓ HAC _ RA ht RN
    exact H hΓ HAC RA ht RN
  intro H Γ A C u e T out hΓ HAC RA ht RN
  classical
  by_cases hp : IsProof (A :: Γ) (.bvar 0)
  · exact ⟨out, proofErase_static_structure_union_recovery_proof_context heq hs hΓ HAC hp ht RN, .refl⟩
  exact H hΓ HAC hp RA ht RN

end Lean4Lean.VEnv.Strengthening
