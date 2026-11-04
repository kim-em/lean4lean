import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiReadoutSelection

/-! # Native eta repair from retained Pi components

Pi readout retains the assigned domain's computation to the selected native
domain. That path alone aligns eta annotations; it may use arbitrary guarded
computation, without purity or beta/universe factorization.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Pi readout selects a native eta target reached by component computation
from the assigned eta expansion. The native and component relations may be
different. No exact assigned-Pi recovery or native image premise is used. -/
theorem proofErase_native_eta_readout_annotation
    (hstep : ErasedScopedPrimitiveDescent Recovery)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) native)
    (H : PiReadout Component (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) native) :
    ∃ expanded, NativeEtaExpansion Recovery (proofEraseCtx Γ) (proofErase Γ f) expanded ∧
      ScopedCompute Component (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) expanded := by
  obtain ⟨D', C, _, RP, HAD, _, RA, _⟩ := proofErase_native_pi_readout hstep hΓ hf RN H
  have hD : env.HasType univs Γ D' (.sort u) := hA.defeqU_l henv hΓ HAD
  have hn : ¬ IsProof Γ f := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
  refine ⟨.lam (proofErase Γ D') (.app ((proofErase Γ f).liftN 1) (etaArgument u)),
    NativeEtaExpansion.intro RP (DomainSort.of_typed hΓ hD), ?_⟩
  rw [proofErase_nativeEtaExpansion hΓ hA hf hn]
  exact .lam RA .refl

/-- Finite eta stages repair the entire assigned eta expansion using the
native guard's next stage and the retained component bound. The right path
can include guarded computations that do not factor through raw beta joins. -/
theorem proofErase_eta_stage_readout_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedEtaExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ f) native)
    (H : PiReadout (ErasedEtaExpansionStage D n) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) native) :
    ∃ expanded, ScopedCompute (ErasedEtaExpansionStage D (max (k + 1) n)) (proofEraseCtx Γ)
        (proofErase Γ f) expanded ∧
      ScopedCompute (ErasedEtaExpansionStage D (max (k + 1) n)) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) expanded := by
  obtain ⟨expanded, RE, RR⟩ := proofErase_native_eta_readout_annotation
    (erased_eta_expansion_stage_descent heq hs k) hΓ hA hf RN H
  have RE' : ErasedEtaExpansionStage D (k + 1) (proofEraseCtx Γ) (proofErase Γ f) expanded :=
    .inr (.inr (.inr (.inr RE)))
  exact ⟨expanded, .base (erased_eta_expansion_stage_mono (Nat.le_max_left _ _) RE'),
    RR.mono (fun R => erased_eta_expansion_stage_mono (Nat.le_max_right _ _) R)⟩

/-- At the union, an actual native Pi readout suffices for a common eta
target, including impure sources and guarded component computations. This
does not assert that every assigned/native pair has such a readout. -/
theorem proofErase_eta_union_readout_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) native)
    (H : PiReadout (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase (A :: Γ) B) native) :
    ∃ expanded, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) expanded ∧
      ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) expanded := by
  obtain ⟨expanded, RE, RR⟩ := proofErase_native_eta_readout_annotation
    (erased_eta_expansion_union_descent heq hs) hΓ hA hf RN H
  exact ⟨expanded, .base (erased_eta_expansion_union_eta RE), RR⟩

end Lean4Lean.VEnv.Strengthening
