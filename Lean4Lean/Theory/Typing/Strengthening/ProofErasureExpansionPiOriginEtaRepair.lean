import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionPiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaReadoutRepair

/-! # Eta annotation repair from arbitrary controlled type paths

Full Pi-origin coverage supplies the retained component histories automatically.
The assigned eta expansion reaches the selected annotation using controlled
beta-expanded computation, while the short function uses one native eta guard.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- An assigned Pi path to an existing native output yields a common eta
target. The assigned eta side uses only controlled beta-expansion stages;
no purity or separately assumed component readout is required. -/
theorem proofErase_eta_union_expansion_type_path_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) native)
    (RT : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) native) :
    ∃ expanded, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) expanded ∧
      ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) expanded := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA'⟩, _, hB⟩ := hPi.forallE_inv henv
  obtain ⟨expanded, RE, RR⟩ := proofErase_native_eta_readout_annotation
    (erased_eta_expansion_union_descent heq hs) hΓ hA hf RN
    (proofErase_expansion_union_pi_readout heq hs hΓ hA' hB RT)
  exact ⟨expanded, .base (erased_eta_expansion_union_eta RE), RR⟩

/-- Finite type computation gives a finite component bound and an explicit
common eta-stage bound. The only extra native stage is the selected eta guard. -/
theorem proofErase_eta_stage_expansion_type_path_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedEtaExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ f) native)
    (RT : ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) native) :
    ∃ later expanded, n ≤ later ∧
      ScopedCompute (ErasedEtaExpansionStage D (max (k+1) later)) (proofEraseCtx Γ)
        (proofErase Γ f) expanded ∧
      ScopedCompute (ErasedEtaExpansionStage D (max (k+1) later)) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) expanded := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA'⟩, _, hB⟩ := hPi.forallE_inv henv
  obtain ⟨later, hn, HR⟩ := proofErase_expansion_stage_pi_readout_later heq hs hΓ hA' hB RT
  obtain ⟨expanded, RL, RR⟩ := proofErase_eta_stage_readout_square heq hs hΓ hA hf RN
    (HR.mono (erased_expansion_into_eta_stage later))
  exact ⟨later, expanded, hn, RL, RR⟩

end Lean4Lean.VEnv.Strengthening
