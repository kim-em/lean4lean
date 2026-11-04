import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaPiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedEtaReadoutRepair

/-! # Eta annotation repair from eta-aware type paths

Typed Pi-origin coverage supplies the retained component histories automatically.
The assigned eta expansion reaches the selected annotation using eta-aware
computation, while the short function uses one native eta guard.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- An assigned Pi path to an existing native output yields a common eta
target. The assigned eta side may also use native eta expansion;
no purity or separately assumed component readout is required. -/
theorem proofErase_eta_union_type_path_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) native)
    (RT : ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) native) :
    ∃ expanded, ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ f) expanded ∧
      ScopedCompute (ErasedEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) expanded := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA'⟩, _, hB⟩ := hPi.forallE_inv henv
  obtain ⟨expanded, RE, RR⟩ := proofErase_native_eta_readout_annotation
    (erased_eta_expansion_union_descent heq hs) hΓ hA hf RN
    (proofErase_eta_union_pi_readout heq hs hΓ hA' hB RT)
  exact ⟨expanded, .base (erased_eta_expansion_union_eta RE), RR⟩

/-- Finite type computation gives a finite component bound and an explicit
common eta-stage bound. The only extra native stage is the selected eta guard. -/
theorem proofErase_eta_stage_type_path_square
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (RN : ScopedTypeRecovery (ErasedEtaExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ f) native)
    (RT : ScopedCompute (ErasedEtaExpansionStage D n) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) native) :
    ∃ later expanded, n ≤ later ∧
      ScopedCompute (ErasedEtaExpansionStage D (max (k+1) later)) (proofEraseCtx Γ)
        (proofErase Γ f) expanded ∧
      ScopedCompute (ErasedEtaExpansionStage D (max (k+1) later)) (proofEraseCtx Γ)
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) expanded := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA'⟩, _, hB⟩ := hPi.forallE_inv henv
  obtain ⟨later, hn, HR⟩ := proofErase_eta_stage_pi_readout_later heq hs hΓ hA' hB RT
  obtain ⟨expanded, RL, RR⟩ := proofErase_eta_stage_readout_square heq hs hΓ hA hf RN
    HR
  exact ⟨later, expanded, hn, RL, RR⟩

end Lean4Lean.VEnv.Strengthening
