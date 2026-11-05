import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedControlJoinBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePureNormalTailReturn

/-! # The compared-control eta repair survives every non-eta output tail

The previous obstruction is not a failure of native-output comparison. Its
comparison survives arbitrary non-eta conversion tails, and the same first eta
stage still joins the outputs. Non-eta joins remain impossible after those tails.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]
namespace EtaRecoveryJoinBoundary

/-- A concrete pair of compared control functions has stage-zero native result
types whose arbitrary non-eta tails still compare at stage zero and join at eta
stage one, while never acquiring a non-eta common reduct. The universal tails
may themselves use all singleton/expansion stages and need not end in normal
forms. This verifies the normal-endpoint return method on the example that
refutes the stronger stage-zero common-reduct conclusion. -/
theorem compared_control_all_noneta_tails_repaired (D : Definitions) :
    ∃ Γ f g T outL outR, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ f (.forallE (.sort (.succ .zero)) T) ∧
      env.HasType univs Γ g (.forallE (.sort (.succ .zero)) T) ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0)
        (proofEraseCtx Γ) false (proofErase Γ f) (proofErase Γ g) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app f (.sort .zero))) outL ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
        (proofErase Γ (.app g (.sort .zero))) outR ∧
      ∀ left right,
        ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) outL left →
        ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) outR right →
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false left right ∧
        (∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) left shared ∧
          ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) right shared) ∧
        ¬ ∃ shared, ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) left shared ∧
          ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) right shared := by
  obtain ⟨Γ, f, g, T, _, _, L, R, hΓ, hf, hg, Hfg, _, _, _, RNL, RNR,
    HC, HEta, _, Hno, HΔ, HP, HQ, HNP, HNQ, P, Q, v, w, hP, hQ, EP, EQ⟩ :=
    compared_control_outputs_need_eta_join D
  refine ⟨Γ, f, g, T, L, R, hΓ, hf, hg, Hfg, RNL, RNR, ?_⟩
  intro left right RL RR
  have LP := proofErase_pure_normal_expansion_return hΓ hP HΔ (EP ▸ HP) (EP ▸ HNP) (EP ▸ RL)
  have RQ := proofErase_pure_normal_expansion_return hΓ hQ HΔ (EQ ▸ HQ) (EQ ▸ HNQ) (EQ ▸ RR)
  rw [EP] at LP
  rw [EQ] at RQ
  have hzero {Δ a b} (H : LevelPrimitive univs a b) :
      ErasedStaticStructureEtaExpansionStage D 0 Δ a b := .inl (.inr H)
  have Lzero : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) left L :=
    LP.mono hzero
  have Rzero : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) right R :=
    RQ.mono hzero
  have Lone : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) left L :=
    Lzero.mono (erased_static_structure_eta_expansion_stage_mono (by decide : 0 ≤ 1))
  have Rone : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ) right R :=
    Rzero.mono (erased_static_structure_eta_expansion_stage_mono (by decide : 0 ≤ 1))
  refine ⟨.compute Lzero Rzero HC,
    ⟨R, Lone.trans HEta, Rone⟩, ?_⟩
  rintro ⟨shared, LS, RS⟩
  exact Hno ⟨shared, RL.trans LS, RR.trans RS⟩

end EtaRecoveryJoinBoundary
end Lean4Lean.VEnv.Strengthening
