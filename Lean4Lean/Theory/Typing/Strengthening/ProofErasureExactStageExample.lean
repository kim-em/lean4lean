import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExactStageUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecoveryExample

/-! # A guarded native image beyond old compared-K recovery

The neutral-unit Eq-recursion example yields an exact stage-one image. It can
instantiate any finite computed-joint computation, including further guarded
layers, even though no old compared-K stage recovers its assigned function type.
-/
namespace Lean4Lean.VEnv.Strengthening.ExactStageSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_type_arrow from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedRecoveryExample
variable [Params]

/-- A concrete guarded image transports arbitrary finite computations. The
negative clause is the established old compared-K recovery obstruction, not a
claim of unrestricted native recovery or of a counterexample to strengthening. -/
theorem guarded_image_instantiates
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family levels) (.sort (.succ u)))
    (hD : ∀ c ∈ [family, ``Eq, ``Eq.rec], ∀ levels rhs, ¬ D.unfolds c levels rhs) :
    let F := VExpr.forallE (.sort (.succ .zero)) (.sort (.succ .zero))
    ∃ Γ, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ (.bvar 0) F ∧
      ScopedTypeRecovery (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
        (proofErase Γ (.bvar 0)) (proofErase Γ F) ∧
      (∀ stage A B, ¬ ProofShape.TypeRecovery (ErasedComparedKStage D stage)
        (contextOracle (proofEraseCtx Γ)) (proofErase Γ (.bvar 0)) (.forallE A B)) ∧
      (∀ n e T out, env.HasType univs (F :: Γ) e T →
        ScopedCompute (ErasedComputedJointStage D n) (proofEraseCtx (F :: Γ))
          (proofErase (F :: Γ) e) out →
        ScopedCompute (ErasedComputedJointStage D (n + 1)) (proofEraseCtx Γ)
          (proofErase Γ (e.inst (.bvar 0))) (out.inst (proofErase Γ (.bvar 0)))) := by
  dsimp only
  obtain ⟨Γ, hΓ, ht, HR, HN⟩ := unit_neutral_scoped_recovery_separation
    heq hs hreg hoff hi hp hx hf hS hD
  have HR' : ScopedTypeRecovery (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (.bvar 0))
      (proofErase Γ (.forallE (.sort (.succ .zero)) (.sort (.succ .zero)))) := by
    rw [erase_type_arrow hΓ]
    exact HR.mono (fun H => erased_joint_into_computed 1
      (erased_recursive_singleton_into_joint 1
        (erased_application_into_recursive_singleton 1 (erased_structure_into_application 1 H))))
  refine ⟨Γ, hΓ, ht, HR', HN, ?_⟩
  intro n e T out he R
  exact compute_inst heq hs hΓ ht HR' he R

end Lean4Lean.VEnv.Strengthening.ExactStageSubstitution
