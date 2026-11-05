import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationStructureEta

/-! # Projection congruence for typed computation chains

The actual source projection supplies its field assignment. Ordinary projection
compatibility transports that assignment along each major equation, including
through symmetric and composite chains. No generic major context is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private equality_simAt from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- A forward computation of an actually equal major lifts through a typed
projection. Its actual field typing synchronizes proof erasure at the endpoints. -/
theorem proofErase_scoped_compute_proj_eq
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ m n A)
    (ht : env.HasType univs Γ (.proj s i m) T)
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ m) (proofErase Γ n)) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ (.proj s i m)) (proofErase Γ (.proj s i n)) := by
  have HP := SimAt.proj henv.orderedStrong hΓ (equality_simAt hΓ HE) T ht
  classical
  by_cases hp : IsProof Γ (.proj s i m)
  · have hp' := (isProof_congr hΓ HP).1 hp
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hp']
    exact .refl
  have hp' : ¬ IsProof Γ (.proj s i n) := fun h => hp ((isProof_congr hΓ HP).2 h)
  rw [show proofErase Γ (.proj s i m) = .proj _ _ _ from if_neg hp,
    show proofErase Γ (.proj s i n) = .proj _ _ _ from if_neg hp']
  exact .proj R

/-- Any typed computation chain of majors lifts through an actual projection
at its original field assignment. Dependent fields and the proposition/data
projection guard are handled by ordinary source-typed compatibility. -/
theorem TypedComputationEq.proj
    (hΓ : OnCtx Γ (env.IsType univs)) (H : TypedComputationEq D Γ m n A)
    (ht : env.HasType univs Γ (.proj s i m) T) :
    TypedComputationEq D Γ (.proj s i m) (.proj s i n) T := by
  induction H generalizing T with
  | step HE R =>
    exact .step (SimAt.proj henv.orderedStrong hΓ (equality_simAt hΓ HE) T ht)
      (proofErase_scoped_compute_proj_eq hΓ HE ht R)
  | symm H ih =>
    have ht' := (SimAt.proj henv.orderedStrong hΓ (equality_simAt hΓ H.defeq.symm) T ht).hasType.2
    exact (ih ht').symm
  | trans _ _ ih₁ ih₂ =>
    have HL := ih₁ ht
    exact HL.trans (ih₂ HL.defeq.hasType.2)

end Lean4Lean.VEnv.Strengthening
