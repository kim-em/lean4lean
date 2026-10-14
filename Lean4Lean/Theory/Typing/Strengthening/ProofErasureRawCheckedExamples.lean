import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawCheckedK
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCheckedBoundary

/-! # Computation from source-checked lambda guards

The Eq.rec source itself gives its endpoint lambdas a common type. Checking
compares their constant bodies and obtains domain alignment from that typing;
no separate erased certificate of the domains is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : PureObservation.Definitions}

/-- Typed Eq.rec computes at stage one when its endpoints are constant-body
lambda probes. Their displayed domains need no input comparison certificate. -/
theorem proofErase_rawChecked_K_probes (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u'))
    (ht : env.HasType univs Γ
      (eqRecApp v w α (domainProbe P) M m (domainProbe Q) p) T) :
    ProofShape.Compute (ErasedRawCheckedKStage D 1)
      (proofErase Γ (eqRecApp v w α (domainProbe P) M m (domainProbe Q) p))
      (proofErase Γ m) := by
  apply proofErase_rawChecked_K_forward heq hs hΓ ht
  rw [proofErase_domainProbe hΓ hP, proofErase_domainProbe hΓ hQ]
  exact .lamCommon (.base .refl)

/-- The same checking guard above arbitrary inserted binders replays below
from the scoped Eq.rec source alone. The result retains its exact erased shape. -/
theorem proofErase_rawChecked_K_probes_below (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u'))
    (ht : env.HasType univs Γ
      (eqRecApp v w α (domainProbe P) M m (domainProbe Q) p) T) :
    ∃ out, env.IsDefEq univs Γ
      (eqRecApp v w α (domainProbe P) M m (domainProbe Q) p) out T ∧
      proofErase Γ out = proofErase Γ m := by
  have R := proofErase_rawChecked_K_probes (D := D) heq hs hΓ hP hQ ht
  have R' := R.liftN (fun H => erased_rawChecked_K_stage_liftN 1 H) (n := n) (k := k)
  obtain ⟨out, H, E⟩ := proofErase_compute_typed_descend
    (erased_rawChecked_K_stage_descent heq hs 1) hΓ hΓ' W ht R'
  exact ⟨out, H, ProofShape.liftN_inj.1 E⟩

/-- The checking guard is strictly larger than the old comparison relation at
all old stages. The example has independently typed domains; replay still
requires the actual source to supply common endpoint types. -/
theorem rawChecked_probes_strict (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (stage : Nat) :
    ProofShape.RawCheckedCompare (ErasedComparedKStage D stage) true
      (proofErase [] (domainProbe (.sort .zero)))
      (proofErase [] (domainProbe (.forallE (.sort .zero) (.sort .zero)))) ∧
    ¬ ErasedRecoveredComparison D stage true []
      (domainProbe (.sort .zero)) (domainProbe (.forallE (.sort .zero) (.sort .zero))) := by
  have hΓ : OnCtx [] (env.IsType univs) := by trivial
  have hP : env.HasType univs [] (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hQ := HasType.forallE hP (HasType.sort (l := .zero) (Γ := [.sort .zero]) (by trivial))
  refine ⟨?_, (checked_probes_strict heq hs stage).2⟩
  rw [proofErase_domainProbe hΓ hP, proofErase_domainProbe hΓ hQ]
  exact .lamCommon (.base .refl)

end Lean4Lean.VEnv.Strengthening
