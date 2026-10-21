import Lean4Lean.Theory.Typing.Strengthening.ProofErasureParallelBetaReplay

/-! # Stripping one parallel development across a typed beta path

The original parallel diamond, exact replay, and exact forward erasure retain
one parallel step on the residual side of an arbitrary finite beta path.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
open private parallel_strip Compute.toParallel parallel_toCompute
  from Lean4Lean.Theory.Typing.Strengthening.DeclarationConfluence
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- A finite beta path competing with one parallel development from a typed
erasure has a parallel residual from the path's output and a finite beta path
from the parallel output. The parallel step bound is retained exactly. -/
theorem proofErase_parallel_beta_strip
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ProofShape.BetaRed (proofErase Γ e) out)
    (P : ProofShape.BetaPar (proofErase Γ e) reduced) :
    ∃ shared, ProofShape.BetaPar out shared ∧ ProofShape.BetaRed reduced shared := by
  obtain ⟨eR, RR, ER⟩ := proofErase_beta_replay hΓ ht R
  obtain ⟨eP, RP, EP⟩ := proofErase_parallel_beta_replay hΓ ht P
  have hd : Definitions.empty.Deterministic := fun H => H.elim
  obtain ⟨shared, RPS, RRS⟩ := parallel_strip hd RP (Compute.toParallel (Compute.of_beta (D := .empty) RR))
  have HR := proofErase_parallel_beta_forward hΓ (beta_eq hΓ ht RR).hasType.2 RRS
  have HP := proofErase_beta_forward hΓ (beta_eq hΓ ht RP.toCompute.to_beta).hasType.2
    (parallel_toCompute RPS).to_beta
  exact ⟨proofErase Γ shared, ER ▸ HR, EP ▸ HP⟩

end Lean4Lean.VEnv.Strengthening
