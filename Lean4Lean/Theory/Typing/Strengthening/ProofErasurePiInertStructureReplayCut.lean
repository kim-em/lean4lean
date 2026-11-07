import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStructureTailTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertReplayFailure

/-! # An actual guarded replay failure in the remaining consumed body case

No native-image assumption is made. An arbitrary finite-stage body tail either
replays within budget and relays structure eta to an outer function eta, or
supplies a typed primitive occurrence that fails local budget-preserving replay.
The latter is still an open case, not a strengthening counterexample.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- The consumed structure case for an arbitrary counted body tail. Its only
remaining replay alternative is a witnessed local failure, with the same
endpoints and count, under the actual one-binder endpoint map. The failure's
root extraction excludes stage-zero roots and retains the precise lifted map.
It does not assert failure of whole-path transport or of field readout. -/
theorem pi_inert_consumed_structure_minimum_function_eta_or_replay_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = A :: Δ)
    (hm : env.HasType univs Γ m (.const family []))
    (RB : ScopedComputeCount (PiInertStage D bodyStage) pb (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) (proofErase Γ m))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (RTail : ScopedComputeCount (PiInertStage D tailStage) tailCost (A :: Δ) target body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') xs') major)
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ (.proj family 0 major) out)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (hcost : cp + 1 + cd + pb + 1 + tailCost + ca + cs + cf ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.proj family 0 original) out → cost ≤ j) :
    (∃ Γ₀, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ ∧
      GlobalPairFunctionEtaProjection D Γ₀ family info (target.inst x') out) ∨
    PiInertCountedReplayFailure D tailStage RTail Δ (ProofShape.Subst.one x') := by
  obtain ⟨_, WI⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  obtain ⟨expanded, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_nativeMaskedStructureExpansion_descent hstep) hΓ hm rfl rfl (.base H)
  have HTtarget : TypedSource (A :: Δ) target :=
    ⟨Γ, expanded, _, hΓ, EΓ, HE.hasType.2, EE⟩
  rcases pi_inert_counted_substitution_or_failure heq hs RTail HTtarget WI with
      ⟨later, j, hj, RJ⟩ | HF
  · have RT : ScopedComputeCount (PiInertStage D later) j Δ
        (target.inst x') (body'.inst x') := by
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RJ
    exact .inl (pi_inert_consumed_structure_projection_minimum_function_eta_of_tail
      heq hs hguard hstep hi hp hf hz hadm hshape hD HT RN SD RP HR RD hΓ EΓ hm RB H
      RT RX RS RF hout hproj (by omega) hmin)
  · exact .inr HF

end Lean4Lean.VEnv.Strengthening
