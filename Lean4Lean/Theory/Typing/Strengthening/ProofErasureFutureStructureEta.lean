import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureConstructor
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRigidExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary

/-! # Structure eta supplies future comparison without computation joins

An actual nonproof variable has no computational path to a constructor. Its
structure-eta expansion retains its constructor head under rigid computation.
The future certificate for typed structure eta therefore covers non-joining
endpoints, including records with nonempty and dependent field telescopes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- A typed structure-eta expansion of a retained variable has a full future
comparison with that variable but no computation join in the full union.
Constructor rigidity is the only unfolding restriction; no normalization of
parameters or projected fields is required. -/
theorem structure_eta_future_without_join
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : ps.length = info.nparams)
    (hx : info.nindices = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ (.bvar i) (VExpr.mkApps (.const family ls) ps))
    (hexp : env.HasType univs Γ (structExpand family info ls ps (.bvar i))
      (VExpr.mkApps (.const family ls) ps))
    (hnp : ¬ IsProof Γ (.bvar i)) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (structExpand family info ls ps (.bvar i))) (proofErase Γ (.bvar i)) ∧
      ¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
          (proofErase Γ (structExpand family info ls ps (.bvar i))) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ (.bvar i)) shared := by
  refine ⟨proofErase_structure_eta_family hΓ hi hp hx hm hexp, ?_⟩
  rintro ⟨shared, RL, RR⟩
  have EI : proofErase Γ (.bvar i) = .bvar i := if_neg hnp
  rw [EI] at RR
  obtain rfl := RR.bvar_fixed erased_joint_union_head
  have hn := mt (isProof_congr hΓ (IsDefEq.structEta hi hp hx hm hexp)).1 hnp
  have EC := proofErase_const_spine hΓ hexp hn
  change proofErase Γ (structExpand family info ls ps (.bvar i)) = _ at EC
  rw [EC] at RL
  have hinert {Δ levels args out} :
      ¬ ErasedJointUnion D Δ (ProofShape.mkApps (.const info.ctorName levels) args) out := by
    intro H
    exact erased_joint_union_no_rigid heq (henv.projectionCtorRigid hi) hD H (constHead_mkApps _ _)
  obtain ⟨args, E, _⟩ := RL.const_spine hinert
  have EH := congrArg ProofShape.constHead E
  simp only [ProofShape.constHead, constHead_mkApps] at EH
  cases EH

end Lean4Lean.VEnv.Strengthening
