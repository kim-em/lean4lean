import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqMotiveReplacement

/-! # Pulling universe exposure back along index computations

The comparison compute rule retains the original indices while any typed
motive may be used at either endpoint. This is a backward observation theorem;
forward transport after contracting an index is a separate obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- If both original indices compute to the changed indices, universe exposure
of the changed probe implies exposure of the original probe. Motives, recursor
universes and proof majors may change independently, subject to actual source
typing and retention. No comparison transitivity or beta-stability is assumed. -/
theorem proofErase_joint_union_eq_index_compute_pullback
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q) T)
    (hn : ¬ IsProof Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q))
    (ht' : env.HasType univs Γ (eqRecApp r' (.succ .zero) (.sort .zero) P' M' (.sort v) Q' q') T')
    (hn' : ¬ IsProof Γ (eqRecApp r' (.succ .zero) (.sort .zero) P' M' (.sort v) Q' q'))
    (RP : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ P'))
    (RQ : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ Q) (proofErase Γ Q'))
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp r' (.succ .zero) (.sort .zero) P' M' (.sort v) Q' q')) (.sort v)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q)) (.sort v) := by
  apply (proofErase_joint_union_eq_universe_minor_iff heq hs hregistry hEq hRec hΓ ht hn).2
  exact .compute RP RQ
    ((proofErase_joint_union_eq_universe_minor_iff heq hs hregistry hEq hRec hΓ ht' hn').1 R)

end Lean4Lean.VEnv.Strengthening
