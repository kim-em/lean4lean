import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqIndexComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointSpineEtaComputation

/-! # Finite spine eta and motive replacements at a fixed observed universe

This extension permits arbitrary typed replacements inside the motive slot of
an Eq universe probe, interleaved with the previously certified spine eta and
full joint computations. It also permits the indices to compute while the
motive is replaced. The observed universe is fixed explicitly; this is
not a contextual closure for changes to arbitrary proposition indices.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Finite paths preserving exposure of the specified minor universe.
Motive replacement needs only actual typed retained endpoints, not equality
or an erased guard relating the two motives. Index changes retain their
original directed computation paths. Other argument contexts remain
outside this fragment. -/
inductive JointProbeMotiveCompute (D : PureObservation.Definitions) (v : VLevel) :
    List ProofShape → ProofShape → ProofShape → Prop where
  | spine : JointSpineEtaCompute D Δ a b → JointProbeMotiveCompute D v Δ a b
  | motive
      (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
      (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
      (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
      (hΓ : OnCtx Γ (env.IsType univs))
      (ht : env.HasType univs Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q) T)
      (hn : ¬ IsProof Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q))
      (ht' : env.HasType univs Γ (eqRecApp r' (.succ .zero) (.sort .zero) P M' (.sort v) Q q') T')
      (hn' : ¬ IsProof Γ (eqRecApp r' (.succ .zero) (.sort .zero) P M' (.sort v) Q q')) :
      JointProbeMotiveCompute D v (proofEraseCtx Γ)
        (proofErase Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q))
        (proofErase Γ (eqRecApp r' (.succ .zero) (.sort .zero) P M' (.sort v) Q q'))
  | indices
      (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
      (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
      (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
      (hΓ : OnCtx Γ (env.IsType univs))
      (ht : env.HasType univs Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q) T)
      (hn : ¬ IsProof Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q))
      (ht' : env.HasType univs Γ (eqRecApp r' (.succ .zero) (.sort .zero) P' M' (.sort v) Q' q') T')
      (hn' : ¬ IsProof Γ (eqRecApp r' (.succ .zero) (.sort .zero) P' M' (.sort v) Q' q'))
      (RP : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ P) (proofErase Γ P'))
      (RQ : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ Q) (proofErase Γ Q')) :
      JointProbeMotiveCompute D v (proofEraseCtx Γ)
        (proofErase Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q))
        (proofErase Γ (eqRecApp r' (.succ .zero) (.sort .zero) P' M' (.sort v) Q' q'))
  | trans : JointProbeMotiveCompute D v Δ a b → JointProbeMotiveCompute D v Δ b c →
      JointProbeMotiveCompute D v Δ a c

/-- Any finite interleaving in this extended fragment preserves the complete
continuation to the specified minor universe. The proof uses certificates of
the original indices at each motive replacement, without normalizing motives. -/
theorem JointProbeMotiveCompute.sort_continuation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : JointProbeMotiveCompute D v Δ a b)
    (RT : ScopedCompute (ErasedJointUnion D) Δ b (.sort v)) :
    ScopedCompute (ErasedJointUnion D) Δ a (.sort v) := by
  induction R with
  | spine R => exact R.sort_continuation heq hs RT
  | motive hregistry hEq hRec hΓ ht hn ht' hn' =>
    exact (proofErase_joint_union_eq_motive_replacement_iff heq hs hregistry hEq hRec hΓ ht hn ht' hn').2 RT
  | indices hregistry hEq hRec hΓ ht hn ht' hn' RP RQ =>
    exact proofErase_joint_union_eq_index_compute_pullback heq hs hregistry hEq hRec
      hΓ ht hn ht' hn' RP RQ RT
  | trans _ _ ih₁ ih₂ => exact ih₁ (ih₂ RT)

/-- Typed motive replacements and the earlier spine eta rules do not enlarge
exposure of the observed universe, even through arbitrary finite interleavings. -/
theorem jointProbeMotiveCompute_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    JointProbeMotiveCompute D v Δ a (.sort v) ↔
      ScopedCompute (ErasedJointUnion D) Δ a (.sort v) :=
  ⟨fun R => R.sort_continuation heq hs .refl, fun R => .spine (.compute R)⟩

/-- The original lower-index criterion survives finite motive replacements,
spine eta, directed index computation and full-joint computation upstairs.
The motive replacements may
use the inserted binders; only their actual endpoint typings are required. -/
theorem eqTypeProbe_motive_paths_sort_below_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q
      (eqApp (.succ .zero) (.sort .zero) (P.liftN n k) (Q.liftN n k))) :
    JointProbeMotiveCompute D v (proofEraseCtx Γ')
      (proofErase Γ' (eqTypeProbe (.succ v) (.sort v) (P.liftN n k) (Q.liftN n k) q)) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  apply (jointProbeMotiveCompute_sort_iff heq hs).trans
  have H := eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec hv hΓ'
    (hP.weakN henv W) (hQ.weakN henv W) hq
  rw [proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ] at H
  exact H.trans (proofErase_joint_union_compare_lift_iff heq hs hΓ hΓ' W hP hQ)

end Lean4Lean.VEnv.Strengthening
