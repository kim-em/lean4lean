import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqMotiveEta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointFreshVariableReadout

/-! # Full Eq prefixes whose indices cannot compare

A singleton head step retains comparison of the original proposition indices.
When that comparison is excluded, even the five-argument prefix computes only
its arguments. A fresh proposition index supplies such an exclusion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Without a comparison of the original proposition indices, a retained
five-argument Eq prefix preserves every argument computation. This includes
all joint singleton primitives after arbitrary computation of the arguments. -/
theorem proofErase_joint_union_eq_separated_spine
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q))
    (hsep : ¬ JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q))
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.const ``Eq.rec [v,.succ .zero])
        ([.sort .zero,P,M,m,Q].map (proofErase Γ))) out) :
    ∃ args : List ProofShape, out = mkApps (.const ``Eq.rec [v,.succ .zero]) args ∧
      List.Forall₂ (ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ))
        ([.sort .zero,P,M,m,Q].map (proofErase Γ)) args := by
  rcases R.const_spine_or_head with H | ⟨j, changed, target, hj, HA, HS⟩
  · exact H
  have HT : TypedSource (proofEraseCtx Γ)
      (mkApps (.const ``Eq.rec [v,.succ .zero])
        ([.sort .zero,P,M,m,Q].map (proofErase Γ))) :=
    ⟨_, _, _, hΓ, rfl, ht, proofErase_const_spine hΓ ht hn⟩
  have HT' := HT.computed_prefix (erased_joint_union_descent heq hs) HA
  have hj5 : j ≤ 5 := by simpa only [List.length_map, List.length_cons, List.length_nil] using hj
  rcases erased_joint_union_typed_core_singleton heq hs hregistry HT' HS with HC | HG
  · obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
    have hlen := HA.length_eq
    simp only [List.length_take, List.length_map, List.length_cons, List.length_nil] at hlen
    exact (erased_iota_eqRec_no_root (hregistry.trans hlookup)
      (hr.eqRec_target heq hn).2.1 hRec (constHead_mkApps _ _)
      (.inl ⟨_, _, rfl, by omega⟩) HC).elim
  · have E := proofErase_singleton_eq_prop_computed_prefix_arity heq
      (erased_joint_union_descent heq hs) erased_joint_union_head
      (erased_joint_union_descent heq hs) erased_joint_union_head
      (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
      hΓ hj5 ht hn HA HG
    subst j
    apply (hsep ?_).elim
    apply proofErase_singleton_eq_prop_computed_five_certificate heq
      (erased_joint_union_certificate_descent heq hs) erased_joint_union_head
      (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
      hΓ hΓ (show Ctx.LiftN 0 0 Γ Γ from .zero []) ht hn (H := HG)
    simpa only [List.map_cons, List.map_nil, List.take, ProofShape.liftN_zero] using HA

end Lean4Lean.VEnv.Strengthening
