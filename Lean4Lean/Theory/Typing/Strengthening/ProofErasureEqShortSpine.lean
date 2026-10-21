import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqPropositionEta

/-! # Computation of proper Eq prefixes retains every argument

The typed singleton arity exclusion applies after arbitrary computation of
the supplied arguments. A first-head occurrence is therefore impossible in
any proper prefix of a retained Prop-carrier Eq recursor. This preserves the
whole argument-path certificate, not just the constant head of the output.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A proper prefix of a typed retained Prop-carrier recursor computes only
its arguments. All argument computations are retained at the original context;
neither normality nor recovery of those arguments is assumed. -/
theorem proofErase_joint_union_eq_prop_short_spine
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hk : k < 5)
    (ht : env.HasType univs Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v (.succ .zero) (.sort .zero) P M m Q))
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.const ``Eq.rec [v,.succ .zero])
        (([.sort .zero,P,M,m,Q].map (proofErase Γ)).take k)) out) :
    ∃ args : List ProofShape, out = ProofShape.mkApps (.const ``Eq.rec [v,.succ .zero]) args ∧
      List.Forall₂ (ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ))
        (([.sort .zero,P,M,m,Q].map (proofErase Γ)).take k) args := by
  rcases R.const_spine_or_head with H | ⟨j, changed, target, hj, HA, HS⟩
  · exact H
  have hjk : j ≤ k := by
    simp only [List.length_take, List.length_map, List.length_cons, List.length_nil] at hj
    omega
  rw [List.take_take, Nat.min_eq_left hjk] at HA
  have HT : TypedSource (proofEraseCtx Γ)
      (mkApps (.const ``Eq.rec [v,.succ .zero])
        ([.sort .zero,P,M,m,Q].map (proofErase Γ))) :=
    ⟨_, _, _, hΓ, rfl, ht, proofErase_const_spine hΓ ht hn⟩
  have HT' := HT.computed_prefix (erased_joint_union_descent heq hs) HA
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
      hΓ (by omega) ht hn HA HG
    omega

end Lean4Lean.VEnv.Strengthening
