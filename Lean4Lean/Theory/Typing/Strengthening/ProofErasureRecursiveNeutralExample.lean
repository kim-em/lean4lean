import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecursiveNeutral
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary

/-! # A non-neutral binder change beyond exact recovered domains

The binder types `(F (fun p => f p)) → Prop` and `(F f) → Prop` differ in
their input domains. The old result-only relation cannot relate them, and
they have no computational join. Recursive neutral checking nevertheless
transports their typed body comparisons and all typed carrier guards.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private context native assigned nativeRaw assignedRaw erasures context_wf
  types_equal normal_forms
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaRecoveryJoinBoundary
open private scoped_normal_fixed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
open private native_walk_typing
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeGuard
variable [Params]

/-- A target native declaration prefix consumes an arbitrary typed guard
whose carrier differs recursively at neutral leaves. Literal native recovery,
both target argument typings, and the actual proposition comparison are
constructed; no native-type comparison or computational join is assumed. -/
theorem proofErase_native_recursive_neutral_propositions
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : InstForallsC env univs Γ (ci.type.instL ls) params (.forallE B (.sort .zero)))
    (HAB : env.IsDefEqU univs Γ A B)
    (HT : NeutralTypeChange 0 (proofErase Γ A) (proofErase Γ B))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y)) :
    let f := VExpr.mkApps (.const c ls) params
    env.HasType univs Γ (.app f x) (.sort .zero) ∧
      env.HasType univs Γ (.app f y) (.sort .zero) ∧
      JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) mode
        (proofErase Γ (.app f x)) (proofErase Γ (.app f y)) := by
  have hf := native_walk_typing (HasType.const hc hw hl) HW
  have hn := not_isProof_function_to_sort hΓ hf
  have RF := proofErase_const_native_recovery (Step := ErasedBetaStableJoint D) hΓ hc hw hl HW hn
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  rw [show proofErase Γ (.forallE B (.sort .zero)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RF
  have HG := proofErase_certified_recursive_neutral_carrier heq hs hΓ hx hy HAB HT H
  have hL := hf.app (hx.defeqU_r henv hΓ HAB)
  have hR := hf.app (hy.defeqU_r henv hΓ HAB)
  refine ⟨hL, hR, ?_⟩
  rw [show proofErase Γ (.app (VExpr.mkApps (.const c ls) params) x) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hL),
    show proofErase Γ (.app (VExpr.mkApps (.const c ls) params) y) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ hR)]
  exact .appCarrier RF (.leaf .refl) HG

private theorem arrow_erase (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) :
    proofErase Γ (.forallE A (.sort .zero)) = .forallE (proofErase Γ A) (.sort .zero) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  rw [show proofErase Γ (.forallE A (.sort .zero)) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA (HasType.sort (by trivial)))),
    show proofErase (A :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓA (HasType.sort (by trivial)))]

/-- Typed non-neutral binders lie strictly outside the old neutral-result
relation and have no computational join in the full union. They are related
by recursive neutral change, are inhabited, and support certified transport
of all typed carrier guards and all typed body comparisons. This separates
the new structural criterion from the earlier exact-domain criterion; it is
not a strict-smallness result for PropositionFront. -/
theorem recursive_neutral_function_binder_example
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' A B u, OnCtx Γ' (env.IsType univs) ∧ env.IsDefEq univs Γ' A B (.sort u) ∧
      NeutralTypeChange 0 (proofErase Γ' A) (proofErase Γ' B) ∧
      ¬ NeutralResultChange 0 (proofErase Γ' A) (proofErase Γ' B) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' A) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ') (proofErase Γ' B) shared) ∧
      (∃ x, env.HasType univs Γ' x A) ∧
      (∀ x y, env.HasType univs Γ' x A → env.HasType univs Γ' y A →
        (JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ')
          (proofErase Γ' A) (proofErase Γ' x) (proofErase Γ' y) ↔
        JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ')
          (proofErase Γ' B) (proofErase Γ' x) (proofErase Γ' y))) ∧
      (∀ x y T mode, env.HasType univs (A :: Γ') x T → env.HasType univs (A :: Γ') y T →
        JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ')) mode
          (proofErase (A :: Γ') x) (proofErase (A :: Γ') y) →
        JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (B :: Γ')) mode
          (proofErase (B :: Γ') x) (proofErase (B :: Γ') y)) := by
  have hC := context_wf hΓ
  have HAB : env.IsDefEq univs (context Γ)
      (.forallE assigned (.sort .zero)) (.forallE native (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) :=
    .forallEDF types_equal (HasType.sort (by trivial))
  obtain ⟨EN, EA⟩ := erasures hΓ
  have EFA := (arrow_erase hC types_equal.hasType.1).trans
    (congrArg (fun x => ProofShape.forallE x (.sort .zero)) EA)
  have EFN := (arrow_erase hC types_equal.hasType.2).trans
    (congrArg (fun x => ProofShape.forallE x (.sort .zero)) EN)
  have HT : NeutralTypeChange 0 (proofErase (context Γ) (.forallE assigned (.sort .zero)))
      (proofErase (context Γ) (.forallE native (.sort .zero))) := by
    rw [EFA, EFN]
    exact .forallE (.neutral (i := 1) (j := 1) (args := [_]) (args' := [_]) (by omega) (by omega)) .refl
  refine ⟨context Γ, _, _, _, hC, HAB, HT, ?_, ?_, ?_, ?_, ?_⟩
  · intro H
    rw [EFA, EFN] at H
    obtain ⟨C', HE, _⟩ := H.forallE_inv
    have HD := (ProofShape.forallE.inj HE).1
    cases HD
  · rintro ⟨shared, RA, RN⟩
    rw [EFA] at RA
    rw [EFN] at RN
    obtain ⟨da, ca, rfl, Rda⟩ := RA.forallE_domain_inv (@erased_joint_union_head _ D)
    obtain ⟨dn, cn, HE, Rdn⟩ := RN.forallE_domain_inv (@erased_joint_union_head _ D)
    cases HE
    have HA := scoped_normal_fixed Rda (fun Δ =>
      (normal_forms (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).2)
    have HN := scoped_normal_fixed Rdn (fun Δ =>
      (normal_forms (Step := ErasedJointUnion D) (@erased_joint_union_head _ D) Δ).1)
    cases HA.symm.trans HN
  · have hP : env.HasType univs (assigned :: context Γ)
        (.forallE (.sort .zero) (.bvar 0)) (.sort .zero) :=
      (IsDefEq.sortDF (by trivial) (by trivial)
        (show VLevel.imax (.succ .zero) .zero ≈ .zero from rfl)).defeq
          (HasType.forallE (HasType.sort (by trivial)) (HasType.bvar .zero))
    exact ⟨_, HasType.lam types_equal.hasType.1 hP⟩
  · intro x y hx hy
    exact ⟨proofErase_certified_recursive_neutral_carrier heq hs hC hx hy HAB.toU HT,
      proofErase_certified_recursive_neutral_carrier heq hs hC (HAB.defeq hx) (HAB.defeq hy)
        HAB.symm.toU HT.symm⟩
  · intro x y T mode hx hy H
    exact proofErase_certified_recursive_neutral_context heq hs hC HAB HT hx hy H

end Lean4Lean.VEnv.Strengthening
