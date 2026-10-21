import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeChangePaths
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveBoxContextExample

/-! # A hidden Box carrier outside the structural relation and certified joins

A beta redex hides one side of the earlier no-join Box conversion. The mixed
path transports full certified checking although the endpoints are neither
BoxTypeChange-related nor computationally joinable in the certified relation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private BoxCarrierAlignment.erase_box
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveBoxGuard
variable [Params]

private def wrapType (A : VExpr) : VExpr :=
  .app (.lam (.sort (.succ .zero)) (.bvar 0)) A

private theorem identity_typed : env.HasType univs Γ
    (.lam (.sort (.succ .zero)) (.bvar 0))
    (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
  .lam (.sort (by trivial)) (.bvar .zero)

private theorem wrap_typed (hA : env.HasType univs Γ A (.sort (.succ .zero))) :
    env.HasType univs Γ (wrapType A) (.sort (.succ .zero)) := identity_typed.app hA

private theorem wrap_erasure (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort (.succ .zero))) :
    proofErase Γ (wrapType A) =
      .app (.lam (.sort (.succ .zero)) (.bvar 0)) (proofErase Γ A) := by
  have hΓS : OnCtx (VExpr.sort (.succ .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  rw [show proofErase Γ (wrapType A) = .app _ _ from
      if_neg (not_isProof_of_sort hΓ (wrap_typed hA)),
    show proofErase Γ (.lam (.sort (.succ .zero)) (.bvar 0)) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ identity_typed),
    show proofErase Γ (.sort (.succ .zero)) = .sort (.succ .zero) from
      if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial))),
    show proofErase (VExpr.sort (.succ .zero) :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_of_sort hΓS (HasType.bvar .zero))]

/-- No relation satisfying the exact-sort local law covers all typed beta
conversion directly. Prop and its identity-wrapper expansion are typed equal
and have a mixed path, but cannot be related. Thus general coverage must use
paths (or a weaker exposure interface), rather than the raw local relation. -/
theorem type_change_laws_miss_typed_beta
    (L : TypeChangeLaws Step Rel) (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ A B, env.IsDefEq univs Γ A B (.sort (.succ .zero)) ∧
      TypeChangePath Rel Γ (.succ .zero) A B ∧
      ¬ Rel 0 (proofErase Γ A) (proofErase Γ B) := by
  have hP : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hW := wrap_typed hP
  have EP : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ hP)
  have EW := wrap_erasure hΓ hP
  have R : ProofShape.BetaRed (proofErase Γ (wrapType (.sort .zero)))
      (proofErase Γ (.sort .zero)) := by
    rw [EW]
    simpa [ProofShape.inst, ProofShape.liftN_zero] using
      (ProofShape.BetaRed.beta (A := .sort (.succ .zero)) (b := .bvar 0)
        (a := proofErase Γ (.sort .zero)))
  have P : TypeChangePath Rel Γ (.succ .zero) (.sort .zero) (wrapType (.sort .zero)) :=
    .beta_back hP hW R
  refine ⟨_, _, P.defeq hΓ, P, ?_⟩
  intro H
  rw [EP] at H
  have E := L.sort_inv H
  rw [EW] at E
  cases E

/-- With the explicitly registered Box, there are inhabited equal types linked
by a structural/beta path but outside the raw structural relation. They have
no certified computational join. Nevertheless all certified typed guards and
body comparisons transport, with their exact term endpoints retained. -/
theorem hidden_box_type_path_example
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 1) (hf : info.numFields = 1)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.app (.const family []) (.bvar 1))))
    (hc : env.constants family = some ⟨0, .forallE (.sort (.succ .zero)) (.sort (.succ .zero))⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ Γ' A B, OnCtx Γ' (env.IsType univs) ∧
      env.IsDefEq univs Γ' A B (.sort (.succ .zero)) ∧
      TypeChangePath (BoxTypeChange family) Γ' (.succ .zero) A B ∧
      ¬ BoxTypeChange family 0 (proofErase Γ' A) (proofErase Γ' B) ∧
      (¬ ∃ shared,
        ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ') (proofErase Γ' A) shared ∧
        ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ') (proofErase Γ' B) shared) ∧
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
  obtain ⟨Γ', X, Y, hΓ', HXY, HT, _, Hbox, _, Hjoin, Hinh, _⟩ :=
    recursive_box_function_field_example heq hs hD hi hp hf hshape hc hΓ
  let A := VExpr.app (.const family []) X
  let B := VExpr.app (.const family []) Y
  have HTbox : BoxTypeChange family 0 (proofErase Γ' A) (proofErase Γ' B) := by
    rw [BoxCarrierAlignment.erase_box hc hΓ' HXY.hasType.1,
      BoxCarrierAlignment.erase_box hc hΓ' HXY.hasType.2]
    exact .box HT.toBox
  have hw := wrap_typed Hbox.hasType.1
  have Ew := wrap_erasure hΓ' Hbox.hasType.1
  have RB : ProofShape.BetaRed (proofErase Γ' (wrapType A)) (proofErase Γ' A) := by
    rw [Ew]
    simpa [ProofShape.inst, ProofShape.liftN_zero] using
      (ProofShape.BetaRed.beta (A := .sort (.succ .zero)) (b := .bvar 0) (a := proofErase Γ' A))
  have P : TypeChangePath (BoxTypeChange family) Γ' (.succ .zero) (wrapType A) B :=
    .trans (.beta hw Hbox.hasType.1 RB) (.related Hbox HTbox)
  have L := BoxTypeChange.transport_laws (erased_beta_stable_joint_descent heq hs)
    erased_beta_stable_joint_head (erased_beta_stable_joint_subst heq hs)
    hi hp hf hshape hc (fun R => erased_joint_union_no_rigid heq (henv.projectionRigid hi) hD
      (erased_beta_stable_joint_into_union R) (constHead_mkApps _ _))
  refine ⟨Γ', wrapType A, B, hΓ', P.defeq hΓ', P, ?_, ?_, ?_, ?_, ?_⟩
  · intro H
    have HB := H.symm
    rw [BoxCarrierAlignment.erase_box hc hΓ' HXY.hasType.2] at HB
    rcases (show BoxTypeChange family 0 (ProofShape.mkApps (.const family []) [_]) _ from HB).const_spine with E | ⟨a, b, _, _, _, E, _⟩
    · rw [Ew] at E
      cases (ProofShape.app.inj E).1
    · rw [Ew] at E
      cases (ProofShape.app.inj E).1
  · rintro ⟨shared, RW, RT⟩
    obtain ⟨out, RS, RA⟩ := proofErase_beta_stable_joint_beta_commute heq hs hΓ' hw RW RB
    exact Hjoin ⟨out, RA.mono erased_beta_stable_joint_into_union,
      (RT.trans (.beta RS)).mono erased_beta_stable_joint_into_union⟩
  · obtain ⟨x, hx⟩ := Hinh
    have HE := proofErase_beta_join_reflect hΓ' hw Hbox.hasType.1 RB .refl
    exact ⟨x, HE.symm.defeq hx⟩
  · intro x y hx hy
    exact ⟨P.carrier heq hs L hΓ' hx hy,
      (P.symm (fun H => H.symm)).carrier heq hs L hΓ'
        ((P.defeq hΓ').defeq hx) ((P.defeq hΓ').defeq hy)⟩
  · intro x y T mode hx hy H
    exact P.context heq hs L hΓ' hx hy H

end Lean4Lean.VEnv.Strengthening
