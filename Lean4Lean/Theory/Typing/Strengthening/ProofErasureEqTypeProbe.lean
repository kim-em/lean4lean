import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnionHeadExposure

/-! # Type-valued Eq probes with arbitrary result types

The sort probe argument does not depend on its minor being Prop. A first-head
primitive of any typed Prop-carrier Eq recursor already reads out equality of
the lower proposition endpoints. This includes a probe returning a unit type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private constant_motive_lift core_computed_probe_prefix_excluded
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
variable [Params]

/-- An Eq recursor returning a specified type S through a constant motive. -/
def eqTypeProbe (u : VLevel) (S P Q q : VExpr) : VExpr :=
  eqRecApp (.succ u) (.succ .zero) (.sort .zero) P
    (constantEqMotive (.succ .zero) (.sort .zero) P (.sort u)) S Q q

/-- The result is type-valued without assuming definitional endpoint equality. -/
theorem eqTypeProbe_typed (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    env.HasType univs Γ (eqTypeProbe u S P Q q) (.sort u) := by
  have hu := hS.sort_r henv hΓ
  exact constant_eqRec_typed (v := .succ u) henv heq hu (by trivial) hΓ
    (HasType.sort (by trivial)) hP (HasType.sort hu) hS hQ hq

/-- Definitional endpoint equality licenses K, returning the specified type. -/
theorem eqTypeProbe_defeq (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HPQ : env.IsDefEqU univs Γ P Q) :
    env.IsDefEq univs Γ (eqTypeProbe u S P Q q) S (.sort u) :=
  eqRecApp_simAt henv heq hΓ HPQ _ (eqTypeProbe_typed heq hΓ hS hP hQ hq)

/-- The probe retains the specified type and erases the equality major. -/
theorem eqTypeProbe_erase (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    proofErase Γ (eqTypeProbe u S P Q q) =
      mkApps (.const ``Eq.rec [.succ u, .succ .zero])
        [.sort .zero, proofErase Γ P,
          proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort u)),
          proofErase Γ S, proofErase Γ Q, .proof] := by
  have ht := eqTypeProbe_typed heq hΓ hS hP hQ hq
  have HE := proofErase_const_spine hΓ (args := [.sort .zero, P,
    constantEqMotive (.succ .zero) (.sort .zero) P (.sort u), S, Q, q]) ht
    (not_isProof_of_sort hΓ ht)
  change proofErase Γ (eqTypeProbe u S P Q q) = _ at HE
  have Hq : proofErase Γ q = .proof := proofErase_eq_proof.2
    ⟨_, hq, HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ⟩
  have HS : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  simpa only [List.map_cons, List.map_nil, Hq, HS] using HE

private theorem type_probe_prefix_typed
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero)) :
    ∃ T, env.HasType univs Γ
        (eqRecBeforeMajor (.succ u) (.succ .zero) (.sort .zero) P
          (constantEqMotive (.succ .zero) (.sort .zero) P (.sort u)) S Q) T ∧
      ¬ IsProof Γ
        (eqRecBeforeMajor (.succ u) (.succ .zero) (.sort .zero) P
          (constantEqMotive (.succ .zero) (.sort .zero) P (.sort u)) S Q) := by
  have hu := hS.sort_r henv hΓ
  have hα := HasType.sort (env := env) (U := univs) (Γ := Γ) (l := .zero) (by trivial)
  have hT := HasType.sort (env := env) (U := univs) (Γ := Γ) (l := u) hu
  have hM := constantEqMotive_typed henv.ordered heq (by trivial) hα hP hT
  have hr := HasType.eqReflApp heq (by trivial) hα hP
  have hm := (constantEqMotive_app henv heq (by trivial) hΓ hα hP hT hP hr).symm.defeq hS
  have ht := eqRecBeforeMajor_typed (v := .succ u) heq hu (by trivial) hα hP hM hm hQ
  refine ⟨_, ht, ?_⟩
  have hEQ := HasType.eqApp heq (by trivial) hα hP hQ
  have hΓE : OnCtx (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hEQ⟩
  have hq : env.HasType univs (eqApp (.succ .zero) (.sort .zero) P Q :: Γ) (.bvar 0)
      (eqApp (.succ .zero) (.sort .zero) P.lift Q.lift) := .bvar .zero
  have hfull := eqTypeProbe_typed heq hΓE (hS.weak henv) (hP.weak henv) (hQ.weak henv) hq
  have hnp := not_isProof_of_sort hΓE hfull
  have hnp' : ¬ IsProof (eqApp (.succ .zero) (.sort .zero) P Q :: Γ)
      (.app ((eqRecBeforeMajor (.succ u) (.succ .zero) (.sort .zero) P
        (constantEqMotive (.succ .zero) (.sort .zero) P (.sort u)) S Q).lift) (.bvar 0)) := by
    simp only [eqRecBeforeMajor, VExpr.lift, VExpr.liftN_mkApps,
      List.map_cons, List.map_nil, constant_motive_lift, VExpr.liftN]
    exact hnp
  have hn := not_isProof_fn hΓE (ht.weak henv) hq hnp'
  exact fun hp => hn ((isProof_liftN hΓ hΓE Ctx.LiftN.one ht).2 hp)

/-- Any change of the head of a lifted type probe descends its proposition
endpoints. The output need not be a sort or be identified semantically. -/
theorem proofErase_joint_union_type_probe_head_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n 0 Γ Γ') (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ' q (eqApp (.succ .zero) (.sort .zero) (P.liftN n) (Q.liftN n)))
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
      (proofErase Γ' (eqTypeProbe u (S.liftN n) (P.liftN n) (Q.liftN n) q)) out)
    (hne : out.constHead ≠ some ``Eq.rec) : env.IsDefEqU univs Γ P Q := by
  have hSw := hS.weakN henv W
  have hPw := hP.weakN henv W
  have hQw := hQ.weakN henv W
  have E := eqTypeProbe_erase heq hΓ' hSw hPw hQw hq
  have R' := R
  rw [E] at R'
  have HT : TypedSource (proofEraseCtx Γ') _ :=
    ⟨_, _, _, hΓ', rfl, eqTypeProbe_typed heq hΓ' hSw hPw hQw hq, E⟩
  obtain ⟨k, changed, out, _, HA, HT, H⟩ :=
    (R'.head_occurrence hne).with_typed_source (erased_joint_union_descent heq hs) HT
  rcases erased_joint_union_typed_core_singleton heq hs hregistry HT H with HC | HG
  · obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
    exact (core_computed_probe_prefix_excluded erased_joint_union_head
      (hregistry.trans hlookup) (hr.eqRec_target heq hn).2.1 hRec HA HC).elim
  obtain ⟨T, ht, hn⟩ := type_probe_prefix_typed heq hΓ hS hP hQ
  have hM := constantEqMotive_typed henv.ordered heq (by trivial)
    (HasType.sort (env := env) (U := univs) (Γ := Γ) (l := .zero) (by trivial)) hP
    (HasType.sort (l := u) (hS.sort_r henv hΓ))
  have EM : proofErase Γ'
      (constantEqMotive (.succ .zero) (.sort .zero) (P.liftN n) (.sort u)) =
      (proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort u))).liftN n := by
    rw [← proofErase_liftN hΓ hΓ' W hM]
    congr 1
    simpa only [VExpr.liftN] using (constant_motive_lift (n := n)
      (w := VLevel.succ .zero) (α := VExpr.sort .zero) (a := P) (T := VExpr.sort u)).symm
  rw [proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ,
    proofErase_liftN hΓ hΓ' W hS, EM] at HA
  have ES : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  apply proofErase_singleton_eq_prop_computed_prefix_descend heq
    (erased_joint_union_descent heq hs) erased_joint_union_head
    (erased_joint_union_descent heq hs) erased_joint_union_head
    (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
    hΓ hΓ' W ht hn (k := k) (H := HG)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, ES, ProofShape.liftN] using HA

end Lean4Lean.VEnv.Strengthening
