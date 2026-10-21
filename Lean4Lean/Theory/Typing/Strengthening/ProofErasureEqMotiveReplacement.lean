import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqMinorEta

/-! # Universe probes are insensitive to typed motive replacement

A retained Eq recursor with a literal universe minor has the same original
index-certificate criterion for every motive for which the full source is
typed and retained. This covers arbitrary changes inside the motive argument
without requiring a contextual transport theorem for their derivations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private core_computed_probe_prefix_excluded
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
variable [Params]

/-- Any retained, typed Prop-carrier Eq recursor with a literal universe minor
computes to that universe exactly when its original indices compare. The
motive is arbitrary; its internal syntax and computations need no recovery or
normality assumptions. -/
theorem proofErase_joint_union_eq_universe_minor_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q) T)
    (hn : ¬ IsProof Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q)) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) := by
  obtain ⟨A, B, hf, hq⟩ := ht.app_inv henv hΓ
  have hnf := not_isProof_fn hΓ hf hq hn
  change env.HasType univs Γ (eqRecBeforeMajor r (.succ .zero) (.sort .zero) P M (.sort v) Q)
    (.forallE A B) at hf
  change ¬ IsProof Γ (eqRecBeforeMajor r (.succ .zero) (.sort .zero) P M (.sort v) Q) at hnf
  obtain ⟨hr, _, _, hP, hM, hm, hQ⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, hf⟩
  have hcanon := eqRecBeforeMajor_typed heq hr (by trivial) (HasType.sort (by trivial)) hP hM hm hQ
  have hq' := argument_at_displayed_domain hΓ hf hcanon hq
  have EQ : proofErase Γ q = .proof := proofErase_eq_proof.2
    ⟨_, hq', HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ⟩
  have ES : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  have hv := hm.sort_inv_l henv
  have ESv : proofErase Γ (.sort v) = .sort v := if_neg (not_isProof_of_sort hΓ (HasType.sort hv))
  have E := proofErase_const_spine hΓ (args := [.sort .zero,P,M,.sort v,Q,q]) ht hn
  simp only [List.map_cons, List.map_nil, ES, ESv, EQ] at E
  change proofErase Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q) = _ at E
  constructor
  · intro R
    rw [E] at R
    have HT : TypedSource (proofEraseCtx Γ)
        (mkApps (.const ``Eq.rec [r,.succ .zero])
          [.sort .zero,proofErase Γ P,proofErase Γ M,.sort v,proofErase Γ Q,.proof]) :=
      ⟨_, _, _, hΓ, rfl, ht, E⟩
    obtain ⟨k, changed, target, _, HA, HT', H⟩ :=
      (R.head_occurrence (by simp only [constHead, ne_eq, reduceCtorEq, not_false_eq_true])).with_typed_source
        (erased_joint_union_descent heq hs) HT
    rcases erased_joint_union_typed_core_singleton heq hs hregistry HT' H with HC | HG
    · obtain ⟨data, hlookup, hreg, hne, _⟩ := heq.recursorRegistration henv
      exact (core_computed_probe_prefix_excluded erased_joint_union_head
        (hregistry.trans hlookup) (hreg.eqRec_target heq hne).2.1 hRec HA HC).elim
    apply proofErase_singleton_eq_prop_computed_prefix_certificate heq
      (erased_joint_union_certificate_descent heq hs) erased_joint_union_head
      (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
      hΓ hΓ (show Ctx.LiftN 0 0 Γ Γ from .zero []) hf hnf (k := k) (H := HG)
    simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      ProofShape.liftN_zero, ES, ESv] using HA
  · intro HC
    obtain ⟨stage, HC⟩ := HC.finite_stage erased_joint_stage_mono
    have HP : JointPrefixPrimitive (ErasedJointStage D stage) (proofEraseCtx Γ)
        (ProofShape.eqRecBeforeMajor r (.succ .zero) (.sort .zero)
          (proofErase Γ P) (proofErase Γ M) (.sort v) (proofErase Γ Q))
        (.lam (eqProofType (.succ .zero) (.sort .zero) (proofErase Γ P) (proofErase Γ Q)) (.sort v)) :=
      .intro (.carrierChecked HC)
    have RP : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) _ _ :=
      .base ⟨stage + 1, .inr (.inr HP)⟩
    rw [E]
    exact (ScopedCompute.app RP .refl).trans (.beta (by
      simpa only [ProofShape.inst] using (BetaRed.beta
        (A := eqProofType (.succ .zero) (.sort .zero) (proofErase Γ P) (proofErase Γ Q))
        (b := .sort v) (a := .proof))))

/-- Any two typed retained motives have identical universe exposure at fixed
indices and a fixed universe minor. No equality between the motives is needed.
In particular, arbitrary eta or other changes inside the motive argument are
covered whenever their actual endpoint typings and retention are supplied. -/
theorem proofErase_joint_union_eq_motive_replacement_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q) T)
    (hn : ¬ IsProof Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q))
    (ht' : env.HasType univs Γ (eqRecApp r' (.succ .zero) (.sort .zero) P M' (.sort v) Q q') T')
    (hn' : ¬ IsProof Γ (eqRecApp r' (.succ .zero) (.sort .zero) P M' (.sort v) Q q')) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp r (.succ .zero) (.sort .zero) P M (.sort v) Q q)) (.sort v) ↔
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp r' (.succ .zero) (.sort .zero) P M' (.sort v) Q q')) (.sort v) :=
  (proofErase_joint_union_eq_universe_minor_iff heq hs hregistry hEq hRec hΓ ht hn).trans
    (proofErase_joint_union_eq_universe_minor_iff heq hs hregistry hEq hRec hΓ ht' hn').symm

open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary

/-- Canonical positive-universe motive typing suffices for the exact criterion;
retention of the recursor follows from typing its result type in that universe.
The motive need not be constant or definitionally equal to a chosen motive. -/
theorem proofErase_joint_union_eq_typed_motive_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hr : r.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hM : env.HasType univs Γ M
      (.forallE (.sort .zero)
        (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ r)))))
    (hm : env.HasType univs Γ (.sort v)
      (.app (.app M P) (eqReflApp (.succ .zero) (.sort .zero) P)))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp (.succ r) (.succ .zero) (.sort .zero) P M (.sort v) Q q)) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) := by
  have hMQ : env.HasType univs Γ (.app M Q)
      (.forallE (eqApp (.succ .zero) (.sort .zero) P Q) (.sort (.succ r))) := by
    simpa [VExpr.inst, VExpr.instVar, VExpr.liftN, eqApp, inst_lift] using hM.app hQ
  have hT : env.HasType univs Γ (.app (.app M Q) q) (.sort (.succ r)) := hMQ.app hq
  have ht := HasType.eqRecApp heq (v := .succ r) hr (by trivial)
    (HasType.sort (by trivial)) hP hM hm hQ hq
  exact proofErase_joint_union_eq_universe_minor_iff heq hs hregistry hEq hRec hΓ ht
    (not_proof_at_positive_type hΓ hT ht)

/-- An arbitrary motive may exist only above the inserted block. Its universe
exposure still characterizes comparison of the original lower indices. No
lower motive, minor typing, or equality major is needed. -/
theorem proofErase_joint_union_eq_motive_below_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.LiftN n k Γ Γ')
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (ht : env.HasType univs Γ'
      (eqRecApp r (.succ .zero) (.sort .zero) (P.liftN n k) M (.sort v) (Q.liftN n k) q) T)
    (hn : ¬ IsProof Γ'
      (eqRecApp r (.succ .zero) (.sort .zero) (P.liftN n k) M (.sort v) (Q.liftN n k) q)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
      (proofErase Γ'
        (eqRecApp r (.succ .zero) (.sort .zero) (P.liftN n k) M (.sort v) (Q.liftN n k) q)) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) := by
  have H := proofErase_joint_union_eq_universe_minor_iff heq hs hregistry hEq hRec hΓ' ht hn
  rw [proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ] at H
  exact H.trans (proofErase_joint_union_compare_lift_iff heq hs hΓ hΓ' W hP hQ)

/-- Any semantic conversion of the probe's motive, including eta inside that
argument, preserves its original comparison criterion. The equality supplies
both the changed motive typing and conversion of the minor's assigned domain;
no erased comparison, recovery or global semantic exposure law is assumed. -/
theorem eqTypeProbe_converted_motive_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (HM : env.IsDefEq univs Γ
      (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))) M
      (.forallE (.sort .zero)
        (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ (.succ v)))))) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqRecApp (.succ (.succ v)) (.succ .zero) (.sort .zero) P M (.sort v) Q q)) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) := by
  have hrefl := HasType.eqReflApp heq (U := univs) (Γ := Γ) (by trivial)
    (HasType.sort (by trivial)) hP
  have HMP := IsDefEq.appDF HM hP
  have HMP' : env.IsDefEq univs Γ
      (.app (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))) P) (.app M P)
      (.forallE (eqApp (.succ .zero) (.sort .zero) P P) (.sort (.succ (.succ v)))) := by
    simpa [VExpr.inst, VExpr.instVar, VExpr.liftN, eqApp, inst_lift] using HMP
  have HN : env.IsDefEq univs Γ
      (.app (.app (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))) P)
        (eqReflApp (.succ .zero) (.sort .zero) P))
      (.app (.app M P) (eqReflApp (.succ .zero) (.sort .zero) P)) (.sort (.succ (.succ v))) :=
    .appDF HMP' hrefl
  have hN := constantEqMotive_app henv heq (by trivial) hΓ
    (HasType.sort (by trivial)) hP (HasType.sort (l := .succ v) hv) hP hrefl
  have hm := HN.defeq (hN.symm.defeq (HasType.sort (l := v) hv))
  exact proofErase_joint_union_eq_typed_motive_iff (r := .succ v)
    heq hs hregistry hEq hRec hv hΓ hP HM.hasType.2 hm hQ hq

end Lean4Lean.VEnv.Strengthening
