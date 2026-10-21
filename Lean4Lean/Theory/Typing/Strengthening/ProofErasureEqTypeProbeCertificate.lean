import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqComputedGuardCertificate
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbeComputation

/-! # Lossless type-probe head readout in the full joint union

Changing the Eq.rec head of a typed probe retains an actual comparison of its
original proposition indices below the inserted block. Conversely, such a
comparison computes the probe to its minor. These are certificate equivalences,
not coverage of arbitrary semantic equality by the joint checker.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private type_probe_prefix_typed
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
open private constant_motive_lift core_computed_probe_prefix_excluded
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
variable [Params]

/-- Any head change of the lifted type probe retains a lower common
comparison of its original proposition endpoints. The path may compute all
supplied arguments before its first primitive, and use any finite stages. -/
theorem proofErase_joint_union_type_probe_head_compare
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
    (hne : out.constHead ≠ some ``Eq.rec) : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (proofErase Γ P) (proofErase Γ Q) := by
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
  apply proofErase_singleton_eq_prop_computed_prefix_certificate heq
    (erased_joint_union_certificate_descent heq hs) erased_joint_union_head
    (fun H => erased_joint_union_no_rigid heq (heq.rigid henv) hEq H (constHead_mkApps _ _))
    hΓ hΓ' W ht hn (k := k) (H := HG)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, ES, ProofShape.liftN] using HA

/-- If the minor does not have Eq.rec at its erased head, exposing any new
head from the probe is equivalent to an existing comparison of its indices.
The reverse direction computes to the original minor, not a selected proxy. -/
theorem eqTypeProbe_union_head_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hS : env.HasType univs Γ S (.sort u))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q))
    (hShead : (proofErase Γ S).constHead ≠ some ``Eq.rec) :
    (∃ out, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe u S P Q q)) out ∧ out.constHead ≠ some ``Eq.rec) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  constructor
  · rintro ⟨out, R, Hout⟩
    exact proofErase_joint_union_type_probe_head_compare heq hs hregistry hEq hRec hΓ hΓ
      (show Ctx.LiftN 0 0 Γ Γ from .zero []) hS hP hQ (by simpa only [VExpr.liftN_zero] using hq)
      (by simpa only [VExpr.liftN_zero] using R) Hout
  · intro HC
    obtain ⟨stage, HC⟩ := HC.finite_stage erased_joint_stage_mono
    exact ⟨_, (eqTypeProbe_compute_stage heq hs hregistry hΓ hS hP hQ hq HC).mono
      (fun H => ⟨stage + 1, H⟩), hShead⟩

/-- A universe-valued Eq probe computes to its literal original universe
exactly when its proposition indices have a joint comparison certificate.
Even exposure of some other head suffices to construct this exact result. -/
theorem eqTypeProbe_union_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (eqTypeProbe (.succ v) (.sort v) P Q q)) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have hS : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  have ES : proofErase Γ (.sort v) = .sort v := if_neg (not_isProof_of_sort hΓ hS)
  constructor
  · intro R
    exact (eqTypeProbe_union_head_iff heq hs hregistry hEq hRec hΓ hS hP hQ hq
      (by rw [ES]; simp [ProofShape.constHead])).1 ⟨_, R, by simp [ProofShape.constHead]⟩
  · intro HC
    obtain ⟨stage, HC⟩ := HC.finite_stage erased_joint_stage_mono
    have R := (eqTypeProbe_compute_stage heq hs hregistry hΓ hS hP hQ hq HC).mono
      (Step' := ErasedJointUnion D) (fun H => ⟨stage + 1, H⟩)
    rwa [ES] at R

end Lean4Lean.VEnv.Strengthening
