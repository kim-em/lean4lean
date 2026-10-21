import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqMotiveSpine

/-! # Eta before an Eq motive without motive recovery

Computations of the proposition index inside the fresh motive binder descend
with their exact certificates. The fresh motive itself is fixed. This replays
the computed beta contractum below the binder for any raw consumed argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eta_body_path from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaResidual
open private compute_spine from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaSpine
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Eta before the motive of a retained Prop-carrier Eq prefix preserves every
literal universe exposure. The supplied raw motive and pending arguments need
no recovery or typing assumptions; the prefix and its domain have actual
canonical typings. Computation of the earlier proposition index is retained. -/
theorem eqRec_motive_eta_spine_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hA : env.HasType univs Γ
      (.forallE (.sort .zero)
        (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ v))))
      (.sort (.succ u)))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,P])
      (.forallE (.forallE (.sort .zero)
        (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ v)))) B))
    (hn : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,P])) :
    let A := VExpr.forallE (.sort .zero)
      (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ v)))
    let f := ProofShape.mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero, proofErase Γ P]
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (proofErase Γ A) (.app (f.liftN 1) (.bvar 0))) (x :: xs)) (.sort w) ↔
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.app f x) xs) (.sort w) := by
  dsimp only
  let A := VExpr.forallE (.sort .zero)
    (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ v)))
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hvar : env.HasType univs (A :: Γ) (.bvar 0)
      (.forallE (.sort .zero)
        (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift.lift (.bvar 0)) (.sort (.succ v)))) := by
    simpa [A, VExpr.lift, VExpr.liftN, eqApp, liftN_liftN, liftN'_liftN_lo, HasType] using
      (HasType.bvar (env := env) (U := univs) (Lookup.zero (ty := A) (Γ := Γ)))
  have EV : proofErase (A :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (not_proof_at_positive_type hΓA (hA.weak henv) (HasType.bvar .zero))
  have EP := proofErase_liftN hΓ hΓA Ctx.LiftN.one hP
  have ES : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  have EF := proofErase_const_spine hΓ hf hn
  simp only [List.map_cons, List.map_nil, ES] at EF
  have Earg : etaArgument (.succ u) = .bvar 0 := by
    unfold etaArgument
    split
    · rename_i H
      have := VLevel.equiv_def.1 H []
      simp [VLevel.eval] at this
    · rfl
  have inst_body (p x : ProofShape) :
      (ProofShape.mkApps (.const ``Eq.rec [.succ v,.succ .zero])
        [.sort .zero,p.liftN 1,.bvar 0]).inst x =
      mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,p,x] := by
    simp only [ProofShape.mkApps, inst_eq_subst, ProofShape.subst, ProofShape.Subst.liftN,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.Subst.cons]
  constructor
  · intro R
    obtain ⟨A', body, x', xs', RF, RX, RT⟩ := R.lambda_spine_sort erased_joint_union_head
    have RF' := RF
    rw [← EF, ← Earg] at RF'
    obtain ⟨_, _, E, _, RB⟩ := eta_body_path heq hs hΓ hA hf hn RF'
    obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj E
    rw [proofErase_eta_body hΓ hA hf hn, EF, Earg] at RB
    have RB' : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
        (mkApps (.const ``Eq.rec [.succ v,.succ .zero])
          [.sort .zero,proofErase (A :: Γ) P.lift,proofErase (A :: Γ) (.bvar 0)]) body := by
      simpa only [EP, EV, ProofShape.mkApps, ProofShape.liftN] using RB
    obtain ⟨p, m, EB, RP, RM⟩ := proofErase_joint_union_eq_motive_spine
      heq hs hregistry hEq hRec hv hΓA (hP.weak henv) hvar RB'
    rw [EV] at RM
    cases RM.bvar_fixed erased_joint_union_head
    rw [EP] at RP
    obtain ⟨P', _, RP', EP'⟩ := proofErase_scoped_compute_certificate_descend
      (erased_joint_union_certificate_descent heq hs) hΓ hΓA Ctx.LiftN.one hP rfl RP
    rw [← EP'] at EB
    rw [EB, inst_body] at RT
    cases RX with | cons RX RXS =>
      exact (compute_spine (.app (.app (.app .refl .refl) RP') RX) RXS).trans RT
  · intro R
    have RB : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (.app (.lam (proofErase Γ A)
          (.app ((mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,proofErase Γ P]).liftN 1)
            (.bvar 0))) x)
        (mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,proofErase Γ P,x]) := by
      have E := inst_body (proofErase Γ P) x
      exact E ▸ ScopedCompute.beta (by simpa only [ProofShape.mkApps, ProofShape.liftN] using
        (BetaRed.beta (A := proofErase Γ A)
          (b := mkApps (.const ``Eq.rec [.succ v,.succ .zero])
            [.sort .zero,(proofErase Γ P).liftN 1,.bvar 0]) (a := x)))
    exact (compute_spine RB (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))).trans R

private theorem motive_prefix_typing
    (heq : env.HasCanonicalEq) (hv : v.WF univs)
    (hP : env.HasType univs Γ P (.sort .zero)) :
    let A := VExpr.forallE (.sort .zero)
      (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ v)))
    env.HasType univs Γ A (.sort (.succ (.succ v))) ∧
    ∃ B, env.HasType univs Γ
      (VExpr.mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,P]) (.forallE A B) := by
  dsimp only
  constructor
  · have hE := HasType.eqApp heq (U := univs) (Γ := .sort .zero :: Γ) (by trivial)
      (HasType.sort (by trivial)) (hP.weak henv) (HasType.bvar .zero)
    have hA := HasType.forallE (HasType.sort (Γ := Γ) (by trivial))
      (HasType.forallE hE (HasType.sort (l := .succ v) hv))
    apply (IsDefEq.sortDF (l := .imax (.succ .zero) (.imax .zero (.succ (.succ v)))) (l' := .succ (.succ v))
      (by exact ⟨by trivial, by trivial, hv⟩) hv ?_).defeq hA
    apply VLevel.equiv_def.2
    intro ls
    simp [VLevel.eval, Lean.Nat.imax]
  · have hc := HasType.const (U := univs) (Γ := Γ) heq.2.2.1
      (ls := [.succ v,.succ .zero]) (by simp; exact ⟨hv, by trivial⟩) rfl
    have h1 := hc.app (HasType.sort (l := .zero) (by trivial))
    simp [canonicalEqRecMotive, canonicalEqRecMinor,
      VExpr.instL, VLevel.inst, VExpr.inst, VExpr.instVar, VExpr.liftN] at h1
    have h2 := h1.app hP
    simp [VExpr.inst, VExpr.instVar] at h2
    exact ⟨_, h2⟩

open private nonproof_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqInitialEta

/-- The actual type probe tolerates eta before its motive without a recovery
assumption on that motive or on either proposition index. Its exact universe
exposure still characterizes comparison of the original indices. -/
theorem eqTypeProbe_motive_eta_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    let A := VExpr.forallE (.sort .zero)
      (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ (.succ v))))
    let f := ProofShape.mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
      [.sort .zero,proofErase Γ P]
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (proofErase Γ A) (.app (f.liftN 1) (.bvar 0)))
        [proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))),
          .sort v,proofErase Γ Q,.proof]) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  dsimp only
  have hS : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  have ht := eqTypeProbe_typed heq hΓ hS hP hQ hq
  have hn := nonproof_head hΓ
    (f := VExpr.mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero]) [.sort .zero,P])
    (args := [constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v)), .sort v,Q,q])
    ht (not_isProof_of_sort hΓ ht)
  obtain ⟨hA, B, hf⟩ := motive_prefix_typing heq (v := .succ v) hv hP
  have H := eqRec_motive_eta_spine_sort_iff (v := .succ v) heq hs hregistry hEq hRec hv hΓ hP hA hf hn
    (x := proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))))
    (xs := [.sort v,proofErase Γ Q,.proof]) (w := v)
  have E := eqTypeProbe_erase heq hΓ hS hP hQ hq
  rw [show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ hS)] at E
  change _ ↔ ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
    (mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
      [.sort .zero,proofErase Γ P,
        proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))),
        .sort v,proofErase Γ Q,.proof]) (.sort v) at H
  rw [← E] at H
  exact H.trans (eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec hv hΓ hP hQ hq)

/-- The motive eta case also preserves the exact comparison certificate
below an arbitrary block of inserted binders. The equality major is needed
only upstairs; neither a lower major nor motive recovery is assumed. -/
theorem eqTypeProbe_motive_eta_sort_below_iff
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
    let A := VExpr.forallE (.sort .zero)
      (.forallE (eqApp (.succ .zero) (.sort .zero) (P.liftN n k).lift (.bvar 0))
        (.sort (.succ (.succ v))))
    let f := ProofShape.mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
      [.sort .zero,proofErase Γ' (P.liftN n k)]
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
      (mkApps (.lam (proofErase Γ' A) (.app (f.liftN 1) (.bvar 0)))
        [proofErase Γ' (constantEqMotive (.succ .zero) (.sort .zero) (P.liftN n k) (.sort (.succ v))),
          .sort v,proofErase Γ' (Q.liftN n k),.proof]) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have H := eqTypeProbe_motive_eta_sort_iff heq hs hregistry hEq hRec hv hΓ'
    (hP.weakN henv W) (hQ.weakN henv W) hq
  exact H.trans (by
    rw [proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ]
    exact proofErase_joint_union_compare_lift_iff heq hs hΓ hΓ' W hP hQ)

end Lean4Lean.VEnv.Strengthening
