import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqSeparatedSpine

/-! # Eta before the final proposition index

The fresh index cannot compare with an earlier proposition lifted from below.
The five-argument eta body therefore has no head computation, even though this
arity normally admits singleton elimination. Its earlier argument paths descend
exactly, without recovery of the consumed proposition.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eta_body_path from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaResidual
open private compute_spine from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaSpine
open private type_probe_prefix_typed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
open private constant_motive_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqHeadExposureBarrier
variable [Params]

/-- Eta before the probe's final proposition index preserves every universe
exposure for any raw consumed index and pending arguments. The fresh index
excludes the five-argument singleton guard; exact certificate descent moves
the earlier proposition and motive computations below that binder. -/
theorem eqTypeProbe_endpoint_eta_spine_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) :
    let M := constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))
    let f := ProofShape.mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
      [.sort .zero,proofErase Γ P,proofErase Γ M,.sort v]
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (.sort .zero) (.app (f.liftN 1) (.bvar 0))) (x :: xs)) (.sort w) ↔
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.app f x) xs) (.sort w) := by
  dsimp only
  let M := constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))
  have hS : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  obtain ⟨T, ht, hn⟩ := type_probe_prefix_typed heq hΓ hS hP hP
  obtain ⟨_, _, _, _, hM, hm, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨T, ht⟩
  have hf := HasType.eqRec4 heq (v := .succ (.succ v)) hv (by trivial)
    (HasType.sort (by trivial)) hP hM hm
  have hnf := not_isProof_fn hΓ hf hP hn
  have ES : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  have ESv : proofErase Γ (.sort v) = .sort v := if_neg (not_isProof_of_sort hΓ hS)
  have EF := proofErase_const_spine hΓ (args := [.sort .zero,P,M,.sort v]) hf hnf
  simp only [List.map_cons, List.map_nil, ES, ESv] at EF
  have hA : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hΓA : OnCtx (.sort .zero :: Γ) (env.IsType univs) := ⟨hΓ, _, hA⟩
  have hvar : env.HasType univs (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have EV : proofErase (.sort .zero :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (not_isProof_of_sort hΓA hvar)
  have EP := proofErase_liftN hΓ hΓA Ctx.LiftN.one hP
  have EM := proofErase_liftN hΓ hΓA Ctx.LiftN.one hM
  have ES' : proofErase (.sort .zero :: Γ) (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓA (HasType.sort (by trivial)))
  have ESv' : proofErase (.sort .zero :: Γ) (.sort v) = .sort v :=
    if_neg (not_isProof_of_sort hΓA (HasType.sort hv))
  have EL : M.lift = constantEqMotive (.succ .zero) (.sort .zero) P.lift (.sort (.succ v)) := by
    simpa only [VExpr.lift, VExpr.liftN] using
      (constant_motive_lift (n := 1) (w := .succ .zero) (α := .sort .zero) (a := P) (T := .sort (.succ v)))
  change proofErase (.sort .zero :: Γ) M.lift = (proofErase Γ M).liftN 1 at EM
  rw [EL] at EM
  have Earg : etaArgument (.succ .zero) = .bvar 0 := by
    unfold etaArgument
    split
    · rename_i H
      have := VLevel.equiv_def.1 H []
      simp [VLevel.eval] at this
    · rfl
  have inst_body (p m x : ProofShape) :
      (mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
        [.sort .zero,p.liftN 1,m.liftN 1,.sort v,.bvar 0]).inst x =
      mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero]) [.sort .zero,p,m,.sort v,x] := by
    simp only [ProofShape.mkApps, inst_eq_subst, ProofShape.subst, ProofShape.Subst.liftN,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.Subst.cons]
  constructor
  · intro R
    obtain ⟨A', body, x', xs', RF, RX, RT⟩ := R.lambda_spine_sort erased_joint_union_head
    have RF' := RF
    rw [← EF, ← Earg] at RF'
    conv at RF' => lhs; arg 1; rw [← ES]
    obtain ⟨_, _, E, _, RB⟩ := eta_body_path heq hs hΓ hA hf hnf RF'
    obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj E
    rw [proofErase_eta_body hΓ hA hf hnf, Earg] at RB
    have EF' := EF
    dsimp only [VExpr.mkApps, List.foldl, M] at EF'
    rw [EF'] at RB
    obtain ⟨T', ht', hn'⟩ := type_probe_prefix_typed heq hΓA (HasType.sort hv) (hP.weak henv) hvar
    have RB' : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (.sort .zero :: Γ))
        (mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
          ([.sort .zero,P.lift,constantEqMotive (.succ .zero) (.sort .zero) P.lift (.sort (.succ v)),
            .sort v,.bvar 0].map (proofErase (.sort .zero :: Γ)))) body := by
      simpa only [List.map_cons, List.map_nil, ES', EP, EM, ESv', EV,
        ProofShape.mkApps, ProofShape.liftN] using RB
    have hsep : ¬ JointCompare (ErasedJointUnion D) (proofEraseCtx (.sort .zero :: Γ)) true
        (proofErase (.sort .zero :: Γ) P.lift) (proofErase (.sort .zero :: Γ) (.bvar 0)) :=
      fun H => proofErase_joint_types_no_fresh_variable (erased_joint_union_descent heq hs)
        erased_joint_union_head hΓ hΓA Ctx.LiftN.one hP hvar (by decide) H
    obtain ⟨args, EB, HA⟩ := proofErase_joint_union_eq_separated_spine
      heq hs hregistry hEq hRec hΓA ht' hn' hsep RB'
    simp only [List.map_cons, List.map_nil, ES', EP, EM, ESv', EV] at HA
    cases HA with | cons RS HA =>
      cases HA with | cons RP HA =>
        cases HA with | cons RM HA =>
          cases HA with | cons RSV HA =>
            cases HA with | cons RV HA =>
              cases HA
              cases RS.sort_fixed erased_joint_union_head
              cases RSV.sort_fixed erased_joint_union_head
              cases RV.bvar_fixed erased_joint_union_head
              obtain ⟨P', _, RP', EP'⟩ := proofErase_scoped_compute_certificate_descend
                (erased_joint_union_certificate_descent heq hs) hΓ hΓA Ctx.LiftN.one hP rfl RP
              obtain ⟨M', _, RM', EM'⟩ := proofErase_scoped_compute_certificate_descend
                (erased_joint_union_certificate_descent heq hs) hΓ hΓA Ctx.LiftN.one hM rfl RM
              rw [← EP', ← EM'] at EB
              rw [EB, inst_body] at RT
              cases RX with | cons RX RXS =>
                exact (compute_spine (.app (.app (.app (.app (.app .refl .refl) RP') RM') .refl) RX) RXS).trans RT
  · intro R
    have E := inst_body (proofErase Γ P) (proofErase Γ M) x
    have RB : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (.app (.lam (.sort .zero) (.app ((mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
          [.sort .zero,proofErase Γ P,proofErase Γ M,.sort v]).liftN 1) (.bvar 0))) x)
        (mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
          [.sort .zero,proofErase Γ P,proofErase Γ M,.sort v,x]) := by
      exact E ▸ ScopedCompute.beta (by simpa only [ProofShape.mkApps, ProofShape.liftN] using
        (BetaRed.beta (A := .sort .zero) (b := mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
          [.sort .zero,(proofErase Γ P).liftN 1,(proofErase Γ M).liftN 1,.sort v,.bvar 0]) (a := x)))
    exact (compute_spine RB (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))).trans R

/-- Eta before the last proposition index preserves the actual probe's exact
index-comparison criterion, without recovery of that index or of its motive. -/
theorem eqTypeProbe_endpoint_eta_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    let M := constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))
    let f := ProofShape.mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
      [.sort .zero,proofErase Γ P,proofErase Γ M,.sort v]
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (.sort .zero) (.app (f.liftN 1) (.bvar 0)))
        [proofErase Γ Q,.proof]) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have H := eqTypeProbe_endpoint_eta_spine_sort_iff heq hs hregistry hEq hRec hv hΓ hP
    (x := proofErase Γ Q) (xs := [.proof]) (w := v)
  have hS : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  have E := eqTypeProbe_erase heq hΓ hS hP hQ hq
  rw [show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ hS)] at E
  change _ ↔ ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
    (mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
      [.sort .zero,proofErase Γ P,
        proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))),
        .sort v,proofErase Γ Q,.proof]) (.sort v) at H
  rw [← E] at H
  exact H.trans (eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec hv hΓ hP hQ hq)

/-- The endpoint eta criterion descends across arbitrary binder insertion.
Only the larger context needs an equality major; the conclusion retains a
comparison certificate of the two original propositions below the block. -/
theorem eqTypeProbe_endpoint_eta_sort_below_iff
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
    let M := constantEqMotive (.succ .zero) (.sort .zero) (P.liftN n k) (.sort (.succ v))
    let f := ProofShape.mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
      [.sort .zero,proofErase Γ' (P.liftN n k),proofErase Γ' M,.sort v]
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
      (mkApps (.lam (.sort .zero) (.app (f.liftN 1) (.bvar 0)))
        [proofErase Γ' (Q.liftN n k),.proof]) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have H := eqTypeProbe_endpoint_eta_sort_iff heq hs hregistry hEq hRec hv hΓ'
    (hP.weakN henv W) (hQ.weakN henv W) hq
  exact H.trans (by
    rw [proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ]
    exact proofErase_joint_union_compare_lift_iff heq hs hΓ hΓ' W hP hQ)

end Lean4Lean.VEnv.Strengthening
