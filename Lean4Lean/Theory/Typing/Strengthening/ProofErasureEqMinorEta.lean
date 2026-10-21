import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqEndpointEta

/-! # Eta before the minor at its actual motive-application domain

A fresh minor completes the four-argument eta body. Proper-prefix exclusion
retains its earlier argument computations, which descend across the original
minor binder. No conversion of that binder to a universe or argument recovery
is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eta_body_path from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaResidual
open private compute_spine from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaSpine
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Eta before an arbitrary positive-universe Eq minor preserves exact
universe exposure for any raw consumed image and pending arguments. The
annotation is the actual motive application. Earlier proposition and motive
paths descend exactly, without recovery of the consumed minor. -/
theorem eqRec_minor_eta_spine_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hM : env.HasType univs Γ M
      (.forallE (.sort .zero)
        (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ v)))))
    (hf : env.HasType univs Γ (VExpr.mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,P,M])
      (.forallE (.app (.app M P) (eqReflApp (.succ .zero) (.sort .zero) P)) B))
    (hnf : ¬ IsProof Γ (VExpr.mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,P,M])) :
    let N := VExpr.app (.app M P) (eqReflApp (.succ .zero) (.sort .zero) P)
    let f := ProofShape.mkApps (.const ``Eq.rec [.succ v,.succ .zero])
      [.sort .zero,proofErase Γ P,proofErase Γ M]
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (proofErase Γ N) (.app (f.liftN 1) (.bvar 0))) (x :: xs)) (.sort w) ↔
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.app f x) xs) (.sort w) := by
  dsimp only
  let N := VExpr.app (.app M P) (eqReflApp (.succ .zero) (.sort .zero) P)
  have hr := HasType.eqReflApp heq (U := univs) (Γ := Γ) (by trivial)
    (HasType.sort (by trivial)) hP
  have hMP : env.HasType univs Γ (.app M P)
      (.forallE (eqApp (.succ .zero) (.sort .zero) P P) (.sort (.succ v))) := by
    simpa [VExpr.inst, VExpr.instVar, VExpr.liftN, eqApp, inst_lift] using hM.app hP
  have hN : env.HasType univs Γ N (.sort (.succ v)) := hMP.app hr
  have hΓN : OnCtx (N :: Γ) (env.IsType univs) := ⟨hΓ, _, hN⟩
  have hm : env.HasType univs (N :: Γ) (.bvar 0)
      (.app (.app M.lift P.lift) (eqReflApp (.succ .zero) (.sort .zero) P.lift)) := by
    simpa only [N, VExpr.lift, VExpr.liftN, eqReflApp] using
      (HasType.bvar (U := univs) (env := env) (Lookup.zero (ty := N) (Γ := Γ)))
  have hMw : env.HasType univs (N :: Γ) M.lift
      (.forallE (.sort .zero)
        (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift.lift (.bvar 0)) (.sort (.succ v)))) := by
    simpa [VExpr.lift, VExpr.liftN, eqApp, liftN_liftN, liftN'_liftN_lo, HasType] using hM.weak henv (B := N)
  have ht := eqRecBeforeMajor_typed heq (v := .succ v) hv (by trivial)
    (HasType.sort (Γ := N :: Γ) (by trivial)) (hP.weak henv) hMw hm (hP.weak henv)
  have hrw := HasType.eqReflApp heq (U := univs) (Γ := N :: Γ) (by trivial)
    (HasType.sort (by trivial)) (hP.weak henv)
  have hfull : env.HasType univs (N :: Γ)
      (.app (eqRecBeforeMajor (.succ v) (.succ .zero) (.sort .zero) P.lift M.lift (.bvar 0) P.lift)
        (eqReflApp (.succ .zero) (.sort .zero) P.lift)) N.lift := by
    simpa [N, VExpr.inst, VExpr.instVar, VExpr.lift, VExpr.liftN, eqApp, eqReflApp,
      inst_lift, liftN_liftN, inst_liftN_lo, inst_liftN'] using ht.app hrw
  have hn := not_isProof_fn hΓN ht hrw (not_proof_at_positive_type hΓN (hN.weak henv) hfull)
  have EP := proofErase_liftN hΓ hΓN Ctx.LiftN.one hP
  have EM := proofErase_liftN hΓ hΓN Ctx.LiftN.one hM
  have EV : proofErase (N :: Γ) (.bvar 0) = .bvar 0 :=
    if_neg (not_proof_at_positive_type hΓN (hN.weak henv) (HasType.bvar .zero))
  have ES : proofErase Γ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))
  have ES' : proofErase (N :: Γ) (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓN (HasType.sort (by trivial)))
  have EF := proofErase_const_spine hΓ hf hnf
  simp only [List.map_cons, List.map_nil, ES] at EF
  have Earg : etaArgument (.succ v) = .bvar 0 := by
    unfold etaArgument
    split
    · rename_i H
      have := VLevel.equiv_def.1 H []
      simp [VLevel.eval] at this
    · rfl
  have inst_body (p m x : ProofShape) :
      (mkApps (.const ``Eq.rec [.succ v,.succ .zero])
        [.sort .zero,p.liftN 1,m.liftN 1,.bvar 0]).inst x =
      mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,p,m,x] := by
    simp only [ProofShape.mkApps, inst_eq_subst, ProofShape.subst, ProofShape.Subst.liftN,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.Subst.cons]
  constructor
  · intro R
    obtain ⟨A', body, x', xs', RF, RX, RT⟩ := R.lambda_spine_sort erased_joint_union_head
    have RF' := RF
    rw [← EF, ← Earg] at RF'
    obtain ⟨_, _, E, _, RB⟩ := eta_body_path heq hs hΓ hN hf hnf RF'
    obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj E
    rw [proofErase_eta_body hΓ hN hf hnf, EF, Earg] at RB
    have RB' : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (N :: Γ))
        (mkApps (.const ``Eq.rec [.succ v,.succ .zero])
          (([.sort .zero,P.lift,M.lift,.bvar 0,P.lift].map (proofErase (N :: Γ))).take 4)) body := by
      simpa only [List.map_cons, List.map_nil, List.take, ES', EP, EM, EV,
        ProofShape.mkApps, ProofShape.liftN] using RB
    obtain ⟨args, EB, HA⟩ := proofErase_joint_union_eq_prop_short_spine
      heq hs hregistry hEq hRec hΓN (by decide : 4 < 5) ht hn RB'
    simp only [List.map_cons, List.map_nil, List.take, ES', EP, EM, EV] at HA
    cases HA with | cons RS HA =>
      cases HA with | cons RP HA =>
        cases HA with | cons RM HA =>
          cases HA with | cons RV HA =>
            cases HA
            cases RS.sort_fixed erased_joint_union_head
            cases RV.bvar_fixed erased_joint_union_head
            obtain ⟨P', _, RP', EP'⟩ := proofErase_scoped_compute_certificate_descend
              (erased_joint_union_certificate_descent heq hs) hΓ hΓN Ctx.LiftN.one hP rfl RP
            obtain ⟨M', _, RM', EM'⟩ := proofErase_scoped_compute_certificate_descend
              (erased_joint_union_certificate_descent heq hs) hΓ hΓN Ctx.LiftN.one hM rfl RM
            rw [← EP', ← EM'] at EB
            rw [EB, inst_body] at RT
            cases RX with | cons RX RXS =>
              exact (compute_spine (.app (.app (.app (.app .refl .refl) RP') RM') RX) RXS).trans RT
  · intro R
    have E := inst_body (proofErase Γ P) (proofErase Γ M) x
    have RB : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (.app (.lam (proofErase Γ N) (.app ((mkApps (.const ``Eq.rec [.succ v,.succ .zero])
          [.sort .zero,proofErase Γ P,proofErase Γ M]).liftN 1) (.bvar 0))) x)
        (mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,proofErase Γ P,proofErase Γ M,x]) := by
      exact E ▸ ScopedCompute.beta (by simpa only [ProofShape.mkApps, ProofShape.liftN] using
        (BetaRed.beta (A := proofErase Γ N) (b := mkApps (.const ``Eq.rec [.succ v,.succ .zero])
          [.sort .zero,(proofErase Γ P).liftN 1,(proofErase Γ M).liftN 1,.bvar 0]) (a := x)))
    exact (compute_spine RB (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))).trans R

private theorem minor_prefix_typing
    (heq : env.HasCanonicalEq) (hv : v.WF univs)
    (hP : env.HasType univs Γ P (.sort .zero))
    (hM : env.HasType univs Γ M
      (.forallE (.sort .zero)
        (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ v))))) :
    ∃ B, env.HasType univs Γ
      (VExpr.mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,P,M])
      (.forallE (.app (.app M P) (eqReflApp (.succ .zero) (.sort .zero) P)) B) := by
  have hc := HasType.const (U := univs) (Γ := Γ) heq.2.2.1
    (ls := [.succ v,.succ .zero]) (by simp; exact ⟨hv, by trivial⟩) rfl
  have h1 := hc.app (HasType.sort (l := .zero) (by trivial))
  simp [canonicalEqRecMotive, canonicalEqRecMinor,
    VExpr.instL, VLevel.inst, VExpr.inst, VExpr.instVar, VExpr.liftN] at h1
  have h2 := h1.app hP
  simp [VExpr.inst, VExpr.instVar] at h2
  have h3 := h2.app hM
  simp [VExpr.inst, VExpr.instVar, inst_lift] at h3
  exact ⟨_, h3⟩

open private type_probe_prefix_typed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe

/-- The actual Eq probe preserves its original index-comparison criterion
under eta before its minor, using the canonical motive-application annotation.
The minor is a universe but no recovery at that computed domain is assumed. -/
theorem eqTypeProbe_minor_eta_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    let M := constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))
    let N := VExpr.app (.app M P) (eqReflApp (.succ .zero) (.sort .zero) P)
    let f := ProofShape.mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
      [.sort .zero,proofErase Γ P,proofErase Γ M]
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.lam (proofErase Γ N) (.app (f.liftN 1) (.bvar 0)))
        [.sort v,proofErase Γ Q,.proof]) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have hS : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  obtain ⟨T, ht, hn⟩ := type_probe_prefix_typed heq hΓ hS hP hQ
  obtain ⟨_, _, _, _, hM, hm, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨T, ht⟩
  obtain ⟨B, hf⟩ := minor_prefix_typing heq (v := .succ v) hv hP hM
  have hnf := not_isProof_fn hΓ hf hm
    (not_isProof_fn hΓ (HasType.eqRec4 heq (v := .succ (.succ v)) hv (by trivial)
      (HasType.sort (by trivial)) hP hM hm) hQ hn)
  have H := eqRec_minor_eta_spine_sort_iff (v := .succ v) heq hs hregistry hEq hRec hv hΓ hP hM hf hnf
    (x := .sort v) (xs := [proofErase Γ Q,.proof]) (w := v)
  have E := eqTypeProbe_erase heq hΓ hS hP hQ hq
  rw [show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ hS)] at E
  change _ ↔ ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
    (mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
      [.sort .zero,proofErase Γ P,
        proofErase Γ (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))),
        .sort v,proofErase Γ Q,.proof]) (.sort v) at H
  rw [← E] at H
  exact H.trans (eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec hv hΓ hP hQ hq)

/-- Minor eta also retains the lower comparison certificate across arbitrary
binder insertion. Its canonical domain and equality major may be upstairs;
no lower proof major or recovery at the motive application is required. -/
theorem eqTypeProbe_minor_eta_sort_below_iff
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
    let N := VExpr.app (.app M (P.liftN n k))
      (eqReflApp (.succ .zero) (.sort .zero) (P.liftN n k))
    let f := ProofShape.mkApps (.const ``Eq.rec [.succ (.succ v),.succ .zero])
      [.sort .zero,proofErase Γ' (P.liftN n k),proofErase Γ' M]
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
      (mkApps (.lam (proofErase Γ' N) (.app (f.liftN 1) (.bvar 0)))
        [.sort v,proofErase Γ' (Q.liftN n k),.proof]) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have H := eqTypeProbe_minor_eta_sort_iff heq hs hregistry hEq hRec hv hΓ'
    (hP.weakN henv W) (hQ.weakN henv W) hq
  exact H.trans (by
    rw [proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ]
    exact proofErase_joint_union_compare_lift_iff heq hs hΓ hΓ' W hP hQ)

end Lean4Lean.VEnv.Strengthening
