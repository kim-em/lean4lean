import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqShortSpine

/-! # The motive prefix without an existing minor premise

A fresh minor variable completes the typed prefix above one binder. Its
argument-path decomposition descends with exact computation certificates.
No inhabitant of the motive's result is assumed in the original context.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
open private ProofShape.subst_bvar_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- The three-argument Prop-carrier Eq prefix computes only its proposition
and motive arguments, even when no minor is available. A fresh minor binder
is eliminated by exact certificate descent, not by an inhabited substitution. -/
theorem proofErase_joint_union_eq_motive_spine
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hM : env.HasType univs Γ M
      (.forallE (.sort .zero)
        (.forallE (eqApp (.succ .zero) (.sort .zero) P.lift (.bvar 0)) (.sort (.succ v)))))
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (mkApps (.const ``Eq.rec [.succ v,.succ .zero])
        [.sort .zero, proofErase Γ P, proofErase Γ M]) out) :
    ∃ p m : ProofShape, out = mkApps (.const ``Eq.rec [.succ v,.succ .zero]) [.sort .zero,p,m] ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ P) p ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ M) m := by
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
  have ES : proofErase (N :: Γ) (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓN (HasType.sort (by trivial)))
  have RL := R.rename (erased_joint_union_rename heq hs)
    (ContextRenaming.of_liftN hΓ hΓN Ctx.LiftN.one)
  have RL' : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (N :: Γ))
      (mkApps (.const ``Eq.rec [.succ v,.succ .zero])
        (([.sort .zero,P.lift,M.lift,.bvar 0,P.lift].map (proofErase (N :: Γ))).take 3))
      (out.liftN 1) := by
    simpa only [List.map_cons, List.map_nil, List.take, ProofShape.mkApps,
      ES, EP, EM, ProofShape.subst_bvar_liftN, ProofShape.liftN] using RL
  obtain ⟨args, EO, HA⟩ := proofErase_joint_union_eq_prop_short_spine
    heq hs hregistry hEq hRec hΓN (by decide : 3 < 5) ht hn RL'
  simp only [List.map_cons, List.map_nil, List.take, ES, EP, EM] at HA
  cases HA with | cons RS HA =>
    cases HA with | cons RP HA =>
      cases HA with | cons RM HA =>
        cases HA
        cases RS.sort_fixed erased_joint_union_head
        obtain ⟨P', _, RP', EP'⟩ := proofErase_scoped_compute_certificate_descend
          (erased_joint_union_certificate_descent heq hs) hΓ hΓN Ctx.LiftN.one hP rfl RP
        obtain ⟨M', _, RM', EM'⟩ := proofErase_scoped_compute_certificate_descend
          (erased_joint_union_certificate_descent heq hs) hΓ hΓN Ctx.LiftN.one hM rfl RM
        refine ⟨proofErase Γ P', proofErase Γ M', ?_, RP', RM'⟩
        apply (ProofShape.liftN_inj (n := 1) (k := 0)).mp
        simpa only [ProofShape.mkApps, ProofShape.liftN, EP', EM'] using EO

end Lean4Lean.VEnv.Strengthening
