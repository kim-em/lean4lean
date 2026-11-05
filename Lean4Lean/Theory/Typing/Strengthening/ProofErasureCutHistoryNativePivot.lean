import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCutComponentHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureControlReturn
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureBetaRecovery

/-! # Recovering a later cut's guard before argument computation

A component history need not certify its current contraction. Its original
contractum nevertheless computes to a pivot with every selected native type of
the current redex. The pivot uses the computed body and the original argument;
argument computation transports its selected type before the guard is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Every native output of the evolved cut is recovered at an intermediate
reachable from the original contractum. That intermediate then computes to the
current raw contractum. Exact recovery of the current argument is not needed:
recover the computed body under the original binder, instantiate the original
argument, and propagate the argument path through the selected type. -/
theorem CutComponentHistory.native_pivot
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : CutComponentHistory D Γ A b x u B s)
    (hn : ¬ IsProof Γ (.app (.lam A b) x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      s.redex selected) :
    ∃ pivot, env.HasType univs Γ pivot (B.inst x) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (proofErase Γ pivot) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ pivot) (s.2.1.inst s.2.2) ∧
      ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ pivot) selected := by
  obtain ⟨⟨C, HAC, EC, RA⟩, ⟨d, Hbd, Ed, RB⟩, ⟨y, Hxy, Ey, RX⟩⟩ := H
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have hdC := Hbd.hasType.2.defeqDFC henv HC
  have hyC := HAC.defeq Hxy.hasType.2
  have EdC : proofErase (C :: Γ) d = s.2.1 :=
    (proofErase_defeqCtx hΓA HC Hbd.hasType.2).symm.trans Ed
  have HE := IsDefEq.appDF (IsDefEq.lamDF HAC Hbd) Hxy
  have hnr : ¬ IsProof Γ (.app (.lam C d) y) := fun hp => hn ((isProof_congr hΓ HE).2 hp)
  have hnf := not_isProof_fn hΓ (HasType.lam HAC.hasType.2 hdC) hyC hnr
  have ER : proofErase Γ (.app (.lam C d) y) = s.redex := by
    rw [show proofErase Γ (.app (.lam C d) y) = .app _ _ from if_neg hnr,
      show proofErase Γ (.lam C d) = .lam _ _ from if_neg hnf, EC, EdC, Ey]
    rfl
  obtain ⟨nativeBody, RNbody, RT⟩ := static_structure_root_beta_native_factor heq hs hΓ
    HAC.hasType.2 hdC hyC (ER ▸ RN)
  have RNold := proofErase_static_structure_union_recovery_backward_context heq hs hΓ HAC
    (EC ▸ RA) hdC RNbody
  have RNpivot := static_structure_union_recovery_inst heq hs hΓ Hxy.hasType.1 HR Hbd.hasType.2 RNold
  obtain ⟨S, hdS, ES⟩ := proofErase_scoped_typeRecovery_replay
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA Hbd.hasType.2 RNold
  obtain ⟨_, hS⟩ := hdS.isType henv hΓA
  have RTS := proofErase_static_structure_compute_inst_argument heq hs hΓA hS Hxy.hasType.1 RX
  rw [proofErase_instN hΓA Hxy.hasType.1 Ctx.InstN.zero hS, ES] at RTS
  rw [Ey] at RT
  have Rfirst := static_structure_union_compute_inst heq hs hΓ Hxy.hasType.1 HR Hbd.hasType.1 RB
  have Epivot := proofErase_instN hΓA Hxy.hasType.1 Ctx.InstN.zero Hbd.hasType.2
  rw [Ed] at Epivot
  have Rlast := proofErase_static_structure_compute_inst_argument heq hs hΓA Hbd.hasType.2 Hxy.hasType.1 RX
  rw [Ed] at Rlast
  exact ⟨d.inst x, Hbd.hasType.2.instN henv.ordered Ctx.InstN.zero Hxy.hasType.1,
    Epivot ▸ Rfirst, Rlast, RNpivot.convert (RTS.trans RT)⟩

end Lean4Lean.VEnv.Strengthening
