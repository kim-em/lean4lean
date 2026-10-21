import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFirstBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbeCertificate

/-! # Removing a function-eta detour from universe exposure

The first head-beta decomposition retains the entire remaining path. Exact
instantiation of the computed eta body then removes the detour while preserving
the final universe. Proof arguments require no recovery premise. Applied to the
Eq probe's last prefix, this preserves its exact index-certificate equivalence.
Earlier-prefix eta and arbitrary full-reduction interleavings remain uncovered.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eta_body_path from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEtaResidual
open private type_probe_prefix_typed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTypeProbe
variable [Params]

private theorem short_to_contractum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (hp : env.HasType univs Γ p A)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (RX : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) x')
    (RF : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u)))
      (.lam A' body)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f p)) (body.inst x') := by
  obtain ⟨_, _, E, _, RB⟩ := eta_body_path heq hs hΓ hA hf hn RF
  obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj E
  have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [lift, VExpr.liftN, inst_liftN_bvar] using
      HasType.app (hf.weak henv) (HasType.bvar .zero)
  have RI := proofErase_joint_union_compute_inst heq hs hΓ hp HR hb RB
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨b', HB, Eb⟩ := proofErase_scoped_compute_realize
    (erased_joint_union_descent heq hs) hΓA hb rfl rfl RB
  obtain ⟨stage, RX⟩ := RX.finite_stage erased_joint_stage_mono
  have RX' := (proofErase_joint_compute_inst_argument heq hs hΓA HB.hasType.2 hp RX).mono
    (Step' := ErasedJointUnion D) (fun H => ⟨stage, H⟩)
  rw [proofErase_instN hΓA hp Ctx.InstN.zero HB.hasType.2, Eb] at RX'
  have RI := RI.trans RX'
  rw [← proofErase_instN hΓA hp Ctx.InstN.zero hb] at RI
  simpa only [VExpr.inst, VExpr.inst_lift, instVar_zero] using RI

/-- A full joint computation from an eta-expanded application reaches a given
literal universe iff the short application does. The expansion, argument and
post-beta tail may compute arbitrarily; only the original argument needs
recovery at its assigned domain. The exact final universe is preserved. -/
theorem proofErase_joint_eta_application_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (hp : env.HasType univs Γ p A)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A)) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.app (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u)))
        (proofErase Γ p)) (.sort v) ↔
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f p)) (.sort v) := by
  constructor
  · intro R
    obtain ⟨A', body, x', RF, RX, RT⟩ := R.lambda_app_sort erased_joint_union_head
    exact (short_to_contractum heq hs hΓ hA hf hn hp HR RX RF).trans RT
  · intro R
    have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
      simpa only [lift, VExpr.liftN, inst_liftN_bvar] using
        HasType.app (hf.weak henv) (HasType.bvar .zero)
    have E : (ProofShape.app ((proofErase Γ f).liftN 1) (etaArgument u)).inst (proofErase Γ p) =
        proofErase Γ (.app f p) := by
      rw [← proofErase_eta_body hΓ hA hf hn,
        ← proofErase_instN (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, u, hA⟩)
          hp Ctx.InstN.zero hb]
      simp only [VExpr.inst, VExpr.inst_lift, instVar_zero]
    exact (show ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) _
      (proofErase Γ (.app f p)) from E ▸ ScopedCompute.beta .beta).trans R

/-- At a proof domain, arbitrary computation after function eta has exactly
its short application's universe exposures, with no recovery assumption. -/
theorem proofErase_joint_eta_proof_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hf : env.HasType univs Γ f (.forallE P B)) (hn : ¬ IsProof Γ f)
    (hp : env.HasType univs Γ p P) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.app (.lam (proofErase Γ P) (.app ((proofErase Γ f).liftN 1) .proof)) .proof) (.sort v) ↔
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app f p)) (.sort v) := by
  have hproof : IsProof Γ p := ⟨P, hp, hP⟩
  simpa only [proofErase_eq_proof.2 hproof, etaArgument, if_pos (show VLevel.zero ≈ VLevel.zero from rfl)] using
    proofErase_joint_eta_application_sort_iff heq hs hΓ hP hf hn hp
      (fun H => (H hproof).elim) (v := v)

/-- Eta expansion of the Eq probe's final five-argument prefix does not change
its exact universe-computation criterion. The entire subsequent joint path may
compute the annotation and body before beta, and continue after beta; the
criterion remains a comparison of the original proposition indices. -/
theorem eqTypeProbe_final_eta_sort_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hv : v.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero))
    (hQ : env.HasType univs Γ Q (.sort .zero))
    (hq : env.HasType univs Γ q (eqApp (.succ .zero) (.sort .zero) P Q)) :
    let F := eqRecBeforeMajor (.succ (.succ v)) (.succ .zero) (.sort .zero) P
      (constantEqMotive (.succ .zero) (.sort .zero) P (.sort (.succ v))) (.sort v) Q
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.app (.lam (proofErase Γ (eqApp (.succ .zero) (.sort .zero) P Q))
        (.app ((proofErase Γ F).liftN 1) .proof)) .proof) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  dsimp only
  have hS : env.HasType univs Γ (.sort v) (.sort (.succ v)) := .sort hv
  obtain ⟨T, ht, hn⟩ := type_probe_prefix_typed heq hΓ hS hP hQ
  obtain ⟨hv', hw, hα, ha, hM, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨T, ht⟩
  have hf := eqRecBeforeMajor_typed heq hv' hw hα ha hM hm hb
  have Hη := proofErase_joint_eta_proof_sort_iff heq hs hΓ
    (HasType.eqApp heq (by trivial) (HasType.sort (by trivial)) hP hQ) hf hn hq (v := v)
  exact Hη.trans (eqTypeProbe_union_sort_iff heq hs hregistry hEq hRec hv hΓ hP hQ hq)

/-- The eta-expanded final prefix may use an equality major available only
above an inserted block. Its exact universe exposure is equivalent to a
comparison certificate of the original proposition indices below that block.
No lower equality proof or lower probe typing is required. -/
theorem eqTypeProbe_final_eta_sort_below_iff
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
    let F := eqRecBeforeMajor (.succ (.succ v)) (.succ .zero) (.sort .zero) (P.liftN n k)
      (constantEqMotive (.succ .zero) (.sort .zero) (P.liftN n k) (.sort (.succ v)))
      (.sort v) (Q.liftN n k)
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ')
      (.app (.lam (proofErase Γ'
        (eqApp (.succ .zero) (.sort .zero) (P.liftN n k) (Q.liftN n k)))
        (.app ((proofErase Γ' F).liftN 1) .proof)) .proof) (.sort v) ↔
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ P) (proofErase Γ Q) := by
  have H := eqTypeProbe_final_eta_sort_iff heq hs hregistry hEq hRec hv hΓ'
    (hP.weakN henv W) (hQ.weakN henv W) hq
  rw [proofErase_liftN hΓ hΓ' W hP, proofErase_liftN hΓ hΓ' W hQ] at H
  exact H.trans (proofErase_joint_union_compare_lift_iff heq hs hΓ hΓ' W hP hQ)

end Lean4Lean.VEnv.Strengthening
