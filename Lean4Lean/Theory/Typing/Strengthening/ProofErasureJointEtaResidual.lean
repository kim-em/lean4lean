import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnionHeadBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUniverseHeadBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEtaBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaClassification

/-! # Retaining full joint computation after function eta

The computed annotation need not support forward context transport. Opening the
result at the original function carrier instead retains the body path in its
original context. Recoverable arguments instantiate this path to an exact
application join. This is a local eta/computation exchange, not coverage of
arbitrary interleavings or of arbitrary arguments.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private lam_inv_aux from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBinderComputation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_sort_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparison
open private universe_oracles from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUniverseHeadBeta
variable [Params]

private theorem eta_body_path
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u))) out) :
    ∃ A' body, out = .lam A' body ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) A' ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) (.app f.lift (.bvar 0))) body := by
  have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [lift, VExpr.liftN, inst_liftN_bvar] using
      HasType.app (hf.weak henv) (HasType.bvar .zero)
  have hnη : ¬ IsProof Γ (.lam A (.app f.lift (.bvar 0))) :=
    fun H => hn ((isProof_congr hΓ (IsDefEq.eta hf)).1 H)
  obtain ⟨A', body, E, RA, RB⟩ := lam_inv_aux heq hs R hΓ hA hb hnη rfl
    (by rw [proofErase_eta_body hΓ hA hf hn])
  exact ⟨A', body, E, RA, RB⟩

/-- Computation of the canonical eta expansion retains an explicit carrier
comparison with the short function at its original Pi carrier. Annotation
changes require neither forward context conversion nor primitive substitution.
The conclusion is a carrier guard, not an inferred function comparison. -/
theorem proofErase_joint_eta_carrier_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u))) out) :
    JointCarrierGuard (ErasedJointUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out (proofErase Γ f) := by
  obtain ⟨A', body, rfl, _, RB⟩ := eta_body_path heq hs hΓ hA hf hn R
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [lift, VExpr.liftN, inst_liftN_bvar] using
      HasType.app (hf.weak henv) (HasType.bvar .zero)
  obtain ⟨b', HB, Eb⟩ := proofErase_scoped_compute_realize
    (erased_joint_union_descent heq hs) hΓA hb rfl rfl RB
  have E : (body.liftN 1 1).inst (etaArgument u) = body := by
    rw [← Eb]
    exact proofErase_eta_inst hΓ hA HB.hasType.2
  apply JointCheck.carrierFunction (DomainSort.of_typed hΓ hA)
  apply JointCheck.carrierChecked
  apply JointCheck.compute (a' := body) (b' := body)
  · apply ScopedCompute.beta
    simpa only [ProofShape.liftN, E] using
      (ProofShape.BetaRed.beta (A := A'.liftN 1)
        (b := body.liftN 1 1) (a := etaArgument u))
  · simpa only [proofEraseCtx, proofErase_eta_body hΓ hA hf hn] using RB
  · exact .leaf .refl

/-- An eta expansion and argument may compute independently before application.
Their application joins the original short-function application exactly.
Only the original argument must recover the original domain; neither the
computed argument nor the changed lambda annotation needs recovery.
No global comparison beta stability, confluence, or eta factorization is used. -/
theorem proofErase_joint_eta_application_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (hp : env.HasType univs Γ p A)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (RX : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ p) argumentOut)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u))) out) :
    ∃ shared,
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (.app out argumentOut) shared ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (proofErase Γ (.app f p)) shared := by
  obtain ⟨A', body, rfl, _, RB⟩ := eta_body_path heq hs hΓ hA hf hn R
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
  refine ⟨body.inst argumentOut, .beta .beta, ?_⟩
  rw [← proofErase_instN hΓA hp Ctx.InstN.zero hb] at RI
  simpa only [VExpr.inst, VExpr.inst_lift, instVar_zero] using RI

/-- If the computed eta annotation is a literal universe, the residual is
an ordinary common comparison. The original annotation may be arbitrary and
may compute through full joint primitives; universe context transport moves
the retained body path to the actual output binder without a global premise. -/
theorem proofErase_joint_eta_universe_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (.app ((proofErase Γ f).liftN 1) (etaArgument u)))
      (.lam (.sort v) body)) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (.lam (.sort v) body) (proofErase Γ f) := by
  obtain ⟨A', body', E, RA, RB⟩ := eta_body_path heq hs hΓ hA hf hn R
  obtain ⟨rfl, rfl⟩ := ProofShape.lam.inj E
  obtain ⟨A₁, HE, EA⟩ := proofErase_scoped_compute_realize
    (erased_joint_union_descent heq hs) hΓ hA rfl rfl RA
  obtain rfl := erase_sort_inv EA
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) B := by
    simpa only [lift, VExpr.liftN, inst_liftN_bvar] using
      HasType.app (hf.weak henv) (HasType.bvar .zero)
  have W : IsDefEqCtx env univs [] (A :: Γ) (.sort v :: Γ) := .succ (.refl hΓ) HE
  have RC := proofErase_joint_union_universe_compute heq hs hΓA W
    (universe_oracles hΓ HE) hb RB
  rw [← proofErase_defeqCtx hΓA W hb, proofErase_eta_body hΓ hA hf hn] at RC
  apply JointCheck.etaBodyL (EA ▸ DomainSort.of_typed hΓ HE.hasType.2)
  apply JointCheck.compute .refl (b' := body)
    (show ScopedCompute (ErasedJointUnion D) (.sort v :: proofEraseCtx Γ)
      (.app ((proofErase Γ f).liftN 1) (etaArgument u)) body from by
        simpa only [proofEraseCtx, EA] using RC)
  exact .leaf .refl

end Lean4Lean.VEnv.Strengthening
