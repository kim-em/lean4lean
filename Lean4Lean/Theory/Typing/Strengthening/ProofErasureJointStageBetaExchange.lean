import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointStageSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Head beta exchange from strictly lower guard stability

The lambda path is instantiated before its source stage can grow. Its final
body has a typed representative at the final annotation, so existing argument
computation congruence handles all copies of the argument afterwards.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- A stage-n+1 lambda/argument computation closes against head beta using
only stage-n proposition beta transport. Neither argument needs exact recovery,
and no stability assumption is made about the union certificates produced. -/
theorem proofErase_joint_stage_beta_exchange_of_lower_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (RF : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) functionOut)
    (RX : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ)
      (proofErase Γ x) argumentOut) :
    ∃ A' bodyOut, functionOut = .lam A' bodyOut ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
        (proofErase Γ (b.inst x)) (bodyOut.inst argumentOut) ∧
      ProofShape.BetaRed (.app functionOut argumentOut) (bodyOut.inst argumentOut) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointStage D (stage + 1)) :=
    erased_joint_stage_descent heq hs (stage + 1)
  obtain ⟨A', bodyOut, rfl, RI⟩ := proofErase_scoped_lambda_inst_compute hstep
    (erased_joint_stage_head (stage + 1))
    (erased_joint_stage_subst_of_lower_beta heq hs hregistry Hbeta) hΓ hA hb hx hn RF
  have EF : proofErase Γ (.lam A b) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) b) := if_neg hn
  obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ (HasType.lam hA hb) rfl EF RF
  obtain ⟨A₀, b₀, rfl, _, EA₀, Eb₀⟩ := erase_lam_inv Ef'
  obtain ⟨⟨v, hA₀⟩, B₀, hb₀⟩ := HF.hasType.2.lam_inv henv hΓ
  obtain ⟨⟨_, HAA⟩, _, _⟩ := (HF.hasType.2.uniqU henv hΓ (HasType.lam hA₀ hb₀)).forallE_inv henv hΓ
  have hx₀ := HAA.defeq hx
  have hΓA₀ : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, v, hA₀⟩
  have RX' := proofErase_joint_compute_inst_argument heq hs hΓA₀ hb₀ hx₀ RX
  rw [proofErase_instN hΓA₀ hx₀ Ctx.InstN.zero hb₀, Eb₀] at RX'
  exact ⟨A', bodyOut, rfl, RI.trans (RX'.mono (fun H => ⟨stage + 1, H⟩)), .beta⟩

end Lean4Lean.VEnv.Strengthening
