import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointStructuralSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointFirstStageSubstitution

/-! # First-layer computation under convertible structural-family substitution -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Structural-family images satisfy the finite recursive guard substitution
interface. The instance uses the proved application repair at stage zero. -/
theorem ComputedZeroGuardSubstitution.structural (hs : D.Sound env univs) :
    ComputedZeroGuardSubstitution D (StructuralImageSubstitution D) :=
  ⟨(fun W => W.interpretation), (fun W => W.cons), (fun H => H.transport_structuralImages hs)⟩

/-- Protected structural-family images transport first-layer computations at the
same stage, even when exact selected-domain recovery is unavailable. -/
theorem proofErase_computed_joint_one_compute_subst_structural
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (E : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : StructuralOrRecoveringImages D cut Γ Γ₀ σ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  rw [proofErase_subst_with hΓ₀ W ht E]
  exact R.transport_firstStage_guard heq hs (ComputedZeroGuardSubstitution.structural hs)
    W.wf ht rfl rfl (StructuralImageSubstitution.of_typed hΓ₀ W E HI)

/-- A selected structural-family path supplies the image invariant for single
instantiation throughout a first-layer computation. -/
theorem proofErase_computed_joint_one_compute_inst_structural
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p T)
    (HR : StructuralFamilyRecovery D cut Γ p (proofErase Γ T) n)
    (he : env.HasType univs (T :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (T :: Γ)) (proofErase (T :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) := by
  obtain ⟨u, hT⟩ := hp.isType henv hΓ
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := T)).substEq hΓT hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN] using
    proofErase_computed_joint_one_compute_subst_structural heq hs hΓ W
      (erasedSubstAgreement_one hΓT hp) (StructuralOrRecoveringImages.inst HR) he R


/-- A beta-exposed family at a dependent structural domain instantiates all
first-layer computations. No shape restriction is imposed on the inner
codomain, and the exact substituted output is preserved. -/
theorem proofErase_computed_joint_one_compute_inst_dependentStructuralFamily
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.forallE (.forallE C K) (.sort w)))
    (HC : AnchoredCarrier 0 (proofErase Γ C))
    (RP : VExpr.BetaRed p (.lam (.forallE E K) body))
    (he : env.HasType univs (.forallE (.forallE C K) (.sort w) :: Γ) e A)
    (R : ScopedCompute (ErasedComputedJointStage D 1)
      (proofEraseCtx (.forallE (.forallE C K) (.sort w) :: Γ))
      (proofErase (.forallE (.forallE C K) (.sort w) :: Γ) e) out) :
    ScopedCompute (ErasedComputedJointStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (e.inst p)) (out.inst (proofErase Γ p)) :=
  proofErase_computed_joint_one_compute_inst_structural heq hs hΓ hp
    (StructuralFamilyRecovery.of_dependent_structural hΓ hp HC RP) he R

end Lean4Lean.VEnv.Strengthening
