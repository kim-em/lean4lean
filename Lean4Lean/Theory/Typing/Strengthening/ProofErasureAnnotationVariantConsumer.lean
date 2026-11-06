import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationVariantChecking

/-! # Arbitrary typed consumers of nonjoining lambda annotations

The paired annotation relation propagates through every occurrence of a typed
consumer's argument. Paired beta simulation and typed checking then handle
independent residuals, even when the consumer duplicates or applies the supplied
lambdas. No computational join of those lambdas or their domains is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- A recursive domain comparison supplies a marked lambda pair. Common Pi
typing and the unchanged body erasure are obtained from reflected domain equality. -/
theorem recursive_lambda_annotation_variant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (HA : RecursiveFamilyCast D true (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C)) :
    env.HasType univs Γ (.lam C b) (.forallE A B) ∧
      AnnotationVariant (CertifiedAnnotationDomains (ErasedJointUnion D) (proofEraseCtx Γ)) 0
        (proofErase Γ (.lam A b)) (proofErase Γ (.lam C b)) := by
  have HAC := HA.reflect heq hs hregistry hΓ hA hC
  have HL := IsDefEq.lamDF HAC hb
  refine ⟨HL.hasType.2, ?_⟩
  by_cases hp : IsProof Γ (.lam A b)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HL).1 hp)]
    exact .refl
  have hpc : ¬ IsProof Γ (.lam C b) := fun H => hp ((isProof_congr hΓ HL).2 H)
  have EB := proofErase_defeqCtx (Γ₁ := A :: Γ) ⟨hΓ, u, hA⟩
    (IsDefEqCtx.succ .zero HAC) hb
  rw [show proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b)
      from if_neg hp,
    show proofErase Γ (.lam C b) = .lam (proofErase Γ C) (proofErase (C :: Γ) b)
      from if_neg hpc, ← EB]
  have HG : CertifiedAnnotationDomains (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C) :=
    ⟨u, DomainSort.of_typed hΓ hA, DomainSort.of_typed hΓ hC, HA.future heq hs hregistry⟩
  simpa only [ProofShape.liftN_zero] using
    (AnnotationVariant.marked (n := 0) (b := proofErase (A :: Γ) b) HG .refl)

/-- Every typed consumer of the two reannotated lambdas retains inferred future
checking. The consumer and lambda body are unrestricted; no endpoint join or
new recovery premise is needed. Ambient substitution and beta redexes created
by any number of argument duplications are included. -/
theorem recursive_annotation_consumer_future
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (HA : RecursiveFamilyCast D true (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C)) :
    env.HasType univs Γ (.lam C b) (.forallE A B) ∧
      BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ false) (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b))) := by
  obtain ⟨hc, V⟩ := recursive_lambda_annotation_variant heq hs hregistry hΓ hA hC hb HA
  have hf := HasType.lam hA hb
  have hΓPi : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
  have VT : AnnotationVariant (CertifiedAnnotationDomains (ErasedJointUnion D) (proofEraseCtx Γ)) 0
      (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b))) := by
    rw [proofErase_instN hΓPi hf Ctx.InstN.zero ht, proofErase_instN hΓPi hc Ctx.InstN.zero ht]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
    apply AnnotationVariant.subst_images
    intro i
    cases i with
    | zero => exact V
    | succ i => exact .refl
  exact ⟨hc, annotation_variant_future VT hΓ (ht.instN henv Ctx.InstN.zero hf)⟩

omit [Params] in
/-- Actual canonical-Eq environments give a finite inferred comparison at
any two beta residuals of an arbitrary typed consumer of the lambda pair.
The only alignment premise is its constructive recursive domain certificate. -/
theorem EnvironmentCore.recursive_annotation_consumer_beta
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ A C u b B t T left right}, env.HasCanonicalEq → OnCtx Γ (env.IsType U) →
      env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort u) →
      env.HasType U (A :: Γ) b B → env.HasType U (.forallE A B :: Γ) t T →
      RecursiveFamilyCast definitions true (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C) →
      ProofShape.BetaRed (proofErase Γ (t.inst (.lam A b))) left →
      ProofShape.BetaRed (proofErase Γ (t.inst (.lam C b))) right →
      ∃ n, JointCompare (ErasedJointStage definitions n) (proofEraseCtx Γ) false left right := by
  letI := henv.params U
  intro Γ A C u b B t T left right heq hΓ hA hC hb ht HA RL RR
  have H := (recursive_annotation_consumer_future heq sound rfl hΓ hA hC hb ht HA).2
  exact (H.1 RL RR).finite_stage erased_joint_stage_mono

end Lean4Lean.VEnv.Strengthening
