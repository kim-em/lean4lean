import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta

/-! # Paired head beta for inferred lambdas applied to proofs

The recovered-image head-beta theorem specializes to proof arguments without
any recovery premise: both proofs erase to the same marker. Displayed domains
may differ and computation may change their annotations. No endpoint beta
stability is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem proof_domain
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hf : env.HasType univs Γ (.lam A b) (.forallE P B))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b C) :
    env.HasType univs Γ A (.sort .zero) := by
  obtain ⟨⟨_, E⟩, _, _⟩ := (hf.uniqU henv hΓ (HasType.lam hA hb)).forallE_inv henv hΓ
  exact (show env.IsDefEqU univs Γ P A from ⟨_, E⟩).of_l henv hΓ hP |>.hasType.2

/-- Inferred comparison of two displayed lambdas survives simultaneous head
beta at proof arguments. Domains may differ and may compute along the source
comparison. Only source descent, primitive substitution and head restriction
are used; no proposition or general endpoint-beta comparison law is assumed. -/
theorem proofErase_joint_inferred_lambdas_inst_proof
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P)
    (hf : env.HasType univs Γ f (.forallE P B)) (hg : env.HasType univs Γ g (.forallE P B))
    (Ef : proofErase Γ f = .lam A b) (Eg : proofErase Γ g = .lam D c)
    (H : JointCompare Step (proofEraseCtx Γ) false (.lam A b) (.lam D c)) :
    JointCompare Step (proofEraseCtx Γ) false (b.inst .proof) (c.inst .proof) := by
  have hproof : IsProof Γ p := ⟨P, hp, hP⟩
  have HC := proofErase_joint_inferred_lambdas_inst_recovered hstep hsubst hhead hΓ hp hf hg Ef Eg
    (fun hn => (hn hproof).elim) (fun hn => (hn hproof).elim) H
  simpa only [proofErase_eq_proof.2 hproof] using HC

/-- The proof-argument application critical pair for actual proposition-valued
lambdas. The proofs may be different, and the two displayed domains may be
converted annotations of the shared proposition domain. Both beta-contracta
have an actual common-mode certificate in the same primitive relation. -/
theorem proofErase_joint_proposition_head_beta_proofs
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam D c) (.forallE P (.sort .zero)))
    (H : JointCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam D c))) :
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hD⟩, C', hc⟩ := hg.lam_inv henv hΓ
  have hA₀ := proof_domain hΓ hP hf hA hb
  have hD₀ := proof_domain hΓ hP hg hD hc
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
  have hqD := argument_at_displayed_domain hΓ hg (HasType.lam hD hc) hq
  have EF : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
    if_neg (not_isProof_function_to_sort hΓ hf)
  have EG : proofErase Γ (.lam D c) = .lam (proofErase Γ D) (proofErase (D :: Γ) c) :=
    if_neg (not_isProof_function_to_sort hΓ hg)
  have HC := proofErase_joint_inferred_lambdas_inst_proof hstep hsubst hhead hΓ hP hp hf hg EF EG
    (by simpa only [EF, EG] using H)
  rw [proofErase_instN (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, _, hA₀⟩) hpA Ctx.InstN.zero hb,
    proofErase_instN (show OnCtx (D :: Γ) (env.IsType univs) from ⟨hΓ, _, hD₀⟩) hqD Ctx.InstN.zero hc,
    proofErase_eq_proof.2 ⟨A, hpA, hA₀⟩, proofErase_eq_proof.2 ⟨D, hqD, hD₀⟩]
  exact JointCompare.common HC

/-- Certified inferred functions close the paired proof head-beta case
without any proposition endpoint-beta hypothesis. The output retains its
certified primitives for further context/type transport and computation. -/
theorem proofErase_certified_proposition_head_beta_proofs
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_joint_proposition_head_beta_proofs (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) erased_beta_stable_joint_head hΓ hP hp hq hf hg H

/-- The same paired head-beta case accepts source stage n+1 inferred function
comparisons using only stage-n proposition transport to certify the input.
No beta transport of the resulting enlarged comparison is assumed. -/
theorem proofErase_joint_stage_proposition_head_beta_proofs
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (H : JointCompare (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_certified_proposition_head_beta_proofs heq hs hΓ hP hp hq hf hg
    (proofErase_joint_compare_certify_of_lower_beta heq hs hregistry Hbeta hΓ hf hg H)

/-- At stage zero the paired proof head-beta case stays at stage zero itself.
Neither certification nor a lower-stage endpoint-beta premise is needed. -/
theorem proofErase_joint_zero_proposition_head_beta_proofs
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (H : JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedJointStage D 0) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_joint_proposition_head_beta_proofs (erased_joint_stage_descent heq hs 0)
    (fun H _ => erased_iota_primitive_subst H) (erased_joint_stage_head 0) hΓ hP hp hq hf hg H

end Lean4Lean.VEnv.Strengthening
