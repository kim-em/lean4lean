import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointSemanticSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta

/-! # Diagonal head beta from semantic head exposure

The shared lambda induction accepts arbitrary typed body instantiation.
Semantic substitution supplies it without exact recovery of the argument.
Head exposure remains unproved; paired carrier-related images are not reduced
here to a common image.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private inferred_lambdas_with_image
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta
open private beta_inst_image from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropBeta
variable [Params]

private theorem body_inst_of_heads
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (Hheads : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (EΓ : proofEraseCtx (P :: Γ) = Δ) (Ea : proofErase (P :: Γ) a = sa)
    (Eb : proofErase (P :: Γ) b = sb) (H : JointCompare Step Δ mode sa sb) :
    JointCompare Step (proofEraseCtx Γ) mode
      (sa.inst (proofErase Γ p)) (sb.inst (proofErase Γ p)) := by
  obtain ⟨u, hP⟩ := hp.isType henv hΓ
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, u, hP⟩
  have W : ContextSubstitution (proofEraseCtx (P :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one (proofErase Γ p)) :=
    ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓP hp)
      (erasedSubstAgreement_one hΓP hp)
  rw [EΓ] at W
  have H' := H.subst_of_head_exposure hstep hsubst Hheads hΓP ha hb EΓ Ea Eb W
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H'

/-- Inferred lambda comparison survives diagonal instantiation at every typed
argument under semantic head exposure. The shared structural induction is the
same one used by the exact-recovery theorem; its image predicate is True here. -/
theorem proofErase_joint_inferred_lambdas_inst_of_heads
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (Hheads : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (hf : env.HasType univs Γ f (.forallE P B)) (hg : env.HasType univs Γ g (.forallE P B))
    (Ef : proofErase Γ f = .lam A b) (Eg : proofErase Γ g = .lam E c)
    (H : JointCompare Step (proofEraseCtx Γ) false (.lam A b) (.lam E c)) :
    JointCompare Step (proofEraseCtx Γ) false
      (b.inst (proofErase Γ p)) (c.inst (proofErase Γ p)) :=
  inferred_lambdas_with_image (fun _ _ _ => True) hstep hsubst hhead
    (fun _ _ => trivial)
    (fun hΓ hp _ ha hb EΓ Ea Eb H => body_inst_of_heads hstep hsubst Hheads
      hΓ hp ha hb EΓ Ea Eb H)
    H rfl hΓ hp hf hg rfl Ef Eg rfl rfl trivial trivial

/-- Actual proposition-valued applications close under head beta when the
arguments have equal erasures. Semantic head exposure replaces all exact
argument-recovery premises; it is still an explicit unproved hypothesis. -/
theorem proofErase_joint_proposition_head_beta_of_heads
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (Hheads : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (Epq : proofErase Γ p = proofErase Γ q)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (H : JointCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hE⟩, C', hc⟩ := hg.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
  have hqE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hq
  have EF : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
    if_neg (not_isProof_function_to_sort hΓ hf)
  have EG : proofErase Γ (.lam E c) = .lam (proofErase Γ E) (proofErase (E :: Γ) c) :=
    if_neg (not_isProof_function_to_sort hΓ hg)
  have HC := proofErase_joint_inferred_lambdas_inst_of_heads hstep hsubst hhead Hheads hΓ hp hf hg EF EG
    (by simpa only [EF, EG] using H)
  rw [proofErase_instN (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, _, hA⟩) hpA Ctx.InstN.zero hb,
    proofErase_instN (show OnCtx (E :: Γ) (env.IsType univs) from ⟨hΓ, _, hE⟩) hqE Ctx.InstN.zero hc, ← Epq]
  exact JointCompare.common HC

/-- Certified diagonal proposition head beta needs only semantic head
exposure beyond the already proved primitive closure and descent laws. -/
theorem proofErase_certified_proposition_head_beta_of_heads
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hheads : ScopedSemanticHeadExposure (ErasedBetaStableJoint D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (Epq : proofErase Γ p = proofErase Γ q)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_joint_proposition_head_beta_of_heads (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) erased_beta_stable_joint_head Hheads hΓ hp hq Epq hf hg H

/-- Lower-stage endpoint-beta transport certifies the source function
comparison. Head exposure then supplies diagonal head beta without requiring
exact recovery of the argument at either displayed lambda annotation. -/
theorem proofErase_joint_stage_proposition_head_beta_of_heads
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hheads : ScopedSemanticHeadExposure (ErasedBetaStableJoint D))
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (Epq : proofErase Γ p = proofErase Γ q)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (H : JointCompare (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_certified_proposition_head_beta_of_heads heq hs Hheads hΓ hp hq Epq hf hg
    (proofErase_joint_compare_certify_of_lower_beta heq hs hregistry Hbeta hΓ hf hg H)

/-- Arguments that beta-reduce to a shared typed image also admit head beta
under semantic head exposure. No exact recovery of that image is needed;
arbitrary carrier-related arguments are not covered by this theorem. -/
theorem proofErase_joint_proposition_head_beta_joined_of_heads
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (Hheads : ScopedSemanticHeadExposure Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P) (hz : env.HasType univs Γ z P)
    (RP : ProofShape.BetaRed (proofErase Γ p) (proofErase Γ z))
    (RQ : ProofShape.BetaRed (proofErase Γ q) (proofErase Γ z))
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (H : JointCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  have HC := proofErase_joint_proposition_head_beta_of_heads hstep hsubst hhead Hheads hΓ hz hz rfl hf hg H
  obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hE⟩, C', hc⟩ := hg.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
  have hzA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hz
  have hqE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hq
  have hzE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hz
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓE : OnCtx (E :: Γ) (env.IsType univs) := ⟨hΓ, v, hE⟩
  have RB : ProofShape.BetaRed (proofErase Γ (b.inst p)) (proofErase Γ (b.inst z)) := by
    rw [proofErase_instN hΓA hpA Ctx.InstN.zero hb, proofErase_instN hΓA hzA Ctx.InstN.zero hb]
    exact beta_inst_image _ RP
  have RC : ProofShape.BetaRed (proofErase Γ (c.inst q)) (proofErase Γ (c.inst z)) := by
    rw [proofErase_instN hΓE hqE Ctx.InstN.zero hc, proofErase_instN hΓE hzE Ctx.InstN.zero hc]
    exact beta_inst_image _ RQ
  exact .compute (.beta RB) (.beta RC) HC

/-- The shared-image head-beta theorem specializes to certified checking.
Head exposure remains explicit, and the two literal image-beta paths remain
necessary inputs to this result. -/
theorem proofErase_certified_proposition_head_beta_joined_of_heads
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (Hheads : ScopedSemanticHeadExposure (ErasedBetaStableJoint D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P) (hz : env.HasType univs Γ z P)
    (RP : ProofShape.BetaRed (proofErase Γ p) (proofErase Γ z))
    (RQ : ProofShape.BetaRed (proofErase Γ q) (proofErase Γ z))
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_joint_proposition_head_beta_joined_of_heads (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) erased_beta_stable_joint_head Hheads hΓ hp hq hz RP RQ hf hg H

end Lean4Lean.VEnv.Strengthening
