import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertifiedChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointLoopReadout

/-! # Paired head beta for inferred lambdas applied to proofs

Inferred function comparison excludes common-mode eta-body and lambda-common
rules. Its displayed lambda bodies can therefore be instantiated together at
proof arguments, even when computation changes their annotations. Both proofs
erase to the same marker; no endpoint beta stability is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_common_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
variable [Params]

private theorem proof_domain
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hf : env.HasType univs Γ (.lam A b) (.forallE P B))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b C) :
    env.HasType univs Γ A (.sort .zero) := by
  obtain ⟨⟨_, E⟩, _, _⟩ := (hf.uniqU henv hΓ (HasType.lam hA hb)).forallE_inv henv hΓ
  exact (show env.IsDefEqU univs Γ P A from ⟨_, E⟩).of_l henv hΓ hP |>.hasType.2

private theorem body_inst
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P)
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (EΓ : proofEraseCtx (P :: Γ) = Δ) (Ea : proofErase (P :: Γ) a = sa)
    (Eb : proofErase (P :: Γ) b = sb) (H : JointCompare Step Δ mode sa sb) :
    JointCompare Step (proofEraseCtx Γ) mode (sa.inst .proof) (sb.inst .proof) := by
  have HR := H.rename_retained hstep (fun _ _ _ W H => .base (hsubst H W.interpretation))
    (show OnCtx (P :: Γ) (env.IsType univs) from ⟨hΓ, _, hP⟩) ha hb EΓ Ea Eb
    (by simpa only [EΓ] using RetainedRenaming.proof_inst hΓ hP hp)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HR

omit [Params] in
private theorem eta_inst (H : EtaHead (.lam A b) (.lam D c)) :
    ProofShape.BetaRed (b.inst .proof) (c.inst .proof) := by
  cases H <;>
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.Subst.cons, ProofShape.Subst.id_lift] using
      (ProofShape.BetaRed.beta (A := D) (b := c) (a := .proof))

private theorem inferred_lambdas
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCheck Step Δ kind sa sb)
    (hk : kind = .compare false)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P)
    (hf : env.HasType univs Γ f (.forallE P B)) (hg : env.HasType univs Γ g (.forallE P B))
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = sa) (Eg : proofErase Γ g = sb)
    (EL : sa = .lam A b) (ER : sb = .lam D c) :
    JointCompare Step Δ false (b.inst .proof) (c.inst .proof) := by
  induction H generalizing Γ P p B f g A b D c with
  | leaf H =>
    cases hk
    cases H with
    | refl => have E := (ProofShape.lam.inj (EL.symm.trans ER)).2
              rw [E]
              exact .leaf .refl
    | sort | const => cases EL
  | lam HD HB ihD ihB | lamSorted SD SD' HD HB ihD ihB =>
    cases hk
    cases EL
    cases ER
    obtain ⟨A₀, b₀, rfl, _, EA, Eb⟩ := erase_lam_inv Ef
    obtain ⟨D₀, c₀, rfl, _, ED, Ec⟩ := erase_lam_inv Eg
    obtain ⟨u, C, hA, hD, hb, hc, Ectx⟩ := lambda_common_context hΓ hf hg
    have hA₀ := proof_domain hΓ hP hf hA hb
    have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
    rw [Ectx] at Ec
    have HC := body_inst hstep hsubst hΓ hA₀ hpA hb hc
      (by simp only [proofEraseCtx, EΓ, EA]) Eb Ec HB
    simpa only [EΓ] using HC
  | etaLams HD Heta ihD =>
    cases hk
    cases EL
    cases ER
    rcases Heta with Heta | Heta
    · exact .compute (.beta (eta_inst Heta)) .refl (.leaf .refl)
    · exact .compute .refl (.beta (eta_inst Heta)) (.leaf .refl)
  | compute RF RG HC ih =>
    obtain ⟨A₀, b₀, rfl, hnF, EA, Eb⟩ := erase_lam_inv (Ef.trans EL)
    obtain ⟨D₀, c₀, rfl, hnG, ED, Ec⟩ := erase_lam_inv (Eg.trans ER)
    obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨⟨v, hD⟩, C', hc⟩ := hg.lam_inv henv hΓ
    have hA₀ := proof_domain hΓ hP hf hA hb
    have hD₀ := proof_domain hΓ hP hg hD hc
    have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
    have hpD := argument_at_displayed_domain hΓ hg (HasType.lam hD hc) hp
    obtain ⟨A', b', ELF, _, RB⟩ := ScopedCompute.lam_inv_typed hstep hsubst hhead hΓ hA EΓ (body := b)
      (by simpa only [EL, EA] using RF)
    obtain ⟨D', c', ERG, _, RC⟩ := ScopedCompute.lam_inv_typed hstep hsubst hhead hΓ hD EΓ (body := c)
      (by simpa only [ER, ED] using RG)
    have WB : ContextSubstitution (proofEraseCtx (A₀ :: Γ)) (proofEraseCtx Γ) (ProofShape.Subst.one .proof) :=
      (RetainedRenaming.proof_inst hΓ hA₀ hpA).interpretation
    have WC : ContextSubstitution (proofEraseCtx (D₀ :: Γ)) (proofEraseCtx Γ) (ProofShape.Subst.one .proof) :=
      (RetainedRenaming.proof_inst hΓ hD₀ hpD).interpretation
    simp only [proofEraseCtx, EΓ] at WB WC
    have RB' := RB.subst hsubst WB
    have RC' := RC.subst hsubst WC
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ hg EΓ Eg RG
    apply JointCheck.compute (a' := b'.inst .proof) (b' := c'.inst .proof)
    · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, EΓ] using RB'
    · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, EΓ] using RC'
    · exact ih hk hΓ hP hp HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' ELF ERG
  | symm HC ih => exact (ih hk hΓ hP hp hg hf EΓ Eg Ef ER EL).symm
  | structFields =>
    have E := congrArg ProofShape.constHead EL
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | app | appCarrier | proj | forallE | forallSorted => cases EL
  | lamCommon | etaBodyL | etaBodyR | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute |
      carrierReduce | carrierNested => cases hk

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
    JointCompare Step (proofEraseCtx Γ) false (b.inst .proof) (c.inst .proof) :=
  inferred_lambdas hstep hsubst hhead H rfl hΓ hP hp hf hg rfl Ef Eg rfl rfl

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
