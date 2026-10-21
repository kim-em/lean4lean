import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertifiedChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointLoopReadout

/-! # Head beta at a diagonally supplied, exactly recovered argument

A non-proof argument must recover both displayed lambda domains. Computation
extends these certificates along the domain paths; symmetry swaps them. This
is a constructive diagonal case, not arbitrary paired carrier substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_common_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private beta_inst_image from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropBeta
variable [Params]

private theorem body_inst_recovered
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P))
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (EΓ : proofEraseCtx (P :: Γ) = Δ) (Ea : proofErase (P :: Γ) a = sa)
    (Eb : proofErase (P :: Γ) b = sb) (H : JointCompare Step Δ mode sa sb) :
    JointCompare Step (proofEraseCtx Γ) mode (sa.inst (proofErase Γ p)) (sb.inst (proofErase Γ p)) := by
  obtain ⟨u, hP⟩ := hp.isType henv hΓ
  have H' := H.subst_recovering hstep (fun H W => hsubst H W.interpretation) (fun H => H)
    (fun _ _ _ W H => .base (hsubst H W.interpretation))
    (show OnCtx (P :: Γ) (env.IsType univs) from ⟨hΓ, _, hP⟩) ha hb EΓ Ea Eb
    (by simpa only [EΓ] using RecoveringSubstitution.inst hΓ hp HR)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H'

private theorem eta_inst_typed
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (he : env.HasType univs Γ e (.forallE P B)) (hf : env.HasType univs Γ f (.forallE P B))
    (H : EtaHead (proofErase Γ e) (proofErase Γ f))
    (Ee : proofErase Γ e = .lam rawA rawB) (Ef : proofErase Γ f = .lam rawD rawC) :
    ProofShape.BetaRed (rawB.inst (proofErase Γ p)) (rawC.inst (proofErase Γ p)) := by
  obtain ⟨A, body, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
  obtain ⟨⟨u, hA⟩, C, hb⟩ := he.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ he (HasType.lam hA hb) hp
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have Hraw : EtaHead (.lam rawA rawB) (.lam rawD rawC) := by rwa [Ee, Ef] at H
  cases Hraw with
  | boundVar =>
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id,
      ProofShape.Subst.cons, ProofShape.Subst.id_lift] using
      (ProofShape.BetaRed.beta (A := rawD) (b := rawC) (a := proofErase Γ p))
  | proof =>
    obtain ⟨g, a, rfl, hnb, Eg, Ha⟩ := erase_app_inv Eb
    have hfPi : env.HasType univs Γ f (.forallE A C) :=
      hf.defeqU_r henv hΓ (he.uniqU henv hΓ (HasType.lam hA hb))
    have hfw := hfPi.weak henv (B := A)
    have Egf : proofErase (A :: Γ) g = proofErase (A :: Γ) f.lift := by
      rw [proofErase_liftN hΓ hΓA Ctx.LiftN.one hfPi, Ef]
      exact Eg
    obtain ⟨_, _, hg, ha⟩ := HasType.app_inv henv hΓA hb
    obtain ⟨_, HC⟩ := (proofErase_reflect hΓA hg hfw Egf).2 (not_isProof_fn hΓA hg ha hnb)
    have Hgf := (HC.defeq hΓA).of_l henv hΓA hg
    obtain ⟨⟨_, hCA⟩, _⟩ := (Hgf.hasType.2.uniqU henv hΓA hfw).forallE_inv henv hΓA
    have haA := hCA.defeq ha
    have hi : env.HasType univs Γ (a.inst p) A := by
      simpa only [VExpr.inst_lift] using haA.instN henv Ctx.InstN.zero hpA
    obtain ⟨Q, haQ, hQ⟩ := proofErase_eq_proof.1 Ha
    have hiQ := haQ.instN henv Ctx.InstN.zero hpA
    have hQi := hQ.instN henv Ctx.InstN.zero hpA
    have hpQ := hpA.defeqU_r henv hΓ (hi.uniqU henv hΓ hiQ)
    have Ep : proofErase Γ p = .proof := proofErase_eq_proof.2 ⟨Q.inst p, hpQ, hQi⟩
    rw [Ep]
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id,
      ProofShape.Subst.cons, ProofShape.Subst.id_lift] using
      (ProofShape.BetaRed.beta (A := rawD) (b := rawC) (a := .proof))

-- The structural argument is shared by exact recovery and semantic head
-- exposure. The image predicate records precisely what body instantiation needs.
private theorem inferred_lambdas_with_image
    (Image : List ProofShape → ProofShape → ProofShape → Prop)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (himage : ∀ {Δ p A A'}, Image Δ p A → ScopedCompute Step Δ A A' → Image Δ p A')
    (hbody : ∀ {Γ p P a b A Δ sa sb mode},
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ p P →
      Image (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P) →
      env.HasType univs (P :: Γ) a A → env.HasType univs (P :: Γ) b A →
      proofEraseCtx (P :: Γ) = Δ → proofErase (P :: Γ) a = sa →
      proofErase (P :: Γ) b = sb → JointCompare Step Δ mode sa sb →
      JointCompare Step (proofEraseCtx Γ) mode
        (sa.inst (proofErase Γ p)) (sb.inst (proofErase Γ p)))
    (H : JointCheck Step Δ kind sa sb)
    (hk : kind = .compare false)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P)
    (hf : env.HasType univs Γ f (.forallE P B)) (hg : env.HasType univs Γ g (.forallE P B))
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = sa) (Eg : proofErase Γ g = sb)
    (EL : sa = .lam A b) (ER : sb = .lam D c)
    (RA : Image Δ (proofErase Γ p) A)
    (RD : Image Δ (proofErase Γ p) D) :
    JointCompare Step Δ false (b.inst (proofErase Γ p)) (c.inst (proofErase Γ p)) := by
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
    have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
    rw [Ectx] at Ec
    have HC := hbody hΓ hpA (by simpa only [EΓ, EA] using RA) hb hc
      (by simp only [proofEraseCtx, EΓ, EA]) Eb Ec HB
    simpa only [EΓ] using HC
  | etaLams HD Heta ihD =>
    cases hk
    cases EL
    cases ER
    rcases Heta with Heta | Heta
    · have HR := eta_inst_typed hΓ hp hf hg (by simpa only [Ef, Eg] using Heta) Ef Eg
      exact .compute (.beta HR) .refl (.leaf .refl)
    · have HR := eta_inst_typed hΓ hp hg hf (by simpa only [Ef, Eg] using Heta) Eg Ef
      exact .compute .refl (.beta HR) (.leaf .refl)
  | compute RF RG HC ih =>
    obtain ⟨A₀, b₀, rfl, hnF, EA, Eb⟩ := erase_lam_inv (Ef.trans EL)
    obtain ⟨D₀, c₀, rfl, hnG, ED, Ec⟩ := erase_lam_inv (Eg.trans ER)
    obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
    obtain ⟨⟨v, hD⟩, C', hc⟩ := hg.lam_inv henv hΓ
    have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
    have hpD := argument_at_displayed_domain hΓ hg (HasType.lam hD hc) hp
    obtain ⟨A', b', ELF, RAA, RB⟩ := ScopedCompute.lam_inv_typed hstep hsubst hhead hΓ hA EΓ (body := b)
      (by simpa only [EL, EA] using RF)
    obtain ⟨D', c', ERG, RDD, RC⟩ := ScopedCompute.lam_inv_typed hstep hsubst hhead hΓ hD EΓ (body := c)
      (by simpa only [ER, ED] using RG)
    have WB : ContextSubstitution (proofEraseCtx (A₀ :: Γ)) (proofEraseCtx Γ)
        (ProofShape.Subst.one (proofErase Γ p)) :=
      ContextSubstitution.of_typed hΓ
        (Ctx.InstN.zero.substEq (show OnCtx (A₀ :: Γ) (env.IsType univs) from ⟨hΓ, _, hA⟩) hpA)
        (erasedSubstAgreement_one ⟨hΓ, _, hA⟩ hpA)
    have WC : ContextSubstitution (proofEraseCtx (D₀ :: Γ)) (proofEraseCtx Γ)
        (ProofShape.Subst.one (proofErase Γ p)) :=
      ContextSubstitution.of_typed hΓ
        (Ctx.InstN.zero.substEq (show OnCtx (D₀ :: Γ) (env.IsType univs) from ⟨hΓ, _, hD⟩) hpD)
        (erasedSubstAgreement_one ⟨hΓ, _, hD⟩ hpD)
    simp only [proofEraseCtx, EΓ] at WB WC
    have RB' := RB.subst hsubst WB
    have RC' := RC.subst hsubst WC
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ hg EΓ Eg RG
    apply JointCheck.compute (a' := b'.inst (proofErase Γ p)) (b' := c'.inst (proofErase Γ p))
    · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, EΓ] using RB'
    · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, EΓ] using RC'
    · exact ih hk hΓ hp HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' ELF ERG
        (himage RA (by simpa only [EA] using RAA))
        (himage RD (by simpa only [ED] using RDD))
  | symm HC ih => exact (ih hk hΓ hp hg hf EΓ Eg Ef ER EL RD RA).symm
  | structFields =>
    have E := congrArg ProofShape.constHead EL
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | app | appCarrier | proj | forallE | forallSorted => cases EL
  | lamCommon | etaBodyL | etaBodyR | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute |
      carrierReduce | carrierNested => cases hk


/-- Diagonal head beta for inferred lambdas at an arbitrary typed argument.
Non-proof arguments must recover both displayed domains exactly. Computation
extends these certificates along its domain paths, and symmetry swaps them;
no recovery at arbitrary convertible annotations is assumed. -/
theorem proofErase_joint_inferred_lambdas_inst_recovered
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (hf : env.HasType univs Γ f (.forallE P B)) (hg : env.HasType univs Γ g (.forallE P B))
    (Ef : proofErase Γ f = .lam A b) (Eg : proofErase Γ g = .lam E c)
    (RA : ¬ IsProof Γ p → ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ p) A)
    (RE : ¬ IsProof Γ p → ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ p) E)
    (H : JointCompare Step (proofEraseCtx Γ) false (.lam A b) (.lam E c)) :
    JointCompare Step (proofEraseCtx Γ) false
      (b.inst (proofErase Γ p)) (c.inst (proofErase Γ p)) :=
  inferred_lambdas_with_image
    (fun Δ p A => p ≠ .proof → ScopedTypeRecovery Step Δ p A)
    hstep hsubst hhead (fun HR R hn => (HR hn).convert R)
    (fun hΓ hp HR ha hb EΓ Ea Eb H => body_inst_recovered hstep hsubst hΓ hp
      (fun hn => HR (fun E => hn (proofErase_eq_proof.1 E))) ha hb EΓ Ea Eb H)
    H rfl hΓ hp hf hg rfl Ef Eg rfl rfl
    (fun hn => RA (fun hp => hn (proofErase_eq_proof.2 hp)))
    (fun hn => RE (fun hp => hn (proofErase_eq_proof.2 hp)))

/-- Actual proposition-valued applications close under head beta when the two
arguments have the same erasure and that erasure recovers both displayed lambda
domains whenever it is retained. The arguments need not themselves be proofs
or literally the same original term. -/
theorem proofErase_joint_proposition_head_beta_recovered
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (Epq : proofErase Γ p = proofErase Γ q)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (RA : ¬ IsProof Γ p → ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (RE : ¬ IsProof Γ p → ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ E))
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
  have HC := proofErase_joint_inferred_lambdas_inst_recovered hstep hsubst hhead hΓ hp hf hg EF EG RA RE
    (by simpa only [EF, EG] using H)
  rw [proofErase_instN (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, _, hA⟩) hpA Ctx.InstN.zero hb,
    proofErase_instN (show OnCtx (E :: Γ) (env.IsType univs) from ⟨hΓ, _, hE⟩) hqE Ctx.InstN.zero hc, ← Epq]
  exact JointCompare.common HC

/-- The recovered-argument head-beta theorem stays inside certified checking,
without an endpoint-beta premise. Exact domain recovery is required only for
the supplied argument, not as an environment-wide coverage principle. -/
theorem proofErase_certified_proposition_head_beta_recovered
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (Epq : proofErase Γ p = proofErase Γ q)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (RA : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedBetaStableJoint D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (RE : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedBetaStableJoint D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ E))
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_joint_proposition_head_beta_recovered (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) erased_beta_stable_joint_head hΓ hp hq Epq hf hg RA RE H

/-- Finite source functions can enter the recovered-argument critical pair
using only lower-stage beta transport to certify their comparison. Argument
recoveries are supplied in the certified target, at the original annotations. -/
theorem proofErase_joint_stage_proposition_head_beta_recovered
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (Epq : proofErase Γ p = proofErase Γ q)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (RA : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedBetaStableJoint D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (RE : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedBetaStableJoint D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ E))
    (H : JointCompare (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_certified_proposition_head_beta_recovered heq hs hΓ hp hq Epq hf hg RA RE
    (proofErase_joint_compare_certify_of_lower_beta heq hs hregistry Hbeta hΓ hf hg H)

/-- Distinct argument erasures are permitted when both beta-reduce to a typed
image recovered at the two displayed domains. The body comparison is built at
that shared image, then both exact image-beta paths are prefixed. The recovery
premise belongs to the shared image, not to its possibly unrecoverable sources. -/
theorem proofErase_joint_proposition_head_beta_joined
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ))
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P) (hz : env.HasType univs Γ z P)
    (RP : ProofShape.BetaRed (proofErase Γ p) (proofErase Γ z))
    (RQ : ProofShape.BetaRed (proofErase Γ q) (proofErase Γ z))
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (RA : ¬ IsProof Γ z → ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ z) (proofErase Γ A))
    (RE : ¬ IsProof Γ z → ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ z) (proofErase Γ E))
    (H : JointCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare Step (proofEraseCtx Γ) true (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  have HC := proofErase_joint_proposition_head_beta_recovered hstep hsubst hhead hΓ hz hz rfl hf hg RA RE H
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

/-- The joined non-proof argument case produces a certified proposition
comparison with no global endpoint-beta assumption. The explicit shared-image
recovery and literal beta joins distinguish this from arbitrary carrier-paired
instantiation, which remains unproved. -/
theorem proofErase_certified_proposition_head_beta_joined
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P) (hz : env.HasType univs Γ z P)
    (RP : ProofShape.BetaRed (proofErase Γ p) (proofErase Γ z))
    (RQ : ProofShape.BetaRed (proofErase Γ q) (proofErase Γ z))
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (RA : ¬ IsProof Γ z → ScopedTypeRecovery (ErasedBetaStableJoint D)
      (proofEraseCtx Γ) (proofErase Γ z) (proofErase Γ A))
    (RE : ¬ IsProof Γ z → ScopedTypeRecovery (ErasedBetaStableJoint D)
      (proofEraseCtx Γ) (proofErase Γ z) (proofErase Γ E))
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) :=
  proofErase_joint_proposition_head_beta_joined (erased_beta_stable_joint_descent heq hs)
    (erased_beta_stable_joint_subst heq hs) erased_beta_stable_joint_head hΓ hp hq hz RP RQ hf hg RA RE H

end Lean4Lean.VEnv.Strengthening
