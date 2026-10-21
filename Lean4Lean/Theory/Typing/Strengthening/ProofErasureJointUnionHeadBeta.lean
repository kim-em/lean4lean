import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointNativeEqRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBinderComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Paired head beta directly in the full joint union

Typed lambda inversion keeps body computations in their original contexts.
Recoverable instantiation then substitutes those paths without unrestricted
primitive substitution or a proposition beta-transport assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_common_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private eta_inst_typed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta
open private lam_inv_aux from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBinderComputation
variable [Params]

/-- Either full-union comparison mode instantiates at an original argument
recovering its assigned domain. The body and recovery may have unrelated finite
stage bounds. Proof arguments need no recovery certificate. -/
theorem proofErase_joint_union_compare_inst_recoverable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (HR : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P))
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx (P :: Γ)) mode
      (proofErase (P :: Γ) a) (proofErase (P :: Γ) b)) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have HX : ∃ stage, ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointStage D stage)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P) := by
    by_cases hn : IsProof Γ p
    · exact ⟨0, fun H => (H hn).elim⟩
    · obtain ⟨stage, HR⟩ := (HR hn).finite_stage erased_joint_stage_mono
      exact ⟨stage, fun _ => HR⟩
  obtain ⟨r, HR⟩ := HX
  obtain ⟨s, H⟩ := H.finite_stage erased_joint_stage_mono
  exact (proofErase_joint_compare_inst_recoverable heq hs hΓ hp HR ha hb H).mono
    (fun H => ⟨r + s, H⟩)

private theorem body_inst_union
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (HR : proofErase Γ p ≠ .proof → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ P))
    (ha : env.HasType univs (P :: Γ) a A) (hb : env.HasType univs (P :: Γ) b A)
    (EΓ : proofEraseCtx (P :: Γ) = Δ) (Ea : proofErase (P :: Γ) a = sa)
    (Eb : proofErase (P :: Γ) b = sb)
    (H : JointCompare (ErasedJointUnion D) Δ mode sa sb) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode
      (sa.inst (proofErase Γ p)) (sb.inst (proofErase Γ p)) := by
  have HC := proofErase_joint_union_compare_inst_recoverable heq hs hΓ hp
    (fun hn => HR (fun E => hn (proofErase_eq_proof.1 E))) ha hb
    (by simpa only [EΓ, Ea, Eb] using H)
  obtain ⟨u, hP⟩ := hp.isType henv hΓ
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, u, hP⟩
  rw [proofErase_instN hΓP hp Ctx.InstN.zero ha,
    proofErase_instN hΓP hp Ctx.InstN.zero hb, Ea, Eb] at HC
  exact HC

private theorem inferred_lambdas_union
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : JointCheck (ErasedJointUnion D) Δ kind sa sb)
    (hk : kind = .compare false)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P)
    (hf : env.HasType univs Γ f (.forallE P B)) (hg : env.HasType univs Γ g (.forallE P B))
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = sa) (Eg : proofErase Γ g = sb)
    (EL : sa = .lam A b) (ER : sb = .lam rawD c)
    (RA : proofErase Γ p ≠ .proof → ScopedTypeRecovery (ErasedJointUnion D) Δ (proofErase Γ p) A)
    (RD : proofErase Γ p ≠ .proof → ScopedTypeRecovery (ErasedJointUnion D) Δ (proofErase Γ p) rawD) :
    JointCompare (ErasedJointUnion D) Δ false (b.inst (proofErase Γ p)) (c.inst (proofErase Γ p)) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointUnion D) := erased_joint_union_descent heq hs
  induction H generalizing Γ P p B f g A b rawD c with
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
    have HC := body_inst_union heq hs hΓ hpA (by simpa only [EΓ, EA] using RA) hb hc
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
    obtain ⟨A', b', ELF, RAA, RB⟩ := lam_inv_aux heq hs RF hΓ hA hb hnF EΓ
      (by rw [EA, Eb, ← EL])
    obtain ⟨D', c', ERG, RDD, RC⟩ := lam_inv_aux heq hs RG hΓ hD hc hnG EΓ
      (by rw [ED, Ec, ← ER])
    have RB' := proofErase_joint_union_compute_inst heq hs hΓ hpA
      (fun hn => by simpa only [EΓ, EA] using RA (fun E => hn (proofErase_eq_proof.1 E))) hb RB
    have RC' := proofErase_joint_union_compute_inst heq hs hΓ hpD
      (fun hn => by simpa only [EΓ, ED] using RD (fun E => hn (proofErase_eq_proof.1 E))) hc RC
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ hg EΓ Eg RG
    apply JointCheck.compute (a' := b'.inst (proofErase Γ p)) (b' := c'.inst (proofErase Γ p))
    · simpa only [EΓ, Eb] using RB'
    · simpa only [EΓ, Ec] using RC'
    · exact ih hk hΓ hp HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' ELF ERG
        (fun hn => (RA hn).convert (by simpa only [EA] using RAA))
        (fun hn => (RD hn).convert (by simpa only [ED] using RDD))
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
theorem proofErase_joint_union_inferred_lambdas_inst_recovered
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (hf : env.HasType univs Γ f (.forallE P B)) (hg : env.HasType univs Γ g (.forallE P B))
    (Ef : proofErase Γ f = .lam A b) (Eg : proofErase Γ g = .lam E c)
    (RA : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) A)
    (RE : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) E)
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false (.lam A b) (.lam E c)) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false
      (b.inst (proofErase Γ p)) (c.inst (proofErase Γ p)) :=
  inferred_lambdas_union heq hs
    H rfl hΓ hp hf hg rfl Ef Eg rfl rfl
    (fun hn => RA (fun hp => hn (proofErase_eq_proof.2 hp)))
    (fun hn => RE (fun hp => hn (proofErase_eq_proof.2 hp)))

/-- Actual proposition-valued applications close under head beta when the two
arguments have the same erasure and that erasure recovers both displayed lambda
domains whenever it is retained. The arguments need not themselves be proofs
or literally the same original term. -/
theorem proofErase_joint_union_proposition_head_beta_recovered
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (Epq : proofErase Γ p = proofErase Γ q)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (RA : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ A))
    (RE : ¬ IsProof Γ p → ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ E))
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hE⟩, C', hc⟩ := hg.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
  have hqE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hq
  have EF : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
    if_neg (not_isProof_function_to_sort hΓ hf)
  have EG : proofErase Γ (.lam E c) = .lam (proofErase Γ E) (proofErase (E :: Γ) c) :=
    if_neg (not_isProof_function_to_sort hΓ hg)
  have HC := proofErase_joint_union_inferred_lambdas_inst_recovered heq hs hΓ hp hf hg EF EG RA RE
    (by simpa only [EF, EG] using H)
  rw [proofErase_instN (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, _, hA⟩) hpA Ctx.InstN.zero hb,
    proofErase_instN (show OnCtx (E :: Γ) (env.IsType univs) from ⟨hΓ, _, hE⟩) hqE Ctx.InstN.zero hc, ← Epq]
  exact JointCompare.common HC

/-- Full-union inferred lambda comparison closes paired proposition head
beta at arbitrary proof arguments. No global union primitive substitution,
certification, or lower-stage proposition beta-transport premise is used. -/
theorem proofErase_joint_union_proposition_head_beta_proofs
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  have Ep := proofErase_eq_proof.2 (show IsProof Γ p from ⟨P, hp, hP⟩)
  have Eq := proofErase_eq_proof.2 (show IsProof Γ q from ⟨P, hq, hP⟩)
  exact proofErase_joint_union_proposition_head_beta_recovered heq hs hΓ hp hq
    (Ep.trans Eq.symm) hf hg (fun hn => (hn ⟨P, hp, hP⟩).elim)
    (fun hn => (hn ⟨P, hp, hP⟩).elim) H

/-- Arguments may differ provided full-union computation takes both to a
typed shared value recovering the two displayed domains. Only the shared
value needs recovery; the paths may contain arbitrary union primitives.
This does not assume beta stability of the resulting comparison. -/
theorem proofErase_joint_union_proposition_head_beta_joined
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (hz : env.HasType univs Γ z P)
    (RP : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ z))
    (RQ : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ q) (proofErase Γ z))
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (RA : ¬ IsProof Γ z → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ z) (proofErase Γ A))
    (RE : ¬ IsProof Γ z → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ z) (proofErase Γ E))
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  have HC := proofErase_joint_union_proposition_head_beta_recovered heq hs hΓ hz hz rfl hf hg RA RE H
  obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hE⟩, C', hc⟩ := hg.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
  have hzA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hz
  have hqE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hq
  have hzE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hz
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓE : OnCtx (E :: Γ) (env.IsType univs) := ⟨hΓ, v, hE⟩
  obtain ⟨r, RP⟩ := RP.finite_stage erased_joint_stage_mono
  obtain ⟨s, RQ⟩ := RQ.finite_stage erased_joint_stage_mono
  have RB := proofErase_joint_compute_inst_argument heq hs hΓA hb hpA RP
  have RC := proofErase_joint_compute_inst_argument heq hs hΓE hc hqE RQ
  rw [← proofErase_instN hΓA hzA Ctx.InstN.zero hb] at RB
  rw [← proofErase_instN hΓE hzE Ctx.InstN.zero hc] at RC
  exact .compute (RB.mono (fun H => ⟨r, H⟩)) (RC.mono (fun H => ⟨s, H⟩)) HC

end Lean4Lean.VEnv.Strengthening
