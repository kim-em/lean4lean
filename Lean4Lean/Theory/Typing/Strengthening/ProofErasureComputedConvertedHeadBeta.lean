import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedLambdaComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Paired head beta through converted recoverable annotations

The inferred-lambda induction carries each argument certificate through its
own computed annotation. Native recovery at the written domain is unnecessary;
the recovered type may change along the computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_common_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport
open private eta_inst_typed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta
variable [Params]

namespace ProofShape
/-- Either joint comparison mode may be used in common mode. Carrier and
inferred-function subchecks retain their own checking modes. -/
theorem ComputedJointCompare.common (H : ComputedJointCompare Step Δ mode a b) : ComputedJointCompare Step Δ true a b := by
  change ComputedJointCheck Step Δ (.compare mode) a b at H
  generalize hk : JointCheckKind.compare mode = kind at H
  induction H generalizing mode with
  | leaf H => exact .leaf H.common
  | app HF HX => exact .app HF HX
  | appCarrier R HF HX => exact .appCarrier R HF HX
  | appComputed R HF HX => exact .appComputed R HF HX
  | proj H => exact .proj H
  | lam HA HB ihA ihB => cases hk; exact .lam HA (ihB rfl)
  | forallE HA HB => exact .forallE HA HB
  | lamSorted S S' HA HB ihA ihB => cases hk; exact .lamSorted S S' HA (ihB rfl)
  | forallSorted S S' HA T T' HB => exact .forallSorted S S' HA T T' HB
  | lamCommon H => exact .lamCommon H
  | etaBodyL S H => exact .etaBodyL S H
  | etaBodyR S H => exact .etaBodyR S H
  | structFields hi hx hp hf hadm H => exact .structFields hi hx hp hf hadm H
  | etaLams HD Hη => exact .etaLams HD Hη
  | compute RA RB H ih => exact .compute RA RB (ih hk)
  | symm H ih => exact .symm (ih hk)
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

end ProofShape

private theorem inferred_lambdas_converted
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : ComputedJointCheck (ErasedComputedJointUnion D) Δ kind sa sb)
    (hk : kind = .compare false)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P)
    (hf : env.HasType univs Γ f (.forallE P B)) (hg : env.HasType univs Γ g (.forallE P B))
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = sa) (Eg : proofErase Γ g = sb)
    (EL : sa = .lam A b) (ER : sb = .lam rawD c)
    (RA : NeutralRecoveringImage D Γ p A)
    (RD : NeutralRecoveringImage D Γ p rawD) :
    ComputedJointCompare (ErasedComputedJointUnion D) Δ false (b.inst (proofErase Γ p)) (c.inst (proofErase Γ p)) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedComputedJointUnion D) := erased_computed_joint_union_descent heq hs
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
    have HC := (EA.symm ▸ RA).compare_inst heq hs hΓ hpA hb hc
      (by simpa only [proofEraseCtx, EΓ, EA, Eb, Ec] using HB)
    simpa only [EΓ, Eb, Ec] using HC
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
    obtain ⟨A', b', ELF, RA', RB⟩ := proofErase_computed_union_lam_compute_inst_converted
      heq hs RF hΓ hA hb hnF hpA (EA.symm ▸ RA) EΓ (by rw [EA, Eb, ← EL])
    obtain ⟨D', c', ERG, RD', RC⟩ := proofErase_computed_union_lam_compute_inst_converted
      heq hs RG hΓ hD hc hnG hpD (ED.symm ▸ RD) EΓ (by rw [ED, Ec, ← ER])
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ hg EΓ Eg RG
    apply ComputedJointCheck.compute (a' := b'.inst (proofErase Γ p)) (b' := c'.inst (proofErase Γ p))
    · simpa only [Eb] using RB
    · simpa only [Ec] using RC
    · exact ih hk hΓ hp HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' ELF ERG RA' RD'
  | symm HC ih => exact (ih hk hΓ hp hg hf EΓ Eg Ef ER EL RD RA).symm
  | structFields =>
    have E := congrArg ProofShape.constHead EL
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | app | appCarrier | appComputed | proj | forallE | forallSorted => cases EL
  | lamCommon | etaBodyL | etaBodyR | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute |
      carrierReduce | carrierNested => cases hk

/-- Inferred lambda comparison contracts diagonally at an argument with a
converted recoverable type for each displayed annotation. Both image
certificates persist through arbitrary computed-union annotation paths. -/
theorem proofErase_computed_union_inferred_lambdas_inst_converted
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p P)
    (hf : env.HasType univs Γ f (.forallE P B)) (hg : env.HasType univs Γ g (.forallE P B))
    (Ef : proofErase Γ f = .lam A b) (Eg : proofErase Γ g = .lam E c)
    (RA : NeutralRecoveringImage D Γ p A) (RE : NeutralRecoveringImage D Γ p E)
    (H : ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) false (.lam A b) (.lam E c)) :
    ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) false
      (b.inst (proofErase Γ p)) (c.inst (proofErase Γ p)) :=
  inferred_lambdas_converted heq hs H rfl hΓ hp hf hg rfl Ef Eg rfl rfl RA RE

/-- Actual proposition-valued applications close under head beta when the two
arguments have the same erasure and the retained image has converted recovery for both
displayed annotations. The arguments need not themselves be proofs
or literally the same original term. -/
theorem proofErase_computed_union_proposition_head_beta_converted
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (Epq : proofErase Γ p = proofErase Γ q)
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (RA : NeutralRecoveringImage D Γ p (proofErase Γ A))
    (RE : NeutralRecoveringImage D Γ p (proofErase Γ E))
    (H : ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) true (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hE⟩, C', hc⟩ := hg.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
  have hqE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hq
  have EF : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
    if_neg (not_isProof_function_to_sort hΓ hf)
  have EG : proofErase Γ (.lam E c) = .lam (proofErase Γ E) (proofErase (E :: Γ) c) :=
    if_neg (not_isProof_function_to_sort hΓ hg)
  have HC := proofErase_computed_union_inferred_lambdas_inst_converted heq hs hΓ hp hf hg EF EG RA RE
    (by simpa only [EF, EG] using H)
  rw [proofErase_instN (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, _, hA⟩) hpA Ctx.InstN.zero hb,
    proofErase_instN (show OnCtx (E :: Γ) (env.IsType univs) from ⟨hΓ, _, hE⟩) hqE Ctx.InstN.zero hc, ← Epq]
  exact ComputedJointCompare.common HC

/-- Computing an argument through every occurrence in a typed body works
in the computed union, with no recovery premise on either the argument or its output. -/
theorem proofErase_computed_union_compute_inst_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ) (proofErase Γ x) out) :
    ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) ((proofErase (A :: Γ) b).inst out) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have H := proofErase_compute_subst_images_of_renaming (erased_computed_joint_union_rename heq hs)
    hΓA.1 W hb (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one out) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H


/-- Arguments may differ provided full-union computation takes both to a
typed shared value with converted recovery for both displayed domains. Only
the shared value needs the image certificate; the paths may contain arbitrary union primitives.
This does not assume beta stability of the resulting comparison. -/
theorem proofErase_computed_union_proposition_head_beta_joined_converted
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p P) (hq : env.HasType univs Γ q P)
    (hz : env.HasType univs Γ z P)
    (RP : ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) (proofErase Γ z))
    (RQ : ScopedCompute (ErasedComputedJointUnion D) (proofEraseCtx Γ) (proofErase Γ q) (proofErase Γ z))
    (hf : env.HasType univs Γ (.lam A b) (.forallE P (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE P (.sort .zero)))
    (RA : NeutralRecoveringImage D Γ z (proofErase Γ A))
    (RE : NeutralRecoveringImage D Γ z (proofErase Γ E))
    (H : ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    ComputedJointCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) true
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  have HC := proofErase_computed_union_proposition_head_beta_converted heq hs hΓ hz hz rfl hf hg RA RE H
  obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨v, hE⟩, C', hc⟩ := hg.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
  have hzA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hz
  have hqE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hq
  have hzE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hz
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓE : OnCtx (E :: Γ) (env.IsType univs) := ⟨hΓ, v, hE⟩
  have RB := proofErase_computed_union_compute_inst_argument heq hs hΓA hb hpA RP
  have RC := proofErase_computed_union_compute_inst_argument heq hs hΓE hc hqE RQ
  rw [← proofErase_instN hΓA hzA Ctx.InstN.zero hb] at RB
  rw [← proofErase_instN hΓE hzE Ctx.InstN.zero hc] at RC
  exact .compute RB RC HC

end Lean4Lean.VEnv.Strengthening
