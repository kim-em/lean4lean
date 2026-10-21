import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUniverseStage
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnionHeadBeta

/-! # Paired head beta through converted universe domains

An argument recovers the literal universe only. Each displayed lambda domain
is converted to that universe before its body comparison or computation is
instantiated. No recovery of either displayed domain is required.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private lambda_common_context from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
open private eta_inst_typed from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveredHeadBeta
open private lam_inv_aux from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointBinderComputation
variable [Params]

private theorem universe_oracles
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.sort v) (.sort u)) :
    ∀ i, UniverseResultChange (contextOracle (proofEraseCtx (A :: Γ)) i)
      (contextOracle (proofEraseCtx (.sort v :: Γ)) i) := by
  intro i
  cases i with
  | zero =>
    change UniverseResultChange ((proofErase Γ A).liftN 1) ((proofErase Γ (.sort v)).liftN 1)
    rw [show proofErase Γ (.sort v) = .sort v from if_neg (not_isProof_of_sort hΓ HE.hasType.2)]
    exact .toSort
  | succ i => exact .refl

private theorem displayed_universe
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam A b) (.forallE (.sort v) B))
    (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b C) :
    env.IsDefEq univs Γ A (.sort v) (.sort u) := by
  obtain ⟨⟨_, HD⟩, _, _⟩ := (hf.uniqU henv hΓ (HasType.lam hA hb)).forallE_inv henv hΓ
  exact (show env.IsDefEqU univs Γ (.sort v) A from ⟨_, HD⟩).symm.of_l henv hΓ hA

/-- A body comparison under a converted universe binder instantiates at an
argument recovering the literal universe. Exact recovery of the original
annotation is not needed, even when the body retains its bound variable. -/
theorem proofErase_joint_union_compare_inst_universe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.sort v) (.sort u))
    (hp : env.HasType univs Γ p (.sort v))
    (HR : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) (.sort v))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have W : IsDefEqCtx env univs [] (A :: Γ) (.sort v :: Γ) := .succ (.refl hΓ) HE
  have HC := (proofErase_joint_union_universe_binder heq hs hΓ HE ha hb).1 H
  exact proofErase_joint_union_compare_inst_recoverable heq hs hΓ hp
    (fun _ => by simpa only [(show proofErase Γ (.sort v) = .sort v from
      if_neg (not_isProof_of_sort hΓ HE.hasType.2))] using HR)
    (ha.defeqDFC henv W) (hb.defeqDFC henv W) HC

private theorem body_inst_universe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.sort v) (.sort u))
    (hp : env.HasType univs Γ p (.sort v))
    (HR : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) (.sort v))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (EΓ : proofEraseCtx (A :: Γ) = Δ) (Ea : proofErase (A :: Γ) a = sa)
    (Eb : proofErase (A :: Γ) b = sb)
    (H : JointCompare (ErasedJointUnion D) Δ mode sa sb) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode
      (sa.inst (proofErase Γ p)) (sb.inst (proofErase Γ p)) := by
  have HC := proofErase_joint_union_compare_inst_universe heq hs hΓ HE hp HR ha hb
    (by simpa only [EΓ, Ea, Eb] using H)
  have hpA := HE.symm.defeq hp
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.1⟩
  rw [proofErase_instN hΓA hpA Ctx.InstN.zero ha,
    proofErase_instN hΓA hpA Ctx.InstN.zero hb, Ea, Eb] at HC
  exact HC

private theorem compute_inst_universe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HE : env.IsDefEq univs Γ A (.sort v) (.sort u))
    (hp : env.HasType univs Γ p (.sort v))
    (HR : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) (.sort v))
    (ha : env.HasType univs (A :: Γ) a T)
    (R : ScopedCompute (ErasedJointUnion D) (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) a) out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ)
      ((proofErase (A :: Γ) a).inst (proofErase Γ p)) (out.inst (proofErase Γ p)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HE.hasType.1⟩
  have W : IsDefEqCtx env univs [] (A :: Γ) (.sort v :: Γ) := .succ (.refl hΓ) HE
  have R' := proofErase_joint_union_universe_compute heq hs hΓA W (universe_oracles hΓ HE) ha R
  have RC := proofErase_joint_union_compute_inst heq hs hΓ hp
    (fun _ => by simpa only [(show proofErase Γ (.sort v) = .sort v from
      if_neg (not_isProof_of_sort hΓ HE.hasType.2))] using HR) (ha.defeqDFC henv W) R'
  rwa [← proofErase_defeqCtx hΓA W ha] at RC

private theorem inferred_lambdas_universe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : JointCheck (ErasedJointUnion D) Δ kind sa sb)
    (hk : kind = .compare false)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.sort level))
    (hf : env.HasType univs Γ f (.forallE (.sort level) B)) (hg : env.HasType univs Γ g (.forallE (.sort level) B))
    (EΓ : proofEraseCtx Γ = Δ) (Ef : proofErase Γ f = sa) (Eg : proofErase Γ g = sb)
    (EL : sa = .lam A b) (ER : sb = .lam rawD c)
    (HR : ScopedTypeRecovery (ErasedJointUnion D) Δ (proofErase Γ p) (.sort level)) :
    JointCompare (ErasedJointUnion D) Δ false (b.inst (proofErase Γ p)) (c.inst (proofErase Γ p)) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedJointUnion D) := erased_joint_union_descent heq hs
  induction H generalizing Γ p B f g A b rawD c with
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
    rw [Ectx] at Ec
    have HA := displayed_universe hΓ hf hA hb
    have HC := body_inst_universe heq hs hΓ HA hp (by simpa only [EΓ] using HR) hb hc
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
    obtain ⟨A', b', ELF, RAA, RB⟩ := lam_inv_aux heq hs RF hΓ hA hb hnF EΓ
      (by rw [EA, Eb, ← EL])
    obtain ⟨D', c', ERG, RDD, RC⟩ := lam_inv_aux heq hs RG hΓ hD hc hnG EΓ
      (by rw [ED, Ec, ← ER])
    have RB' := compute_inst_universe heq hs hΓ (displayed_universe hΓ hf hA hb) hp
      (by simpa only [EΓ] using HR) hb RB
    have RC' := compute_inst_universe heq hs hΓ (displayed_universe hΓ hg hD hc) hp
      (by simpa only [EΓ] using HR) hc RC
    obtain ⟨f', HF, Ef'⟩ := proofErase_scoped_compute_realize hstep hΓ hf EΓ Ef RF
    obtain ⟨g', HG, Eg'⟩ := proofErase_scoped_compute_realize hstep hΓ hg EΓ Eg RG
    apply JointCheck.compute (a' := b'.inst (proofErase Γ p)) (b' := c'.inst (proofErase Γ p))
    · simpa only [EΓ, Eb] using RB'
    · simpa only [EΓ, Ec] using RC'
    · exact ih hk hΓ hp HF.hasType.2 HG.hasType.2 EΓ Ef' Eg' ELF ERG
        HR
  | symm HC ih => exact (ih hk hΓ hp hg hf EΓ Eg Ef ER EL HR).symm
  | structFields =>
    have E := congrArg ProofShape.constHead EL
    simp only [ProofShape.constHead_mkApps, ProofShape.constHead] at E
    cases E
  | app | appCarrier | proj | forallE | forallSorted => cases EL
  | lamCommon | etaBodyL | etaBodyR | carrierIntro | carrierChecked |
      carrierSubsingleton | carrierFunction | carrierSymm | carrierCompute |
      carrierReduce | carrierNested => cases hk

/-- Inferred lambda comparison survives diagonal head beta at a recovered
universe-valued argument. The displayed domains may be arbitrary converted
types, with no computation to a sort and no recovery at those annotations. -/
theorem proofErase_joint_union_inferred_lambdas_inst_universe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hp : env.HasType univs Γ p (.sort v))
    (hf : env.HasType univs Γ f (.forallE (.sort v) B))
    (hg : env.HasType univs Γ g (.forallE (.sort v) B))
    (Ef : proofErase Γ f = .lam A b) (Eg : proofErase Γ g = .lam E c)
    (HR : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) (.sort v))
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false (.lam A b) (.lam E c)) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false
      (b.inst (proofErase Γ p)) (c.inst (proofErase Γ p)) :=
  inferred_lambdas_universe heq hs H rfl hΓ hp hf hg rfl Ef Eg rfl rfl HR

/-- Paired proposition head beta for arguments with the same erasure and
recovery at their common universe. Only that universe must be recovered;
neither displayed lambda annotation needs an exact recovery certificate. -/
theorem proofErase_joint_union_proposition_head_beta_universe
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ p (.sort v)) (hq : env.HasType univs Γ q (.sort v))
    (Epq : proofErase Γ p = proofErase Γ q)
    (hf : env.HasType univs Γ (.lam A b) (.forallE (.sort v) (.sort .zero)))
    (hg : env.HasType univs Γ (.lam E c) (.forallE (.sort v) (.sort .zero)))
    (HR : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ p) (.sort v))
    (H : JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam E c))) :
    JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) true (proofErase Γ (b.inst p)) (proofErase Γ (c.inst q)) := by
  obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
  obtain ⟨⟨w, hE⟩, C', hc⟩ := hg.lam_inv henv hΓ
  have hpA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hp
  have hqE := argument_at_displayed_domain hΓ hg (HasType.lam hE hc) hq
  have EF : proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b) :=
    if_neg (not_isProof_function_to_sort hΓ hf)
  have EG : proofErase Γ (.lam E c) = .lam (proofErase Γ E) (proofErase (E :: Γ) c) :=
    if_neg (not_isProof_function_to_sort hΓ hg)
  have HC := proofErase_joint_union_inferred_lambdas_inst_universe heq hs hΓ hp hf hg EF EG HR
    (by simpa only [EF, EG] using H)
  rw [proofErase_instN (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, _, hA⟩) hpA Ctx.InstN.zero hb,
    proofErase_instN (show OnCtx (E :: Γ) (env.IsType univs) from ⟨hΓ, _, hE⟩) hqE Ctx.InstN.zero hc, ← Epq]
  exact JointCompare.common HC

end Lean4Lean.VEnv.Strengthening
