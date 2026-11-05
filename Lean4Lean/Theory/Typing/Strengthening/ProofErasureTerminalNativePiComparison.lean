import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalPiInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativePiDomainComparison
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTerminalLambdaTrace

/-! # Native body-type comparisons at a converted terminal reference binder

Written and selected Pi domains may differ independently. Native body recovery
stays in each original scope; their selected types compare at the fixed terminal
reference binder. This distinction avoids assuming exact native context transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Compared native Pi outputs of independently annotated actual lambdas
supply a comparison of their exact selected body types at a terminal reference
binder. Common assigned Pi typing supplies ordinary domain alignment; no
written-annotation check or computation between annotations is assumed.
Native body recoveries remain in their respective original scopes. -/
theorem stage_zero_terminal_native_lambda_codomains_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ C (.sort u)) (HC : TerminalDomain Γ C)
    (hf : env.HasType univs Γ (.lam A a) (.forallE C T))
    (hg : env.HasType univs Γ (.lam A₂ b) (.forallE C T))
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam A a)) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam A₂ b)) (.forallE Z W))
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.forallE X Y) (.forallE Z W)) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) a) Y ∧
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (A₂ :: Γ))
      (proofErase (A₂ :: Γ) b) W ∧
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx (C :: Γ)) false Y W := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  have hnf : ¬ IsProof Γ (.lam A a) := fun H => RF.ne_proof (proofErase_eq_proof.2 H)
  have hng : ¬ IsProof Γ (.lam A₂ b) := fun H => RG.ne_proof (proofErase_eq_proof.2 H)
  obtain ⟨HCA, haC⟩ := lambda_body_at_reference_pi hΓ hC hf
  obtain ⟨HCD, hbC⟩ := lambda_body_at_reference_pi hΓ hC hg
  have ha := haC.defeqDFC henv (IsDefEqCtx.succ .zero HCA)
  have hb := hbC.defeqDFC henv (IsDefEqCtx.succ .zero HCD)
  rw [show proofErase Γ (.lam A a) = .lam _ _ from if_neg hnf] at RF
  rw [show proofErase Γ (.lam A₂ b) = .lam _ _ from if_neg hng] at RG
  obtain ⟨RX, Ra⟩ := stage_zero_lambda_native_parts heq hs hΓ HCA.hasType.2 ha RF
  obtain ⟨RZ, Rb⟩ := stage_zero_lambda_native_parts heq hs hΓ HCD.hasType.2 hb RG
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HCA.hasType.2⟩
  have hΓD : OnCtx (A₂ :: Γ) (env.IsType univs) := ⟨hΓ, u, HCD.hasType.2⟩
  obtain ⟨P, haP, EP⟩ := proofErase_scoped_typeRecovery_replay hstep hΓA ha Ra
  obtain ⟨Q, hbQ, EQ⟩ := proofErase_scoped_typeRecovery_replay hstep hΓD hb Rb
  obtain ⟨v, hP⟩ := haP.isType henv hΓA
  obtain ⟨z, hQ⟩ := hbQ.isType henv hΓD
  refine ⟨Ra, Rb, ?_⟩
  have RP : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) P)) (.forallE X Y) := by
    rw [EP]
    exact .forallE RX .refl
  have RQ : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A₂) (proofErase (A₂ :: Γ) Q)) (.forallE Z W) := by
    rw [EQ]
    exact .forallE RZ .refl
  have EP' : proofErase (C :: Γ) P = Y :=
    (proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HCA.symm) hP).symm.trans EP
  have EQ' : proofErase (C :: Γ) Q = W :=
    (proofErase_defeqCtx hΓD (IsDefEqCtx.succ .zero HCD.symm) hQ).symm.trans EQ
  simpa only [EP', EQ'] using
    stage_zero_terminal_computed_pi_codomains_compare heq hs hΓ HC HCA HCD hP hQ RP RQ HT

/-- Compared native Pi outputs of two functions at a common actual Pi yield
comparison of their exact instantiated result types at any shared argument
when the assigned domain is terminal-valued. The functions need not be literal
lambdas. Selected domains may differ, and no result-type check is assumed. -/
theorem stage_zero_terminal_native_application_types_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ C (.sort u)) (HC : TerminalDomain Γ C)
    (hf : env.HasType univs Γ f (.forallE C T))
    (hg : env.HasType univs Γ g (.forallE C T))
    (hp : env.HasType univs Γ p C)
    (RF : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE X Y))
    (RG : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ g) (.forallE Z W))
    (HT : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) mode
      (.forallE X Y) (.forallE Z W)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ) false
      (Y.inst (proofErase Γ p)) (W.inst (proofErase Γ p)) := by
  have hstep : ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D 0) :=
    erased_static_structure_eta_expansion_stage_descent heq hs 0
  obtain ⟨P, hfP, EP⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf RF
  obtain ⟨Q, hgQ, EQ⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hg RG
  obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv EP
  obtain ⟨A₂, E, rfl, _, ED, EE⟩ := erase_forallE_inv EQ
  obtain ⟨⟨v, hA⟩, w, hB⟩ := (hfP.isType henv hΓ).forallE_inv henv
  obtain ⟨⟨z, hD⟩, r, hE⟩ := (hgQ.isType henv hΓ).forallE_inv henv
  obtain ⟨⟨_, HCA⟩, _⟩ := (hf.uniqU henv hΓ hfP).forallE_inv henv hΓ
  obtain ⟨⟨_, HCD⟩, _⟩ := (hg.uniqU henv hΓ hgQ).forallE_inv henv hΓ
  have HCA := HCA.toU.of_l henv hΓ hC
  have HCD := HCD.toU.of_l henv hΓ hC
  have hpA := HCA.defeq hp
  have hpD := HCD.defeq hp
  have R := stage_zero_terminal_pi_inst_compare heq hs hΓ (HC.convert hΓ HCA)
    hA hB hD hE hpA (by simpa only [EP, EQ] using HT)
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, v, hA⟩
  have hΓD : OnCtx (A₂ :: Γ) (env.IsType univs) := ⟨hΓ, z, hD⟩
  rw [proofErase_instN hΓA hpA Ctx.InstN.zero hB,
    proofErase_instN hΓD hpD Ctx.InstN.zero hE, EB, EE] at R
  exact R

end Lean4Lean.VEnv.Strengthening
