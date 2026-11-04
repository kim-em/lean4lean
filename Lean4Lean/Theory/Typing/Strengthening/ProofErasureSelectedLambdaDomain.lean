import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentNeutralFunctionCarrierConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentTerminalFunctionCarrierConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRankedTypeFamily

/-! # Written lambda domains related to finite selected domains

The relation records actual domain conversion separately from the lambda's
body recovery path. Guard conversion is proved for each constructor.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A selected raw domain is the written domain itself, a protected neutral
carrier, or a dependent function domain obtained by converting its protected
neutral or terminal-valued input, or a finite dependent family ending in a
universe with terminal inputs or locally bound type parameters. Every branch
has a proved guard-transfer law. -/
inductive SelectedLambdaDomain (cut : Nat) (Γ : List VExpr) : ProofShape → VExpr → Prop where
  | exact : SelectedLambdaDomain cut Γ (proofErase Γ A) A
  /-- A neutral selected carrier supplies ordinary checking regardless of the
  written domain; its guards cannot expose a structural checking rule. -/
  | neutral : AnchoredCarrier cut raw → SelectedLambdaDomain cut Γ raw A
  | dependent : env.IsDefEq univs Γ A B (.sort u) →
      AnchoredCarrier cut (proofErase Γ A) →
      SelectedLambdaDomain cut Γ (proofErase Γ (.forallE A C)) (.forallE B C)
  /-- Whole dependent function guards also transfer when the converted inner
  input domain classifies all its values as terminal images. -/
  | dependentTerminal : env.IsDefEq univs Γ A B (.sort u) →
      TerminalDomain Γ A →
      SelectedLambdaDomain cut Γ (proofErase Γ (.forallE A C)) (.forallE B C)
  /-- An arbitrary selected type converts to a dependent family ending in a
  universe. The target's finite terminal input tree controls guard readout. -/
  | typeFamily : env.IsDefEq univs Γ S B (.sort u) → TerminalTypeFamily Γ B →
      SelectedLambdaDomain cut Γ (proofErase Γ S) B

  /-- Local universe parameters in this target are preserved by outer
  substitution, so specialized generic inputs have a proved guard-transfer law. -/
  | polymorphicFamily : env.IsDefEq univs Γ S B (.sort u) → PolymorphicTypeFamily Γ B →
      SelectedLambdaDomain cut Γ (proofErase Γ S) B

  /-- Every finite level of native higher-order input readout is available.
  The rank bounds the certificate's construction, not the substituted terms. -/
  | rankedFamily : env.IsDefEq univs Γ S B (.sort u) → NativeFamilyFramework.Ranked n Γ B →
      SelectedLambdaDomain cut Γ (proofErase Γ S) B

/-- A single type-valued function is a one-binder instance of the general
terminal-input family target. -/
theorem SelectedLambdaDomain.typeFunction
    (HE : env.IsDefEq univs Γ S (.forallE B (.sort v)) (.sort u))
    (HT : TerminalDomain Γ B) :
    SelectedLambdaDomain cut Γ (proofErase Γ S) (.forallE B (.sort v)) :=
  .typeFamily HE (.function HT .sort)

/-- Typed substitution preserves the selected and written annotations while
keeping protected input heads outside the local binder suffix. -/
theorem SelectedLambdaDomain.subst
    (H : SelectedLambdaDomain cut Γ raw A)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hA : env.HasType univs Γ A (.sort v))
    (WH : PreservesCarrierHeads cut cut' τ) :
    SelectedLambdaDomain cut' Γ₀ (raw.subst τ) (A.subst σ) := by
  cases H with
  | exact =>
    rw [← proofErase_subst_with hΓ₀ W hA ES]
    exact .exact
  | neutral HA => exact .neutral (HA.subst WH)
  | @dependent A B u C HAB HA =>
    obtain ⟨_, _, hC⟩ := hA.forallE_inv henv
    have HC : IsDefEqCtx env univs [] (B :: Γ) (A :: Γ) :=
      .succ (.refl W.wf) HAB.symm
    have hC' := hC.defeqDFC henv HC
    have hAC := HasType.forallE HAB.hasType.1 hC'
    rw [← proofErase_subst_with hΓ₀ W hAC ES]
    apply SelectedLambdaDomain.dependent (by
      simpa only [VExpr.subst] using HAB.subst henv.orderedStrong W hΓ₀)
    simpa only [proofErase_subst_with hΓ₀ W HAB.hasType.1 ES] using HA.subst WH

  | @dependentTerminal A B u C HAB HA =>
    obtain ⟨_, _, hC⟩ := hA.forallE_inv henv
    have HC : IsDefEqCtx env univs [] (B :: Γ) (A :: Γ) :=
      .succ (.refl W.wf) HAB.symm
    have hC' := hC.defeqDFC henv HC
    have hAC := HasType.forallE HAB.hasType.1 hC'
    rw [← proofErase_subst_with hΓ₀ W hAC ES]
    apply SelectedLambdaDomain.dependentTerminal (by
      simpa only [VExpr.subst] using HAB.subst henv.orderedStrong W hΓ₀)
    exact HA.subst hΓ₀ W HAB.hasType.1

  | typeFamily HE HT =>
    rw [← proofErase_subst_with hΓ₀ W HE.hasType.1 ES]
    exact .typeFamily (HE.subst henv.orderedStrong W hΓ₀) (HT.subst hΓ₀ W HE.hasType.2)

  | polymorphicFamily HE HT =>
    rw [← proofErase_subst_with hΓ₀ W HE.hasType.1 ES]
    exact .polymorphicFamily (HE.subst henv.orderedStrong W hΓ₀) (HT.subst hΓ₀ W HE.hasType.2)

  | rankedFamily HE HT =>
    rw [← proofErase_subst_with hΓ₀ W HE.hasType.1 ES]
    exact .rankedFamily (HE.subst henv.orderedStrong W hΓ₀)
      (NativeFamilyFramework.ranked_subst HT hΓ₀ W HE.hasType.2)

/-- A guard at the selected domain transfers to the actual written lambda
domain. Only finite supplied guards and actual endpoint typings are used. -/
theorem SelectedLambdaDomain.guard
    (hs : D.Sound env univs) (H : SelectedLambdaDomain cut Γ raw A)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HX : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ) raw
      (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ x) (proofErase Γ y) := by
  cases H with
  | exact => exact HX
  | neutral HA =>
    exact .carrierChecked (HX.checked_of_no_exposure (HA.inert (erased_joint_stage_head 0)))
  | @dependent A B u C HAB HA =>
    obtain ⟨_, hBC⟩ := hx.isType henv hΓ
    obtain ⟨_, _, hC⟩ := hBC.forallE_inv henv
    have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, _, HAB.hasType.2⟩
    have HC : IsDefEqCtx env univs [] (B :: Γ) (A :: Γ) :=
      .succ (.refl hΓ) HAB.symm
    have hC' := hC.defeqDFC henv HC
    have HPi := IsDefEq.forallEDF HAB hC'
    have hx' := HPi.symm.defeq hx
    have hy' := HPi.symm.defeq hy
    have HA₀ : AnchoredCarrier 0 (proofErase Γ A) := by
      obtain ⟨i, args, _, EE⟩ := HA
      exact ⟨i, args, by omega, EE⟩
    have HX' := proofErase_computed_joint_dependent_neutral_function_carrier_convert hs hΓ HAB HA₀ hx' hy'
      (by simpa only [show proofErase Γ (.forallE A C) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ HPi.hasType.1)] using HX)
    rw [show proofErase Γ (.forallE B C) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hBC),
      proofErase_defeqCtx hΓB HC hC]
    exact HX'

  | @dependentTerminal A B u C HAB HA =>
    obtain ⟨_, hBC⟩ := hx.isType henv hΓ
    obtain ⟨_, _, hC⟩ := hBC.forallE_inv henv
    have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, _, HAB.hasType.2⟩
    have HC : IsDefEqCtx env univs [] (B :: Γ) (A :: Γ) :=
      .succ (.refl hΓ) HAB.symm
    have hC' := hC.defeqDFC henv HC
    have HPi := IsDefEq.forallEDF HAB hC'
    have hx' := HPi.symm.defeq hx
    have hy' := HPi.symm.defeq hy
    have HX' := proofErase_computed_joint_dependent_terminal_function_carrier_convert hs hΓ HAB HA hx' hy'
      (by simpa only [show proofErase Γ (.forallE A C) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ HPi.hasType.1)] using HX)
    rw [show proofErase Γ (.forallE B C) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hBC),
      proofErase_defeqCtx hΓB HC hC]
    exact HX'

  | typeFamily HE HT =>
    exact HT.carrier_convert hs hΓ (HE.symm.defeq hx) (HE.symm.defeq hy) HE.toU HX

  | polymorphicFamily HE HT =>
    exact HT.carrier_convert hs hΓ (HE.symm.defeq hx) (HE.symm.defeq hy) HE.toU HX

  | rankedFamily HE HT =>
    exact NativeFamilyFramework.ranked_carrier_convert HT hs hΓ
      (HE.symm.defeq hx) (HE.symm.defeq hy) HE.toU HX

end Lean4Lean.VEnv.Strengthening
