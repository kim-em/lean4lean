import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpecializedDomainContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionCarrierConversion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpecializationBoundary

/-! # Dependent type-family carrier conversion with generic parameters

Finite target families may use terminal domains or domains whose generic value
admits a sort specialization. The latter uses a shared test through each whole
recursive context conversion. This covers the polymorphic predicate family
excluded by TerminalTypeFamily. No arbitrary substitution closure is asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private convert_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeFunctionCarrierConversion
variable [Params]

/-- Finite function targets ending in a universe, with independently certified
input domains. Specializable inputs retain their test during binder conversion;
the complete grammar is not claimed stable under arbitrary substitution. -/
inductive SpecializedTypeFamily : List VExpr → VExpr → Prop where
  | sort : SpecializedTypeFamily Γ (.sort u)
  | function : (TerminalDomain Γ A ∨ SortSpecialization (A :: Γ) (.bvar 0)) →
      SpecializedTypeFamily (A :: Γ) B → SpecializedTypeFamily Γ (.forallE A B)

/-- Every earlier terminal-input target is included in the new grammar. -/
theorem TerminalTypeFamily.specialized (H : TerminalTypeFamily Γ T) :
    SpecializedTypeFamily Γ T := by
  induction H with
  | sort => exact .sort
  | function HA _ ih => exact .function (.inl HA) ih

/-- Arbitrary actual source carriers equal to a certified target family admit
complete carrier readout. Every context transport and recursive codomain step
is proved; there is no assumed comparison, recovery, or transport obligation. -/
theorem SpecializedTypeFamily.carrier_convert (HT : SpecializedTypeFamily Γ T)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ T) (proofErase Γ f) (proofErase Γ g) := by
  induction HT generalizing f g A with
  | sort => exact TerminalTypeFamily.sort.carrier_convert hs hΓ hf hg HE H
  | @function Γ T K HA _ ih =>
    have transport : ComputedCarrierBinderTransport D Γ T := by
      intro A u f g C hΓ HAB hf hg H
      rcases HA with HA | HA
      · exact proofErase_computed_joint_zero_carrier_terminal_context hs hΓ HAB
          (HA.convert hΓ HAB.symm) hf hg H
      · exact proofErase_computed_joint_zero_carrier_specialized_context hs hΓ HAB HA hf hg H
    exact convert_raw hs transport (fun hΓ hf hg HE H => ih hΓ hf hg HE H)
      hΓ H hf hg HE rfl rfl rfl rfl

/-- The generic predicate family now has an explicit certificate, although its
inner input was proved outside the earlier terminal-domain grammar. -/
theorem specializedTypeFamily_polymorphic_predicate
    (hΓ : OnCtx Γ (env.IsType univs)) :
    SpecializedTypeFamily Γ
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort .zero))) :=
  .function (.inl .sort) (.function (.inr (sortSpecialization_generic_value hΓ).1) .sort)

/-- The new coverage is strict on an actual well-typed polymorphic family. -/
theorem specializedTypeFamily_strict_extension
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ T u, env.HasType univs Γ T (.sort u) ∧ SpecializedTypeFamily Γ T ∧
      ¬ TerminalTypeFamily Γ T :=
  ⟨_, _, polymorphic_predicate_type_typed, specializedTypeFamily_polymorphic_predicate hΓ,
    terminalTypeFamily_polymorphic_predicate_failure hΓ⟩

/-- Any finite computed guard at an actual carrier equal to ∀ X : Type, X → Prop
reads at that target, even when the source annotations are only ordinarily equal
and their raw erasures differ. -/
theorem proofErase_computed_joint_polymorphic_predicate_carrier_convert
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A
      (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort .zero))))
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.sort .zero))))
      (proofErase Γ f) (proofErase Γ g) :=
  (specializedTypeFamily_polymorphic_predicate hΓ).carrier_convert hs hΓ hf hg HE H

end Lean4Lean.VEnv.Strengthening
