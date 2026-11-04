import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFiniteHigherOrderFamily

/-! # A typed target beyond the previous polymorphic grammar

The new target accepts a function that itself accepts a type-valued function.
Its input's generic value is neither terminal nor callable by the earlier
literal-universe-input tree. Level one nevertheless proves full carrier readout.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeFamilyFramework.RankedFamilyBoundary
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A function from Type to Prop. -/
def low : VExpr := .forallE (.sort (.succ .zero)) (.sort .zero)
/-- A function consuming low. -/
def middle : VExpr := .forallE low (.sort .zero)
/-- A function consuming middle, outside the old input grammar. -/
def high : VExpr := .forallE middle (.sort .zero)

private theorem low_typed : env.HasType univs Γ low
    (.sort (.imax (.succ (.succ .zero)) (.succ .zero))) :=
  .forallE (HasType.sort (by trivial)) (HasType.sort (by trivial))

private theorem middle_typed : env.HasType univs Γ middle
    (.sort (.imax (.imax (.succ (.succ .zero)) (.succ .zero)) (.succ .zero))) :=
  .forallE low_typed (HasType.sort (by trivial))

/-- The boundary target is an actual type in every well-formed ambient context. -/
theorem high_typed : env.HasType univs Γ high
    (.sort (.imax (.imax (.imax (.succ (.succ .zero)) (.succ .zero)) (.succ .zero)) (.succ .zero))) :=
  .forallE middle_typed (HasType.sort (by trivial))

/-- The old callable predicate cannot describe the middle input: its generic
function accepts a Pi type, while every callable function exposes a sort input. -/
theorem middle_not_callable (hΓ : OnCtx Γ (env.IsType univs)) : ¬ CallableDomain Γ middle := by
  intro H
  have hΓM : OnCtx (middle :: Γ) (env.IsType univs) := ⟨hΓ, _, middle_typed⟩
  have hf : env.HasType univs (middle :: Γ) (.bvar 0) (.forallE low (.sort .zero)) := .bvar .zero
  obtain ⟨u, C, hf', _⟩ := (show TypeInputImage (middle :: Γ) (.bvar 0) from H).function hΓM hf
  obtain ⟨⟨_, HC⟩, _, _⟩ := (hf'.uniqU henv hΓM hf).forallE_inv henv hΓM
  exact HC.toU.sort_forallE_inv henv hΓM

/-- Level one includes a well-typed target excluded by the complete previous
polymorphic grammar, including its callable and local-parameter constructors. -/
theorem strict_extension (hΓ : OnCtx Γ (env.IsType univs)) :
    Ranked 1 Γ high ∧ ¬ PolymorphicTypeFamily Γ high := by
  constructor
  · exact Extension.native (.function (.function .sort .sort) .sort) (.base .sort)
  · intro H
    change ParameterizedTypeFamily Γ [] (.forallE middle (.sort .zero)) at H
    cases H with
    | function HM _ =>
      have hΓM : OnCtx (middle :: Γ) (env.IsType univs) := ⟨hΓ, _, middle_typed⟩
      have hf : env.HasType univs (middle :: Γ) (.bvar 0) (.forallE low (.sort .zero)) := .bvar .zero
      exact HM.not_function hΓM hf
    | callable HM _ => exact middle_not_callable hΓ HM

/-- An arbitrary supplied whole-carrier guard transfers to the new target,
even if its actual source carrier has unrelated erased head syntax. -/
theorem carrier_convert (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A high)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ high) (proofErase Γ f) (proofErase Γ g) :=
  ranked_carrier_convert (strict_extension hΓ).1 hs hΓ hf hg HE H

end Lean4Lean.VEnv.Strengthening.NativeFamilyFramework.RankedFamilyBoundary
