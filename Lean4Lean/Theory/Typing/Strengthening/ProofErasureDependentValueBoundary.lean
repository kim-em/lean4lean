import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentValueFamily

/-! # Generic value results lie outside every old finite family level

The polymorphic identity carrier returns its bound type parameter. It is an
inhabited dependent type and has a new level-one certificate, whereas every old
Ranked certificate ends syntactically in a universe. The exclusion is uniform
in the old level, not just a comparison with level zero.
-/
namespace Lean4Lean.VEnv.Strengthening.NativeFamilyFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape

/-- Ignore all Pi inputs and check whether the final codomain is a sort. -/
def SortResult : VExpr → Prop
  | .sort _ => True
  | .forallE _ B => SortResult B
  | _ => False

variable [Params]

/-- Locally parameterized inputs in the old grammar never changed its final
universe result requirement. -/
theorem parameterized_sortResult (H : ParameterizedTypeFamily Γ ps T) : SortResult T := by
  induction H with
  | sort => trivial
  | function _ _ ih | callable _ _ ih | forallUniverse _ _ ih | parameter _ _ ih => exact ih

/-- No finite number of old native-input extensions admits a non-sort result. -/
theorem ranked_sortResult (H : Ranked n Γ T) : SortResult T := by
  cases n with
  | zero => exact parameterized_sortResult H
  | succ n =>
    change Extension (Ranked n) Γ T at H
    induction H with
    | base HT => exact parameterized_sortResult HT
    | native _ _ ih => exact ih

namespace DependentValueBoundary

/-- The carrier of polymorphic identity: ∀ X : Type, X → X. -/
def identityType : VExpr := .forallE (.sort (.succ .zero)) (.forallE (.bvar 0) (.bvar 1))
/-- Its canonical inhabitant. -/
def identity : VExpr := .lam (.sort (.succ .zero)) (.lam (.bvar 0) (.bvar 0))

/-- The dependent carrier is actually well typed. -/
theorem identityType_typed : env.HasType univs Γ identityType
    (.sort (.imax (.succ (.succ .zero)) (.imax (.succ .zero) (.succ .zero)))) :=
  .forallE (HasType.sort (by trivial)) (.forallE (.bvar .zero) (.bvar (.succ .zero)))

/-- The boundary concerns an inhabited type, not an impossible context. -/
theorem identity_typed : env.HasType univs Γ identity identityType :=
  .lam (HasType.sort (by trivial)) (.lam (.bvar .zero) (.bvar .zero))

/-- A local parameter is retained through its value binder and used as result. -/
theorem identity_family : ValueRanked 1 Γ identityType :=
  .forallUniverse (by trivial)
    (.parameter (u := .zero) (by simp)
      (.result (u := .zero) (by simp [shiftTypeParameters])))

/-- The new result case is outside every old finite native-input level. -/
theorem identity_boundary : ValueRanked 1 Γ identityType ∧ ∀ n, ¬ Ranked n Γ identityType :=
  ⟨identity_family, fun _ H => ranked_sortResult H⟩

/-- Whole-carrier readout now applies to the generic-value-returning identity
type from any ordinarily equal source, not just syntactically matching Pis. -/
theorem identity_carrier_convert
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f A) (hg : env.HasType univs Γ g A)
    (HE : env.IsDefEqU univs Γ A identityType)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ f) (proofErase Γ g)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx Γ)
      (proofErase Γ identityType) (proofErase Γ f) (proofErase Γ g) :=
  valueRanked_carrier_convert identity_family hs hΓ hf hg HE H

/-- Native functions accepting polymorphic identity values can now be target
binders of the full recursive checker transport. -/
theorem consumer_carrier_context
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A (.forallE identityType (.sort .zero)) (.sort u))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (ErasedJointStage D 0) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (ErasedJointStage D 0)
      (proofEraseCtx (.forallE identityType (.sort .zero) :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  letI := valueRanked_inputLaws D 1
  exact carrier_context hs hΓ HAB (Tree.function identity_family .sort) ha hb H

end DependentValueBoundary
end Lean4Lean.VEnv.Strengthening.NativeFamilyFramework
