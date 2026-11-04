import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSpecializationBoundary
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredUnitImages

/-! # Generic values at an expanded carrier retain ordinary separation

The actual source carrier is a beta-expanded reference to a generic type
parameter. Despite its non-neutral head, a whole computed guard cannot identify
the two generic values, even in the union of all computed stages.
-/
namespace Lean4Lean.VEnv.Strengthening.SpecializationExample
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Two generic values above their arbitrary Type parameter. -/
def context (Γ : List VExpr) : List VExpr := .bvar 1 :: .bvar 0 :: .sort (.succ .zero) :: Γ
/-- The selected carrier beta-expands the parameter at index two. -/
def carrier : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 3)) (.sort .zero)

private theorem context_wf (hΓ : OnCtx Γ (env.IsType univs)) :
    OnCtx (context Γ) (env.IsType univs) :=
  ⟨⟨⟨hΓ, _, HasType.sort (by trivial)⟩, _, HasType.bvar .zero⟩,
    _, HasType.bvar (.succ .zero)⟩

/-- Actual beta equality aligns the expanded source with the type parameter. -/
theorem carrier_equal : env.IsDefEq univs (context Γ) carrier (.bvar 2) (.sort (.succ .zero)) :=
  IsDefEq.beta (HasType.bvar (.succ (.succ (.succ .zero)))) (HasType.sort (by trivial))

/-- The two endpoints really inhabit the expanded source carrier. -/
theorem endpoints_typed : env.HasType univs (context Γ) (.bvar 0) carrier ∧
    env.HasType univs (context Γ) (.bvar 1) carrier :=
  ⟨carrier_equal.symm.defeq (HasType.bvar .zero),
    carrier_equal.symm.defeq (HasType.bvar (.succ .zero))⟩

private theorem specialized (hΓ : OnCtx Γ (env.IsType univs)) :
    SortSpecialization (context Γ) (.bvar 0) ∧ SortSpecialization (context Γ) (.bvar 1) := by
  have W : Ctx.InstN Γ (.sort .zero) (.sort (.succ .zero)) 2 (context Γ)
      (.sort .zero :: .sort .zero :: Γ) := .succ (.succ .zero)
  exact ⟨SortSpecialization.type_parameter W (context_wf hΓ) (by trivial) (HasType.bvar .zero),
    SortSpecialization.type_parameter W (context_wf hΓ) (by trivial) (HasType.bvar (.succ .zero))⟩

/-- This selected carrier has an application head and so is not syntactically
anchored neutral. Generic value specialization nevertheless rules out the full
guard, rather than assuming source neutrality or a selected computation path. -/
theorem expanded_carrier_separation (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    (∃ f a, proofErase (context Γ) carrier = .app f a) ∧
    ¬ ComputedJointCarrierGuard (ErasedComputedJointUnion D) (proofEraseCtx (context Γ))
      (proofErase (context Γ) carrier)
      (proofErase (context Γ) (.bvar 0)) (proofErase (context Γ) (.bvar 1)) := by
  constructor
  · exact ⟨_, _, if_neg (not_isProof_of_sort (context_wf hΓ) carrier_equal.hasType.1)⟩
  · intro H
    have HC := proofErase_computed_carrier_specialization_checked
      (erased_computed_joint_union_descent heq hs) (context_wf hΓ)
      endpoints_typed.1 endpoints_typed.2 (.inl (specialized hΓ).1) H
    have E₀ : proofErase (context Γ) (.bvar 0) = .bvar 0 := if_neg (specialized hΓ).1.not_isProof
    have E₁ : proofErase (context Γ) (.bvar 1) = .bvar 1 := if_neg (specialized hΓ).2.not_isProof
    rw [E₀, E₁] at HC
    have E := HC.bvar_injective erased_computed_joint_union_head
    cases E

end Lean4Lean.VEnv.Strengthening.SpecializationExample
