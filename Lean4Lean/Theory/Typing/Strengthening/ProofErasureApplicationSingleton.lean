import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSingletonComparison

/-! # Recovered application checking for every singleton family guard

The generic prefix machinery now accepts ApplicationCompare for the entire
transported/requested family comparison, including nested index expressions.
The source realization restriction is retained for future typed substitution;
no substitution or completeness law is asserted here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- The previous comparator satisfies the generic family descent interface. -/
theorem erased_scoped_family_descent (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedFamilyDescent (fun Δ => ProofShape.ScopedCompare Step Δ true) := by
  intro Γ Γ' n k P Q hΓ hΓ' W hP hQ HC
  exact ((proofErase_scoped_compare_descend hstep hΓ hΓ' W rfl hP hQ HC).1
    (.refl ⟨_, HasType.sort (by trivial : VLevel.zero.WF univs)⟩)).of_l henv hΓ hP

/-- Recursive recovered applications descend inside arbitrary family guards,
not only when they are endpoints of the specialized Eq prefix rule. -/
theorem erased_application_family_descent (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedFamilyDescent (fun Δ => ProofShape.ApplicationCompare Step Δ true) := by
  intro Γ Γ' n k P Q hΓ hΓ' W hP hQ HC
  exact ((proofErase_application_compare_descend hstep hΓ hΓ' W rfl hP hQ HC).1
    (.refl ⟨_, HasType.sort (by trivial : VLevel.zero.WF univs)⟩)).of_l henv hΓ hP

namespace ProofShape
/-- Pointwise inclusion of family comparisons preserves the fixed code/output. -/
theorem SingletonPrimitiveWith.mono
    (hcmp : ∀ {Δ a b}, Cmp Δ a b → Cmp' Δ a b)
    (H : SingletonPrimitiveWith Cmp Δ a b) : SingletonPrimitiveWith Cmp' Δ a b := by
  cases H with
  | intro V ha hcalc HG => exact .intro V ha hcalc (hcmp HG)

/-- Every raw singleton prefix still has a constant-headed source. -/
theorem SingletonPrimitiveWith.head (H : SingletonPrimitiveWith Cmp Δ a b) : PrimitiveHead a := by
  cases H
  have aux : ∀ (args : List ProofShape) (f : ProofShape), PrimitiveHead f → PrimitiveHead (mkApps f args) := by
    intro args
    induction args with
    | nil => exact fun _ H => H
    | cons a args ih => exact fun f H => ih (.app f a) H
  exact aux _ _ trivial

/-- General singleton prefixes whose family guards recursively recover
application domains. The exact generated program is the original one. -/
def ApplicationSingletonPrimitive
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (e out : ProofShape) : Prop :=
  TypedSource Δ e ∧ SingletonPrimitiveWith (fun Δ => ApplicationCompare Step Δ true) Δ e out

/-- Enlarging computation enlarges every recursive family comparison. -/
theorem ApplicationSingletonPrimitive.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : ApplicationSingletonPrimitive Step Δ e out) : ApplicationSingletonPrimitive Step' Δ e out :=
  ⟨H.1, H.2.mono (fun H => H.mono hstep)⟩

/-- Every earlier typed singleton primitive embeds with the same program and
source realization, because old family comparisons embed recursively. -/
theorem ScopedTypedSingletonPrimitive.application
    (H : ScopedTypedSingletonPrimitive Step Δ e out) : ApplicationSingletonPrimitive Step Δ e out := by
  refine ⟨H.1, ?_⟩
  cases H.2 with
  | intro V ha hcalc HG => exact .intro V ha hcalc (ScopedCompare.application HG)
end ProofShape

/-- General recovered-application singleton prefixes descend below every block. -/
theorem erased_application_singleton_descent (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (ProofShape.ApplicationSingletonPrimitive Step) :=
  fun hΓ hΓ' W ht H => erased_singleton_with_descent heq
    (erased_application_family_descent hstep) hΓ hΓ' W ht H.2

/-- The richer family guard still replays the actual registered singleton
prefix, with the literal generated output including its residual telescope. -/
theorem erased_application_singleton_replay (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrefixReplay D (ProofShape.ApplicationSingletonPrimitive Step) :=
  fun hΓ ht H => erased_singleton_with_replay heq
    (erased_application_family_descent hstep) hΓ ht H.2

end Lean4Lean.VEnv.Strengthening
