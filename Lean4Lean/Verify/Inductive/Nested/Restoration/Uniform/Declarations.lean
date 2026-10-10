import Lean4Lean.Verify.Inductive.Nested.Restoration.Uniform.Whnf
import Lean4Lean.Verify.Inductive.Nested.Restoration.ContainerSpecializations

/-! # Discharging the non-`whnf` parameter-uniformity inputs of a nested run
(owner: Restoration-A)

The `NestedRun` part of the source branch's `Nested/Restoration/Uniform/Declarations.lean`
(the generic part is `Uniform/Heads.lean`): name prefixes. Pending on Restoration-B's
`restorationTablesRestoring`: `NestedRun.auxHeadsFacts` (the auxiliary heads are fresh in the
source environment, lie in the reserved `_nested` namespace, and contain every key of
`aux2nested`) and the lowered constructor-type lemmas. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open InductiveSignature

namespace VerifyInductive

open Kernel

private def nameDepth' : Name → Nat
  | .anonymous => 0
  | .str p _ => nameDepth' p + 1
  | .num p _ => nameDepth' p + 1

private theorem NamePrefix.depth_le' {P x : Name} (H : NamePrefix P x) :
    nameDepth' P ≤ nameDepth' x := by
  induction H with
  | refl => exact Nat.le_refl _
  | str _ _ ih => simp only [nameDepth']; omega
  | num _ _ ih => simp only [nameDepth']; omega

theorem NamePrefix.trans {Q A B : Name} (h₁ : NamePrefix Q A) (h₂ : NamePrefix A B) :
    NamePrefix Q B := by
  induction h₂ with
  | refl => exact h₁
  | str s _ ih => exact .str s ih
  | num k _ ih => exact .num k ih

/-- Replacing a prefix `P` of `x` by `A` yields a name with prefix `A`. -/
theorem NamePrefix.replacePrefix_prefix {P x : Name} (H : NamePrefix P x) (A : Name) :
    NamePrefix A (x.replacePrefix P A) := by
  induction H with
  | refl => rw [Name.replacePrefix_self]; exact .refl
  | @str p s H ih =>
    have hne : Name.str p s ≠ P := by
      intro h; have := H.depth_le'; rw [← h] at this; simp [nameDepth'] at this; omega
    simp only [Name.replacePrefix, beq_iff_eq, hne, if_false, Name.mkStr]
    exact .str s ih
  | @num p k H ih =>
    have hne : Name.num p k ≠ P := by
      intro h; have := H.depth_le'; rw [← h] at this; simp [nameDepth'] at this; omega
    simp only [Name.replacePrefix, beq_iff_eq, hne, if_false, Name.mkNum]
    exact .num k ih

theorem NamePrefix.isPrefixOf {P x : Name} (H : NamePrefix P x) : P.isPrefixOf x = true := by
  induction H with
  | refl => cases P <;> simp [Name.isPrefixOf]
  | str s _ ih => simp [Name.isPrefixOf, ih]
  | num k _ ih => simp [Name.isPrefixOf, ih]

theorem namePrefix_of_isPrefixOf {P : Name} :
    ∀ {x : Name}, P.isPrefixOf x = true → NamePrefix P x
  | .anonymous, h => by
    simp only [Name.isPrefixOf, beq_iff_eq] at h
    subst h; exact .refl
  | .str p s, h => by
    simp only [Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact .refl
    · exact .str s (namePrefix_of_isPrefixOf h)
  | .num p k, h => by
    simp only [Name.isPrefixOf, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact .refl
    · exact .num k (namePrefix_of_isPrefixOf h)

/-! ### Run-level facts about the auxiliary heads -/

end VerifyInductive
end Lean4Lean
