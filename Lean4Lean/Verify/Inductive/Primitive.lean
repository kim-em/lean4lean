import Lean4Lean.Primitive
import Lean4Lean.Verify.Expr

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The two declaration shapes for which the executable kernel checker enables
the primitive-name exception.  This is an operational dispatch predicate, not
the abstract inductive well-formedness specification. -/
def PrimitiveInductiveShape (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) : Prop :=
  lparams = [] ∧ nparams = 0 ∧ isUnsafe = false ∧
    (types = [{
        name := ``Bool
        type := .sort (.succ .zero)
        ctors := [
          { name := ``Bool.false, type := .const ``Bool [] },
          { name := ``Bool.true, type := .const ``Bool [] }] }] ∨
      ∃ binderName binderInfo,
        types = [{
          name := ``Nat
          type := .sort (.succ .zero)
          ctors := [
            { name := ``Nat.zero, type := .const ``Nat [] },
            { name := ``Nat.succ,
              type := .forallE binderName (.const ``Nat [])
                (.const ``Nat []) binderInfo }] }])

/-- Successful primitive recognition has exactly the canonical `Bool` or
`Nat` syntax.  In particular the `true` branch is finite and can be verified
separately from the ordinary fresh-name pipeline. -/
theorem checkPrimitiveInductive_eq_true_iff
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) :
    Primitive.checkInductive env lparams nparams types isUnsafe =
        .ok true ↔
      PrimitiveInductiveShape lparams nparams types isUnsafe := by
  unfold Primitive.checkInductive PrimitiveInductiveShape
  constructor
  · intro h
    split at h
    · rename_i hpre
      have hpre' : (!isUnsafe && lparams.isEmpty && nparams == 0) = true :=
        hpre
      simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hpre'
      obtain ⟨⟨hisUnsafe, hlparams⟩, hnparams⟩ := hpre'
      have hisUnsafe' : isUnsafe = false := by
        cases isUnsafe <;> simp_all
      subst isUnsafe
      subst lparams
      subst nparams
      cases types with
      | nil =>
        simp only at h
        cases h
      | cons type tail =>
        cases tail with
        | cons other rest =>
          simp only at h
          cases h
        | nil =>
          simp only at h
          by_cases htype : (type.type == .sort (.succ .zero)) = true
          · rw [if_pos htype] at h
            by_cases hbool : type.name = ``Bool
            · simp only [hbool] at h
              split at h
              · rename_i _ hctors
                refine ⟨rfl, rfl, rfl, Or.inl ?_⟩
                congr 1
                have htypeEq : type.type = .sort (.succ .zero) :=
                  Expr.eqv_sort.mp htype
                cases type
                simp_all
              · change Except.error _ = Except.ok true at h
                cases h
            · by_cases hnat : type.name = ``Nat
              · simp only [hnat] at h
                split at h
                · rename_i _ binderName binderInfo hctors
                  refine ⟨rfl, rfl, rfl, Or.inr
                    ⟨binderName, binderInfo, ?_⟩⟩
                  congr 1
                  have htypeEq : type.type = .sort (.succ .zero) :=
                    Expr.eqv_sort.mp htype
                  cases type
                  simp_all
                · change Except.error _ = Except.ok true at h
                  cases h
              · simp only at h
                change Except.ok false = Except.ok true at h
                cases h
          · rw [if_neg htype] at h
            change Except.ok false = Except.ok true at h
            cases h
    · change Except.ok false = Except.ok true at h
      cases h
  · rintro ⟨rfl, rfl, rfl, hshape⟩
    rcases hshape with hbool | ⟨binderName, binderInfo, hnat⟩
    · subst types
      simp
      change Except.ok true = Except.ok true
      rfl
    · subst types
      simp
      change Except.ok true = Except.ok true
      rfl

/-- Every successful primitive precheck is either the ordinary path or one of
the two canonical bootstrap declarations. -/
theorem checkPrimitiveInductive_result
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (hresult : Primitive.checkInductive env lparams nparams types
      isUnsafe = .ok allowPrimitive) :
    allowPrimitive = false ∨
      PrimitiveInductiveShape lparams nparams types isUnsafe := by
  cases allowPrimitive with
  | false => exact Or.inl rfl
  | true =>
    exact Or.inr ((checkPrimitiveInductive_eq_true_iff env lparams nparams
      types isUnsafe).mp hresult)

end VerifyInductive
end Lean4Lean
