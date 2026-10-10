import Lean4Lean.Primitive
import Lean4Lean.Verify.Expr
import Lean4Lean.Verify.Inductive.Lowering

/-!
# The primitive declaration shapes

Primitive declarations are `Bool` and `Nat`, recognized by `Primitive.checkInductive`
(section 3.1 of the design notes). `PrimitiveInductiveShape` is the dispatch predicate: a
successful recognition has exactly the canonical `Bool` or `Nat` syntax
(`checkPrimitiveInductive_eq_true_iff`), so the primitive path is verified for two finite
declarations.

Wave 2 scaffold: owned by the `Install/`+`Primitive/`+`Prelude/` agent (source branch:
`Primitive/{Shape,Lowering}.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The two declaration shapes for which the executable kernel checker enables
the primitive-name exception. This is an operational dispatch predicate, not
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

/-- Successful primitive recognition has exactly the canonical `Bool` or `Nat` syntax. In
particular the `true` branch is finite and can be verified separately from the ordinary
fresh-name pipeline. -/
theorem checkPrimitiveInductive_eq_true_iff
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) :
    Primitive.checkInductive env lparams nparams types isUnsafe = .ok true ↔
      PrimitiveInductiveShape lparams nparams types isUnsafe := by
  -- WAVE 2 STUB (Primitive): the source branch's proof (`Primitive/Shape.lean`), 90 lines of
  -- case analysis on `Primitive.checkInductive`.
  sorry

theorem PrimitiveInductiveShape.types_nonempty
    (H : PrimitiveInductiveShape lparams nparams types isUnsafe) : types ≠ [] := by
  rcases H with ⟨-, -, -, h | ⟨_, _, h⟩⟩ <;> simp [h]

theorem PrimitiveInductiveShape.isUnsafe_eq
    (H : PrimitiveInductiveShape lparams nparams types isUnsafe) : isUnsafe = false := H.2.2.1

/-- The lowering run is the identity on a primitive declaration: no nested occurrence. -/
theorem loweringRun.primitiveNoop (env : Environment) (fuel : Nat) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    (loweringRun env fuel nparams types lparams).WF fun res =>
      res.types = types ∧ res.aux2nested.size = 0 := by
  -- WAVE 2 STUB (Primitive): the source branch's `ElimNestedInductive.run'.primitiveNoopWF`
  -- (`Primitive/Lowering.lean`).
  have := Hshape; sorry

end VerifyInductive
end Lean4Lean
