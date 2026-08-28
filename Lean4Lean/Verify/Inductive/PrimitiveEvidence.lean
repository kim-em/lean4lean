import Lean4Lean.Verify.Inductive.Primitive
import Lean4Lean.Verify.Inductive.Constructor.LiteralDisjoint

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Literal expansion never mentions the `Bool` family header.  This is the
literal-side positivity premise needed by the finite primitive `Bool` branch. -/
theorem primitiveBoolLiteralDisjoint :
    checkPositivityStep.LiteralDisjoint #[.const ``Bool []] := by
  exact (checkPositivityStep.IndConstArray.ofExact (names := [``Bool])
    rfl).literalDisjoint (by
      simp [checkPositivityStep.LiteralConstructorNamesDisjoint,
        checkPositivityStep.literalConstructorNames])

/-- Literal expansion uses `Nat.zero` and `Nat.succ`, not the `Nat` family
header itself.  Consequently the primitive `Nat` declaration also satisfies
the literal-side positivity premise. -/
theorem primitiveNatLiteralDisjoint :
    checkPositivityStep.LiteralDisjoint #[.const ``Nat []] := by
  exact (checkPositivityStep.IndConstArray.ofExact (names := [``Nat])
    rfl).literalDisjoint (by
      simp [checkPositivityStep.LiteralConstructorNamesDisjoint,
        checkPositivityStep.literalConstructorNames])

/-- Header translation preserves the ordered concrete family names. -/
theorem _root_.Lean4Lean.TrInductDeclHeaders.typeNames
    (H : TrInductDeclHeaders env lparams nparams types isUnsafe decl
      envTypes) :
    decl.types.map (·.name) = types.map (·.name) := by
  have go : ∀ {sources targets},
      List.Forall₂ (TrInductiveTypeHeaders env envTypes lparams)
          sources targets →
        targets.map (·.name) = sources.map (·.name) := by
    intro sources targets htypes
    induction htypes with
    | nil => rfl
    | cons h _ ih => simp [h.header.name, ih]
  exact go H.types

/-- Once the primitive dispatch shape has been materialized, its concrete
inductive-constant array satisfies literal disjointness automatically. -/
theorem PrimitiveInductiveShape.materializedLiteralDisjoint
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe)
    (Hdecl : TrInductDeclHeaders env lparams nparams types isUnsafe decl
      envTypes)
    (Hmaterialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
      env lparams Delta stats decl depth) :
    checkPositivityStep.LiteralDisjoint stats.indConsts := by
  rcases Hshape with ⟨rfl, rfl, rfl, htypes | htypes⟩
  · have hconsts :
        (decl.types.map fun type => Expr.const type.name stats.levels).toArray =
          (types.map fun type => Expr.const type.name stats.levels).toArray := by
      simpa [List.map_map, Function.comp_def] using congrArg
        (fun names =>
          (names.map fun name => Expr.const name stats.levels).toArray)
        Hdecl.typeNames
    rw [Hmaterialized.consts, hconsts, Hmaterialized.levelParams, htypes]
    exact primitiveBoolLiteralDisjoint
  · rcases htypes with ⟨binderName, binderInfo, htypes⟩
    have hconsts :
        (decl.types.map fun type => Expr.const type.name stats.levels).toArray =
          (types.map fun type => Expr.const type.name stats.levels).toArray := by
      simpa [List.map_map, Function.comp_def] using congrArg
        (fun names =>
          (names.map fun name => Expr.const name stats.levels).toArray)
        Hdecl.typeNames
    rw [Hmaterialized.consts, hconsts, Hmaterialized.levelParams, htypes]
    exact primitiveNatLiteralDisjoint

/-- The generated recursor names are not themselves primitive-reserved, even
on the finite `Bool`/`Nat` bootstrap branch. -/
theorem PrimitiveInductiveShape.recursorsNonprimitive
    (Hshape : PrimitiveInductiveShape lparams nparams types isUnsafe) :
    ∀ owner (_howner : owner < types.toArray.size),
      ¬ Kernel.Environment.primitives.contains
        (Lean.mkRecName types.toArray[owner]!.name) := by
  rcases Hshape with ⟨rfl, rfl, rfl, htypes | htypes⟩
  · subst types
    intro owner howner
    have : owner = 0 := by simpa using howner
    subst owner
    simp
    native_decide
  · rcases htypes with ⟨binderName, binderInfo, htypes⟩
    subst types
    intro owner howner
    have : owner = 0 := by simpa using howner
    subst owner
    simp
    native_decide

end VerifyInductive
end Lean4Lean
