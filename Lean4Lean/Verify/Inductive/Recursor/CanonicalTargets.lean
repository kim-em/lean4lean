import Lean4Lean.Verify.Inductive.Recursor.Generation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The executable recursor checker supplies typing for a separately chosen
canonical translation. Translation agreement is typed equality, which also
covers the different parameter terms admitted by projection desugaring. -/
theorem RecursorTypeTranslations.typeOfTranslation
    (H : RecursorTypeTranslations env lparams elimLevel c stats indTypes recInfos)
    (henv : env.WF) (owner : Nat) (howner : owner < indTypes.size)
    (Hcanonical : TrExprS env (AddInductive.getRecLevelParams elimLevel lparams) []
      (AddInductive.declareRecursors.recursorType stats recInfos c.lctx owner) target) :
    env.IsType (AddInductive.getRecLevelParams elimLevel lparams).length [] target := by
  rcases H.typeAt owner howner with ⟨checked, Hchecked, Htyped⟩
  exact Htyped.defeqU_l henv trivial
    (Hchecked.uniq henv (show VLCtx.IsDefEq env
      (AddInductive.getRecLevelParams elimLevel lparams).length [] [] from
        .refl henv trivial) Hcanonical)

/-- Install the specified canonical target, retaining its exact name, type,
and universe arity. The checker witness supplies well-formedness without
choosing another abstract translation for this owner. -/
theorem RecursorTypeTranslations.recursorInfoTranslationOfTarget
    (H : RecursorTypeTranslations env lparams elimLevel c stats indTypes recInfos)
    (henv : env.WF) (k : Bool) (owner : Nat) (howner : owner < indTypes.size)
    (rules : List RecursorRule)
    (Hcanonical : TrExprS env (AddInductive.getRecLevelParams elimLevel lparams) []
      (AddInductive.declareRecursors.recursorType stats recInfos c.lctx owner) target) :
    let recursor : VConstVal := {
      uvars := (AddInductive.getRecLevelParams elimLevel lparams).length
      type := target
      name := Lean.mkRecName indTypes[owner]!.name }
    TrConstVal c.safety env
      (.recInfo (AddInductive.declareRecursors.recursorInfo stats indTypes
        elimLevel recInfos (recInfos.flatMap (·.minors)).size
        (recInfos.map (·.motive)).size (indTypes.map (·.name)).toList
        c.lctx k (c.safety != .safe) lparams owner rules)) recursor ∧
    recursor.toVConstant.WF env := by
  dsimp only
  refine ⟨⟨⟨?_, rfl, TrExprS.inferImplicit Hcanonical 1000 false⟩, rfl⟩,
    H.typeOfTranslation henv owner howner Hcanonical⟩
  have hsafety := H.notPartial
  cases hs : c.safety <;>
    simp_all [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, AddInductive.declareRecursors.recursorInfo]

end VerifyInductive
end Lean4Lean
