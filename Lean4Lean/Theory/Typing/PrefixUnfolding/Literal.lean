import Lean4Lean.Theory.Typing.PrefixUnfolding.Layout
import Lean4Lean.Theory.Typing.Confluence.SingletonExtractionTyping

/-! # Literal constructor evidence at a singleton prefix

The singleton equation construction uses a prefix whose opened indices are
literally constructor indices at a typed field instance. Retaining this evidence
allows a computational interpretation to check only that occurrence.
-/
namespace Lean4Lean.InductiveSignature.RecursorData
open VExpr VEnv

/-- The opened singleton prefix comes from literal constructor indices at a
typed field instance. Its fresh major need not be the constructor itself. -/
def LiteralSingletonPrefix (data : RecursorData) (env : VEnv) (U : Nat)
    (Γ : List VExpr) (levels : List VLevel) (args : List VExpr) (program : PrefixUnfolding) : Prop :=
  ∃ S E fields, data.singletonLayout env levels = some S ∧ data.propElim levels = some E ∧
    TelInst env U (program.domains.reverse ++ Γ) (data.propParams levels ++ S.fields)
      ((data.openedArguments args).take data.numParams ++ fields) ∧
    ((data.openedArguments args).drop data.indexOffset).take data.numIndices =
      E.ctorIndices.map (·.instOuter ((data.openedArguments args).take data.numParams ++ fields))

end Lean4Lean.InductiveSignature.RecursorData
