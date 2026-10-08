import Lean4Lean.Verify.Typing.Syntactic.Consumers

/-! Syntactic translation (`Lean4Lean/Verify/Typing/Syntactic/`).

`trSyn?` computes the translation of a kernel expression without typing: bound variables are
resolved in the context, let-bound values are inlined, literals are encoded, projections are kept
primitive, and an unscoped expression (a loose bound variable, an unknown free variable, an
undeclared universe parameter, a metavariable) has no translation. -/

namespace Lean4Lean.Tests.SyntacticTranslation

open Lean

deriving instance BEq for VLevel
deriving instance BEq for VExpr

def nat : Expr := .const ``Nat []
def zero : Expr := .const ``Nat.zero []

-- a let-bound value is inlined, and the declared type is not consulted
#guard trSyn? [] [] (.letE `x nat zero (.bvar 0) false) == some (.const ``Nat.zero [])
-- a dead let with an ill-typed value still translates: its typing is a residual obligation
#guard trSyn? [] [] (.letE `x nat (.sort .zero) zero false) == some (.const ``Nat.zero [])
-- binders
#guard trSyn? [] [] (.lam `x nat (.bvar 0) .default) ==
  some (.lam (.const ``Nat []) (.bvar 0))
#guard trSyn? [`u] [] (.forallE `α (.sort (.param `u)) (.bvar 0) .default) ==
  some (.forallE (.sort (.param 0)) (.bvar 0))
-- literals are encoded
#guard trSyn? [] [] (.lit (.natVal 2)) == some (.natLit 2)
#guard trSyn? [] [] (.lit (.strVal "ab")) == some (.trLiteral (.strVal "ab"))
-- projections are not resolved
#guard trSyn? [] [] (.proj `Prod 0 zero) == some (.proj `Prod 0 (.const ``Nat.zero []))
-- unscoped expressions
#guard trSyn? [] [] (.bvar 0) == none
#guard trSyn? [] [] (.fvar ⟨`x⟩) == none
#guard trSyn? [] [] (.sort (.param `u)) == none
#guard trSyn? [] [] (.mvar ⟨`m⟩) == none
-- a free variable of the context
#guard trSyn? [] [(some (⟨`x⟩, []), .vlam (.const ``Nat []))] (.fvar ⟨`x⟩) == some (.bvar 0)

-- the quotient types are computed
example : trSyn? [`u] [] QuotInit.tQuotC = some quotConst.type := rfl
example : trSyn? [`u, `v] [] QuotInit.tLiftC = some quotLiftConst.type := rfl

end Lean4Lean.Tests.SyntacticTranslation
