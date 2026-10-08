import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.Pattern

namespace Lean4Lean

/-- The computational head of an equation, after its argument telescope. -/
def VExpr.equationHead : VExpr → VExpr
  | .lam _ body => body.equationHead
  | e => e.getAppFnArgs.1

/-- The fixed function head of a native pattern. -/
def Pattern.constHead : Pattern → Option Name
  | .const name => some name
  | .elim .. => none
  | .app fn _ | .var fn => fn.constHead

/-- Native computation must originate at an equation actually present in the
environment. Typing soundness alone would also permit invented reflexive or
eta rules at constructor heads, which are not executable equations. -/
def VEnv.PatternHeadsStoredRule (env : VEnv) (pattern : Pattern) : Prop :=
  ∃ equation name levels, env.defeqs equation ∧ pattern.constHead = some name ∧
    equation.lhs.equationHead = .const name levels

/-- No installed native equation computes at this constant's head. -/
def VEnv.ConstHeadRigid (env : VEnv) (name : Name) : Prop :=
  ∀ equation, env.defeqs equation → ∀ levels,
    equation.lhs.equationHead ≠ .const name levels

end Lean4Lean
