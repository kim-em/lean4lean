import Lean.Expr

namespace Lean

/-- Every universe parameter is among the declaration's parameters.
Universe metavariables are rejected. -/
def Level.paramsIn (params : List Name) : Level → Bool
  | .zero => true
  | .succ u => paramsIn params u
  | .max u v | .imax u v => paramsIn params u && paramsIn params v
  | .param name => params.contains name
  | .mvar _ => false

/-- Check the universe scope of concrete consumed syntax. Term variables
are permitted; binder domains, constant levels, and sorts are all visited. -/
def Expr.levelParamsIn (params : List Name) : Expr → Bool
  | .sort u => u.paramsIn params
  | .const _ levels => levels.all (Level.paramsIn params)
  | .app fn arg | .lam _ fn arg _ | .forallE _ fn arg _ =>
      levelParamsIn params fn && levelParamsIn params arg
  | .letE _ type value body _ =>
      levelParamsIn params type && levelParamsIn params value && levelParamsIn params body
  | .mdata _ e | .proj _ _ e => levelParamsIn params e
  | .mvar _ => false
  | .bvar _ | .fvar _ | .lit _ => true

end Lean
