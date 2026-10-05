import Lean4Lean.Theory.VExpr

/-! Pure telescope and application-spine syntax, below environments and typing. -/

namespace Lean4Lean

/-- Split exactly `n` leading forall binders, retaining domains in outermost to
innermost order. -/
def VExpr.takeForalls : Nat → VExpr → Option (List VExpr × VExpr)
  | 0, e => some ([], e)
  | n + 1, .forallE dom body => do
    let (doms, result) ← body.takeForalls n
    return (dom :: doms, result)
  | _ + 1, _ => none

/-- Head and left-to-right arguments of an application spine. -/
def VExpr.getAppFnArgs (e : VExpr) : VExpr × List VExpr :=
  go e []
where
  go : VExpr → List VExpr → VExpr × List VExpr
    | .app fn arg, args => go fn (arg :: args)
    | fn, args => (fn, args)

def VExpr.wrapLams (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .lam body

def VExpr.wrapForalls (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .forallE body

end Lean4Lean
