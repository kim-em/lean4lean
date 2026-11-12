import Lean4Lean.Theory.VExpr

/-! `VExpr.ProjNamesOK`: every projection type name of a term satisfies a predicate. -/

namespace Lean4Lean

namespace VExpr

/-- Every projection type name of the term satisfies `ok`. -/
def ProjNamesOK (ok : Name → Prop) : VExpr → Prop
  | .bvar _ | .sort _ | .const .. => True
  | .app f a | .lam f a | .forallE f a => f.ProjNamesOK ok ∧ a.ProjNamesOK ok
  | .proj n _ e => ok n ∧ e.ProjNamesOK ok

theorem ProjNamesOK.liftN {ok : Name → Prop} {n : Nat} :
    ∀ {e : VExpr} {k : Nat}, e.ProjNamesOK ok → (e.liftN n k).ProjNamesOK ok
  | .bvar _, _, _ | .sort _, _, _ | .const .., _, _ => trivial
  | .app _ _, _, h => ⟨ProjNamesOK.liftN h.1, ProjNamesOK.liftN h.2⟩
  | .lam _ _, _, h => ⟨ProjNamesOK.liftN h.1, ProjNamesOK.liftN h.2⟩
  | .forallE _ _, _, h => ⟨ProjNamesOK.liftN h.1, ProjNamesOK.liftN h.2⟩
  | .proj _ _ _, _, h => ⟨h.1, ProjNamesOK.liftN h.2⟩

end VExpr
end Lean4Lean
