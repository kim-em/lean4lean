import Lean4Lean.Theory.Inductive

namespace Lean4Lean

open Lean

/-- A verified source projection translates to the same primitive projection
node in the abstract syntax, given that the major and the projection are well formed. The
target is fixed by the indices of the relation (`TrProj.target_eq`). -/
inductive TrProj {env : VEnv} {U : Nat} (Gamma : List VExpr)
    (structName : Name) (index : Nat) (major : VExpr) : VExpr → Prop
  | direct
      (majorWF : VExpr.WF env U Gamma major)
      (targetWF : VExpr.WF env U Gamma (.proj structName index major)) :
      TrProj Gamma structName index major (.proj structName index major)

namespace TrProj

theorem target_eq
    (H : TrProj (env := env) (U := U) Gamma structName index major target) :
    target = .proj structName index major := by
  cases H
  rfl

theorem target_not_forall
    (H : TrProj (env := env) (U := U) Gamma structName index major target) :
    target ≠ .forallE domain body := by
  cases H
  intro h
  cases h

end TrProj

end Lean4Lean
