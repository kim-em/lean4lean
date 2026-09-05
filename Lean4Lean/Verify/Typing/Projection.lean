import Lean4Lean.Theory.Inductive

namespace Lean4Lean

open Lean

/-- A verified source projection translates to the same primitive projection
node in the abstract syntax. The two well-formedness fields are proof
artifacts only: the target is fixed by the indices of the relation, so a
certificate cannot choose another implementation or result expression. -/
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

theorem target_bvarHead?_eq_none
    (H : TrProj (env := env) (U := U) Gamma structName index major target) :
    target.bvarHead? = none := by
  cases H
  rfl

end TrProj

end Lean4Lean
