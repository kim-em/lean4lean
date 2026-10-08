import Lean4Lean.Theory.Typing.CaseReduction
import Lean4Lean.Theory.Inductive.NativeRecursorData

/-! Scope and term-renaming facts for the actual singleton reconstruction
program. These facts retain its selected index and proof-field programs. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr

/-- Closed declaration syntax commutes with renaming the simultaneous
occurrence arguments. It cannot retain any unrenamed free variable. -/
theorem instantiateParams_lift' {body : VExpr} {args : List VExpr}
    (hbody : body.ClosedN args.length) :
    (instantiateParams body args).lift' ρ =
      instantiateParams body (args.map (·.lift' ρ)) := by
  let σ : VExpr.Subst := fun i =>
    if hi : i < args.length then args[args.length - 1 - i] else .bvar (i - args.length)
  change (body.subst σ).lift' ρ = _
  rw [VExpr.lift'_subst]
  unfold instantiateParams
  dsimp only [σ]
  apply VExpr.subst_congr_closedN hbody
  intro i hi
  simp only [VExpr.Subst.lift_r, List.length_map, dif_pos hi, List.getElem_map]

end Lean4Lean.InductiveSignature.CaseSchema

namespace Lean4Lean.InductiveSignature.NativeRecursorData
open VExpr CaseSchema
variable {levels : List VLevel}

end Lean4Lean.InductiveSignature.NativeRecursorData
