import Lean4Lean.Theory.Typing.AnchoredNativeSyntax
import Lean4Lean.Theory.Typing.Lemmas

/-! Literal constant telescope metadata, independent of source observations. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr InductiveSignature

structure ConstantTelescope (declaredType : VExpr) where
  domains : List VExpr
  result : VExpr
  type_eq : declaredType = wrapForalls domains result

/-- The original telescope variables, in declaration order. -/
def constantCaptureVariables (count : Nat) : List VExpr :=
  (List.range count).reverse.map VExpr.bvar

theorem constantCaptureVariables_scope {expression : VExpr} {count : Nat}
    (member : expression ∈ constantCaptureVariables count) : expression.ClosedN count := by
  obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp member
  exact List.mem_range.mp (List.mem_reverse.mp indexMember)

private theorem wrapForalls_domain_scope
    {domains : List VExpr} {result domain : VExpr} {count index : Nat}
    (closed : (wrapForalls domains result).ClosedN count)
    (origin : domains[index]? = some domain) : domain.ClosedN (count + index) := by
  induction domains generalizing count index with
  | nil => simp at origin
  | cons A rest ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at origin
      subst domain
      exact closed.1
    | succ index =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih closed.2 origin

theorem ConstantTelescope.domain_scope {declaredType domain : VExpr} {index : Nat}
    (signature : ConstantTelescope declaredType)
    (closed : declaredType.Closed) (origin : signature.domains[index]? = some domain) :
    domain.ClosedN index := by
  rw [signature.type_eq] at closed
  simpa only [Nat.zero_add] using wrapForalls_domain_scope closed origin

private theorem telescope_contextClosed {domains source : List VExpr} {result : VExpr}
    (scope : CtxClosed source) (closed : (wrapForalls domains result).ClosedN source.length) :
    CtxClosed (domains.reverse ++ source) := by
  induction domains generalizing source with
  | nil => exact scope
  | cons A domains ih =>
    have later := ih (source := A :: source) ⟨scope, closed.1⟩ closed.2
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using later

theorem ConstantTelescope.contextClosed {declaredType : VExpr}
    (signature : ConstantTelescope declaredType) (closed : declaredType.Closed) :
    CtxClosed signature.domains.reverse := by
  rw [signature.type_eq] at closed
  simpa only [List.append_nil] using telescope_contextClosed (source := []) trivial closed

private theorem wrapForalls_result_scope {domains : List VExpr} {result : VExpr} {count : Nat}
    (closed : (wrapForalls domains result).ClosedN count) :
    result.ClosedN (count + domains.length) := by
  induction domains generalizing count with
  | nil => exact closed
  | cons A domains ih =>
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih closed.2

theorem ConstantTelescope.result_scope {declaredType : VExpr}
    (signature : ConstantTelescope declaredType) (closed : declaredType.Closed) :
    signature.result.ClosedN signature.domains.length := by
  rw [signature.type_eq] at closed
  simpa only [Nat.zero_add] using wrapForalls_result_scope closed

end Lean4Lean.AnchoredSource.Adapted
