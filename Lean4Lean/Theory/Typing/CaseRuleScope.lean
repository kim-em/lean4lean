import Lean4Lean.Theory.Typing.CaseRhsTyping
import Lean4Lean.Theory.Inductive.ProjectionProgram

/-! The original closed case header supplies the scope of every generated
right-hand side. The selected minor's literal telescope supplies the field
domains; no equation-typing or equation-scope oracle is required. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr

private theorem forall_domain_scope {domains : List VExpr} {body : VExpr}
    (closed : (wrapForalls domains body).ClosedN count)
    (index : Nat) (bound : index < domains.length) :
    domains[index].ClosedN (count + index) := by
  induction domains generalizing count index with
  | nil => simp at bound
  | cons domain domains ih =>
    cases index with
    | zero => exact closed.1
    | succ index =>
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1] using
        ih closed.2 index (by simpa using bound)

/-- The generated case equation uses only domains already scoped by its
original generic header, followed by the selected minor's own fields. -/
theorem Generates.rhs_closed {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule} {type : VExpr}
    (generated : schema.Generates block owner rule)
    (header : schema.genericType owner = some type)
    (restoration : schema.restoration.Scoped) (closed : type.Closed) :
    rule.equation.rhs.Closed := by
  obtain ⟨pre, fields, tail, result, index, bound, headerShape,
    rhsShape, _, minorShape⟩ := generated.rhs_layout header restoration
  have prefixScope : ∀ i (hi : i < pre.length), pre[i].ClosedN i := by
    intro i hi
    simpa only [Nat.zero_add] using
      forall_domain_scope (count := 0) (headerShape ▸ closed) i hi
  have minorScope : (wrapForalls fields result).ClosedN pre.length := by
    rw [← minorShape]
    have scope := (prefixScope index bound).liftN (n := pre.length - index) (j := 0)
    simpa only [Nat.add_sub_of_le (Nat.le_of_lt bound)] using scope
  rw [rhsShape]
  apply ClosedN.wrapLams_closed
  · intro i hi
    simp only [Nat.zero_add]
    by_cases before : i < pre.length
    · simpa only [List.getElem_append_left before] using prefixScope i before
    · rw [List.getElem_append_right (by omega)]
      have scope := forall_domain_scope minorScope (i - pre.length) (by
        simp only [List.length_append] at hi
        omega)
      simpa only [Nat.add_sub_of_le (by omega : pre.length ≤ i)] using scope
  · apply ClosedN.mkApps_closed
    · change fields.length + (pre.length - 1 - index) < 0 + (pre ++ fields).length
      simp only [List.length_append]
      omega
    · intro argument member
      simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at member
      obtain ⟨i, hi, rfl⟩ := member
      change 0 + i < 0 + (pre ++ fields).length
      simp only [List.length_append]
      omega

end Lean4Lean.InductiveSignature.CaseSchema
