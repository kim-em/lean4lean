import Lean4Lean.Theory.Typing.NativeInitialFieldOccurrences
import Lean4Lean.Theory.Typing.SourcePiFormation

/-! Declared field lookup is fixed by the original equation telescope. The
instantiated domain identity is a scoped syntax calculation, independent of
an inferred natural type at the corresponding native argument. -/
namespace Lean4Lean.InductiveSignature
open VExpr _root_.Lean4Lean.VEnv NativeRecursorData
open private telescope_scope from Lean4Lean.Theory.Typing.NativeProjectionCompleteness
set_option backward.isDefEq.respectTransparency false

private theorem vars_take (count position : Nat) (bound : position ≤ count) :
    (vars count 0).take position = bvarRange position count := by
  apply List.ext_getElem
  · simp only [List.length_take, vars, List.length_map, List.length_reverse,
      List.length_range, bvarRange_length]
    omega
  · intro i hi hi'
    simp only [List.getElem_take, vars, List.getElem_map, List.getElem_reverse,
      List.getElem_range, List.length_range, Nat.zero_add,
      bvarRange, List.getElem_map, List.getElem_range]

/-- A literal original telescope domain, at its actual capture variable. -/
theorem declaredFieldOrigin
    {domains : List VExpr} {result domain : VExpr} {position : Nat}
    (scope : (wrapForalls domains result).Closed)
    (selected : domains[position]? = some domain) :
    domain.ClosedN position ∧
    Lookup domains.reverse (domains.length - 1 - position)
      (domain.instOuter ((vars domains.length 0).take position)) := by
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp selected
  have domainScope : domain.ClosedN position := by
    simpa only [equal, Nat.zero_add] using (telescope_scope scope).1 position bound
  refine ⟨domainScope, ?_⟩
  rw [vars_take _ _ (Nat.le_of_lt bound), instOuter_range_bvar' domain position domains.length domainScope
    (Nat.le_of_lt bound)]
  simpa only [List.append_nil, equal] using Lookup.reverse_append domains [] position bound

/-- Match the lookup index with a literal field occurrence retained by the
initial capture parser. -/
theorem declaredFieldOccurrence
    {domains : List VExpr} {result domain : VExpr} {position index : Nat}
    (scope : (wrapForalls domains result).Closed)
    (selected : domains[position]? = some domain)
    (occurrence : (vars domains.length 0)[position]? = some (.bvar index)) :
    domain.ClosedN position ∧
    Lookup domains.reverse index
      (domain.instOuter ((vars domains.length 0).take position)) := by
  obtain ⟨domainScope, lookup⟩ := declaredFieldOrigin scope selected
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  have varsBound : position < (vars domains.length 0).length := by simpa [vars] using bound
  rw [List.getElem?_eq_getElem varsBound] at occurrence
  simp only [vars, List.getElem_map, List.getElem_reverse, List.getElem_range,
    List.length_range, Nat.zero_add, Option.some.injEq, VExpr.bvar.injEq] at occurrence
  exact ⟨domainScope, occurrence ▸ lookup⟩

/-- The formation payload is selected from the original Strong proof's
literal Pi tree; its own sort is retained instead of inferred from an outer
converted sort. -/
theorem HasTypeStrong.declaredFieldOrigin
    {env : VEnv} {U : Nat} {domains : List VExpr} {result domain : VExpr}
    {level : VLevel} {structural : Bool} {position : Nat}
    (henv : env.Ordered)
    (original : env.HasTypeStrong U [] (wrapForalls domains result) (.sort level) structural)
    (selected : domains[position]? = some domain) :
    domain.ClosedN position ∧
    Lookup domains.reverse (domains.length - 1 - position)
      (domain.instOuter ((vars domains.length 0).take position)) ∧
    ∃ ownLevel, env.IsDefEqStrong U ((domains.take position).reverse) domain domain (.sort ownLevel) := by
  have scope := original.refl.defeq.closedN henv trivial
  obtain ⟨domainScope, lookup⟩ := Lean4Lean.InductiveSignature.declaredFieldOrigin scope selected
  obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp selected
  have payload := (SourcePiFormation.telescope ⟨level, original.refl⟩
    original.refl.sourcePiFormation.1).1 position bound
  exact ⟨domainScope, lookup, by simpa only [List.append_nil, equal] using payload.1⟩

end Lean4Lean.InductiveSignature

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

/-- The selected capture instruction supplies its actual declared telescope
position; the original captured variable determines the final lookup index. -/
theorem NativeIndexTemplates.declaredSourceLookup
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program) {index : Nat}
    (scope : (wrapForalls (program.equationBody.domains.map (·.instL program.levels))
      (program.equationBody.type.instL program.levels)).Closed)
    (occurrence : (vars program.equationBody.domains.length 0)[data.indexOffset + templates.field]? =
      some (.bvar index)) :
    templates.declaredDomain.ClosedN
      ((vars program.equationBody.domains.length 0).take (data.indexOffset + templates.field)).length ∧
    Lookup (program.equationBody.domains.map (·.instL program.levels)).reverse index
      (templates.declaredDomain.instOuter
        ((vars program.equationBody.domains.length 0).take (data.indexOffset + templates.field))) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, instructions, _⟩ :=
    saturatedProgram_spec templates.selected
  have domains := fieldInstructions_domains program.source
    ((program.equationBody.domains.drop data.indexOffset).map (·.instL program.levels))
  rw [← instructions] at domains
  have selected := congrArg (fun ds => ds[templates.field]?) domains
  rw [List.getElem?_map, templates.declaredOrigin] at selected
  have exactDomain : (program.equationBody.domains.map (·.instL program.levels))[data.indexOffset + templates.field]? = some templates.declaredDomain := by
    simpa only [Option.map_some, CaptureInstruction.domain, List.map_drop,
      List.getElem?_drop] using selected.symm
  obtain ⟨domainScope, lookup⟩ := InductiveSignature.declaredFieldOccurrence scope exactDomain
    (by simpa only [List.length_map] using occurrence)
  have bound := (List.getElem?_eq_some_iff.mp exactDomain).1
  simp only [List.length_map] at bound lookup
  refine ⟨?_, lookup⟩
  simpa only [List.length_take, vars, List.length_map, List.length_reverse,
    List.length_range, Nat.min_eq_left (Nat.le_of_lt bound)] using domainScope

end Lean4Lean.AnchoredSource.Adapted
