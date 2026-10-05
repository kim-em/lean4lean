import Lean4Lean.Theory.Inductive.ProjectionProgram

namespace Lean4Lean.InductiveSignature.CaseSchema

private theorem ProjectionData.prefix_step {data : ProjectionData}
    {domains : List VExpr} {targets : List VLevel} {previous result : List ProjectionFunction}
    (hout : data.prefix block owner levels domains targets previous = some result)
    (hp : p ∈ result) :
    p ∈ previous ∨ ∃ domain target previous', p = data.step block owner levels domain target previous' := by
  induction targets generalizing domains previous with
  | nil => simp only [ProjectionData.prefix] at hout; cases hout; exact .inl hp
  | cons target targets ih =>
    cases domains with
    | nil => cases hout
    | cons domain domains =>
      obtain h | h := ih hout
      · obtain h | h := List.mem_append.1 h
        · exact .inl h
        · exact .inr ⟨domain, target, previous, List.mem_singleton.1 h⟩
      · exact .inr h

/-- Every returned projection is an actual step of the total generator. -/
theorem projectionPrefix_step {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {result : List ProjectionFunction} {uvars : Nat}
    (hout : schema.projectionPrefix block owner uvars levels targets = some result)
    (hp : p ∈ result) :
    ∃ data, schema.projectionData owner levels = some data ∧
      ∃ domain target previous, p = data.step block owner.val levels domain target previous := by
  unfold projectionPrefix at hout
  split at hout <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at hout
  obtain ⟨data, hdata, hout⟩ := hout
  refine ⟨data, hdata, ?_⟩
  obtain h | h := ProjectionData.prefix_step hout hp
  · cases h
  · exact h

private theorem filterMap_select {α β : Type} (f : α → β) (p : α → Bool) (xs : List α) :
    xs.filterMap (fun x => if p x then some (f x) else none) = (xs.filter p).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h, ih]

/-- Successful projection extraction retains the source telescope lengths and
has precisely one case minor. -/
theorem projectionData_counts {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {data : ProjectionData}
    (H : schema.projectionData owner levels = some data) :
    data.params.length = schema.signature.params.length ∧
    data.indices.length = schema.signature.families[owner].indices.length ∧
    (schema.view owner).constructors.size = 1 := by
  unfold projectionData at H
  split at H <;> try contradiction
  split at H <;> try contradiction
  rename_i ctor hctors
  dsimp only at H
  split at H <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨params, hp, indices, hi, fields, hf, cindices, hci, major, hm, ctorExpr, hc, H⟩ := H
  split at H <;> try contradiction
  cases H
  refine ⟨?_, ?_, ?_⟩
  · exact (List.Forall₂.length_eq (List.mapM_eq_some.mp hp)).symm
  · exact (List.Forall₂.length_eq (List.mapM_eq_some.mp hi)).symm
  · simp only [view, filterMap_select, List.size_toArray, List.length_map, hctors, List.length_singleton]

end Lean4Lean.InductiveSignature.CaseSchema
