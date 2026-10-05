import Lean4Lean.Theory.Inductive.ProjectionProgram

/-! Declaration-generated structure eta templates. Eta is a separate equality
principle; generating these terms does not derive eta from case iota. -/

namespace Lean4Lean.InductiveSignature.CaseSchema

/-- Reconstruct the original constructor from all its generated field
projections in the common-parameter/major context. -/
def ProjectionData.etaReconstruction (data : ProjectionData)
    (projections : List ProjectionFunction) : VExpr :=
  instantiateParams data.constructor <|
    vars data.params.length 1 ++ projections.map fun projection =>
      VExpr.mkApps projection.value (vars data.params.length 1 ++ [.bvar 0])

/-- A complete, closed template for the structure eta equality. Indexed
families are rejected, matching the separate structure eta principle. Every
field is supplied by this schema's actual projection generator. -/
def structureEta (schema : CaseSchema) (block : Name)
    (owner : Fin schema.signature.families.size) (uvars : Nat)
    (levels fieldSorts : List VLevel) : Option VDefEq := do
  let data ← schema.projectionData owner levels
  if data.indices.length != 0 || data.fields.length != fieldSorts.length then none else
  let projections ← schema.projectionPrefix block owner uvars levels fieldSorts
  let domains := data.params ++ [data.major]
  return {
    uvars := uvars
    lhs := VExpr.wrapLams domains (data.etaReconstruction projections)
    rhs := VExpr.wrapLams domains (.bvar 0)
    type := VExpr.wrapForalls domains data.major.lift }

/-- Prefix generation returns exactly the initial functions followed by one
new function for each requested field sort. -/
theorem ProjectionData.prefix_length {data : ProjectionData}
    {domains : List VExpr} {targets : List VLevel} {previous result : List ProjectionFunction}
    (H : data.prefix block owner levels domains targets previous = some result) :
    result.length = previous.length + targets.length := by
  induction targets generalizing domains previous with
  | nil => simp only [ProjectionData.prefix] at H; cases H; simp
  | cons target targets ih =>
    cases domains with
    | nil => cases H
    | cons domain domains =>
      have h := ih H
      simp only [List.length_append, List.length_cons, List.length_nil] at h ⊢
      omega

theorem projectionPrefix_length {schema : CaseSchema} {uvars : Nat}
    {owner : Fin schema.signature.families.size}
    (H : schema.projectionPrefix block owner uvars levels targets = some result) :
    result.length = targets.length := by
  unfold projectionPrefix at H
  split at H <;> try contradiction
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨data, hdata, H⟩ := H
  simpa using ProjectionData.prefix_length H

private theorem eta_vars_closed (count : Nat) :
    ∀ e ∈ vars count 1, e.ClosedN (count + 1) := by
  intro e he
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  change 1 + i < count + 1
  omega

private theorem eta_domains_closed {data : ProjectionData}
    (H : data.Scoped) (hi : data.indices.length = 0) :
    ∀ i (hi : i < (data.params ++ [data.major]).length),
      (data.params ++ [data.major])[i].ClosedN i := by
  intro i hbound
  by_cases hp : i < data.params.length
  · simpa only [List.getElem_append_left hp] using H.params i hp
  · have he : i = data.params.length := by
      simp only [List.length_append, List.length_singleton] at hbound
      omega
    subst i
    rw [List.getElem_append_right (Nat.le_refl _)]
    simpa only [Nat.sub_self, List.getElem_singleton, hi, Nat.add_zero] using H.major

/-- The reconstructed constructor is scoped under the same common
parameters and major as the generated projections. -/
theorem ProjectionData.etaReconstruction_closed {data : ProjectionData}
    (H : data.Scoped) (hfields : projections.length = data.fields.length)
    (hprojections : ∀ p ∈ projections, p.value.Closed) :
    (data.etaReconstruction projections).ClosedN (data.params.length + 1) := by
  unfold etaReconstruction instantiateParams
  apply H.constructor.subst_closed
  intro i hi
  split
  · apply List.forall_mem_append.mpr ⟨eta_vars_closed _, ?_⟩ _ (List.getElem_mem _)
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    apply ((hprojections p hp).mono (Nat.zero_le _)).mkApps_closed
    intro arg harg
    rcases List.mem_append.mp harg with harg | harg
    · exact eta_vars_closed _ arg harg
    · obtain rfl := List.mem_singleton.mp harg
      exact Nat.zero_lt_succ _
  · rename_i hbad
    simp only [List.length_append, List.length_map, vars, List.length_reverse,
      List.length_range, hfields] at hbad
    omega

/-- Successful generation supplies a closed equality template, with no
primitive projection syntax inserted by the reconstruction. Typing and the
separate eta rule remain obligations of the registered-schema consumer. -/
theorem structureEta_closed {schema : CaseSchema} {uvars : Nat}
    {owner : Fin schema.signature.families.size}
    (H : schema.structureEta block owner uvars levels fieldSorts = some equation) :
    equation.lhs.Closed ∧ equation.rhs.Closed ∧ equation.type.Closed := by
  unfold structureEta at H
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨data, hdata, H⟩ := H
  split at H <;> try contradiction
  rename_i hvalid
  simp only [Bool.or_eq_true, bne_iff_ne, not_or, Decidable.not_not] at hvalid
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨projections, hg, he⟩ := H
  cases he
  have hscoped := projectionData_scoped hdata
  have hdoms := eta_domains_closed hscoped hvalid.1
  have hctor := ProjectionData.etaReconstruction_closed hscoped
    ((projectionPrefix_length hg).trans hvalid.2.symm)
    (fun p hp => (projectionPrefix_closed hg p hp).1)
  have hmajor : data.major.ClosedN data.params.length := by
    simpa only [hvalid.1, Nat.add_zero] using hscoped.major
  refine ⟨VExpr.ClosedN.wrapLams_closed (by simpa using hdoms) ?_,
    VExpr.ClosedN.wrapLams_closed (by simpa using hdoms) ?_,
    VExpr.ClosedN.wrapForalls_closed (by simpa using hdoms) ?_⟩
  · simpa using hctor
  · change 0 < 0 + (data.params ++ [data.major]).length
    simp
  · simpa using hmajor.liftN (n := 1)

end Lean4Lean.InductiveSignature.CaseSchema
