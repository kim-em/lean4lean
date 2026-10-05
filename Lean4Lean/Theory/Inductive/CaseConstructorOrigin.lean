import Lean4Lean.Theory.Inductive.NativeConstructorCoverage

/-! Constructor provenance for registered abstract case rules.
Original constructors belong to the checked source declaration; restored
container constructors carry concrete equations already present in the base
environment. -/

namespace Lean4Lean.InductiveSignature.CaseSchema

/-- A generated case rule selects either an original constructor or a
constructor whose native equation was installed by a certified prior
container. The parser does not introduce new constructor names. -/
theorem Certified.case_constructor_origin {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {rule : AppliedRule} {key : Name}
    (H : schema.Certified base source sourceBlock)
    (hgen : schema.Generates key owner rule) :
    (∃ ctor ∈ source.constructorConstants, rule.application.ctorName = ctor.name) ∨
    (∃ equation, base.defeqs equation ∧ ∃ fn levels args,
      equation.lhs.stripLams =
        .app fn (VExpr.mkApps (.const rule.application.ctorName levels) args)) := by
  obtain ⟨expanded, g, auxiliaries, hdata, hprior, hr, _⟩ := H
  obtain ⟨rules, hrules, hmem, hparse⟩ := hgen
  obtain ⟨index, hrestore⟩ := equation_origin hrules hmem
  have hparsed := Instance.parsed_constructor _ index hrestore hparse
  obtain ⟨ctor, hctor, _, hview⟩ := view_constructor_origin index
  obtain ⟨position, hposition, hget⟩ := List.mem_iff_getElem.mp hctor
  let original : Fin schema.signature.constructors.size := ⟨position, by simpa using hposition⟩
  have hname : (schema.view owner).constructors[index].name =
      schema.signature.constructors[original].name := by
    rw [hview]
    simp only [caseConstructor]
    simpa only [original, Fin.getElem_fin, Array.getElem_toList] using
      (congrArg (fun c => c.name) hget).symm
  rw [hname, hr] at hparsed
  rcases hdata.constructor_name_origin original with ⟨ctor, hctor, hname⟩ |
      ⟨a, ha, ctor, hctor, hname⟩
  · exact .inl ⟨ctor, hctor, hparsed.trans hname⟩
  · obtain ⟨equation, hequation, fn, levels, args, hmajor⟩ :=
      hprior.constructor_equation a ha ctor hctor
    refine .inr ⟨equation, hequation, fn, levels, args, ?_⟩
    rw [hparsed.trans hname]
    exact hmajor

end Lean4Lean.InductiveSignature.CaseSchema
