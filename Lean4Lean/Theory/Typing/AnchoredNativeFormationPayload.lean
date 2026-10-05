import Lean4Lean.Theory.Typing.AnchoredNativeCaptureGuard
import Lean4Lean.Theory.Typing.SourcePiFormation
import Lean4Lean.Theory.Inductive.SaturatedNativeRenaming

/-! Read the two native field domains from retained original formation
payloads. The syntax equalities come from the selected registered telescope
and saturated program, including the exact restored equation instruction.
No newly derived typing proof is passed to a semantic induction here. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem native_telescope_eq
    (h : NativeRecursorData.takeForalls count expression = some (domains, body)) :
    expression = wrapForalls domains body := by
  induction count generalizing expression domains body with
  | zero =>
    simp only [NativeRecursorData.takeForalls, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | succ count ih =>
    cases expression <;> simp only [NativeRecursorData.takeForalls] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨tail, result⟩, ht, rfl, rfl⟩ := h
    exact congrArg (VExpr.forallE _) (ih ht)

private theorem instantiate_telescope (domains : List VExpr) (body : VExpr) (levels : List VLevel) :
    (wrapForalls domains body).instL levels =
      wrapForalls (domains.map (·.instL levels)) (body.instL levels) := by
  induction domains with
  | nil => rfl
  | cons domain rest ih => exact congrArg (VExpr.forallE (domain.instL levels)) ih

private theorem payload_at
    {P : List VExpr → VExpr → VExpr → Prop}
    (root : ∃ level, P Γ (wrapForalls domains body) (.sort level))
    (tree : SourcePiFormation P Γ (wrapForalls domains body))
    (origin : domains[index]? = some domain) :
    (∃ level, P ((domains.take index).reverse ++ Γ) domain (.sort level)) ∧
      SourcePiFormation P ((domains.take index).reverse ++ Γ) domain := by
  have bound : index < domains.length := List.getElem?_eq_some_iff.mp origin |>.1
  have equal : domains[index] = domain := (List.getElem?_eq_some_iff.mp origin).2
  simpa only [equal] using (tree.telescope root).1 index bound

/-- The capture instruction's annotation is literally the corresponding
field of the selected equation's universe-instantiated telescope. -/
theorem NativeIndexTemplates.declaredOrigin_exact
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program) :
    (program.equationBody.domains.map (·.instL program.levels))[data.indexOffset + templates.field]? = some templates.declaredDomain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, instructions, _⟩ :=
    saturatedProgram_spec templates.selected
  have domains := fieldInstructions_domains program.source
    ((program.equationBody.domains.drop data.indexOffset).map (·.instL program.levels))
  rw [← instructions] at domains
  have selected := congrArg (fun ds => ds[templates.field]?) domains
  rw [List.getElem?_map, templates.declaredOrigin] at selected
  simpa only [Option.map_some, CaptureInstruction.domain, List.map_drop,
    List.getElem?_drop] using selected.symm

/-- Both source contexts are fixed by the original telescopes, in context
order. `P` and `Q` can retain the actual raw formation and its already-produced
semantic result at different predecessor declaration stages. -/
theorem NativeIndexTemplates.sourceDomains
    {P Q : List VExpr → VExpr → VExpr → Prop}
    {data : NativeRecursorData} {program : SaturatedProgram data}
    (templates : NativeIndexTemplates program)
    (naturalRoot : ∃ level, P [] (templates.recursorType.instL program.levels) (.sort level))
    (naturalTree : SourcePiFormation P [] (templates.recursorType.instL program.levels))
    (declaredRoot : ∃ level, Q [] (program.equation.type.instL program.levels) (.sort level))
    (declaredTree : SourcePiFormation Q [] (program.equation.type.instL program.levels)) :
    ((∃ level, P templates.naturalContext templates.naturalDomain (.sort level)) ∧
      SourcePiFormation P templates.naturalContext templates.naturalDomain) ∧
    ((∃ level, Q templates.declaredContext templates.declaredDomain (.sort level)) ∧
      SourcePiFormation Q templates.declaredContext templates.declaredDomain) := by
  have naturalEq := native_telescope_eq templates.telescope
  rw [naturalEq] at naturalRoot naturalTree
  obtain ⟨_, _, _, _, _, _, _, _, _, extraction, _⟩ :=
    saturatedProgram_spec templates.selected
  have declaredEq := (CaseSchema.EquationBody.extract_sound extraction).2.2
  rw [← declaredEq, instantiate_telescope] at declaredRoot declaredTree
  exact ⟨by simpa only [List.append_nil, NativeIndexTemplates.naturalContext] using
      payload_at naturalRoot naturalTree templates.naturalOrigin,
    by simpa only [List.append_nil, NativeIndexTemplates.declaredContext, List.map_take] using
      payload_at declaredRoot declaredTree templates.declaredOrigin_exact⟩

end Lean4Lean.AnchoredSource.Adapted
