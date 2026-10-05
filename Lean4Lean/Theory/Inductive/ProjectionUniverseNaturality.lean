import Lean4Lean.Theory.Inductive.ProjectionProgramLemmas
import Lean4Lean.Theory.Inductive.RestorationNaturality

/-! Universe substitution of the actual restored projection data. All scope
guards inspect term binders and are preserved by universe specialization. -/

namespace Lean4Lean.InductiveSignature.CaseSchema
open VExpr

def ProjectionData.instL (data : ProjectionData) (packed : List VLevel) : ProjectionData :=
  { params := data.params.map (VExpr.instL packed)
    indices := data.indices.map (VExpr.instL packed)
    major := data.major.instL packed
    fields := data.fields.map (VExpr.instL packed)
    constructor := data.constructor.instL packed
    constructorIndices := data.constructorIndices.map (VExpr.instL packed) }

theorem telescopeScoped_instL (h : telescopeScoped n domains = true) :
    telescopeScoped n (domains.map (VExpr.instL packed)) = true := by
  rw [telescopeScoped_iff] at h ⊢
  intro i hi
  simp only [List.length_map] at hi
  simpa only [List.getElem_map] using (h i hi).instL (ls := packed)

private theorem restore_list_instL {r : Restoration} {input output : List VExpr}
    (H : input.mapM (fun e => r.expr (e.instL levels)) = some output) :
    input.mapM (fun e => r.expr (e.instL (levels.map (·.inst packed)))) =
      some (output.map (VExpr.instL packed)) := by
  induction input generalizing output with
  | nil => cases H; rfl
  | cons e es ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at H
    obtain ⟨out, he, outs, hs, h⟩ := H
    cases h
    have he' := r.expr_instL (e.instL levels) packed
    rw [he, Option.map_some, VExpr.instL_instL] at he'
    simp only [List.mapM_cons, ← he', ih hs, List.map_cons]
    rfl

theorem projectionData_instL {schema : CaseSchema}
    {owner : Fin schema.signature.families.size} {data : ProjectionData}
    (H : schema.projectionData owner levels = some data) :
    schema.projectionData owner (levels.map (·.inst packed)) = some (data.instL packed) := by
  unfold projectionData at H ⊢
  simp only [List.length_map]
  split at H <;> try contradiction
  rename_i hlevels
  rw [if_neg hlevels]
  split at H <;> try contradiction
  rename_i ctor hctor
  dsimp only at H ⊢
  split at H <;> try contradiction
  rename_i hindices
  rw [if_neg hindices]
  simp only [bind, Option.bind_eq_some_iff] at H
  obtain ⟨params, hp, indices, hi, fields, hf, cindices, hci,
    major, hm, constructor, hc, H⟩ := H
  split at H <;> try contradiction
  rename_i hscope
  cases H
  have hp' := restore_list_instL (packed := packed) hp
  have hi' := restore_list_instL (packed := packed) hi
  have hf' := restore_list_instL (packed := packed) hf
  have hci' := restore_list_instL (packed := packed) hci
  have hvars (n k : Nat) : (vars n k).map (VExpr.instL packed) = vars n k := by
    simp [vars, List.map_map, Function.comp_def, VExpr.instL]
  have hm' := schema.restoration.expr_instL
    (schema.signature.familyApp owner levels (vars params.length indices.length)
      (vars indices.length 0)) packed
  rw [hm, Option.map_some] at hm'
  simp only [InductiveSignature.familyApp, VExpr.instL_mkApps, VExpr.instL,
    List.map_append, hvars] at hm'
  have hc' := schema.restoration.expr_instL
    (mkApps (.const ctor.name levels) (vars params.length fields.length ++ vars fields.length 0)) packed
  rw [hc, Option.map_some] at hc'
  simp only [VExpr.instL_mkApps, VExpr.instL, List.map_append, hvars] at hc'
  simp only [bind, hp', hi', hf', hci', Option.bind_some, List.length_map,
    InductiveSignature.familyApp, ← hm', ← hc']
  have hscope' : (telescopeScoped 0 (params.map (VExpr.instL packed)) &&
      telescopeScoped params.length (indices.map (VExpr.instL packed)) &&
      telescopeScoped params.length (fields.map (VExpr.instL packed)) &&
      decide ((major.instL packed).ClosedN (params.length + indices.length)) &&
      decide ((constructor.instL packed).ClosedN (params.length + fields.length)) &&
      (cindices.map (VExpr.instL packed)).all (fun e =>
        decide (e.ClosedN (params.length + fields.length)))) = true := by
    simp at hscope
    obtain ⟨⟨⟨⟨⟨hpS, hiS⟩, hfS⟩, hmS⟩, hcS⟩, hciS⟩ := hscope
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_map, List.all_eq_true,
      Function.comp_def]
    exact ⟨⟨⟨⟨⟨telescopeScoped_instL hpS, telescopeScoped_instL hiS⟩,
      telescopeScoped_instL hfS⟩, hmS.instL⟩, hcS.instL⟩,
      fun e he => (hciS e he).instL⟩
  rw [hscope']
  rfl

end Lean4Lean.InductiveSignature.CaseSchema
