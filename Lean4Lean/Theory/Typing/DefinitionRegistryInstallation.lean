import Lean4Lean.Theory.Typing.DefinitionPatterns
import Batteries.Tactic.OpenPrivate

/-! The definition-pattern table follows actual constant/equation
installation. Successful insertion proves freshness and lookup completeness. -/

namespace Lean4Lean.VEnv
variable {env extended : VEnv} {values : List VDefVal} {value : VDefVal}
open private addConsts_as_values addDefEqs_as_rules
  from Lean4Lean.Theory.Typing.NativeConstructorRigidity

/-- Add exactly the values of a checked definition block to its pattern table. -/
def installDefinitions (old : Name → Option VDefVal) (values : List VDefVal)
    (name : Name) : Option VDefVal :=
  (values.find? (fun value => value.name == name)).orElse (fun _ => old name)

theorem DefinitionRegistered.of_addConsts
    (hadd : env.addConsts values = some extended) (hvalue : value ∈ values) :
    DefinitionRegistered (extended.addDefEqs values) value := by
  rw [addDefEqs_as_rules]
  exact ⟨by simpa only [VEnv.addDefEqRules_constants] using
      VEnv.addConsts_constants hadd value hvalue,
    VEnv.addDefEqRules_mem (List.mem_map.mpr ⟨value, hvalue, rfl⟩)⟩

private theorem definition_names_nodup
    (hadd : env.addConsts values = some extended) : (values.map (·.name)).Nodup := by
  induction values generalizing env with
  | nil => trivial
  | cons value values ih =>
    simp only [VEnv.addConsts, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hadd
    obtain ⟨middle, hfirst, hrest⟩ := hadd
    have hrest : middle.addConsts values = some extended := hrest
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hrest⟩
    intro hm
    obtain ⟨other, hm, hn⟩ := List.mem_map.mp hm
    have hf := VEnv.addConstVals_names_fresh (addConsts_as_values ▸ hrest)
      other.toVConstVal (List.mem_map.mpr ⟨other, hm, rfl⟩)
    have hs := VEnv.addConst_self hfirst
    change middle.constants other.name = none at hf
    rw [hn, hs] at hf
    contradiction

private theorem definition_find (hnd : (values.map (·.name)).Nodup)
    (hmem : value ∈ values) :
    values.find? (fun other => other.name == value.name) = some value := by
  induction values with
  | nil => cases hmem
  | cons first tail ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | hmem
    · simp
    · have hn : first.name ≠ value.name := by
        intro he
        exact hnd.1 (List.mem_map.mpr ⟨value, hmem, he.symm⟩)
      simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hn]
      exact ih hnd.2 hmem

/-- Successful declaration installation gives every definition its own
lookup entry, including mutually recursive definitions. -/
theorem installDefinitions_lookup
    (hadd : env.addConsts values = some extended) (hvalue : value ∈ values) :
    installDefinitions old values value.name = some value := by
  unfold installDefinitions
  rw [definition_find (definition_names_nodup hadd) hvalue]
  rfl

/-- New definitions cannot shadow an earlier registered definition. -/
theorem installDefinitions_preserves
    (hadd : env.addConsts values = some extended)
    (hregistered : DefinitionRegistered env previous) (hold : old previous.name = some previous) :
    installDefinitions old values previous.name = some previous := by
  unfold installDefinitions
  cases hf : values.find? (fun value => value.name == previous.name) with
  | none => exact hold
  | some fresh =>
    have hn : fresh.name = previous.name := by simpa using List.find?_some hf
    have hnone := VEnv.addConstVals_names_fresh (addConsts_as_values ▸ hadd)
      fresh.toVConstVal (List.mem_map.mpr ⟨fresh, List.mem_of_find?_eq_some hf, rfl⟩)
    change env.constants fresh.name = none at hnone
    rw [hn, hregistered.1] at hnone
    contradiction

/-- The new table contains only actual installed values and defining
equations; the earlier table is transported through this concrete extension. -/
theorem installDefinitions_registered
    (hadd : env.addConsts values = some extended)
    (hold : ∀ name value, old name = some value → DefinitionRegistered env value ∧ value.name = name)
    (hlookup : installDefinitions old values name = some value) :
    DefinitionRegistered (extended.addDefEqs values) value ∧ value.name = name := by
  unfold installDefinitions at hlookup
  cases hf : values.find? (fun value => value.name == name) with
  | none =>
    have hlookup : old name = some value := by simpa [hf] using hlookup
    have hle : env ≤ extended.addDefEqs values := by
      rw [addDefEqs_as_rules]
      exact (VEnv.addConsts_le hadd).trans VEnv.addDefEqRules_le
    exact ⟨(hold _ _ hlookup).1.mono hle, (hold _ _ hlookup).2⟩
  | some found =>
    simp only [hf, Option.orElse_some, Option.some.injEq] at hlookup
    subst found
    exact ⟨.of_addConsts hadd (List.mem_of_find?_eq_some hf), by simpa using List.find?_some hf⟩

/-- Each definition just installed has a concrete delta pattern and a
finite reduction trace for every valid universe arity. This is the defining
equation part of coverage, derived from insertion rather than assumed. -/
theorem installDefinitions_equationTrace
    (hadd : env.addConsts values = some extended)
    (henv : (extended.addDefEqs values).WF) (hvalue : value ∈ values)
    (hlength : levels.length = value.uvars) :
    NativeReductionTrace (extended.addDefEqs values) U
      (DefinitionPattern (installDefinitions old values)) Γ
      (value.toDefEq.lhs.instL levels) (value.toDefEq.rhs.instL levels) :=
  DefinitionPattern.equation_trace (installDefinitions_lookup hadd hvalue)
    ((DefinitionRegistered.of_addConsts hadd hvalue).closed henv) hlength

end Lean4Lean.VEnv
