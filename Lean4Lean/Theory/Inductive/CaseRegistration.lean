import Lean4Lean.Theory.Typing.EnvLemmas

/-! Registration of declaration-derived case schemas at the constructor
boundary. Freshness follows from the actual installation history. -/

namespace Lean4Lean

private theorem definitions_le (env : VEnv) (cis : List VDefVal) :
    env ≤ env.addDefEqs cis := by
  induction cis generalizing env with
  | nil => exact .rfl
  | cons ci cis ih => exact VEnv.addDefEq_le.trans (ih _)

private theorem declaration_le (H : VDecl.WF env decl env') : env ≤ env' := by
  cases H with
  | «axiom» _ h | «opaque» _ h => exact VEnv.addConst_le h
  | «def» _ h => exact (VEnv.addConst_le h).trans VEnv.addDefEq_le
  | «example» => exact .rfl
  | mutualDef _ h _ => exact (VEnv.addConsts_le h).trans (definitions_le ..)
  | quot _ h =>
    simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := h
    exact (VEnv.addConst_le ha).trans <| (VEnv.addConst_le hb).trans <|
      (VEnv.addConst_le hc).trans <| (VEnv.addConst_le hd).trans VEnv.addDefEq_le
  | induct _ h =>
    cases h with
    | intro _ _ _ h =>
      simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨types, ht, ctors, hc, recs, hr, rfl⟩ := h
      exact (VEnv.addConstVals_le ht).trans <| (VEnv.addConstVals_le hc).trans <|
        VEnv.addProjections_le.trans <| (VEnv.addConstVals_le hr).trans VEnv.addDefEqRules_le

/-- Every registry entry retains its independent formation derivation and
the exact source constants justified when it was registered. -/
theorem VEnv.WF.eliminator_origin {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) :
    ∃ (base : VEnv) (source : VInductDecl) (block : VInductBlock), base.WF ∧ base ≤ env ∧
      schema.Certified base source block ∧
      source.types.head?.map (·.name) = some key ∧
      (∀ value ∈ block.types ++ block.ctors,
        env.constants value.name = some value.toVConstant) := by
  rcases H with ⟨ds, H⟩
  induction H with
  | empty => cases hlookup
  | decl h _ ih =>
    rw [h.eliminators] at hlookup
    obtain ⟨base, source, block, hb, hle, hf, hk, hc⟩ := ih hlookup
    exact ⟨base, source, block, hb, hle.trans (declaration_le h), hf, hk,
      fun value hv => (declaration_le h).constants (hc value hv)⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [VEnv.addProjections_eliminators] at hlookup
    obtain ⟨base, source, block, hb, hle, hf, hk, hc⟩ := ih hlookup
    exact ⟨base, source, block, hb, hle.trans VEnv.addProjections_le, hf, hk,
      fun value hv => VEnv.addProjections_le.constants (hc value hv)⟩
  | inductEliminators hb _ hle hf hk hc _ _ ih =>
    rcases hlookup with ⟨rfl, rfl⟩ | hlookup
    · exact ⟨_, _, _, ⟨_, hb⟩, hle.trans VEnv.addEliminator_le, hf, hk, hc.1⟩
    · obtain ⟨base, source, block, hb, hle, hf, hk, hc⟩ := ih hlookup
      exact ⟨base, source, block, hb, hle.trans VEnv.addEliminator_le, hf, hk, hc⟩

/-- Schema ownership cannot precede the native family it describes. -/
theorem VEnv.WF.eliminator_family_present {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) (hname : name ∈ schema.originalFamilies) :
    ∃ value, env.constants name = some value := by
  obtain ⟨base, source, block, _, _, hformed, _, hconstants⟩ := H.eliminator_origin hlookup
  obtain ⟨expanded, g, auxiliaries, hdata, _, _, hnames⟩ := hformed
  rw [hnames] at hname
  obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hname
  refine ⟨family.toVConstant, hconstants family.toVConstVal ?_⟩
  apply List.mem_append_left
  rw [hdata.types]
  exact List.mem_map.mpr ⟨family, hfamily, rfl⟩

theorem VEnv.WF.eliminator_key_mem {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) : key ∈ schema.originalFamilies := by
  obtain ⟨base, source, block, _, _, hformed, hkey, _⟩ := H.eliminator_origin hlookup
  obtain ⟨expanded, g, auxiliaries, _, _, _, hnames⟩ := hformed
  rw [hnames]
  cases htypes : source.types with
  | nil => simp [htypes] at hkey
  | cons family families =>
    simp only [htypes, List.head?_cons, Option.map_some, Option.some.injEq] at hkey
    simp [← hkey]

/-- Native projection metadata determines one abstract symbol, including
its owner slot, even when the two translations start with separate witnesses. -/
theorem VEnv.WF.eliminator_slot_unique {env : VEnv} {leftIndex rightIndex : Nat} (H : env.WF)
    (hleft : env.eliminators leftKey left) (hright : env.eliminators rightKey right)
    (hleftName : left.originalFamilies[leftIndex]? = some name)
    (hrightName : right.originalFamilies[rightIndex]? = some name) :
    leftKey = rightKey ∧ left = right ∧ leftIndex = rightIndex := by
  obtain ⟨rfl, rfl⟩ := H.eliminators_owner_unique hleft hright
    (List.mem_of_getElem? hleftName) (List.mem_of_getElem? hrightName)
  refine ⟨rfl, rfl, (List.getElem?_inj ?_ (H.eliminators_originalFamilies_nodup hleft)).mp
    (hleftName.trans hrightName.symm)⟩
  exact (List.getElem?_eq_some_iff.mp hleftName).1

namespace InductiveSignature.CaseSchema

/-- The checked source header installation already guarantees freshness of
the schema's key and native owners. Registration asks for no new freshness
certificate from the verifier. -/
theorem Certified.fresh {schema : CaseSchema} {base : VEnv}
    (H : schema.Certified base source block) (hbase : base.WF)
    (hkey : source.types.head?.map (·.name) = some key) : schema.Fresh base key := by
  obtain ⟨expanded, g, auxiliaries, hdata, _, _, hnames⟩ := H
  obtain ⟨types, ctors, htypes, _, _, _⟩ := hdata.sourceWF.2.2.2.2
  have hnew : ∀ name ∈ schema.originalFamilies, base.constants name = none := by
    intro name hname
    rw [hnames] at hname
    obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hname
    exact VEnv.addConstVals_names_fresh htypes family.toVConstVal
      (List.mem_map.mpr ⟨family, hfamily, rfl⟩)
  have hkeyMem : key ∈ schema.originalFamilies := by
    rw [hnames]
    cases ht : source.types with
    | nil => simp [ht] at hkey
    | cons family families =>
      simp only [ht, List.head?_cons, Option.map_some, Option.some.injEq] at hkey
      simp [← hkey]
  constructor
  · intro previous hprevious
    obtain ⟨value, hvalue⟩ := hbase.eliminator_family_present hprevious
      (hbase.eliminator_key_mem hprevious)
    rw [hnew key hkeyMem] at hvalue
    contradiction
  · intro previousKey previous hprevious name hleft hright
    obtain ⟨value, hvalue⟩ := hbase.eliminator_family_present hprevious hright
    rw [hnew name hleft] at hvalue
    contradiction

/-- Constant checking preserves the registry, so freshness transports to
the constructor-complete stage where the case schemas become available. -/
theorem Fresh.of_registry_eq {schema : CaseSchema} {base env : VEnv}
    (H : schema.Fresh base key) (heq : env.eliminators = base.eliminators) :
    schema.Fresh env key := by
  unfold Fresh at *
  rw [heq]
  exact H

/-- Register all case schemas immediately after source headers and
constructors. The finite formation witness suffices; generated concrete
recursors and their equations have not been installed or assumed correct. -/
theorem Certified.register_after_constructors {schema : CaseSchema} {base envTypes envCtors : VEnv}
    (H : schema.Certified base source block) (hbase : base.WF)
    (hkey : source.types.head?.map (·.name) = some key)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    (envCtors.addEliminator key schema).WF := by
  have hctorsWF : envCtors.WF := by
    obtain ⟨expanded, g, auxiliaries, hdata, _, _⟩ := H
    obtain ⟨types, ctors, ht, hc, htypesWF, hctorsWF⟩ := hdata.sourceWF.2.2.2.2
    rw [hdata.types] at htypes
    rw [htypes] at ht
    cases ht
    rw [hdata.ctors] at hctors
    apply VEnv.WF.addConstVals (cis := source.constructorConstants) _ hctorsWF hctors
    apply VEnv.WF.addConstVals hbase _ htypes
    intro value hvalue
    obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hvalue
    exact htypesWF family hfamily
  have hfresh := (H.fresh hbase hkey).of_registry_eq
    ((VEnv.addConstVals_eliminators hctors).trans (VEnv.addConstVals_eliminators htypes))
  apply hbase.inductEliminators hctorsWF
    ((VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)) H hkey _
    ((VEnv.addConstVals_defeqs hctors).trans (VEnv.addConstVals_defeqs htypes)) hfresh
  intro value hvalue
  rcases List.mem_append.mp hvalue with hvalue | hvalue
  · exact (VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hvalue)
  · exact VEnv.addConstVals_get hctors hvalue

end InductiveSignature.CaseSchema

end Lean4Lean
