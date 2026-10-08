import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Theory.Inductive.CompilationLemmas

/-! Registration of declaration-derived case schemas at the constructor
boundary. Freshness follows from the actual installation history.

Registration also carries the certified fact
`CaseSchema.ProjNamesRegistered` (the schema projects only out of structures
registered at registration time). This is a new obligation for producers of a
registration (`register_after_constructors`, `CheckingEnv.Valid.registerCases`
take it as a hypothesis); it is exposed for every registry entry by
`VEnv.WF.eliminatorsProjNamesRegistered`. -/

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
    | intro _ _ _ _ h => exact VInductBlock.install_base_le h

theorem VDecl.WF.le (H : VDecl.WF env decl env') : env ≤ env' := declaration_le H

namespace VEnv.InductRegistration

theorem le (R : VEnv.InductRegistration env decl key schema env') : env ≤ env' := by
  obtain ⟨_, _, _, _, _, _, hinstall, _⟩ := R
  exact VInductBlock.install_base_le hinstall

/-- The registered block's families and constructors are installed. -/
theorem constants (R : VEnv.InductRegistration env decl key schema env') :
    ∃ block : VInductBlock, schema.Certified env decl block ∧
      decl.types.head?.map (·.name) = some key ∧
      ∀ value ∈ block.types ++ block.ctors, env'.constants value.name = some value.toVConstant := by
  obtain ⟨block, envTypes, envCtors, _, _, _, hinstall, ht, hc, _, hcert, hkey, _⟩ := R
  refine ⟨block, hcert, hkey, fun value hv => ?_⟩
  have hle := VInductBlock.install_ctors_le hinstall ht hc
  rcases List.mem_append.mp hv with hv | hv
  · exact hle.constants ((VEnv.addConstVals_le hc).constants (VEnv.addConstVals_get ht hv))
  · exact hle.constants (VEnv.addConstVals_get hc hv)

theorem projNames (R : VEnv.InductRegistration env decl key schema env') :
    schema.ProjNamesRegistered env' key := by
  obtain ⟨block, envTypes, envCtors, _, _, _, hinstall, ht, hc, _, _, _, hprojs, _⟩ := R
  exact hprojs.mono (VInductBlock.install_ctors_le hinstall ht hc)

end VEnv.InductRegistration

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
  | decl h hds ih =>
    rcases h.eliminators_iff.mp hlookup with ⟨source, -, R⟩ | hlookup
    · obtain ⟨block, hcert, hkey, hc⟩ := R.constants
      exact ⟨_, source, block, ⟨_, hds⟩, R.le, hcert, hkey, hc⟩
    obtain ⟨base, source, block, hb, hle, hf, hk, hc⟩ := ih hlookup
    exact ⟨base, source, block, hb, hle.trans (declaration_le h), hf, hk,
      fun value hv => (declaration_le h).constants (hc value hv)⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [VEnv.addProjections_eliminators] at hlookup
    obtain ⟨base, source, block, hb, hle, hf, hk, hc⟩ := ih hlookup
    exact ⟨base, source, block, hb, hle.trans VEnv.addProjections_le, hf, hk,
      fun value hv => VEnv.addProjections_le.constants (hc value hv)⟩
  | inductEliminators hb _ hle hf hk hc _ _ _ ih =>
    rcases hlookup with ⟨rfl, rfl⟩ | hlookup
    · exact ⟨_, _, _, ⟨_, hb⟩, hle.trans VEnv.addEliminator_le, hf, hk, hc.1⟩
    · obtain ⟨base, source, block, hb, hle, hf, hk, hc⟩ := ih hlookup
      exact ⟨base, source, block, hb, hle.trans VEnv.addEliminator_le, hf, hk, hc⟩

/-- Every registry entry retains the header agreement certified at its registration. -/
theorem VEnv.WF.eliminator_headerAgreement {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) :
    ∃ (base : VEnv) (source : VInductDecl) (block : VInductBlock), base.WF ∧ base ≤ env ∧
      schema.Certified base source block ∧ schema.HeaderAgreement base source ∧
      (∀ value ∈ block.types ++ block.ctors,
        env.constants value.name = some value.toVConstant) := by
  rcases H with ⟨ds, H⟩
  induction H with
  | empty => cases hlookup
  | decl h hds ih =>
    rcases h.eliminators_iff.mp hlookup with ⟨source, -, R⟩ | hlookup
    · have hle := R.le
      obtain ⟨block, hcert, hkey, hc⟩ := R.constants
      obtain ⟨block', -, -, -, -, -, hinstall', -, -, -, hcert', -, -, hhdr⟩ := R
      exact ⟨_, source, block, ⟨_, hds⟩, hle, hcert, hhdr, hc⟩
    obtain ⟨base, source, block, hb, hle, hf, hh, hc⟩ := ih hlookup
    exact ⟨base, source, block, hb, hle.trans (declaration_le h), hf, hh,
      fun value hv => (declaration_le h).constants (hc value hv)⟩
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [VEnv.addProjections_eliminators] at hlookup
    obtain ⟨base, source, block, hb, hle, hf, hh, hc⟩ := ih hlookup
    exact ⟨base, source, block, hb, hle.trans VEnv.addProjections_le, hf, hh,
      fun value hv => VEnv.addProjections_le.constants (hc value hv)⟩
  | inductEliminators hb _ hle hf hk hc _ _ _ ih =>
    rcases hlookup with ⟨rfl, rfl⟩ | hlookup
    · exact ⟨_, _, _, ⟨_, hb⟩, hle.trans VEnv.addEliminator_le, hf, hc.2.2.2.2, hc.1⟩
    · obtain ⟨base, source, block, hb, hle, hf, hh, hc⟩ := ih hlookup
      exact ⟨base, source, block, hb, hle.trans VEnv.addEliminator_le, hf, hh, hc⟩

/-- Schema ownership cannot precede the native family it describes. -/
theorem VEnv.WF.eliminator_family_present {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) (hname : name ∈ schema.originalFamilies) :
    ∃ value, env.constants name = some value := by
  obtain ⟨base, source, block, _, _, hformed, _, hconstants⟩ := H.eliminator_origin hlookup
  obtain ⟨expanded, auxiliaries, hdata, _, _, hnames, hdisj⟩ := hformed
  rw [hnames] at hname
  obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hname
  refine ⟨family.toVConstant, hconstants family.toVConstVal ?_⟩
  apply List.mem_append_left
  rw [hdata.types]
  exact List.mem_map.mpr ⟨family, hfamily, rfl⟩

theorem VEnv.WF.eliminator_key_mem {env : VEnv} (H : env.WF)
    (hlookup : env.eliminators key schema) : key ∈ schema.originalFamilies := by
  obtain ⟨base, source, block, _, _, hformed, hkey, _⟩ := H.eliminator_origin hlookup
  obtain ⟨expanded, auxiliaries, _, _, _, hnames, hdisj⟩ := hformed
  rw [hnames]
  cases htypes : source.types with
  | nil => simp [htypes] at hkey
  | cons family families =>
    simp only [htypes, List.head?_cons, Option.map_some, Option.some.injEq] at hkey
    simp [← hkey]

/-- Every registered case schema projects only out of structures registered in
the environment: the fact certified at registration, transported along the
later extensions. -/
theorem VEnv.WF.eliminatorsProjNamesRegistered {env : VEnv} (H : env.WF) :
    ∀ block schema, env.eliminators block schema → schema.ProjNamesRegistered env block := by
  intro block schema hlookup
  rcases H with ⟨ds, H⟩
  induction H with
  | empty => cases hlookup
  | decl h _ ih =>
    rcases h.eliminators_iff.mp hlookup with ⟨source, -, R⟩ | hlookup
    · exact R.projNames
    exact (ih hlookup).mono (declaration_le h)
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [VEnv.addProjections_eliminators] at hlookup
    exact (ih hlookup).mono VEnv.addProjections_le
  | inductEliminators _ _ _ _ _ hc _ _ _ ih =>
    rcases hlookup with ⟨rfl, rfl⟩ | hlookup
    · exact hc.2.2.1.mono VEnv.addEliminator_le
    · exact (ih hlookup).mono VEnv.addEliminator_le

namespace InductiveSignature.CaseSchema

/-- The checked source header installation already guarantees freshness of
the schema's key and native owners. Registration asks for no new freshness
certificate from the verifier. -/
theorem Certified.fresh {schema : CaseSchema} {base : VEnv}
    (H : schema.Certified base source block) (hbase : base.WF)
    (hkey : source.types.head?.map (·.name) = some key) : schema.Fresh base key := by
  obtain ⟨expanded, auxiliaries, hdata, _, _, hnames, hdisj⟩ := H
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

theorem view_constructor_names (schema : CaseSchema)
    (owner : Fin schema.signature.families.size) :
    (schema.view owner).constructors.toList.map (·.name) =
      (schema.signature.declarationFamily owner).ctors.map (·.name) := by
  simp only [view, List.toList_toArray, declarationFamily, List.map_filterMap]
  apply congrArg (List.filterMap · schema.signature.constructors.toList)
  funext ctor
  by_cases ho : ctor.owner = owner
  · simp [ho, caseConstructor]
  · have hv : ctor.owner.val ≠ owner.val := fun hv => ho (Fin.ext hv)
    simp [ho, hv]

/-- A certified schema is compatible with the structures registered by its own
declaration and by its base: a structure of the declaration has exactly the
declaration's single constructor, and a structure of the base is not an original
family of the schema, since those are fresh in the base. -/
theorem Certified.structCompat {schema : CaseSchema} {base envTypes envCtors : VEnv}
    (H : schema.Certified base source block) (hbase : base.WF)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    schema.StructCompat (envCtors.addProjections block.projections) := by
  obtain ⟨expanded, auxiliaries, hdata, _, _, hnames, _⟩ := H
  intro s info hproj owner hname
  rw [hnames, List.getElem?_map] at hname
  obtain ⟨family, hfamily, rfl⟩ := Option.map_eq_some_iff.mp hname
  have hmem : family ∈ source.types := List.mem_of_getElem? hfamily
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hfamily
  rcases VEnv.addProjections_iff.mp hproj with ⟨entry, hentry, hentryName, rfl⟩ | hold
  · rw [hdata.projections] at hentry
    obtain ⟨type, htype, ctor, hctorsType, rfl⟩ := VInductDecl.projectionEntries_origin hentry
    have heq : family = type :=
      VInductDecl.type_eq_of_mem_name hdata.sourceWF.2.1 hmem htype hentryName
    subst heq
    obtain ⟨_, direct, _, _, _, hfamilies⟩ := hdata.correspondence
    have hlen := Lean4Lean.List.Forall₂.length_eq hfamilies
    have hdecl : owner.val < schema.signature.declaration.types.length := by
      simp [declaration]
    have hrel := Lean4Lean.List.Forall₂.getElem_of hfamilies owner.val hdecl
      (by rw [← hlen]; exact hdecl)
    have hfam : schema.signature.declaration.types[owner.val] =
        schema.signature.declarationFamily owner := by
      simp [declaration, declarationFamily]
    rw [hfam, List.getElem_append_left hlt, hget] at hrel
    rw [view_constructor_names, ctorNames_eq_of_forall₂ hrel.constructors (fun _ _ h => h.1),
      hctorsType]
    rfl
  · exfalso
    rw [VEnv.addConstVals_projections hctors, VEnv.addConstVals_projections htypes] at hold
    obtain ⟨c, hc⟩ := hbase.ordered.projectionConstant hold
    have hfresh := VEnv.addConstVals_names_fresh htypes family.toVConstVal (by
      rw [hdata.types]
      exact List.mem_map.mpr ⟨family, hmem, rfl⟩)
    have hfresh' : base.constants family.name = none := hfresh
    rw [hfresh'] at hc
    contradiction

/-- Constant checking preserves the registry, so freshness transports to
the constructor-complete stage where the case schemas become available. -/
theorem Fresh.of_registry_eq {schema : CaseSchema} {base env : VEnv}
    (H : schema.Fresh base key) (heq : env.eliminators = base.eliminators) :
    schema.Fresh env key := by
  unfold Fresh at *
  rw [heq]
  exact H

end InductiveSignature.CaseSchema

namespace VEnv.InductRegistration
open InductiveSignature

theorem fresh (R : VEnv.InductRegistration env decl key schema env') (henv : env.WF) :
    schema.Fresh env key := by
  obtain ⟨block, _, _, _, _, _, _, _, _, _, hcert, hkey, _⟩ := R
  exact hcert.fresh henv hkey

/-- One declaration step registers one eliminator. -/
theorem unique (R : VEnv.InductRegistration env decl key schema env') (henv : env.WF)
    (R' : VEnv.InductRegistration env decl' key' schema' env') :
    key = key' ∧ schema = schema' := by
  have hfresh := R.fresh henv
  obtain ⟨block', _, _, _, _, _, hinstall', _, _, hE', _⟩ := R'
  obtain ⟨block, _, _, _, _, _, hinstall, _, _, hE, _⟩ := R
  have h1 : env'.eliminators key schema := by
    rw [VInductBlock.install_eliminators_iff hinstall, hE]; simp
  rw [VInductBlock.install_eliminators_iff hinstall', hE'] at h1
  rcases h1 with h1 | h1
  · simp only [List.mem_singleton, Prod.mk.injEq] at h1; exact h1
  · exact (hfresh.1 _ h1).elim

end VEnv.InductRegistration

/-- Fresh registration fixes a schema for every abstract block key. -/
theorem VEnv.WF.eliminators_unique (H : VEnv.WF env)
    (hleft : env.eliminators key left) (hright : env.eliminators key right) :
    left = right := by
  rcases H with ⟨ds, H⟩
  induction H with
  | empty => cases hleft
  | decl h hds ih =>
    have henv : VEnv.WF _ := ⟨_, hds⟩
    rcases h.eliminators_iff.mp hleft with ⟨source, rfl, R⟩ | hleft <;>
      rcases h.eliminators_iff.mp hright with ⟨source', hs, R'⟩ | hright
    · cases hs; exact (R.unique henv R').2
    · exact ((R.fresh henv).1 _ hright).elim
    · exact ((R'.fresh henv).1 _ hleft).elim
    · exact ih hleft hright
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [VEnv.addProjections_eliminators] at hleft hright
    exact ih hleft hright
  | inductEliminators _ _ _ _ _ _ hfresh _ _ ih =>
    rcases hleft with ⟨rfl, rfl⟩ | hleft
    · rcases hright with ⟨_, rfl⟩ | hright
      · rfl
      · exact (hfresh.1 _ hright).elim
    · rcases hright with ⟨rfl, rfl⟩ | hright
      · exact (hfresh.1 _ hleft).elim
      · exact ih hleft hright

theorem VEnv.WF.eliminators_originalFamilies_nodup (H : VEnv.WF env)
    (hlookup : env.eliminators key schema) : schema.originalFamilies.Nodup := by
  rcases H with ⟨ds, H⟩
  induction H with
  | empty => cases hlookup
  | decl h _ ih =>
    rcases h.eliminators_iff.mp hlookup with ⟨source, -, R⟩ | hlookup
    · obtain ⟨block, hcert, -⟩ := R.constants
      exact hcert.originalFamilies_nodup
    exact ih hlookup
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [VEnv.addProjections_eliminators] at hlookup
    exact ih hlookup
  | inductEliminators _ _ _ hformed _ _ _ _ _ ih =>
    rcases hlookup with ⟨_, rfl⟩ | hlookup
    · exact hformed.originalFamilies_nodup
    · exact ih hlookup

/-- A native family has one registered block and schema. In particular,
typed projection translation cannot choose another block's owner slot. -/
theorem VEnv.WF.eliminators_owner_unique (H : VEnv.WF env)
    (hleft : env.eliminators leftKey left) (hright : env.eliminators rightKey right)
    (hnameLeft : name ∈ left.originalFamilies)
    (hnameRight : name ∈ right.originalFamilies) : leftKey = rightKey ∧ left = right := by
  rcases H with ⟨ds, H⟩
  induction H with
  | empty => cases hleft
  | decl h hds ih =>
    have henv : VEnv.WF _ := ⟨_, hds⟩
    rcases h.eliminators_iff.mp hleft with ⟨source, rfl, R⟩ | hleft <;>
      rcases h.eliminators_iff.mp hright with ⟨source', hs, R'⟩ | hright
    · cases hs; exact R.unique henv R'
    · exact ((R.fresh henv).2 _ _ hright hnameLeft hnameRight).elim
    · exact ((R'.fresh henv).2 _ _ hleft hnameRight hnameLeft).elim
    · exact ih hleft hright
  | inductProjections _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
    simp only [VEnv.addProjections_eliminators] at hleft hright
    exact ih hleft hright
  | inductEliminators _ _ _ _ _ _ hfresh _ _ ih =>
    rcases hleft with ⟨rfl, rfl⟩ | hleft
    · rcases hright with ⟨rfl, rfl⟩ | hright
      · exact ⟨rfl, rfl⟩
      · exact (hfresh.2 _ _ hright hnameLeft hnameRight).elim
    · rcases hright with ⟨rfl, rfl⟩ | hright
      · exact (hfresh.2 _ _ hleft hnameRight hnameLeft).elim
      · exact ih hleft hright


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

/-- Register all case schemas immediately after source headers and
constructors. The finite formation witness suffices; generated concrete
recursors and their equations have not been installed or assumed correct. -/
theorem Certified.register_after_constructors {schema : CaseSchema} {base envTypes envCtors : VEnv}
    (H : schema.Certified base source block) (hbase : base.WF)
    (hkey : source.types.head?.map (·.name) = some key)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors)
    (hprojs : schema.ProjNamesRegistered envCtors key)
    (hheader : schema.HeaderAgreement base source) :
    (envCtors.addEliminator key schema).WF := by
  have hcompat : schema.StructCompat envCtors :=
    StructCompat.of_projections (H.structCompat hbase htypes hctors)
      VEnv.addProjections_le.projections
  have hctorsWF : envCtors.WF := by
    obtain ⟨expanded, auxiliaries, hdata, _, _⟩ := H
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
  have hcoherent : source.ProjectionsCoherent envCtors := by
    intro type htype info hinfo
    exfalso
    rw [VEnv.addConstVals_projections hctors, VEnv.addConstVals_projections htypes] at hinfo
    obtain ⟨ci, hci⟩ := hbase.ordered.projectionConstant hinfo
    obtain ⟨expanded, auxiliaries, hdata, _, _⟩ := H
    have hmem : type.toVConstVal ∈ block.types := by
      rw [hdata.types]; exact List.mem_map.mpr ⟨type, htype, rfl⟩
    have hfresh := VEnv.addConstVals_names_fresh htypes _ hmem
    change base.constants type.name = none at hfresh
    rw [hfresh] at hci
    cases hci
  apply hbase.inductEliminators hctorsWF
    ((VEnv.addConstVals_le htypes).trans (VEnv.addConstVals_le hctors)) H hkey _
    ((VEnv.addConstVals_defeqs hctors).trans (VEnv.addConstVals_defeqs htypes)) hprojs
    hcoherent hheader hfresh hcompat
  intro value hvalue
  rcases List.mem_append.mp hvalue with hvalue | hvalue
  · exact (VEnv.addConstVals_le hctors).constants (VEnv.addConstVals_get htypes hvalue)
  · exact VEnv.addConstVals_get hctors hvalue

end InductiveSignature.CaseSchema

namespace VInductBlock
open InductiveSignature

/-- The constructor stage of a declaration installed from its checked source is well formed. -/
theorem _root_.Lean4Lean.VInductDecl.SourceWF.ctorsWF {base envTypes envCtors : VEnv}
    {decl : VInductDecl} (hsource : decl.SourceWF base) (hbase : base.WF)
    (htypes : base.addConstVals decl.typeConstants = some envTypes)
    (hctors : envTypes.addConstVals decl.constructorConstants = some envCtors) :
    envCtors.WF := by
  obtain ⟨types, ctors, ht, hc, htypesWF, hctorsWF⟩ := hsource.2.2.2.2
  rw [htypes] at ht
  cases ht
  apply VEnv.WF.addConstVals (cis := decl.constructorConstants) _ hctorsWF hctors
  apply VEnv.WF.addConstVals hbase _ htypes
  intro value hvalue
  obtain ⟨family, hfamily, rfl⟩ := List.mem_map.mp hvalue
  exact htypesWF family hfamily

/-- The constructor stage of a block with its certified eliminators is well formed. -/
theorem EliminatorsWF.elimWF {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : VInductBlock.EliminatorsWF base decl block) (hbase : base.WF)
    (hsource : decl.SourceWF base) (htypesSource : block.types = decl.typeConstants)
    (hctorsSource : block.ctors = decl.constructorConstants)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    (envCtors.addEliminators block.eliminators).WF := by
  obtain ⟨envTypes', envCtors', ht', hc', H⟩ := H
  cases htypes.symm.trans ht'
  cases hctors.symm.trans hc'
  rcases H with ⟨hE, -⟩ | ⟨key, schema, hE, hcert, hkey, hprojs, hhdr⟩
  · rw [hE]
    exact hsource.ctorsWF hbase (htypesSource ▸ htypes) (hctorsSource ▸ hctors)
  · rw [hE]
    exact hcert.register_after_constructors hbase hkey htypes hctors hprojs hhdr

/-- The projection stage of a certified block is well formed. -/
theorem EliminatorsWF.projectionsWF {base envTypes envCtors : VEnv} {decl : VInductDecl}
    {block : VInductBlock} (H : VInductBlock.EliminatorsWF base decl block) (hbase : base.WF)
    (hdecl : decl.WF base) (hcompile : decl.CompilesTo base block)
    (htypes : base.addConstVals block.types = some envTypes)
    (hctors : envTypes.addConstVals block.ctors = some envCtors) :
    ((envCtors.addEliminators block.eliminators).addProjections block.projections).WF := by
  have ht' : base.addConstVals decl.typeConstants = some envTypes := by
    simpa only [hcompile.types] using htypes
  have helimWF := H.elimWF hbase hdecl.1 hcompile.types hcompile.ctors htypes hctors
  obtain ⟨_, _, _, _, H⟩ := H
  rcases H with ⟨-, hP⟩ | ⟨key, schema, hE, hcert, hkey, _, hhdr⟩
  · rw [hP]; exact helimWF
  have parameters := hdecl.sourceParameterWF ht'
  exact VEnv.WF.inductProjections hbase helimWF ⟨key, schema, hE, hcert, hkey, hhdr⟩
    hcompile.sourceNames hdecl.1.originalTypes hdecl.1.2.2.2.1 (hdecl.1.constructorsWF_at ht')
    parameters parameters.rawCtorShape hcompile.types hcompile.ctors
    hcompile.projections htypes hctors

end VInductBlock
end Lean4Lean

namespace Lean4Lean
open InductiveSignature

theorem VInductBlock.install_projections_iff {env env' : VEnv} {block : VInductBlock}
    (H : VInductBlock.install env block = some env') :
    env'.projections name info ↔
      (∃ entry ∈ block.projections, name = entry.typeName ∧ info = entry.info) ∨
        env.projections name info := by
  obtain ⟨_, _, _, ht, hc, hr, rfl⟩ := VInductBlock.install_stages H
  rw [VEnv.addDefEqRules_projections, VEnv.addConstVals_projections hr, VEnv.addProjections_iff,
    VEnv.addEliminators_projections, VEnv.addConstVals_projections hc,
    VEnv.addConstVals_projections ht]

/-- A certified eliminator covers each projection entry of its block. -/
private theorem covered_of_certified {decl : VInductDecl} {block : VInductBlock}
    {schema : CaseSchema} {base : VEnv} (hcert : schema.Certified base decl block)
    (hprojections : block.projections = decl.projectionEntries)
    {entry : VProjectionEntry} (hentry : entry ∈ block.projections) :
    entry.typeName ∈ schema.originalFamilies := by
  rw [hprojections] at hentry
  obtain ⟨type, htype, ctor, _, rfl⟩ := VInductDecl.projectionEntries_origin hentry
  obtain ⟨_, _, _, _, _, hnames, _⟩ := hcert
  rw [hnames]
  exact List.mem_map.mpr ⟨type, htype, rfl⟩

/-- **Every registered structure has a registered case eliminator.** Projections are only
registered together with, and after, the certified case eliminator of their declaration. -/
theorem VEnv.WF.projections_eliminated {env : VEnv} (H : env.WF)
    (hp : env.projections name info) :
    ∃ key schema, env.eliminators key schema ∧ name ∈ schema.originalFamilies := by
  rcases H with ⟨ds, H⟩
  induction H generalizing name info with
  | empty => cases hp
  | decl h _ ih =>
    have hle := VDecl.WF.le h
    cases h with
    | «axiom» _ hadd | «opaque» _ hadd =>
      rw [VEnv.addConst_projections hadd] at hp
      obtain ⟨k, s, hs, hn⟩ := ih hp
      exact ⟨k, s, hle.eliminators hs, hn⟩
    | «def» _ hadd =>
      obtain ⟨k, s, hs, hn⟩ := ih (by
        have hp' := hp
        simp only [VEnv.addDefEq] at hp'
        rwa [VEnv.addConst_projections hadd] at hp')
      exact ⟨k, s, hle.eliminators hs, hn⟩
    | «example» => exact ih hp
    | mutualDef _ hadd _ =>
      rw [VEnv.addDefEqs_projections, VEnv.addConsts_projections hadd] at hp
      obtain ⟨k, s, hs, hn⟩ := ih hp
      exact ⟨k, s, hle.eliminators hs, hn⟩
    | quot _ hadd =>
      rw [VEnv.addQuot_projections hadd] at hp
      obtain ⟨k, s, hs, hn⟩ := ih hp
      exact ⟨k, s, hle.eliminators hs, hn⟩
    | induct _ hadd =>
      cases hadd with
      | intro _ hcompile _ helim hinstall =>
        rcases (VInductBlock.install_projections_iff hinstall).mp hp with
          ⟨entry, hentry, rfl, rfl⟩ | hold
        · obtain ⟨_, _, _, _, helim⟩ := helim
          rcases helim with ⟨-, hP⟩ | ⟨key, schema, hE, hcert, _⟩
          · rw [hP] at hentry; cases hentry
          refine ⟨key, schema, ?_, covered_of_certified hcert hcompile.projections hentry⟩
          rw [VInductBlock.install_eliminators_iff hinstall, hE]
          simp
        · obtain ⟨k, s, hs, hn⟩ := ih hold
          exact ⟨k, s, hle.eliminators hs, hn⟩
  | inductEliminators _ _ _ _ _ _ _ _ _ ih =>
    obtain ⟨k, s, hs, hn⟩ := ih hp
    exact ⟨k, s, .inr hs, hn⟩
  | inductProjections _ _ hcert _ _ _ _ _ _ _ _ hprojections _ _ _ ih =>
    rw [VEnv.addProjections_iff] at hp
    rcases hp with ⟨entry, hentry, rfl, rfl⟩ | hold
    · obtain ⟨key, schema, hE, hcertS, _⟩ := hcert
      refine ⟨key, schema, ?_, covered_of_certified hcertS hprojections hentry⟩
      rw [VEnv.addProjections_eliminators, VEnv.addEliminators_iff, hE]
      simp
    · obtain ⟨k, s, hs, hn⟩ := ih hold
      exact ⟨k, s, by rw [VEnv.addProjections_eliminators]; exact hs, hn⟩

end Lean4Lean
