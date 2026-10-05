import Lean4Lean.Theory.Typing.NativeRecursorRegistration

/-! Native metadata is installed from the same finite instance and abstract
schema as the actual recursor block. Registry lookup adds no semantic data. -/

namespace Lean4Lean.InductiveSignature.NativeRecursorData

/-- One occurrence descriptor for each family of the shared native instance. -/
def compilationEntries (key : Name) (source : VInductDecl) (s : InductiveSignature)
    (auxiliaries : List ContainerSpecialization) (g : Instance s) : List NativeRecursorData :=
  (List.finRange s.families.size).map fun owner =>
    ofInstance key (CaseSchema.ofCompilation source s auxiliaries) g owner

/-- Extend the metadata table with the entries of one installed block. -/
def installEntries (old : Name → Option NativeRecursorData) (entries : List NativeRecursorData)
    (name : Name) : Option NativeRecursorData :=
  (entries.find? (fun data => data.name == name)).orElse (fun _ => old name)

end Lean4Lean.InductiveSignature.NativeRecursorData

namespace Lean4Lean.VEnv
open InductiveSignature NativeRecursorData
variable {block : VInductBlock} {name : Name}

/-- Every generated family descriptor has concrete whole-block provenance. -/
theorem NativeRecursorRegistered.ofCompilation
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hprior : CertifiedSpecializations base auxiliaries)
    (hbase : base ≤ installBase)
    (hinstall : block.install installBase = some installed) (hle : installed ≤ env)
    (owner : Fin s.families.size) :
    NativeRecursorRegistered env
      (ofInstance key (CaseSchema.ofCompilation source s auxiliaries) g owner) :=
  ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, hprior, hbase, rfl, rfl, rfl, rfl, rfl, hinstall, hle⟩

theorem NativeRecursorRegistered.compilationEntries
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hprior : CertifiedSpecializations base auxiliaries)
    (hbase : base ≤ installBase)
    (hinstall : block.install installBase = some installed) (hle : installed ≤ env)
    (hentry : data ∈ compilationEntries key source s auxiliaries g) :
    NativeRecursorRegistered env data := by
  obtain ⟨owner, _, rfl⟩ := List.mem_map.mp hentry
  exact .ofCompilation hdata hprior hbase hinstall hle owner

/-- The metadata table has exactly the names of the restored installed
recursors, in the same family order. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.nativeEntries_names
    (hdata : CompilationData base source expanded s g auxiliaries block) :
    (compilationEntries key source s auxiliaries g).map (·.name) =
      block.recursors.map (·.name) := by
  have hrestored := List.mapM_eq_some.mp hdata.recursors
  have hn : g.recursors.map (fun rec =>
      (compilationRestoration source auxiliaries).recursorName rec.name) =
      block.recursors.map (·.name) := by
    generalize g.recursors = originals at hrestored ⊢
    generalize block.recursors = actuals at hrestored ⊢
    induction hrestored with
    | nil => rfl
    | cons h hs ih =>
      simp only [Restoration.recursor, bind, Option.bind_eq_some_iff] at h
      obtain ⟨type, _, he⟩ := h
      cases he
      exact congrArg (List.cons _) ih
  rw [← hn]
  simp only [compilationEntries, List.map_map, Function.comp_def, ofInstance, name,
    CaseSchema.ofCompilation, Instance.recursors, Instance.recursor]
  simp only [hdata.recursorNames]

/-- Successful whole-block installation makes every new metadata name
fresh in the previous environment. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.nativeEntries_fresh
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hinstall : block.install installBase = some installed)
    (hentry : data ∈ compilationEntries key source s auxiliaries g) :
    installBase.constants data.name = none := by
  have hname : data.name ∈ block.recursors.map (·.name) := by
    rw [← hdata.nativeEntries_names (key := key)]
    exact List.mem_map.mpr ⟨data, hentry, rfl⟩
  obtain ⟨rec, hrec, heq⟩ := List.mem_map.mp hname
  simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at hinstall
  obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hinstall
  have hf := VEnv.addConstVals_names_fresh hr rec hrec
  have hle : installBase ≤ ctors.addProjections block.projections := ((VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)).trans
    (VEnv.addProjections_le)
  cases hv : installBase.constants data.name with
  | none => rfl
  | some value =>
    have hsome := hle.constants hv
    rw [← heq] at hsome
    rw [hf] at hsome
    contradiction


/-- Restoration succeeds for every selected native family because the
entire restored recursor list was actually installed. -/
theorem NativeRecursorRegistered.recursorType_exists
    (H : NativeRecursorRegistered env data) : ∃ type, data.recursorType = some type := by
  obtain ⟨base, installBase, source, expanded, g, auxiliaries, block, installed,
    hdata, _, _, hr, _, hu, hl, ht, hi, he⟩ := H
  have hinstance : data.nativeInstance = g := by
    cases g with
    | mk U levels target recNames =>
      simp only [nativeInstance, Instance.mk.injEq]
      exact ⟨hu, hl, ht, funext fun owner => (hdata.recursorNames owner).symm⟩
  have hgenerated : g.recursor data.owner ∈ g.recursors :=
    List.mem_map.mpr ⟨data.owner, List.mem_finRange _, rfl⟩
  obtain ⟨actual, _, hrestore⟩ := Lean4Lean.List.Forall₂.forall_exists_l
    (List.mapM_eq_some.mp hdata.recursors) _ hgenerated
  simp only [Restoration.recursor, Instance.recursor, bind, Option.bind_eq_some_iff] at hrestore
  obtain ⟨type, htype, _⟩ := hrestore
  exact ⟨type, by simpa only [NativeRecursorData.recursorType, hinstance, hr] using htype⟩

theorem NativeRecursorRegistered.constant_exists
    (H : NativeRecursorRegistered env data) :
    ∃ value, env.constants data.name = some value := by
  obtain ⟨type, htype⟩ := H.recursorType_exists
  exact ⟨_, H.recursorType htype⟩

theorem _root_.Lean4Lean.InductiveSignature.CompilationData.nativeEntries_nodup
    (hdata : CompilationData base source expanded s g auxiliaries block) :
    ((compilationEntries key source s auxiliaries g).map (·.name)).Nodup := by
  rw [hdata.nativeEntries_names]
  have hh := hdata.names
  simp only [List.map_append, List.nodup_append] at hh
  exact hh.2.1

private theorem nativeEntries_find (entries : List NativeRecursorData)
    (hnodup : (entries.map (·.name)).Nodup) (hmem : data ∈ entries) :
    entries.find? (fun value => value.name == data.name) = some data := by
  induction entries with
  | nil => cases hmem
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hmem with he | hm
    · subst head
      simp
    · have hne : head.name ≠ data.name := by
        intro he
        apply hnodup.1
        exact List.mem_map.mpr ⟨data, hm, he.symm⟩
      simp only [List.find?_cons, beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true, ↓reduceIte]
      exact ih hnodup.2 hm

/-- Every newly installed family remains individually addressable by its
actual restored name. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.nativeEntries_lookup
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hmem : data ∈ compilationEntries key source s auxiliaries g) :
    NativeRecursorData.installEntries old (compilationEntries key source s auxiliaries g)
      data.name = some data := by
  unfold NativeRecursorData.installEntries
  rw [nativeEntries_find _ hdata.nativeEntries_nodup hmem]
  rfl

/-- Installing a new block cannot replace metadata of an earlier
registered native recursor: its concrete constant name is already occupied. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.nativeEntries_preserves
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hinstall : block.install installBase = some installed)
    (hregistered : NativeRecursorRegistered installBase previous)
    (hold : old previous.name = some previous) :
    NativeRecursorData.installEntries old (compilationEntries key source s auxiliaries g)
      previous.name = some previous := by
  unfold NativeRecursorData.installEntries
  cases hf : (compilationEntries key source s auxiliaries g).find?
      (fun data => data.name == previous.name) with
  | none => exact hold
  | some fresh =>
    have hname : fresh.name = previous.name := by simpa using List.find?_some hf
    have hnone := hdata.nativeEntries_fresh hinstall (List.mem_of_find?_eq_some hf)
    obtain ⟨value, hsome⟩ := hregistered.constant_exists
    rw [hname, hsome] at hnone
    contradiction

/-- Lookup in an extended table is justified by an actual earlier
registration or one of the new finite block entries. -/
theorem NativeRecursorRegistered.installEntries
    (hold : ∀ name data, old name = some data → NativeRecursorRegistered env data ∧ data.name = name)
    (hnew : ∀ data ∈ entries, NativeRecursorRegistered env data)
    (hlookup : NativeRecursorData.installEntries old entries name = some data) :
    NativeRecursorRegistered env data ∧ data.name = name := by
  unfold NativeRecursorData.installEntries at hlookup
  cases hf : entries.find? (fun data => data.name == name) with
  | none => exact hold _ _ (by simpa [hf] using hlookup)
  | some value =>
    simp only [hf, Option.orElse_some, Option.some.injEq] at hlookup
    subst value
    exact ⟨hnew data (List.mem_of_find?_eq_some hf), by simpa using List.find?_some hf⟩

/-- Concrete installation supplies the `recursorData_registered` part of
`Params` for the extended table, including every earlier entry. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.installNativeRegistry
    (hdata : CompilationData base source expanded s g auxiliaries block)
    (hprior : CertifiedSpecializations base auxiliaries)
    (hbase : base ≤ installBase)
    (hinstall : block.install installBase = some installed) (hle : installed ≤ env)
    (hold : ∀ name data, old name = some data →
      NativeRecursorRegistered installBase data ∧ data.name = name)
    (hentry : NativeRecursorData.installEntries old
      (compilationEntries key source s auxiliaries g) name = some data) :
    NativeRecursorRegistered env data ∧ data.name = name := by
  have hinstalled : installBase ≤ installed := by
    simp only [VInductBlock.install, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hinstall
    obtain ⟨types, ht, ctors, hc, recursors, hr, rfl⟩ := hinstall
    exact (((VEnv.addConstVals_le ht).trans (VEnv.addConstVals_le hc)).trans
      (VEnv.addProjections_le.trans (VEnv.addConstVals_le hr))).trans VEnv.addDefEqRules_le
  apply NativeRecursorRegistered.installEntries (entries := compilationEntries key source s auxiliaries g)
    (fun name data h => ⟨(hold name data h).1.mono (hinstalled.trans hle), (hold name data h).2⟩)
    (fun _ h => NativeRecursorRegistered.compilationEntries hdata hprior hbase hinstall hle h) hentry

end Lean4Lean.VEnv
