import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.CompilationData
import Lean4Lean.Theory.Inductive.CompilationMajors
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceConstructors

/-! # The constructors of the restored rules

The facts `NestedRun.assemblyRecursors` (`AssemblyRecursors.lean`) reads about the constructor
of every restored recursor rule: its kernel `ctorInfo` and parameter count, its constructor
shape in the source constructor stage, the source-or-container alternative, and their
distinctness within one family. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### The constructors of one family of a compiled signature -/

theorem list_filter_map_eq_filterMap {α β : Type _} (p : α → Bool) (f : α → β) :
    ∀ l : List α, (l.filter p).map f = l.filterMap fun x => if p x then some (f x) else none
  | [] => rfl
  | x :: l => by
    by_cases h : p x <;> simp [List.filter_cons, h, list_filter_map_eq_filterMap p f l]

/-- The names of the constructors a family owns, in generation order, are those of its family
in the signature's declaration. -/
theorem ownedConstructors_names (s : InductiveSignature) (owner : Fin s.families.size) :
    (s.ownedConstructors owner).map (fun index => s.constructors[index].name) =
      (s.declarationFamily owner).ctors.map (·.name) := by
  unfold InductiveSignature.ownedConstructors InductiveSignature.declarationFamily
  rw [list_filter_map_eq_filterMap, List.map_filterMap]
  have hlist : s.constructors.toList = (List.finRange s.constructors.size).map
      (fun i => s.constructors[i]) := by
    apply List.ext_getElem <;> simp
  rw [hlist, List.filterMap_map]
  congr 1
  funext i
  simp only [Function.comp_def, beq_iff_eq, Fin.ext_iff]
  split <;> simp

/-- The restored head name of a name that is not an auxiliary head is the name itself. -/
theorem Restoration.restoredHeadName_of_not_head {r : Restoration} {name : Name}
    (h : name ∉ r.heads.map (·.auxiliary)) : r.restoredHeadName name = name := by
  simp only [Restoration.restoredHeadName, Restoration.heads_find?_eq_none h]

/-- The restored head name of an auxiliary head is its target. -/
theorem Restoration.restoredHeadName_of_mem {r : Restoration} (hr : r.Scoped)
    {spec : HeadSpecialization} (hmem : spec ∈ r.heads) :
    r.restoredHeadName spec.auxiliary = spec.target := by
  simp only [Restoration.restoredHeadName, Restoration.find?_of_nodup hr.1 hmem]

/-- The two kinds of family of a compiled signature: a source family, whose constructors are the
source family's (their restored names are themselves), or the family of a container
specialization, whose constructors are the renamed container constructors (restored to the
container constructors). -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.familyCases {env : VEnv} {source expanded : VInductDecl}
    {s : InductiveSignature} {g : Instance s} {auxiliaries : List ContainerSpecialization}
    {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    (owner : Fin s.families.size) :
    (∃ hsrc : owner.val < source.types.length,
      s.families[owner].name = (source.types[owner.val]'hsrc).name ∧
      (s.declarationFamily owner).ctors.map (·.name) =
        (source.types[owner.val]'hsrc).ctors.map (·.name)) ∨
    (∃ _hge : source.types.length ≤ owner.val, ∃ hidx : owner.val - source.types.length <
        auxiliaries.length,
      s.families[owner].name = (auxiliaries[owner.val - source.types.length]'hidx).auxiliary ∧
      (s.declarationFamily owner).ctors.map (·.name) =
        (auxiliaries[owner.val - source.types.length]'hidx).source.ctors.map
          (auxiliaries[owner.val - source.types.length]'hidx).constructorName) := by
  obtain ⟨envTypes', direct, -, hdirect, -, Hfam⟩ := Hd.correspondence
  have hdeclLen : s.declaration.types.length = s.families.size := by
    simp [InductiveSignature.declaration]
  have hlen := Lean4Lean.List.Forall₂.length_eq Hfam
  have howner : owner.val < s.declaration.types.length := by rw [hdeclLen]; exact owner.isLt
  have howner' : owner.val < (source.types ++ direct).length := hlen ▸ howner
  have Hat := Lean4Lean.List.forall₂_getElem Hfam owner.val howner howner'
  have hdf : s.declaration.types[owner.val]'howner = s.declarationFamily owner := by
    simp [InductiveSignature.declaration, InductiveSignature.declarationFamily]
  rw [hdf] at Hat
  have hnames : (s.declarationFamily owner).ctors.map (·.name) =
      ((source.types ++ direct)[owner.val]'howner').ctors.map (·.name) :=
    List.Forall₂.map_eq (fun _ _ h => h.1) Hat.constructors
  have hfam : s.families[owner].name = ((source.types ++ direct)[owner.val]'howner').name :=
    Hat.name
  by_cases hsrc : owner.val < source.types.length
  · left
    refine ⟨hsrc, ?_, ?_⟩
    · rw [hfam, List.getElem_append_left hsrc]
    · rw [hnames, List.getElem_append_left hsrc]
  · right
    have hge : source.types.length ≤ owner.val := Nat.le_of_not_lt hsrc
    have hidx : owner.val - source.types.length < direct.length := by
      have := howner'; simp only [List.length_append] at this; omega
    have hFdirect := List.mapM_eq_some.mp hdirect
    have hidx' : owner.val - source.types.length < auxiliaries.length :=
      (Lean4Lean.List.Forall₂.length_eq hFdirect) ▸ hidx
    have hd := Lean4Lean.List.forall₂_getElem hFdirect _ hidx' hidx
    have hheads := ContainerSpecialization.directFamily_heads hd
    simp only [ContainerSpecialization.heads, List.map_cons, List.map_map, List.cons.injEq,
      Function.comp_def] at hheads
    refine ⟨hge, hidx', ?_, ?_⟩
    · rw [hfam, List.getElem_append_right hge]; exact hheads.1.symm
    · rw [hnames, List.getElem_append_right hge, ← hheads.2]

/-- The constructor names of a family of a declaration with distinct names are distinct. -/
theorem familyCtorNames_nodup {decl : VInductDecl} (hnd : decl.sourceNames.Nodup)
    {family : VInductiveType} (hfamily : family ∈ decl.types) :
    (family.ctors.map (·.name)).Nodup := by
  have h := (List.nodup_append.mp hnd).2.1
  simp only [VInductDecl.constructorConstants, List.flatMap, List.map_flatten,
    List.map_map] at h
  exact h.sublist (List.sublist_flatten_of_mem
    (List.mem_map_of_mem (f := List.map VConstVal.name ∘ VInductiveType.ctors) hfamily))

theorem list_nodup_map_on {α β : Type _} {f : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => .nil
  | x :: l, H, hnd => by
    rw [List.nodup_cons] at hnd
    refine List.nodup_cons.mpr ⟨fun hm => ?_, list_nodup_map_on
      (fun a ha b hb => H a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) hnd.2⟩
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
    exact hnd.1 (H x List.mem_cons_self y (List.mem_cons_of_mem _ hy) hxy.symm ▸ hy)

/-- The constructor names of a family of a compiled signature are distinct. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.declarationFamily_names_nodup {env : VEnv}
    {source expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    (owner : Fin s.families.size) :
    ((s.declarationFamily owner).ctors.map (·.name)).Nodup := by
  obtain ⟨family, hfamily, -, -, -, -, hnames⟩ := Hd.model.family owner
  rw [hnames]
  exact familyCtorNames_nodup Hd.expandedWF.2.1 hfamily

/-- The restored constructor head of a constructor name of a source family is itself. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.restoredHeadName_source {env : VEnv}
    {source expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    {name : Name} (hname : name ∈ familyNames source.types) :
    (compilationRestoration source auxiliaries).restoredHeadName name = name :=
  Restoration.restoredHeadName_of_not_head
    (Hd.toCaseCompilationData.source_head_disjoint hname)

/-- The restored constructor head of a renamed container constructor is the container
constructor. -/
theorem _root_.Lean4Lean.InductiveSignature.CompilationData.restoredHeadName_auxiliary {env : VEnv}
    {source expanded : VInductDecl} {s : InductiveSignature} {g : Instance s}
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hd : CompilationData env source expanded s g auxiliaries block)
    {a : ContainerSpecialization} (ha : a ∈ auxiliaries) {c : VConstVal}
    (hc : c ∈ a.source.ctors) :
    (compilationRestoration source auxiliaries).restoredHeadName (a.constructorName c) =
      c.name := by
  have hmem : HeadSpecialization.mk (a.constructorName c) source.uvars source.nparams c.name
      a.levels a.arguments ∈ (compilationRestoration source auxiliaries).heads :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c, hc, rfl⟩)⟩
  exact Restoration.restoredHeadName_of_mem Hd.restorationScoped hmem

end VerifyInductive

namespace VerifyInductive

/-- **Stub (restB).** The constructor of every restored rule: the restored constructor of a
generated constructor `index` of family `owner` is a kernel constructor of the output whose
parameter count is the restored family head's argument count (the source family's parameters,
or the container's specialization arguments), a constructor of the source constructor stage
with the constructor shape at that count plus the field count, and either one of the source
declaration's constructors at its parameter count or a constructor of a container installed
below at the container's.

What it needs: for a source owner, `restoredHeadName` is the identity on its constructors
(`CompilationData.restoredFamilyHead_spec`'s first alternative), and the source constructors'
`ctorInfo`s and `TrIndType`s are the base's (`RestoredBlockBase.sourceTranslations`); for an
auxiliary owner, the restored constructor is a constructor of `a.container`, whose installation
(`ContainersInstalled`, then `InstalledBlocks` of the source environment) provides its
`ctorInfo`, its translation and its `numParams = a.container.nparams = a.arguments.length`. -/
theorem NestedRun.restoredRuleConstructors
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (Hcert : ContainersInstalled (ves.venv (if isUnsafe then .unsafe else .safe)) auxiliaries)
    (Hdata : CompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.lowered.loweredDecl E.lowered.signature E.lowered.generatedInstance auxiliaries block)
    (owner : Fin E.lowered.signature.families.size) {head : RestoredFamilyHead}
    (hhead : E.lowered.generatedInstance.restoredFamilyHead
      (compilationRestoration sourceDecl auxiliaries) owner = some head)
    (index : Fin E.lowered.signature.constructors.size)
    (hown : E.lowered.signature.constructors[index].owner = owner) :
    (∃ cval : ConstructorVal, outEnv.constants.find?
        ((compilationRestoration sourceDecl auxiliaries).restoredHeadName
          E.lowered.signature.constructors[index].name) = some (.ctorInfo cval) ∧
      cval.numParams = head.arguments.length) ∧
    (∃ ci, E.sourceCore.envCtors.constants
        ((compilationRestoration sourceDecl auxiliaries).restoredHeadName
          E.lowered.signature.constructors[index].name) = some ci ∧
      ci.type.CtorShape (head.arguments.length +
        E.lowered.signature.constructors[index].fields.length)) ∧
    ((∃ c ∈ sourceDecl.constructorConstants,
        (compilationRestoration sourceDecl auxiliaries).restoredHeadName
          E.lowered.signature.constructors[index].name = c.name ∧
        head.arguments.length = sourceDecl.nparams) ∨
      (∃ Dc, VEnv.InstalledBelow (ves.venv (if isUnsafe then .unsafe else .safe)) Dc ∧
        ∃ c ∈ Dc.constructorConstants,
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            E.lowered.signature.constructors[index].name = c.name ∧
          head.arguments.length = Dc.nparams)) := by
  -- WAVE 3 STUB (restB): see the docstring.
  have := wf; have := Hsources; have := D; have := Hcert; have := Hdata; have := hhead
  have := hown; sorry

/-- **Stub (restB).** The restored constructors of one family are distinct: the identity on a
source family's constructors, and on an auxiliary family's the constructors of its container's
family (`CaseCompilationData.directFamily_restored_constructor_names`), whose names are distinct
in the installed container. -/
theorem NestedRun.restoredRuleConstructors_nodup
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {auxiliaries : List ContainerSpecialization} {block : VInductBlock}
    (Hcert : ContainersInstalled (ves.venv (if isUnsafe then .unsafe else .safe)) auxiliaries)
    (Hdata : CompilationData (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
      E.lowered.loweredDecl E.lowered.signature E.lowered.generatedInstance auxiliaries block)
    (owner : Fin E.lowered.signature.families.size) :
    ((E.lowered.signature.ownedConstructors owner).map fun index =>
      (compilationRestoration sourceDecl auxiliaries).restoredHeadName
        E.lowered.signature.constructors[index].name).Nodup := by
  have := Hcert
  have hmap : (E.lowered.signature.ownedConstructors owner).map (fun index =>
      (compilationRestoration sourceDecl auxiliaries).restoredHeadName
        E.lowered.signature.constructors[index].name) =
      ((E.lowered.signature.declarationFamily owner).ctors.map (·.name)).map
        (compilationRestoration sourceDecl auxiliaries).restoredHeadName := by
    rw [← ownedConstructors_names, List.map_map]; rfl
  rw [hmap]
  refine list_nodup_map_on ?_ (Hdata.declarationFamily_names_nodup owner)
  rcases Hdata.familyCases owner with ⟨hsrc, -, hnames⟩ | ⟨-, hidx, -, hnames⟩
  · intro x hx y hy hxy
    rw [hnames] at hx hy
    have hmem : ∀ z ∈ (sourceDecl.types[owner.val]'hsrc).ctors.map (·.name),
        z ∈ familyNames sourceDecl.types := fun z hz =>
      mem_familyNames.mpr ⟨_, List.getElem_mem hsrc, .inr (by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz; exact ⟨c, hc, rfl⟩)⟩
    rwa [Hdata.restoredHeadName_source (hmem x hx),
      Hdata.restoredHeadName_source (hmem y hy)] at hxy
  · intro x hx y hy hxy
    rw [hnames] at hx hy
    have ha := List.getElem_mem hidx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hy
    rw [Hdata.restoredHeadName_auxiliary ha hc, Hdata.restoredHeadName_auxiliary ha hc'] at hxy
    simp only [ContainerSpecialization.constructorName, hxy]


end VerifyInductive
end Lean4Lean
