import Lean4Lean.Verify.Inductive.CompletedRecursorSetup
import Lean4Lean.Verify.Inductive.Recursor.ReplayCompat
import Lean4Lean.Verify.Inductive.Header.LoopType

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive
/-! Facts about the completed recursor phases entered from the ordinary
header/constructor pipeline (`ConstructorPhasesResult`).  The recursor result
itself is `CompletedRecursorPhasesResult R.completed`; the lemmas here only
add what is visible through the declared header and constructor traces
(source lookups for nested restoration and the declared installation). -/

/-- Header metadata installed at the start of the verified pipeline remains
retrievable, unchanged, after constructors and recursors are installed. -/
theorem CompletedRecursorPhasesResult.findHeaderOfMem
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hc : ContextWF c)
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (hentry : (info, value) ∈ Hheaders.entries) :
    outEnv.find? info.name = some info := by
  have hheader := Hheaders.installed.findOfMem Hc.checking.tr.map_wf hentry
  have hctor := R.declared.installed.preservesFind
    Hheaders.context.checking.tr.map_wf hheader
  have hlocalWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.declared.context.checking.tr.map_wf
  apply H.installed.preservesFind hlocalWF
  rwa [H.localExtends.env_eq]

/-- Exact source-family metadata is present after the complete lowered
installation, including the constructor-name list used by restoration. -/
theorem CompletedRecursorPhasesResult.findSourceHeader
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hc : ContextWF c) (H : CompletedRecursorPhasesResult R.completed outEnv)
    (howner : owner ∈ indTypes.toList) :
    ∃ info : InductiveVal,
      outEnv.find? owner.name = some (.inductInfo info) ∧
      info.ctors = owner.ctors.map (fun ctor => ctor.name) ∧
      info.all = indTypes.toList.map (fun type => type.name) := by
  rcases Hheaders.sourceAligned with ⟨numNested, Haligned⟩
  have htypesLength : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      Hheaders.translation.types
  have hsize : stats.nindices.size = indTypes.size := by
    rw [Array.size_eq_length_toList, Hheaders.materialized.indices,
      List.length_map]
    exact htypesLength.symm
  rcases inductiveTypeInfos_source_mem stats nparams indTypes numNested
      isUnsafe c.lparams hsize howner with
    ⟨info, hinfo, hname, hctors, hall⟩
  rcases Haligned.findInfo hinfo with ⟨value, hentry⟩
  refine ⟨info, ?_, hctors, hall⟩
  rw [← hname]
  exact H.findHeaderOfMem Hc hentry

private theorem mkAuxRecNameMap_fold_recNames
    (names : List Name) (acc : Array Name × NameMap Name × Nat)
    (mainName : Name) :
    (names.foldl (fun b name =>
      (b.1.push (Lean.mkRecName name),
        b.2.1.insert (Lean.mkRecName name)
          ((Lean.mkRecName mainName).appendIndexAfter b.2.2),
        b.2.2 + 1)) acc).1.toList =
      acc.1.toList ++ names.map Lean.mkRecName := by
  induction names generalizing acc with
  | nil => simp
  | cons name names ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp

private theorem mkAuxRecNameMap_fold_find_none
    (names : List Name) (acc : Array Name × NameMap Name × Nat)
    (mainName query : Name)
    (hacc : acc.2.1.find? query = none)
    (hnot : query ∉ names.map Lean.mkRecName) :
    (names.foldl (fun b name =>
      (b.1.push (Lean.mkRecName name),
        b.2.1.insert (Lean.mkRecName name)
          ((Lean.mkRecName mainName).appendIndexAfter b.2.2),
        b.2.2 + 1)) acc).2.1.find? query = none := by
  induction names generalizing acc with
  | nil => simpa using hacc
  | cons name names ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    apply ih _ _ hnot.2
    change (show Std.TreeMap Name Name Name.quickCmp from acc.2.1)[query]? =
      none at hacc
    change (Std.TreeMap.insert
      (show Std.TreeMap Name Name Name.quickCmp from acc.2.1)
      (Lean.mkRecName name)
      ((Lean.mkRecName mainName).appendIndexAfter acc.2.2))[query]? = none
    rw [Std.TreeMap.getElem?_insert]
    split
    · rename_i heq
      have : Lean.mkRecName name = query := by simpa using heq
      exact False.elim (hnot.1 this.symm)
    · exact hacc

/-- The first component of the production auxiliary-recursor map is exactly
the recursor-name image of the extra family names recorded in the installed
main-family metadata. -/
theorem mkAuxRecNameMap_recNames
    (main : InductiveType) (rest : List InductiveType)
    (env : Environment) (info : InductiveVal)
    (hfind : env.find? main.name = some (.inductInfo info))
    (hlength : (main :: rest).length < info.all.length) :
    (Lean4Lean.mkAuxRecNameMap env (main :: rest)).1 =
      (info.all.drop (main :: rest).length).map Lean.mkRecName := by
  have hlength' : rest.length + 1 < info.all.length := by
    simpa using hlength
  simp [Lean4Lean.mkAuxRecNameMap, hfind, hlength',
    mkAuxRecNameMap_fold_recNames]

theorem mkAuxRecNameMap_recNames_mem
    (main : InductiveType) (rest : List InductiveType)
    (env : Environment) (info : InductiveVal)
    (hfind : env.find? main.name = some (.inductInfo info))
    (hmem : recName ∈
      (Lean4Lean.mkAuxRecNameMap env (main :: rest)).1) :
    ∃ name ∈ info.all, recName = Lean.mkRecName name := by
  by_cases hlength : (main :: rest).length < info.all.length
  · rw [mkAuxRecNameMap_recNames main rest env info hfind hlength] at hmem
    rcases List.mem_map.mp hmem with ⟨name, hname, rfl⟩
    exact ⟨name, List.mem_of_mem_drop hname, rfl⟩
  · have hlength' : ¬ rest.length + 1 < info.all.length := by
      simpa using hlength
    simp [Lean4Lean.mkAuxRecNameMap, hfind, hlength'] at hmem
    change recName ∈ ([] : List Name) at hmem
    simp at hmem

/-- The second component of the production auxiliary-recursor map has no
entry outside the exact recursor-name suffix used to build it. -/
theorem mkAuxRecNameMap_recMap_find_none
    (main : InductiveType) (rest : List InductiveType)
    (env : Environment) (info : InductiveVal)
    (hfind : env.find? main.name = some (.inductInfo info))
    (hnot : query ∉
      (info.all.drop (main :: rest).length).map Lean.mkRecName) :
    (Lean4Lean.mkAuxRecNameMap env (main :: rest)).2.find? query = none := by
  by_cases hlength : (main :: rest).length < info.all.length
  · have hlength' : rest.length + 1 < info.all.length := by
      simpa using hlength
    simpa [Lean4Lean.mkAuxRecNameMap, hfind, hlength'] using
      mkAuxRecNameMap_fold_find_none
        (info.all.drop (rest.length + 1)) (#[], {}, 1) main.name query
        (by rfl) (by simpa using hnot)
  · have hlength' : ¬ rest.length + 1 < info.all.length := by
      simpa using hlength
    simp [Lean4Lean.mkAuxRecNameMap, hfind, hlength']
    change ({} : NameMap Name).find? query = none
    rfl

/-- Every key returned by the production auxiliary-recursor map also occurs
in its first component.  The executable builds the list and map in the same
fold; this theorem exposes that shared domain without unfolding the fold at
later restoration call sites. -/
theorem mkAuxRecNameMap_recMap_find_mem
    (main : InductiveType) (rest : List InductiveType)
    (env : Environment) (info : InductiveVal)
    (hfind : env.find? main.name = some (.inductInfo info))
    (hmap : (Lean4Lean.mkAuxRecNameMap env (main :: rest)).2.find? query =
      some mapped) :
    query ∈ (Lean4Lean.mkAuxRecNameMap env (main :: rest)).1 := by
  by_cases hlength : (main :: rest).length < info.all.length
  · rw [mkAuxRecNameMap_recNames main rest env info hfind hlength]
    by_contra hnot
    have hnone := mkAuxRecNameMap_recMap_find_none main rest env info hfind hnot
    rw [hnone] at hmap
    cases hmap
  · have hsuffix : info.all.drop (main :: rest).length = [] :=
      List.drop_eq_nil_iff.mpr (Nat.le_of_not_gt hlength)
    have hsuffix' : info.all.drop (rest.length + 1) = [] := by
      simpa using hsuffix
    have hnone := mkAuxRecNameMap_recMap_find_none (query := query)
      main rest env info hfind
      (by
        intro hmem
        simpa [hsuffix'] using hmem)
    rw [hnone] at hmap
    cases hmap

theorem mkRecName_injective : Function.Injective Lean.mkRecName := by
  intro left right heq
  simpa [Lean.mkRecName, Lean.Name.getPrefix] using
    congrArg Lean.Name.getPrefix heq

/-- A recursor shape's existential owner position is the concrete generated
position whenever the declaration's source names are duplicate-free.  This
is the positional bridge needed before transporting a lowered shape back to
the corresponding source-family index. -/
theorem VInductDecl.NestedRecursorShape.ownerIdx_eq_of_name
    {decl : VInductDecl} {owner : VInductiveType} {recursor : VConstVal}
    (H : decl.NestedRecursorShape owner recursor)
    (ownerIdx : Nat) (howner : ownerIdx < decl.types.length)
    (hname : recursor.name = decl.recursorName decl.types[ownerIdx])
    (hnodup : decl.sourceNames.Nodup) :
    H.ownerIdx = ownerIdx := by
  have htypeNames : (decl.types.map (fun type => type.name)).Nodup := by
    have hprefix := (List.nodup_append.mp hnodup).1
    simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductiveType.toVConstVal, Function.comp_def] using hprefix
  have hshapeMap : H.ownerIdx <
      (decl.types.map (fun type => type.name)).length := by
    simpa using H.owner_lt
  have hownerMap : ownerIdx <
      (decl.types.map (fun type => type.name)).length := by
    simpa using howner
  apply (List.getElem_inj (h₀ := hshapeMap) (h₁ := hownerMap)
    htypeNames).mp
  rw [List.getElem_map, List.getElem_map, H.owner_eq]
  exact mkRecName_injective (H.name.symm.trans hname)

/-- Constructor metadata installed in the middle phase remains retrievable,
unchanged, after recursor installation. -/
theorem CompletedRecursorPhasesResult.findConstructorOfMem
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (hentry : (info, value) ∈ R.declared.entries) :
    outEnv.find? info.name = some info := by
  have hctor := R.declared.installed.findOfMem
    Hheaders.context.checking.tr.map_wf hentry
  have hlocalWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.declared.context.checking.tr.map_wf
  apply H.installed.preservesFind hlocalWF
  rwa [H.localExtends.env_eq]

/-- Source alignment identifies the exact concrete constructor metadata that
nested restoration will read from the final lowered environment. -/
theorem CompletedRecursorPhasesResult.findSourceConstructor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (howner : owner ∈ indTypes.toList) (hctor : ctor ∈ owner.ctors) :
    ∃ info : ConstructorVal,
      outEnv.find? ctor.name = some (.ctorInfo info) ∧
      info.type = ctor.type := by
  rcases R.declared.sourceAligned.findSource howner hctor with
    ⟨info, value, hentry, hname, htype, _hlevels, _hunsafe⟩
  refine ⟨info, ?_, htype⟩
  rw [← hname]
  exact H.findConstructorOfMem hentry

/-- The concrete constructor read by an operational restoration step is the
positionally aligned lowered constructor installed by the verified producer.
Only equality of the fold item name is required; lookup functionality then
forces equality of the complete `ConstructorVal`, and hence of its type. -/
theorem RestoredConstructorStep.oldType_eq_ofInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hstep : RestoredConstructorStep result outEnv ctorName
      sourceProdEnv targetProdEnv)
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (howner : owner ∈ indTypes.toList) (hctor : ctor ∈ owner.ctors)
    (hname : ctorName = ctor.name) :
    Hstep.oldInfo.type = ctor.type := by
  rcases H.findSourceConstructor howner hctor with
    ⟨info, hlookup, htype⟩
  have hstepLookup :
      outEnv.find? ctor.name = some (.ctorInfo Hstep.oldInfo) := by
    simpa [hname] using Hstep.lookup
  have hinfo : Hstep.oldInfo = info := by
    have heq : ConstantInfo.ctorInfo Hstep.oldInfo = .ctorInfo info :=
      Option.some.inj (hstepLookup.symm.trans hlookup)
    exact ConstantInfo.ctorInfo.inj heq
  rw [hinfo]
  exact htype

/-- Safety, universe parameters, and name of the constructor read by
restoration are all fixed by the verified lowered installation. -/
theorem RestoredConstructorStep.metadataOfInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hstep : RestoredConstructorStep result outEnv ctorName
      sourceProdEnv targetProdEnv)
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (howner : owner ∈ indTypes.toList) (hctor : ctor ∈ owner.ctors)
    (hname : ctorName = ctor.name) :
    c.safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety ∧
      Hstep.oldInfo.levelParams = c.lparams ∧
      Hstep.oldInfo.name = ctor.name ∧
      Hstep.oldInfo.isUnsafe = isUnsafe := by
  rcases R.declared.sourceAligned.findSource howner hctor with
    ⟨info, value, hentry, hinfoName, _hinfoType, hlevels, hunsafe⟩
  have hlookup := H.findConstructorOfMem hentry
  have hstepLookup :
      outEnv.find? ctor.name = some (.ctorInfo Hstep.oldInfo) := by
    simpa [hname] using Hstep.lookup
  have hinfo : Hstep.oldInfo = info := by
    have hlookup' : outEnv.find? info.name = some (.ctorInfo info) := by
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using hlookup
    rw [hinfoName] at hlookup'
    have heq : ConstantInfo.ctorInfo Hstep.oldInfo = .ctorInfo info :=
      Option.some.inj (hstepLookup.symm.trans hlookup')
    exact ConstantInfo.ctorInfo.inj heq
  subst info
  exact ⟨R.declared.installed.entrySafety hentry, hlevels, hinfoName,
    hunsafe⟩

/-- The constructor fold nested inside an operational family restoration is
indexed by exactly the constructor-name list of the aligned installed lowered
family.  This is the family-level lookup bridge used before applying
`oldType_eq_ofInstalled` pointwise. -/
theorem RestoredInductiveStep.oldConstructors_eq_ofInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hstep : RestoredInductiveStep result outEnv auxRec allIndNames indType
      sourceProdEnv targetProdEnv)
    (Hc : ContextWF c) (H : CompletedRecursorPhasesResult R.completed outEnv)
    (howner : owner ∈ indTypes.toList)
    (hname : indType.name = owner.name) :
    Hstep.oldInfo.ctors = owner.ctors.map (fun ctor => ctor.name) := by
  rcases H.findSourceHeader Hc howner with
    ⟨info, hlookup, hctors, _hall⟩
  have hstepLookup :
      outEnv.find? owner.name = some (.inductInfo Hstep.oldInfo) := by
    simpa [hname] using Hstep.lookup
  have hinfo : Hstep.oldInfo = info := by
    have heq : ConstantInfo.inductInfo Hstep.oldInfo = .inductInfo info :=
      Option.some.inj (hstepLookup.symm.trans hlookup)
    exact ConstantInfo.inductInfo.inj heq
  rw [hinfo]
  exact hctors

/-- Every generated primary recursor is retrievable with the exact production
metadata retained by the verified recursor phase. -/
theorem CompletedRecursorPhasesResult.findRecursorOfMem
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (hentry : (info, value) ∈ H.entries) :
    outEnv.find? info.name = some info := by
  have hlocalWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]
    exact R.declared.context.checking.tr.map_wf
  exact H.installed.findOfMem hlocalWF hentry

/-- The generated primary recursor for every lowered family is present in the
final environment and satisfies both telescope preconditions consumed by
nested restoration. -/
theorem CompletedRecursorPhasesResult.findSourceRecursor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (ownerIdx : Nat) (howner : ownerIdx < indTypes.size) :
    ∃ info : RecursorVal,
      outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
        some (.recInfo info) ∧
      RestoreTelescope info.type nparams ∧
      ∀ rule ∈ info.rules, RestoreTelescope rule.rhs nparams := by
  have htypes : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have hrecInfo : ownerIdx < H.recInfos.size := by
    rw [H.cardinality.records, ← htypes]
    exact howner
  have hentry : ownerIdx < H.entries.length := by
    rw [H.generated.length]
    exact hrecInfo
  let E := H.generated.entry ownerIdx hentry
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    ownerIdx hrecInfo
  have hparams : nparams = stats.params.size :=
    R.core.nparams.symm.trans H.cardinality.params.symm
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  refine ⟨E.info, ?_, E.typeRestoreTelescope selections.params hparams,
    E.rulesRestoreTelescope hparams⟩
  change outEnv.find? H.entries[ownerIdx].1.name =
    some H.entries[ownerIdx].1 at hlookup
  rw [E.source_eq] at hlookup
  change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
  rwa [E.name] at hlookup

/-- Assemble the complete per-family lookup/telescope premise consumed by
the operational nested-restoration fold. Constructor telescope syntax is the
only remaining source-side premise; header, constructor, and recursor lookups
and both generated recursor telescopes are derived from installation. -/
theorem CompletedRecursorPhasesResult.restorationSources
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hc : ContextWF c) (H : CompletedRecursorPhasesResult R.completed outEnv)
    (HctorTelescope : ∀ owner ∈ indTypes.toList, ∀ ctor ∈ owner.ctors,
      RestoreTelescope ctor.type nparams) :
    ∀ owner, owner ∈ indTypes.toList →
      ∃ oldInfo : InductiveVal,
        outEnv.find? owner.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            outEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type nparams) ∧
        ∃ recInfo : RecursorVal,
          outEnv.find? (Lean.mkRecName owner.name) = some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs nparams := by
  intro owner howner
  rcases H.findSourceHeader Hc howner with
    ⟨oldInfo, hheader, hctors, _hall⟩
  rcases List.mem_iff_getElem.mp howner with ⟨ownerIdx, hownerIdx, rfl⟩
  rcases H.findSourceRecursor ownerIdx (by simpa using hownerIdx) with
    ⟨recInfo, hrecursor, hrecType, hrecRules⟩
  refine ⟨oldInfo, hheader, ?_, recInfo, ?_, hrecType, hrecRules⟩
  · intro ctorName hctorName
    rw [hctors] at hctorName
    rcases List.mem_map.mp hctorName with ⟨ctor, hctor, rfl⟩
    rcases H.findSourceConstructor (List.getElem_mem hownerIdx) hctor with
      ⟨ctorInfo, hlookup, htype⟩
    refine ⟨ctorInfo, hlookup, ?_⟩
    rw [htype]
    exact HctorTelescope _ (List.getElem_mem hownerIdx) ctor hctor
  · have hbang : indTypes[ownerIdx]! = indTypes[ownerIdx] := by
      have hownerArray : ownerIdx < indTypes.size := by simpa using hownerIdx
      simp [Array.getElem!_eq_getD, Array.getD, hownerArray]
    rw [hbang] at hrecursor
    exact hrecursor

/-- The operational primary-restoration lookup identifies its old universe
parameter list with the exact generated recursor entry. -/
theorem CompletedRecursorPhasesResult.restoredPrimaryRecursorLevelParams
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName = Lean.mkRecName indTypes[ownerIdx]!.name) :
    Hstep.oldInfo.levelParams =
      (H.generated.entry ownerIdx hentry).info.levelParams := by
  let E := H.generated.entry ownerIdx hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[ownerIdx].1.name =
      some H.entries[ownerIdx].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have holdInfo : Hstep.oldInfo = E.info := by
    have hstepLookup : outEnv.find?
        (Lean.mkRecName indTypes[ownerIdx]!.name) =
          some (.recInfo Hstep.oldInfo) := by
      simpa [holdRecName] using Hstep.lookup
    exact ConstantInfo.recInfo.inj (Option.some.inj
      (hstepLookup.symm.trans hlookupE))
  exact congrArg (fun info : RecursorVal => info.levelParams) holdInfo

/-- The installed generated entry fixes the universe arity of the old
recursor metadata read by primary restoration. -/
theorem CompletedRecursorPhasesResult.restoredPrimaryRecursorMetadata
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName = Lean.mkRecName indTypes[ownerIdx]!.name) :
    c.safety ≤ (ConstantInfo.recInfo Hstep.oldInfo).safety ∧
      Hstep.oldInfo.levelParams.length =
        (H.entries[ownerIdx]'hentry).2.uvars := by
  let E := H.generated.entry ownerIdx hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[ownerIdx].1.name =
      some H.entries[ownerIdx].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have holdInfo : Hstep.oldInfo = E.info := by
    have hstepLookup : outEnv.find?
        (Lean.mkRecName indTypes[ownerIdx]!.name) =
          some (.recInfo Hstep.oldInfo) := by
      simpa [holdRecName] using Hstep.lookup
    exact ConstantInfo.recInfo.inj (Option.some.inj
      (hstepLookup.symm.trans hlookupE))
  constructor
  · rw [← H.localExtends.safety_eq, holdInfo]
    exact E.translated.1.1
  · rw [holdInfo]
    simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      E.translated.1.2.1

/-- Identify an operational primary-restoration step with its exact generated
recursor entry and expose the complete old/restored telescope alignment.  In
particular, callers do not choose an unrelated generated entry or reconstruct
the local binder selection: installation, the restoration lookup, and the
retained `mkRecInfos` state determine all of them. -/
theorem CompletedRecursorPhasesResult.restoredPrimaryTelescopeAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName =
      Lean.mkRecName indTypes[ownerIdx]!.name)
    (hresultNparams : result.nparams = nparams)
    (hresultParams : result.params.size = result.nparams) :
    Nonempty (GeneratedRecursorRestorationTelescopeAlignment result outEnv
      auxRec Hstep.restored.newInfo (H.generated.entry ownerIdx hentry)) := by
  have hrecInfo : ownerIdx < H.recInfos.size := by
    simpa [H.generated.length] using hentry
  let E := H.generated.entry ownerIdx hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[ownerIdx].1.name =
      some H.entries[ownerIdx].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have holdInfo : Hstep.oldInfo = E.info := by
    have hstepLookup : outEnv.find?
        (Lean.mkRecName indTypes[ownerIdx]!.name) =
          some (.recInfo Hstep.oldInfo) := by
      simpa [holdRecName] using Hstep.lookup
    exact ConstantInfo.recInfo.inj (Option.some.inj
      (hstepLookup.symm.trans hlookupE))
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    ownerIdx hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias ownerIdx hrecInfo
  have hrestoration : RecursorRestoration result outEnv auxRec allIndNames
      oldRecName Hstep.restored.newRecName E.info Hstep.restored.newInfo := by
    simpa [holdInfo] using Hstep.restored.restoration
  have hparams : result.nparams = stats.params.size :=
    hresultNparams.trans <| R.core.nparams.symm.trans
      H.cardinality.params.symm
  exact hrestoration.generatedTelescopeAlignment E selections hrecInfo
    hselectionNoAlias hparams hresultParams

/-- A primary restoration step inherits one of the two source-declaration
universe arities admitted for generated recursors.  This packages the lookup
argument identifying the step's old metadata with the exact generated entry,
so later source-restoration proofs do not need to repeat it. -/
theorem CompletedRecursorPhasesResult.restoredPrimaryRecursorUvars
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName = Lean.mkRecName indTypes[ownerIdx]!.name)
    (sourceDecl : VInductDecl)
    (hsourceUvars : sourceDecl.uvars = c.lparams.length) :
    Hstep.oldInfo.levelParams.length = sourceDecl.uvars ∨
      Hstep.oldInfo.levelParams.length = sourceDecl.uvars + 1 := by
  let E := H.generated.entry ownerIdx hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[ownerIdx].1.name =
      some H.entries[ownerIdx].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have holdInfo : Hstep.oldInfo = E.info := by
    have hstepLookup : outEnv.find?
        (Lean.mkRecName indTypes[ownerIdx]!.name) =
          some (.recInfo Hstep.oldInfo) := by
      simpa [holdRecName] using Hstep.lookup
    exact ConstantInfo.recInfo.inj (Option.some.inj
      (hstepLookup.symm.trans hlookupE))
  rw [holdInfo, E.levels, H.localExtends.lparams_eq]
  rw [hsourceUvars]
  exact AddInductive.getRecLevelParams_length

/-- The installed ordinary recursor phase already realizes the independent
source-recursion specification for the declaration it compiled.  This is the
pointwise form useful to later restoration proofs; for a genuinely nested
source declaration, that declaration is still the expanded lowered one. -/
theorem CompletedRecursorPhasesResult.sourcePrimaryRecursorSemantics
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length) :
    Nonempty (SourcePrimaryRecursorSemantics decl
      (decl.types[ownerIdx]'(by
        have howner : ownerIdx < H.recInfos.size := by
          simpa [H.generated.length] using hentry
        simpa [H.cardinality.records] using howner))
      ((R.declared.venvCtors.addEliminators R.declared.eliminators).addProjections decl.projectionEntries)) := by
  have Hcore : TrInductDeclCore sourceEnv H.localContext.lparams nparams
      indTypes.toList isUnsafe decl Hheaders.context.venv
      R.declared.venvCtors := by
    rw [H.localExtends.lparams_eq]
    exact R.core
  have Hsemantics := H.generated.sourcePrimaryRecursorSemantics H.localWF
    H.bindings H.params H.noAlias H.cardinality Hcore ownerIdx hentry
  change Nonempty (SourcePrimaryRecursorSemantics decl _
    R.declared.context.venv) at Hsemantics
  rwa [R.declared.contextVEnv] at Hsemantics

/-- Direct executable-to-source realization for a restored primary recursor.
Unlike `restoredPrimaryRecursorSemantics`, this theorem does not transport a
shape from the expanded abstract declaration.  It derives the source shape
from the generated concrete binder selections, operational restoration, and
translation of the restored type in the canonical source environment. -/
def CompletedRecursorPhasesResult.restoredSourcePrimaryRecursorRealization
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (ownerIdx : Nat) (hentry : ownerIdx < H.entries.length)
    (Hstep : RestoredRecursorStep result outEnv auxRec allIndNames
      oldRecName sourceProdEnv targetProdEnv)
    (holdRecName : oldRecName =
      Lean.mkRecName indTypes[ownerIdx]!.name)
    (sourceDecl : VInductDecl)
    (hsourceOwner : ownerIdx < sourceDecl.types.length)
    (recursor : VConstVal) (canonicalEnv : VEnv)
    (hname : recursor.name = sourceDecl.recursorName
      (sourceDecl.types[ownerIdx]'hsourceOwner))
    (huvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1)
    (huvarArity : Hstep.oldInfo.levelParams.length = recursor.uvars)
    (hresultNparams : result.nparams = nparams)
    (hnparams : sourceDecl.nparams = result.nparams)
    (hmotives : sourceDecl.types.length ≤
      (H.recInfos.map (·.motive)).size)
    (hminors : sourceDecl.ownedConstructors.length ≤
      (H.recInfos.flatMap (·.minors)).size)
    (hindices : (sourceDecl.types[ownerIdx]'hsourceOwner).numIndices =
      H.recInfos[ownerIdx]!.indices.size)
    (Htype : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
      Hstep.restored.newInfo.type recursor.type) :
    SourcePrimaryRecursorRealization sourceDecl
      (sourceDecl.types[ownerIdx]'hsourceOwner) Hstep canonicalEnv recursor := by
  have hrecInfo : ownerIdx < H.recInfos.size := by
    simpa [H.generated.length] using hentry
  let E := H.generated.entry ownerIdx hentry
  have hlookup := H.findRecursorOfMem (List.getElem_mem hentry)
  have hlookupE : outEnv.find? (Lean.mkRecName indTypes[ownerIdx]!.name) =
      some (.recInfo E.info) := by
    change outEnv.find? H.entries[ownerIdx].1.name =
      some H.entries[ownerIdx].1 at hlookup
    rw [E.source_eq] at hlookup
    change outEnv.find? E.info.name = some (.recInfo E.info) at hlookup
    rwa [E.name] at hlookup
  have holdInfo : Hstep.oldInfo = E.info := by
    have hstepLookup : outEnv.find?
        (Lean.mkRecName indTypes[ownerIdx]!.name) =
          some (.recInfo Hstep.oldInfo) := by
      simpa [holdRecName] using Hstep.lookup
    exact ConstantInfo.recInfo.inj (Option.some.inj
      (hstepLookup.symm.trans hlookupE))
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    ownerIdx hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias ownerIdx hrecInfo
  have hrestoration : RecursorRestoration result outEnv auxRec allIndNames
      oldRecName Hstep.restored.newRecName E.info
        Hstep.restored.newInfo := by
    simpa [holdInfo] using Hstep.restored.restoration
  have hparams : result.nparams = stats.params.size :=
    hresultNparams.trans <| R.core.nparams.symm.trans
      H.cardinality.params.symm
  have Htype' : TrExprS canonicalEnv E.info.levelParams []
      Hstep.restored.newInfo.type recursor.type := by
    simpa [holdInfo] using Htype
  have Hshape := hrestoration.nestedRecursorShape E selections hrecInfo
    hselectionNoAlias hparams sourceDecl
    (sourceDecl.types[ownerIdx]'hsourceOwner) hsourceOwner rfl recursor hname
    huvars hnparams hmotives hminors hindices Htype'
  have HisType := hrestoration.translatedTypeIsType E selections hrecInfo
    hselectionNoAlias hparams Htype'
  have huvarArity' : E.info.levelParams.length = recursor.uvars := by
    simpa [holdInfo] using huvarArity
  rw [huvarArity'] at HisType
  refine {
    source := {
      recursor := recursor
      name := hname
      isType := HisType
      shape := Hshape }
    recursor_eq := rfl
    refinement := ⟨huvarArity, Htype⟩ }

theorem DeclaredHeadersResult.typesWF
    (H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes outEnv) :
    ∀ ci ∈ H.entries.map Prod.snd, ci.toVConstant.WF sourceEnv := by
  rw [H.values]
  intro ci hci
  simp only [VInductDecl.typeConstants] at hci
  rcases List.mem_map.mp hci with ⟨target, htarget, rfl⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r H.translation.types target
      htarget with ⟨source, _, Htarget⟩
  exact Htarget.header.wf

theorem DeclaredConstructorsResult.ctorsWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : DeclaredConstructorsResult H outEnv) :
    ∀ ci ∈ R.entries.map Prod.snd,
      ci.toVConstant.WF H.context.venv := by
  rw [R.values]
  intro ci hci
  simp only [VInductDecl.constructorConstants, List.mem_flatMap] at hci
  rcases hci with ⟨target, htarget, hci⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r R.translation.types target
      htarget with ⟨source, _, Htarget⟩
  rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget ci hci with
    ⟨ctor, _, Hctor⟩
  exact Hctor.wf

/-- The ordinary staged installation trace (headers, then constructors,
then recursors) of a recursor phase entered from the declared header and
constructor pipeline.  Unlike `CompletedRecursorPhasesResult.staged`, it
retains the separate header and constructor installations. -/
def CompletedRecursorPhasesResult.declaredStaged
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv) :
    StagedBlock c.safety c.env sourceEnv Hheaders.entries R.declared.entries
      H.entries decl.projectionEntries outEnv H.outVEnv where
  envTypes := headerEnv
  venvTypes := Hheaders.context.venv
  envCtors := ctorEnv
  venvCtors := R.declared.venvCtors
  typesAdded := Hheaders.installed
  ctorsAdded := R.declared.installed
  eliminators := R.declared.eliminators
  casesWF := R.completed.casesWF
  projectedWF := by
    simpa [ConstructorPhasesResult.completed, R.declared.contextVEnv] using
      R.completed.projectedWF
  recursorsAdded := by
    rw [← R.declared.contextVEnv]
    simpa [ConstructorPhasesResult.completed, H.localExtends.safety_eq,
      H.localExtends.env_eq] using H.installed

def CompletedRecursorPhasesResult.declaredBlockCertificate
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    BlockCertificate c.safety c.env sourceEnv Hheaders.entries
      R.declared.entries H.entries rules outEnv H.outVEnv := by
  let Hgenerated : GeneratedRecursors c.safety
      ((R.declared.venvCtors.addEliminators R.declared.eliminators).addProjections decl.projectionEntries)
      c.lparams H.elimLevel H.localContext stats indTypes H.recInfos
      H.entries := by
    rw [← R.declared.contextVEnv]
    simpa [ConstructorPhasesResult.completed, H.localExtends.safety_eq,
      H.localExtends.lparams_eq] using
      H.generated
  let Hgenerated' : GeneratedRecursors c.safety
      ((H.declaredStaged.venvCtors.addEliminators H.declaredStaged.eliminators).addProjections
        decl.projectionEntries)
      c.lparams H.elimLevel H.localContext stats indTypes H.recInfos H.entries := Hgenerated
  exact Hgenerated'.toBlockCertificate decl.projectionEntries H.declaredStaged
    H.localWF H.bindings H.params Hheaders.typesWF R.declared.ctorsWF hrules

/-- The declared block registers the declaration's certified case eliminators. -/
theorem CompletedRecursorPhasesResult.declaredBlockEliminatorsWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) :
    VInductBlock.EliminatorsWF sourceEnv decl (H.declaredBlockCertificate rules hrules).block :=
  R.declared.eliminatorsWF.congr_block Hheaders.values R.declared.values rfl rfl

/-- The block's case eliminators are certified over every larger environment in which its
families and constructors install. -/
theorem CompletedRecursorPhasesResult.declaredBlockEliminatorsReplay
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : CompletedRecursorPhasesResult R.completed outEnv)
    (rules : List VDefEq)
    (hrules : ∀ df ∈ rules, df.WF H.outVEnv) {env' : VEnv} (hle : sourceEnv ≤ env') :
    VInductBlock.EliminatorsReplay env' decl (H.declaredBlockCertificate rules hrules).block :=
  R.declared.eliminatorsOrdinary.replay hle Hheaders.values R.declared.values rfl rfl

/-- Rebase a conversion between two dependent prefixes along a conversion
of their common suffix.  Both prefix contexts are known well formed from the
original conversion, so changing the suffix on each side is admissible even
when the two dependent prefixes use different representatives. -/
theorem VEnv.IsDefEqCtx.rebaseCommonSuffix
    (henv : env.WF)
    (Hsuffix : VEnv.IsDefEqCtx env U [] outer inner)
    (Hprefix : VEnv.IsDefEqCtx env U []
      (left ++ inner) (right ++ inner)) :
    VEnv.IsDefEqCtx env U []
      (left ++ outer) (right ++ outer) := by
  have HleftToOuter :=
    VEnv.IsDefEqCtx.extendSamePrefix
      (Hsuffix.symm henv.ordered) Hprefix.isType
  have HrightInner := (Hprefix.symm henv.ordered).isType
  have HrightToOuter :=
    VEnv.IsDefEqCtx.extendSamePrefix
      (Hsuffix.symm henv.ordered) HrightInner
  exact VEnv.IsDefEqCtx.transEmpty henv
    (HleftToOuter.symm henv.ordered) <|
      VEnv.IsDefEqCtx.transEmpty henv Hprefix HrightToOuter

end VerifyInductive
end Lean4Lean
