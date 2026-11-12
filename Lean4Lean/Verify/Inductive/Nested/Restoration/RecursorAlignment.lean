import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredRuleAvoidance
import Lean4Lean.Theory.Typing.IotaSoundnessLemmas
import Lean4Lean.Verify.Inductive.Nested.Restoration.HeaderRenaming
import Lean4Lean.Verify.Inductive.Nested.Restoration.FreshRecursorSteps

/-! Recursor alignment of a validated nested run: every recursor of the output is
aligned with its abstract translation (`NewRecursorsAligned`).

`NestedRun.recursorsAligned_of` discharges the `Hprovenance`
hypothesis of `NestedRun.assemblyOfRun_of_run`.

The hypothesis quantifies over an arbitrary specialization list carrying
`RestorationTablesAgree`. The restoration `compilationRestoration decl auxiliaries`
is determined by the table data (`RestorationTablesAgree.expr_eq`,
`Nested/Restoration/HeaderRenaming.lean`), so the specialization list of
`restorationTablesRestoringAll`, for which all the formation facts are
available, may be used instead. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

open private Lean.Kernel.Environment.add from Lean.Environment

theorem Kernel.Environment.find?_eq_constants {env : Environment}
    (hwf : env.constants.WF) (name : Name) :
    env.find? name = env.constants.find? name := by
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?]

/-- A source family's header in the lowered environment carries its name. -/
theorem NestedRun.loweredSourceKeyed {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType} {sourceEnv : VEnv}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat} {isUnsafe : Bool}
    {safety : DefinitionSafety} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv L)
    {t : InductiveType} (ht : t ∈ sourceTypes) {info : InductiveVal}
    (hfind : E.loweredEnv.find? t.name = some (.inductInfo info)) :
    info.name = t.name := by
  have hloweredNames : result.types.toArray.toList.map (·.name) =
      E.lowered.loweredDecl.types.map (·.name) :=
    forall₂_map_eq (fun _ _ h => h.header.name.symm) E.lowered.constructors.core.types
  have hmem : t.name ∈ result.types.toArray.toList.map (·.name) := by
    rw [hloweredNames]
    have h := List.mem_map_of_mem (f := (·.name)) ht
    rw [E.sourceNames_eq, List.map_take] at h
    exact List.mem_of_mem_take h
  obtain ⟨u, hu, hun⟩ := List.mem_map.mp hmem
  obtain ⟨iv, -, hinfo, hname, -⟩ := E.lowered.constructors.family_of_mem hu
  have h' := E.lowered.recursors.findHeaderOfMem hinfo
  rw [hname, hun, hfind] at h'
  cases h'
  rw [hname, hun]

/-- **The major inductive of a restored recursor is an inductive type of the
output environment**: a restored source family header, or the container
family of the nested occurrence recorded by lowering. -/
theorem NestedRun.restoredMajorFound
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    {c₀ : AddInductive.Context} {Hc₀ : ContextWF c₀}
    {loweredEnv₀ : Environment} {L : LoweredRun Hc₀ nparams result.types.toArray loweredEnv₀}
    (E : NestedRun result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv L)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecked sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (Haux : List.Forall₂ (SpecializationGenerates
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.lowered.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedOccurrenceReplacementAbs
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.lowered.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.lowered.loweredDecl.types ++
      E.lowered.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTablesAgree sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (owner : Fin E.lowered.signature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.lowered.generatedInstance.recursorName owner) s t) :
    ∃ info, outEnv.constants.find? Hstep.restored.newInfo.getMajorInduct =
      some (.inductInfo info) := by
  let r := compilationRestoration sourceDecl auxiliaries
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hfamNodup : (familyNames (E.lowered.loweredDecl.types.take sourceDecl.types.length) ++
      familyNames (E.lowered.loweredDecl.types.drop sourceDecl.types.length)).Nodup := by
    have h := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.lowered.loweredDecl.types] at h
    simpa only [familyNames, List.flatMap_append] using h
  have hfamRec : ∀ hi, (E.lowered.loweredDecl.types[owner.val]'hi).name ∉
      r.recursors.map Prod.fst := by
    intro hi hmem
    rw [compilationRestoration_recursors_fst] at hmem
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
    have haux : a.auxiliary ∈
        (E.lowered.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
      rw [← auxiliarySpecializations_names Haux Hexpansion]
      exact List.mem_map_of_mem ha
    obtain ⟨t, ht, hta⟩ := List.mem_map.mp haux
    have h1 : (E.lowered.loweredDecl.types[owner.val]'hi).name ∈
        familyNames E.lowered.loweredDecl.types :=
      mem_familyNames_of_type (List.getElem_mem hi)
    have h2 : (E.lowered.loweredDecl.types[owner.val]'hi).name ∈
        E.lowered.loweredDecl.types.map (fun t => t.name.str "rec") := by
      rw [← heq, ← hta]
      exact List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec")
        (List.mem_of_mem_drop ht)
    exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 rfl
  have hfamKey : ∀ hi, (E.lowered.loweredDecl.types[owner.val]'hi).name ∈
      r.heads.map (·.auxiliary) →
      ∃ nested, result.aux2nested.find?
        (E.lowered.loweredDecl.types[owner.val]'hi).name = some nested := by
    intro hi hmem
    rw [hheads] at hmem
    by_cases hlt : owner.val < sourceDecl.types.length
    · exfalso
      have htake : E.lowered.loweredDecl.types[owner.val]'hi ∈
          E.lowered.loweredDecl.types.take sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val, by simp; omega, by simp⟩
      exact (List.nodup_append.mp hfamNodup).2.2 _ (mem_familyNames_of_type htake) _ hmem rfl
    · have hdrop : E.lowered.loweredDecl.types[owner.val]'hi ∈
          E.lowered.loweredDecl.types.drop sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val - sourceDecl.types.length, by simp; omega, by
          simp only [List.getElem_drop]; congr 1; omega⟩
      have hname := List.mem_map_of_mem (f := (·.name)) hdrop
      rw [← auxiliarySpecializations_names Haux Hexpansion] at hname
      obtain ⟨a, ha, haeq⟩ := List.mem_map.mp hname
      obtain ⟨nested, hnested⟩ := D.familyLookup a ha
      exact ⟨nested, haeq ▸ hnested⟩
  have hnestedHead : ∀ name nested, result.aux2nested.find? name = some nested →
      ∃ c ls, nested.getAppFn = .const c ls := by
    intro name nested h
    obtain ⟨I, ls, -, h1, -⟩ := E.auxNestedHead wf Hsources h
    exact ⟨I, ls, h1⟩
  obtain ⟨hi', domain, c, ls, Hbinder, hc, hdisj⟩ := E.restoredMajorHead wf Hsources
    (D.agreement VEnv.empty lparams) hheads hparamsSize D.paramsFVars hnestedHead owner Hstep
    hfamRec hfamKey
  have hmi : Hstep.restored.newInfo.getMajorInduct = c := by
    rw [RecursorVal.getMajorInduct_of_binderAt _ Hbinder, hc]
    rfl
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  obtain ⟨entries, Htrace, -, hheaders⟩ := E.restoration.freshExtensionRecursorSteps hwf
  have houtWF : outEnv.constants.WF := Htrace.targetWF hwf
  rw [hmi]
  rcases hdisj with ⟨hnot, hceq⟩ | ⟨nested, ls', hfindN, hfn⟩
  · have hsourceLength : sourceTypes.length = sourceDecl.types.length := by
      have Hcore := E.sourceCore.core
      rw [E.sourceCoreDecl_eq] at Hcore
      exact Lean4Lean.List.Forall₂.length_eq Hcore.types
    have hlt : owner.val < sourceDecl.types.length := by
      by_contra hge
      apply hnot
      rw [compilationRestoration_heads_auxiliary,
        auxiliarySpecializations_headNames Haux Hexpansion]
      apply mem_familyNames_of_type
      exact List.mem_iff_getElem.mpr ⟨owner.val - sourceDecl.types.length, by simp; omega, by
        simp only [List.getElem_drop]; congr 1; omega⟩
    have hmemNames : (E.lowered.loweredDecl.types[owner.val]'hi').name ∈
        sourceTypes.map (·.name) := by
      rw [E.sourceNames_eq]
      exact List.mem_map_of_mem
        (List.mem_iff_getElem.mpr ⟨owner.val, by simp; omega, by simp⟩)
    obtain ⟨t0, ht0, ht0name⟩ := List.mem_map.mp hmemNames
    obtain ⟨s1, t1, Hind, hmemH⟩ := hheaders t0 ht0
    have hfindH := Htrace.findEntry hwf hmemH
    have hhname : (ConstantInfo.inductInfo Hind.restored.header.newInfo).name = t0.name := by
      change Hind.restored.header.newInfo.name = t0.name
      rw [Hind.restored.header.restored]
      exact (E.loweredSourceKeyed ht0 Hind.lookup : Hind.oldInfo.name = t0.name)
    rw [hhname, Kernel.Environment.find?_eq_constants houtWF] at hfindH
    rw [hceq, ← ht0name]
    exact ⟨_, hfindH⟩
  · obtain ⟨I0, ls0, info0, hfn0, hfind0⟩ := E.auxNestedHead wf Hsources hfindN
    rw [hfn] at hfn0
    simp only [Expr.const.injEq] at hfn0
    rw [hfn0.1]
    rw [Kernel.Environment.find?_eq_constants hwf] at hfind0
    exact ⟨_, Htrace.preservesSourceMapFind hwf hfind0⟩

end VerifyInductive

end Lean4Lean
