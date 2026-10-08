import Lean4Lean.Verify.Inductive.Nested.LoweredRulesAvoid

/-! # Avoidance of all restorable names by the lowered rules

The restorable names of the compilation restoration of a nested run are the
auxiliary family names `_nested.i`, the auxiliary constructor names (the
container constructor names with the container prefix replaced by
`_nested.i`), and the lowered auxiliary recursor names `_nested.i.rec`.

* `NestedValidatedRunResult.restorableNames_reserved`: every restorable name
  lies in the reserved `_nested` namespace.
* `NestedValidatedRunResult.restorableNames_lit`: hence no literal mentions a
  restorable name.
-/

namespace Lean.Expr

open Lean4Lean

/-- **Two trailing hit shapes at different levels give trailing avoidance.** -/
theorem HitTrailWith.toHitTrailAvoids_two {heads names X : List Name} {np : Nat}
    {ls ls' : List Level} {e : Expr}
    (H : HitTrailWith heads np (HitShape names [] ls) e)
    (H' : HitTrailWith heads np (HitShape names [] ls') e)
    (hne : ls ≠ ls') (hX : ∀ n ∈ X, n ∈ names)
    (hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts names) :
    e.HitTrailAvoids heads X np := by
  induction H with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit l => exact .lit _ ((hlit l).mono hX)
  | app _ _ htrail ihf iha =>
    cases H' with
    | app hf' ha' htrail' =>
      exact .app (ihf hf') (iha ha') fun c us hfn hc x hx =>
        ((htrail c us hfn hc x hx).avoids_of_two (htrail' c us hfn hc x hx) hne hlit).mono hX
  | lam _ _ iht ihb => cases H' with | lam ht hb => exact .lam (iht ht) (ihb hb)
  | forallE _ _ iht ihb => cases H' with | forallE ht hb => exact .forallE (iht ht) (ihb hb)
  | letE _ _ _ iht ihv ihb =>
    cases H' with | letE ht hv hb => exact .letE (iht ht) (ihv hv) (ihb hb)
  | mdata _ ih => cases H' with | mdata h => exact .mdata (ih h)
  | proj _ ih => cases H' with | proj h => exact .proj (ih h)

end Lean.Expr

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open InductiveSignature
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

section Reserved

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- **Every restorable name lies in the reserved `_nested` namespace.** Each
auxiliary family name is `_nested.i` (`resultFamilyNamesReservedOfEmpty`),
each auxiliary constructor name is obtained by replacing the container prefix
of a container constructor name by the auxiliary family name (the replacement
is effective, `RestorationTableData.ctorRenamed`), and each auxiliary recursor
name is `A.rec` for an auxiliary family name `A`. -/
theorem NestedValidatedRunResult.restorableNames_reserved
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      (`_nested).isPrefixOf n = true := by
  rcases E.lowering with ⟨finalState, Hrun, -, -⟩
  have hres := Hrun.resultFamilyNamesReservedOfEmpty rfl
  have hauxRes : ∀ a ∈ auxiliaries, NamePrefix `_nested a.auxiliary := by
    intro a ha
    obtain ⟨nested, hfind⟩ := D.familyLookup a ha
    exact namePrefix_of_isPrefixOf (hres _ _ hfind)
  intro n hn
  simp only [Restoration.restorableNames, compilationRestoration_heads_auxiliary,
    compilationRestoration_recursors_fst, List.mem_append, List.mem_flatMap,
    List.mem_map] at hn
  rcases hn with ⟨a, ha, hn⟩ | ⟨a, ha, rfl⟩
  · simp only [ContainerSpecialization.headNames, List.mem_cons, List.mem_map] at hn
    rcases hn with rfl | ⟨ctor, hctor, rfl⟩
    · exact (hauxRes a ha).isPrefixOf
    · have hP := namePrefix_of_replacePrefix_ne (D.ctorRenamed a ha ctor hctor)
      exact ((hauxRes a ha).trans' (hP.replacePrefix_prefix a.auxiliary)).isPrefixOf
  · exact (NamePrefix.str "rec" (hauxRes a ha)).isPrefixOf

/-- **No literal mentions a restorable name**: the constants of the
constructor form of a literal (`Nat.zero`, `Nat.succ`, `Char.ofNat`,
`String.ofList`, `List.nil`, `List.cons`, `Char`) lie outside the reserved
`_nested` namespace. -/
theorem NestedValidatedRunResult.restorableNames_lit
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ l : Literal, l.toConstructor.AvoidsConsts
      (compilationRestoration sourceDecl auxiliaries).restorableNames := by
  intro l
  have h := avoidsConsts_lit_of_reserved (E.restorableNames_reserved D) l
  cases h with
  | lit _ h => exact h

end Reserved

/-! ### Freshness of the recursor names -/

/-- The entries of a lockstep installation are fresh in its source. -/
theorem AddConstants.entry_fresh {safety : DefinitionSafety} {env : Environment}
    {venv : VEnv} {entries : List (ConstantInfo × VConstVal)} {outEnv : Environment}
    {outVEnv : VEnv}
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hwf : env.constants.WF) :
    ∀ entry ∈ entries, env.find? entry.1.name = none := by
  induction H with
  | nil => intro entry h; simp at h
  | cons hn hnprim htr hciwf hadd hdelta Htail ih =>
    rename_i venvHead ci ci' venvNext rest outProd outAbs envHead
    have hfreshMap : envHead.constants.find? ci.name = none := by
      rwa [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at hn
    have hnextWF : (envHead.add ci).constants.WF := by
      change (envHead.constants.insert ci.name ci).WF
      exact hwf.insert ci.name ci hfreshMap
    intro entry hentry
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · exact hn
    · have h := ih hnextWF entry htail
      cases hold : envHead.find? entry.1.name with
      | none => rfl
      | some found =>
        exfalso
        have hne : ci.name ≠ entry.1.name := by
          intro heq; rw [← heq, hn] at hold; cases hold
        have := addConstant_find_of_ne envHead ci entry.1.name hwf hn hne hold
        change (envHead.add ci).find? entry.1.name = some found at this
        rw [h] at this; cases this

section RecNames

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- The lowered auxiliary recursor names of a nested run: `A.rec` for the
lowered families `A` after the source families. -/
def NestedValidatedRunResult.auxRecNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) : List Name :=
  (E.production.loweredDecl.types.drop sourceDecl.types.length).map
    fun t => t.name.str "rec"

/-- Lowered recursor names are not lowered family or constructor names. -/
theorem NestedValidatedRunResult.auxRecNames_not_familyNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {n : Name} (hn : n ∈ E.auxRecNames) :
    n ∉ familyNames E.production.loweredDecl.types := by
  obtain ⟨-, -, -, -, -, -, -, hnodup⟩ := E.auxHeadsFacts wf Hsources
  intro hfam
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
  exact (List.nodup_append.1 hnodup).2.2 _ hfam _
    (List.mem_map.2 ⟨t, List.mem_of_mem_drop ht, rfl⟩) rfl

/-- Lowered recursor names lie in the reserved `_nested` namespace. -/
theorem NestedValidatedRunResult.auxRecNames_reserved
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ n ∈ E.auxRecNames, (`_nested).isPrefixOf n = true := by
  obtain ⟨-, -, -, -, -, hreserved, -, -⟩ := E.auxHeadsFacts wf Hsources
  intro n hn
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
  have h := hreserved t.name (List.mem_flatMap.2 ⟨t, ht, List.mem_cons_self⟩)
  exact (NamePrefix.str "rec" (namePrefix_of_isPrefixOf h)).isPrefixOf

/-- **The lowered recursor names are fresh in the recursor-pass environment**:
the recursor installation adds each of them to it. -/
theorem NestedValidatedRunResult.auxRecNames_fresh_ctorEnv
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) :
    ∀ n ∈ E.auxRecNames, E.production.ctorEnv.find? n = none := by
  let P := E.production.production
  have hwf : P.localContext.env.constants.WF := by
    rw [P.localExtends.env_eq]
    exact E.production.constructors.completed.context.checking.tr.map_wf
  intro n hn
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hn
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (List.mem_of_mem_drop ht)
  have hname := P.toCompletedRecursorConstruction.indTypeName_eq hi
  have hrec : i < P.toCompletedRecursorConstruction.recInfos.size := by
    rw [P.toCompletedRecursorConstruction.recInfos_size_eq]; exact hi
  have hent : i < P.entries.length := by rw [P.generated.length]; exact hrec
  have G := P.generated.entry i hent
  have hfresh := P.installed.entry_fresh hwf P.entries[i] (List.getElem_mem hent)
  rw [G.source_eq] at hfresh
  change P.localContext.env.find? G.info.name = none at hfresh
  rw [G.name, ← E.recursorPassEnv] at *
  rw [hname]
  exact hfresh

/-- The lowered recursor names are fresh in the source environment. -/
theorem NestedValidatedRunResult.auxRecNames_fresh_source
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) :
    ∀ n ∈ E.auxRecNames, sourceProdEnv.find? n = none := by
  intro n hn
  cases h : sourceProdEnv.find? n with
  | none => rfl
  | some ci =>
    have := E.ctorEnv_preserves wf h
    rw [E.auxRecNames_fresh_ctorEnv n hn] at this
    cases this

/-- The lowered recursor names are fresh in the header environment. -/
theorem NestedValidatedRunResult.auxRecNames_fresh_headerVEnv
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    ∀ n ∈ E.auxRecNames, E.production.headers.context.venv.constants n = none := by
  intro n hn
  have hadded := E.production.constructors.core.typesAdded
  have hne : ∀ ci ∈ E.production.loweredDecl.typeConstants, ci.name ≠ n := by
    intro ci hci heq
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hci
    exact E.auxRecNames_not_familyNames wf Hsources hn
      (heq ▸ List.mem_flatMap.2 ⟨t', ht', List.mem_cons_self⟩)
  rw [VEnv.addConstVals_constants_of_forall_ne hadded hne]
  cases hv : E.production.initialEnv.constants n with
  | none => rfl
  | some ci =>
    exfalso
    rw [E.production_initialEnv] at hv
    obtain ⟨ci', hfind, -⟩ :=
      (wf.tr (safety := if isUnsafe then .unsafe else .safe)).find?_iff.2 ⟨ci, hv⟩
    rw [E.auxRecNames_fresh_source wf n hn] at hfind; cases hfind

theorem hitPrimNames_not_reserved : ∀ n ∈ hitPrimNames, (`_nested).isPrefixOf n = false := by
  decide

theorem hitStrNames_not_reserved : ∀ n ∈ hitStrNames, (`_nested).isPrefixOf n = false := by
  decide

/-- **The environment condition of the hit-shape invariant at the lowered
recursor names**, without parameters, at any level list: the lowered
recursor names are not constants of the recursor-pass environment, and no
constant's type, value or rule mentions them. -/
theorem NestedValidatedRunResult.envHitShape_auxRecNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (ls : List Level) :
    EnvHitShape E.production.ctorEnv E.auxRecNames 0 ls := by
  have hfresh : ∀ n ∈ E.auxRecNames, sourceProdEnv.find? n = none :=
    E.auxRecNames_fresh_source wf
  have hfreshC := E.auxRecNames_fresh_ctorEnv
  have hpres : ∀ {n ci}, sourceProdEnv.find? n = some ci →
      E.production.ctorEnv.find? n = some ci := E.ctorEnv_preserves wf
  have hwfP : E.production.c.env.constants.WF := by
    rw [E.productionEnv]; exact (wf.tr (safety := .unsafe)).map_wf
  have horigin : ∀ {n ci}, E.production.ctorEnv.find? n = some ci →
      sourceProdEnv.find? n = some ci ∨
      (∃ indType ∈ E.production.indTypes.toList, ∃ info : InductiveVal,
        ci = .inductInfo info ∧ n = indType.name ∧ info.type = indType.type ∧
        info.levelParams = lparams) ∨
      (∃ owner ∈ E.production.indTypes.toList, ∃ ctor ∈ owner.ctors, ∃ info : ConstructorVal,
        ci = .ctorInfo info ∧ n = ctor.name ∧ info.type = ctor.type ∧
        info.levelParams = lparams) := by
    intro n ci h
    have := E.production.ctorEnv_origin hwfP h
    rwa [E.productionEnv, E.productionLParams] at this
  have hnotIn : ∀ {n ci}, E.production.ctorEnv.find? n = some ci → n ∉ E.auxRecNames :=
    fun h hn => by rw [hfreshC _ hn] at h; cases h
  let sf : DefinitionSafety := if isUnsafe then .unsafe else .safe
  have hheaderV : E.production.headers.context.venv.Ordered :=
    E.production.headers.context.checking.tr.wf.ordered
  have hheaderSub : ∀ s info, E.production.headers.context.venv.projections s info →
      ∃ info', (ves.venv sf).projections s info' := by
    intro s info h
    rw [VEnv.addConstVals_projections_eq E.production.constructors.core.typesAdded,
      E.production_initialEnv] at h
    exact ⟨info, h⟩
  have hreserved := E.auxRecNames_reserved wf Hsources
  refine {
    prims := ?prims
    strs := ?strs
    type_avoids := ?type_avoids
    value_avoids := ?value_avoids
    rules_avoid := ?rules_avoid
    head_kind := ?head_kind
    head_type := ?head_type
    rec_major := ?rec_major
    type_projs := ?type_projs
    value_projs := ?value_projs
    rules_projs := ?rules_projs }
  case prims =>
    intro n hn hmem
    have h1 := hreserved n hmem
    rw [hitPrimNames_not_reserved n hn] at h1; cases h1
  case strs =>
    intro _ n hn hmem
    have h1 := hreserved n hmem
    rw [hitStrNames_not_reserved n hn] at h1; cases h1
  case type_avoids =>
    intro n ci h _
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, rfl, htype, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, rfl, htype, -⟩
    · exact (old_type_avoids wf hfresh hold).1
    · show info.type.AvoidsConsts _
      rw [htype]
      obtain ⟨e', htr⟩ := E.familyType_tr hmem
      exact avoids_of_tr wf hfresh _ htr
    · show info.type.AvoidsConsts _
      rw [htype]
      obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr howner hctor
      exact checkPositivityStep.TrExprS.sourceAvoidsFresh
        (E.auxRecNames_fresh_headerVEnv wf Hsources) htr
  case value_avoids =>
    intro n ci v h hv
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · exact (old_value_avoids wf hfresh hold hv).1
    · cases hv
    · cases hv
  case rules_avoid =>
    intro n r h rule hrule
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · exact (old_rules_avoid wf hfresh hold hrule).1
    · cases heq
    · cases heq
  case head_kind =>
    intro n ci h hn
    exact absurd hn (hnotIn h)
  case head_type =>
    intro n ci h hn
    exact absurd hn (hnotIn h)
  case rec_major =>
    intro n r h
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · exact old_rec_major wf hpres hfresh hold
    · cases heq
    · cases heq
  case type_projs =>
    intro n ci h
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -, htype, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -, htype, -⟩
    · obtain ⟨e', htr⟩ := (old_type_avoids wf hfresh hold).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · show info.type.ProjsOK _
      rw [htype]
      obtain ⟨e', htr⟩ := E.familyType_tr hmem
      exact projsOK_of_tr_sub wf hpres hfresh sf (wf.tr (safety := sf)).wf.ordered
        (fun s i h => ⟨i, h⟩) htr
    · show info.type.ProjsOK _
      rw [htype]
      obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr howner hctor
      exact projsOK_of_tr_sub wf hpres hfresh sf hheaderV hheaderSub htr
  case value_projs =>
    intro n ci v h hv
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · obtain ⟨e', htr⟩ := (old_value_avoids wf hfresh hold hv).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · cases hv
    · cases hv
  case rules_projs =>
    intro n r h rule hrule
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · obtain ⟨e', htr⟩ := (old_rules_avoid wf hfresh hold hrule).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · cases heq
    · cases heq

/-- **The trailing-provenance inputs at the lowered recursor names**, at any
level list. -/
theorem NestedValidatedRunResult.trailInputs_auxRecNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (ls : List Level) :
    E.production.production.toCompletedRecursorConstruction.TrailInputs
      E.auxRecNames ls := by
  let sf : DefinitionSafety := if isUnsafe then .unsafe else .safe
  have hfresh : ∀ n ∈ E.auxRecNames, sourceProdEnv.find? n = none :=
    E.auxRecNames_fresh_source wf
  have hpres : ∀ {n ci}, sourceProdEnv.find? n = some ci →
      E.production.production.toCompletedRecursorConstruction.localContext.env.find?
        n = some ci := by
    intro n ci h
    have := E.ctorEnv_preserves wf h
    rw [← E.recursorPassEnv] at this
    exact this
  have hnp : result.nparams = nparams := by
    obtain ⟨_, Hrun, _, _⟩ := E.lowering
    exact Hrun.resultNParams
  have hheaderV : E.production.headers.context.venv.Ordered :=
    E.production.headers.context.checking.tr.wf.ordered
  have hheaderSub : ∀ s info, E.production.headers.context.venv.projections s info →
      ∃ info', (ves.venv sf).projections s info' := by
    intro s info h
    rw [VEnv.addConstVals_projections_eq E.production.constructors.core.typesAdded,
      E.production_initialEnv] at h
    exact ⟨info, h⟩
  have hmem : ∀ i, i < E.production.indTypes.size →
      E.production.indTypes[i]! ∈ E.production.indTypes.toList := by
    intro i hi
    rw [getElem!_pos E.production.indTypes i hi]
    exact Array.getElem_mem_toList hi
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine E.production.production.toCompletedRecursorConstruction.paramDecls_trail
      (fun n hn => ?_) (fun s info h => ?_)
    · rw [E.production_initialEnv]
      cases hc : (ves.venv sf).constants n with
      | none => rfl
      | some ci =>
        obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨ci, hc⟩
        rw [hfresh n hn] at hfind; cases hfind
    · rw [E.production_initialEnv] at h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, -⟩ :=
        (wf.tr (safety := sf)).wf.ordered.projectionShape h
      obtain ⟨ci, hci, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨_, hlookup⟩
      exact projHitOK_of_old wf hpres hfresh hci
  · intro i hi
    obtain ⟨e', htr⟩ := E.familyType_tr (hmem i hi)
    exact ⟨avoids_of_tr wf hfresh _ htr,
      projsOK_of_tr_sub wf hpres hfresh sf (wf.tr (safety := sf)).wf.ordered
        (fun s i h => ⟨i, h⟩) htr⟩
  · intro i hi ctor hctor
    obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr (hmem i hi) hctor
    refine ⟨?_, checkPositivityStep.TrExprS.sourceAvoidsFresh
        (E.auxRecNames_fresh_headerVEnv wf Hsources) htr,
      projsOK_of_tr_sub wf hpres hfresh sf hheaderV hheaderSub htr⟩
    obtain ⟨body, hl, -⟩ := E.ctorTypes_headType wf Hsources _ (hmem i hi) ctor hctor
    rw [E.statsParamsSize, hnp]
    exact ⟨body, hl.leadingBinders⟩
  · intro i hi n lv hn hmemN
    have H := E.production.production.toCompletedRecursorConstruction
    have hi' : i < E.production.loweredDecl.types.length := by
      rw [← E.production.production.toCompletedRecursorConstruction.recInfos_size_eq]
      exact hi
    have h := E.production.production.toCompletedRecursorConstruction.validStats.indConstAt hi'
    rw [getElem!_def, h] at hn
    cases hn
    exact E.auxRecNames_not_familyNames wf Hsources hmemN
      (List.mem_flatMap.2 ⟨_, List.getElem_mem hi', List.mem_cons_self⟩)

/-- A level list of length `lparams.length + 2`, different from `badLevels`. -/
def badLevels₂ (lparams : List Name) : List Level :=
  List.replicate (lparams.length + 2) .zero

theorem badLevels_ne_badLevels₂ (lparams : List Name) : badLevels lparams ≠ badLevels₂ lparams := by
  intro h
  have := congrArg List.length h
  simp [badLevels, badLevels₂] at this

/-- **Input-side avoidance of the lowered recursor names by the lowered
rules.** The trailing provenance chain runs at the lowered recursor names
without parameters at two different level lists (`badLevels`, `badLevels₂`):
the recursor-pass environment does not contain them and no constant mentions
them (`envHitShape_auxRecNames`), and the recursive calls put the recursors
only at spine heads (`HitTrailWith.instantiate1'_argClosed`). The trailing
arguments mention them only at both level lists, hence not at all. -/
theorem NestedValidatedRunResult.loweredRulesAvoid_auxRecNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (heads : List Name) :
    E.LoweredRulesAvoid heads E.auxRecNames := by
  intro owner rec hfind rule hrule
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfFind owner hfind
  let C := E.production.production
  have howner : owner.val < C.recInfos.size := by rw [← C.generated.length]; exact hi
  have hrule' : rule ∈ (C.generated.entry owner.val hi).info.rules := by rw [hinfo]; exact hrule
  rw [(C.generated.entry owner.val hi).rules_eq] at hrule'
  simp only [List.mem_map] at hrule'
  obtain ⟨blueprint, hmem, rfl⟩ := hrule'
  have W : ∀ ls, WhnfHitOKFacts E.auxRecNames [] ls
      E.production.production.localContext.env := by
    intro ls
    refine .of_env ?_ (fun a ha => by simp at ha)
    rw [E.recursorPassEnv]
    exact E.envHitShape_auxRecNames wf Hsources ls
  obtain ⟨HT, HL⟩ := C.toCompletedRecursorConstruction.ruleRhsTrail
    (E.trailInputs_auxRecNames wf Hsources (badLevels lparams)) (W _)
    heads result.nparams owner.val howner
    (AddInductive.getRecLevels C.elimLevel E.production.stats.levels) blueprint hmem
  obtain ⟨HT', -⟩ := C.toCompletedRecursorConstruction.ruleRhsTrail
    (E.trailInputs_auxRecNames wf Hsources (badLevels₂ lparams)) (W _)
    heads result.nparams owner.val howner
    (AddInductive.getRecLevels C.elimLevel E.production.stats.levels) blueprint hmem
  have hsize : E.production.stats.params.size = result.nparams := E.statsParamsSize
  rw [hsize] at HL
  have hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts E.auxRecNames :=
    avoidsConsts_lit_of_reserved (E.auxRecNames_reserved wf Hsources)
  exact ⟨HT.toHitTrailAvoids_two HT' (badLevels_ne_badLevels₂ lparams) (fun _ h => h) hlit, HL⟩

end RecNames

end VerifyInductive
end Lean4Lean
