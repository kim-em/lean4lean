import Lean4Lean.Verify.Inductive.Nested.Restoration.LoweredRuleAvoidance
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.ProjNames

/-! # Avoidance of all restorable names by the lowered rules

The restorable names of the compilation restoration of a nested run are the
auxiliary family names `_nested.i`, the auxiliary constructor names (the
container constructor names with the container prefix replaced by
`_nested.i`), and the lowered auxiliary recursor names `_nested.i.rec`
(`restorableNames_cover`).

* `NestedValidatedRunResult.restorableNames_reserved`: every restorable name
  lies in the reserved `_nested` namespace; `restorableNames_lit`: hence no
  literal mentions a restorable name.
* `NestedValidatedRunResult.loweredRulesAvoid_auxRecNames`: the lowered rules
  avoid the lowered auxiliary recursor names (trailing arguments of hits of
  any head list, literals, parameter domains). The recursor names are fresh
  in the recursor-pass environment (`auxRecNames_fresh_ctorEnv`: the
  recursor installation adds them), so the hit-shape invariant holds at them
  at every level list (`envHitShape_auxRecNames`); the trailing provenance
  chain `ruleRhsTrail` admits the recursor names (their occurrences in the
  rules are the heads of the recursive calls), and running it at two
  different level lists excludes them from trailing positions
  (`HitTrailWith.toHitTrailAvoids_two`).
* `NestedValidatedRunResult.loweredRules_projsOK`: the lowered rules project
  out of no restorable name. The projection condition of the hit-shape chain
  (`CompletedRecursorConstruction.ruleRhsProjsOK`) excludes the auxiliary
  families and constructors; the translation of a rule in the recursor-pass
  environment registers only base structures and lowered families, which
  excludes the recursor names.
* `NestedValidatedRunResult.loweredRulesAvoid_restorable_of_families`: the
  lowered rules avoid every restorable name, given that they avoid the
  auxiliary family names (`E.LoweredRulesAvoid heads E.auxFamilyNames`).

The auxiliary family names do occur in the recursor-pass environment (in the
lowered constructor types), so the level argument does not apply to them.
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

namespace Lean.Expr

open Lean4Lean

namespace ProjsOK

variable {ok : Name → Prop}

theorem mkLambda' {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId} {b : Expr}
    (hxs : xs = (ys.map Expr.fvar).toArray) (H : ProjsOK ok b)
    (hdecl : ∀ y ∈ ys, ∃ d, lctx.find? y = some d ∧ d.DeclProjsOK ok) :
    ProjsOK ok (lctx.mkLambda xs b) := by
  subst hxs
  simpa [LocalContext.mkLambda] using H.mkBinding' (isLambda := true) (lctx := lctx) hdecl

theorem and' {ok₁ ok₂ : Name → Prop} : ∀ {e : Expr}, ProjsOK ok₁ e → ProjsOK ok₂ e →
    ProjsOK (fun s => ok₁ s ∧ ok₂ s) e
  | .app _ _, h₁, h₂ => ⟨and' h₁.1 h₂.1, and' h₁.2 h₂.2⟩
  | .lam _ _ _ _, h₁, h₂ => ⟨and' h₁.1 h₂.1, and' h₁.2 h₂.2⟩
  | .forallE _ _ _ _, h₁, h₂ => ⟨and' h₁.1 h₂.1, and' h₁.2 h₂.2⟩
  | .letE _ _ _ _ _, h₁, h₂ => ⟨and' h₁.1 h₂.1, and' h₁.2.1 h₂.2.1, and' h₁.2.2 h₂.2.2⟩
  | .mdata _ e, h₁, h₂ => and' (e := e) h₁ h₂
  | .proj _ _ _, h₁, h₂ => ⟨⟨h₁.1, h₂.1⟩, and' h₁.2 h₂.2⟩
  | .bvar _, _, _ | .fvar _, _, _ | .mvar _, _, _ | .sort _, _, _ | .const .., _, _
  | .lit _, _, _ => trivial

end ProjsOK

end Lean.Expr

namespace Lean.Expr

open Lean4Lean

/-- Trailing avoidance of a list covered by two avoided lists. -/
theorem HitTrailAvoids.of_cover {heads L L₁ L₂ : List Name} {np : Nat}
    (hcover : ∀ n ∈ L, n ∈ L₁ ∨ n ∈ L₂) {e : Expr}
    (h₁ : e.HitTrailAvoids heads L₁ np) (h₂ : e.HitTrailAvoids heads L₂ np) :
    e.HitTrailAvoids heads L np := by
  induction h₁ with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit _ h => cases h₂ with | lit _ h' => exact .lit _ (AvoidsConsts.of_cover hcover h h')
  | app _ _ htrail ihf iha =>
    cases h₂ with
    | app hf ha htrail' =>
      exact .app (ihf hf) (iha ha) fun c us hfn hc x hx =>
        AvoidsConsts.of_cover hcover (htrail c us hfn hc x hx) (htrail' c us hfn hc x hx)
  | lam _ _ iht ihb => cases h₂ with | lam ht hb => exact .lam (iht ht) (ihb hb)
  | forallE _ _ iht ihb => cases h₂ with | forallE ht hb => exact .forallE (iht ht) (ihb hb)
  | letE _ _ _ iht ihv ihb =>
    cases h₂ with | letE ht hv hb => exact .letE (iht ht) (ihv hv) (ihb hb)
  | mdata _ ih => cases h₂ with | mdata h => exact .mdata (ih h)
  | proj _ ih => cases h₂ with | proj h => exact .proj (ih h)

/-- Lambda-prefix avoidance of a list covered by two avoided lists. -/
theorem LamPrefixAvoids.of_cover {L L₁ L₂ : List Name}
    (hcover : ∀ n ∈ L, n ∈ L₁ ∨ n ∈ L₂) {k : Nat} {e : Expr}
    (h₁ : LamPrefixAvoids L₁ k e) (h₂ : LamPrefixAvoids L₂ k e) :
    LamPrefixAvoids L k e := by
  induction h₁ with
  | zero => exact .zero _
  | succ hd _ ih =>
    cases h₂ with | succ hd' hb => exact .succ (AvoidsConsts.of_cover hcover hd hd') (ih hb)

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

/-! ### The projection condition of the generated rule right-hand sides -/

section RuleProjs

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
    sourceEnv indTypes ctorEnv}

namespace CompletedRecursorConstruction

variable (H : CompletedRecursorConstruction R)

/-- **The projection condition of one rule blueprint**: its field
declarations and its recursive-call templates satisfy the projection
condition of the hit-shape chain. -/
theorem blueprintProjsOK {heads : List Name} (I : H.HitShapeInputs heads)
    (W : WhnfHitOKFacts heads stats.params.toList stats.levels H.localContext.env)
    (owner : Nat) (howner : owner < H.recInfos.size) (localIndex : Nat)
    (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (∀ y ∈ (H.origins.minorShapes owner howner localIndex hlocal).fields_bound.fvars,
      ∃ d, (H.origins.minorShapes owner howner localIndex hlocal).sourceFullContext.lctx.find? y
        = some d ∧ d.DeclProjsOK (projHitOK H.localContext.env heads)) ∧
    (∀ j, j < (H.origins.minorShapes owner howner localIndex hlocal).hypotheses.size →
      (H.recInfos[owner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).template.ProjsOK
        (projHitOK H.localContext.env heads)) := by
  have hsourceOwner := H.sourceOwner howner
  have hsrc := H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have hcallRoots : RecInfoRuleBlueprintOriginAt stats
      (H.origins.minorShapes owner howner localIndex hlocal)
      H.recInfos[owner]!.minors[localIndex]!
      H.recInfos[owner]!.ruleBlueprints[localIndex]! :=
    H.blueprints.entry owner howner localIndex hlocal
  obtain ⟨Hsem⟩ := H.blueprintSemantics.entry owner howner localIndex hlocal
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at hsrc hcallRoots Hsem ⊢
  generalize H.recInfos[owner]!.ruleBlueprints[localIndex]! = B at hcallRoots Hsem ⊢
  obtain ⟨-, -, hsourceCtors, -, traversal, htrav, -, -, -, -, -, -, -, -,
    hsrcLE⟩ := hsrc
  obtain ⟨origins, hshape, hstats, -, F, -⟩ := Hsem
  obtain ⟨-, -, -, -, -, callOrigins, -, hcallShape, -, -, Hcalls⟩ := hcallRoots
  have hcallOrigins : callOrigins = origins :=
    Option.some.inj (hcallShape.symm.trans hshape)
  subst callOrigins
  have hT : traversal = F.traversal := Option.some.inj (htrav.symm.trans F.traversal_eq)
  subst hT
  have hp := H.params_fvar
  have Hroot := F.rootWF.toBindingContextWF
  have hTL : BindingContextLE F.traversal.terminalContext H.localContext :=
    F.terminalExtension.contextLE
  have Hprefix : RecursorParamPrefix stats 0 S.constructor.type
      F.traversal.parameterTail := by
    have := F.traversal.parameterPrefix
    rwa [F.traversal_stats, F.traversal_constructor] at this
  have hctorMem : S.constructor ∈ indTypes[owner]!.ctors := by
    rw [← hsourceCtors]; exact List.mem_of_getElem? S.sourceConstructor
  have Htail := Hprefix.hitOK H.params.expressions
    (I.constructorTypes owner hsourceOwner _ hctorMem).1
    (I.constructorTypes owner hsourceOwner _ hctorMem).2
  obtain ⟨-, hfieldsTerm⟩ := F.traversal.decisions.hitOK Hroot hp Htail
  rw [F.traversal_fields] at hfieldsTerm
  have hfieldDecls : ∀ y ∈ S.fields_bound.fvars, ∃ d,
      S.sourceFullContext.lctx.find? y = some d ∧
        d.DeclProjsOK (projHitOK H.localContext.env heads) := by
    intro y hy
    obtain ⟨fv, index, name, type, bi, kind, hfv, hmem, hfind, htype⟩ :=
      hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hy)
    cases hfv
    refine ⟨.cdecl index y name type bi kind, ?_, htype.2⟩
    rw [← hsrcLE.declarations y (S.fields_bound.members y hy),
      hTL.declarations y hmem, hfind]
  have hparamTerm : ∀ pv, Expr.fvar pv ∈ stats.params →
      pv ∈ F.traversal.terminalContext.lctx.fvars := fun pv h =>
    (F.traversal.decisions.freshBindings Hroot).choose_spec.1.fvars
      (F.parameterSuffix.param_mem h)
  have hfr : origins.fieldRoot = F.traversal.terminalContext :=
    S.hypothesis_origins_fieldRoot origins F.traversal hshape F.traversal_eq
  refine ⟨hfieldDecls, fun j hj => ?_⟩
  obtain ⟨originRoot, sourceType, recL, Rorigin, O, D, hle, hup, hD, hcall⟩ :=
    Hcalls.rooted j hj
  rw [hstats] at hup
  rw [hfr] at hle
  have henv : originRoot.env = H.localContext.env := hle.env_eq.trans hTL.env_eq.symm
  have hscope : Rorigin.HitOKScope H.localContext.env heads stats.params.toList
      stats.levels
      (fun fv => fv ∈ ExprArrayFVarIds S.fields ∨
        fv ∈ ExprArrayFVarIds stats.params) := by
    refine ⟨hup, fun fv decl hP hfind => ?_⟩
    rw [Rorigin.lctx_eq] at hfind
    rcases hP with hf | hpar
    · rw [S.fields_bound.exprArrayFVarIds] at hf
      obtain ⟨fv', index, name, type, bi, kind, hfv, hmem, hfind', htype⟩ :=
        hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hf)
      cases hfv
      rw [hle.declarations fv hmem, hfind'] at hfind
      cases hfind
      exact LocalDecl.HitOK.of_cdecl htype
    · rw [H.params.exprArrayFVarIds] at hpar
      have hmemP := H.params.mem_fvars_iff.1 hpar
      rw [hle.declarations fv (hparamTerm fv hmemP),
        ← hTL.declarations fv (hparamTerm fv hmemP)] at hfind
      exact I.paramDecls fv hpar decl hfind
  have hjr : j < S.recursiveFields.size := by rw [← S.hypotheses_size]; exact hj
  have hfieldMem : S.recursiveFields[j]! ∈ S.fields := by
    rw [← F.traversal_fields]
    apply F.traversal.decisions.selected_subset
    rw [F.traversal_recursiveFields, getElem!_pos S.recursiveFields j hjr]
    exact Array.getElem_mem hjr
  have hfieldP : ∀ fv, S.recursiveFields[j]! = .fvar fv →
      (fun fv => fv ∈ ExprArrayFVarIds S.fields ∨
        fv ∈ ExprArrayFVarIds stats.params) fv := by
    intro fv hfv
    left
    rw [hfv] at hfieldMem
    exact mem_exprArrayFVarIds_of_fvar_mem hfieldMem
  obtain ⟨hargs, hexp, -⟩ := O.templateFacts W hp henv Rorigin hscope hfieldP
  rw [hcall]
  obtain ⟨ffv, hffv, -⟩ := O.field_fvar
  refine Expr.ProjsOK.mkLambda' O.arguments_bound.expressions ?_ ?_
  · refine ⟨Expr.ProjsOK.mkAppN' trivial (hexp.2.getAppArgs_slice' _),
      Expr.ProjsOK.mkAppN' (by rw [hffv]; trivial) ?_⟩
    intro a ha
    rw [O.arguments_bound.expressions] at ha
    simp only [List.mem_map] at ha
    obtain ⟨y, -, rfl⟩ := ha
    trivial
  · intro y hy
    have hyCur : y ∈ O.current.lctx.fvars := O.arguments_bound.members y hy
    obtain ⟨index, name, ty, bi, kind, hfind⟩ := O.current_wf.findCDecl y hyCur
    exact ⟨_, hfind, (hargs y hy _ hfind).1.declProjsOK⟩

/-- **Generated rule right-hand sides satisfy the projection condition** of
the hit-shape chain: they are built from the parameters, motives and minor
premises of the recursor type, the constructor fields, and the recursive-call
templates, whose substituent (a recursor applied to free variables) has no
projection. -/
theorem ruleRhsProjsOK {heads : List Name} (I : H.HitShapeInputs heads)
    (W : WhnfHitOKFacts heads stats.params.toList stats.levels H.localContext.env)
    (owner : Nat) (howner : owner < H.recInfos.size) (lvls : List Level)
    (blueprint : AddInductive.RecRuleBlueprint)
    (hmem : blueprint ∈ H.recInfos[owner]!.ruleBlueprints.toList) :
    (blueprint.build indTypes stats (H.recInfos.map (·.motive))
        (H.recInfos.flatMap (·.minors)) lvls H.localContext.lctx).rhs.ProjsOK
      (projHitOK H.localContext.env heads) := by
  obtain ⟨localIndex, hlocalB, hget⟩ := List.mem_iff_getElem.1 hmem
  have hlocalB' : localIndex < H.recInfos[owner]!.ruleBlueprints.size := by simpa using hlocalB
  have hlocal : localIndex < H.origins.minorTypes[owner]!.size := by
    rw [← H.blueprints.rows_size owner howner]; exact hlocalB'
  have hB : H.recInfos[owner]!.ruleBlueprints[localIndex]! = blueprint := by
    rw [getElem!_pos _ localIndex hlocalB']; simpa using hget
  obtain ⟨hfieldDecls, hcalls⟩ := H.blueprintProjsOK I W owner howner localIndex hlocal
  have hentry := H.blueprints.entry owner howner localIndex hlocal
  rw [hB] at hcalls hentry
  obtain ⟨-, hBfields, hBlctx, hBminor, traversal, origins, -, hshape, -, -, hcallOrigins⟩ :=
    hentry
  have hcallsSize := hcallOrigins.size_eq
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at *
  have hminorsSize : localIndex < H.recInfos[owner]!.minors.size := by
    rw [← (H.origins.minors owner howner).size_eq]; exact hlocal
  have hminorMem : blueprint.minor ∈ H.recInfos[owner]!.minors := by
    rw [hBminor, getElem!_pos _ localIndex hminorsSize]; exact Array.getElem_mem hminorsSize
  obtain ⟨minorFv, hminorFv, -⟩ :=
    BoundFVarArray.fvar_of_mem (H.bindings.minors owner howner) hminorMem
  simp only [AddInductive.RecRuleBlueprint.build]
  have hbody : (mkAppN (mkAppN blueprint.minor blueprint.fields)
      (blueprint.recursiveCalls.map fun call =>
        call.build indTypes stats (H.recInfos.map (·.motive))
          (H.recInfos.flatMap (·.minors)) lvls)).ProjsOK
        (projHitOK H.localContext.env heads) := by
    refine Expr.ProjsOK.mkAppN' (Expr.ProjsOK.mkAppN' (by rw [hminorFv]; trivial)
      fun a ha => ?_) fun a ha => ?_
    · rw [hBfields] at ha
      obtain ⟨y, rfl, -⟩ := BoundFVarArray.fvar_of_mem S.fields_bound
        (Array.mem_toList_iff.1 ha)
      trivial
    · simp only [Array.toList_map, List.mem_map] at ha
      obtain ⟨call, hcall, rfl⟩ := ha
      obtain ⟨j, hj, hcallj⟩ := List.mem_iff_getElem.1 hcall
      have hj' : j < blueprint.recursiveCalls.size := by simpa using hj
      have hcallEq : blueprint.recursiveCalls[j]! = call := by
        rw [getElem!_pos _ j hj']; simpa using hcallj
      have htemplate := hcalls j (by rw [← hcallsSize]; exact hj')
      rw [hcallEq] at htemplate
      simp only [AddInductive.RecCallBlueprint.build, Expr.instantiate1_eq]
      refine htemplate.instantiate1' ?_ 0
      refine Expr.ProjsOK.mkAppN' (Expr.ProjsOK.mkAppN' (Expr.ProjsOK.mkAppN' trivial
        fun a ha => ?_) fun a ha => ?_) fun a ha => ?_
      · obtain ⟨fv, rfl⟩ := H.params_fvar a ha
        trivial
      · obtain ⟨fv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.bindings.motives
          (Array.mem_toList_iff.1 ha)
        trivial
      · obtain ⟨fv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.bindings.flatMinors
          (Array.mem_toList_iff.1 ha)
        trivial
  have hfields : (blueprint.lctx.mkLambda blueprint.fields
      (mkAppN (mkAppN blueprint.minor blueprint.fields)
        (blueprint.recursiveCalls.map fun call =>
          call.build indTypes stats (H.recInfos.map (·.motive))
            (H.recInfos.flatMap (·.minors)) lvls))).ProjsOK
        (projHitOK H.localContext.env heads) := by
    revert hbody
    rw [hBlctx, hBfields]
    intro hbody
    exact Expr.ProjsOK.mkLambda' S.fields_bound.expressions hbody hfieldDecls
  refine Expr.ProjsOK.mkLambda' H.params.expressions ?_ ?_
  · refine Expr.ProjsOK.mkLambda' H.bindings.motives.expressions ?_
      (fun y hy => H.motiveDeclProjsOK I W (H.bindings.motives.mem_fvars_iff.1 hy))
    refine Expr.ProjsOK.mkLambda' H.bindings.flatMinors.expressions hfields
      (fun y hy => H.minorDeclProjsOK I W (H.bindings.flatMinors.mem_fvars_iff.1 hy))
  · intro y hy
    obtain ⟨index, name, type, bi, kind, hfind⟩ :=
      H.localWF.findCDecl y (H.params.members y hy)
    exact ⟨_, hfind, (I.paramDecls y hy _ hfind).declProjsOK⟩

end CompletedRecursorConstruction

end RuleProjs

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

/-- A lockstep installation of constants registers no projection. -/
theorem AddConstants.projections_eq {safety : DefinitionSafety} {env : Environment}
    {venv : VEnv} {entries : List (ConstantInfo × VConstVal)} {outEnv : Environment}
    {outVEnv : VEnv}
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    outVEnv.projections = venv.projections := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ hadd _ _ ih => rw [ih, VEnv.addConst_projections hadd]

/-- **The lowered rule right-hand sides project out of no restorable name.**
The projection condition of the hit-shape chain (`ruleRhsProjsOK`) excludes
projections out of the auxiliary families and constructors, and the
translation of the right-hand side in the recursor-pass environment registers
only base structures and lowered families, none of which is an auxiliary
recursor name or a restorable base name. -/
theorem NestedValidatedRunResult.loweredRules_projsOK
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ (owner : Fin E.production.production.generationSignature.families.size)
      (rec : RecursorVal),
      E.loweredEnv.find? (E.production.production.canonicalGeneration.recursorName owner) =
        some (.recInfo rec) →
      ∀ rule ∈ rec.rules, rule.rhs.ProjsOK
        (· ∉ (compilationRestoration sourceDecl auxiliaries).restorableNames) := by
  intro owner rec hfind rule hrule
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfFind owner hfind
  let P := E.production.production
  obtain ⟨envTypes, generated, aux', hadded, -, Haux, Hexpansion, -, D', -⟩ :=
    E.restorationTablesRestoring wf Hsources
  obtain ⟨-, -, -, -, -, -, -, hnodup⟩ := E.auxHeadsFacts wf Hsources
  have howner : owner.val < P.recInfos.size := by rw [← P.generated.length]; exact hi
  have hrule' : rule ∈ (P.generated.entry owner.val hi).info.rules := by
    rw [hinfo]; exact hrule
  -- the projection condition of the hit-shape chain
  have W := E.whnfHitOKFacts wf Hsources
  rw [← E.statsLevels] at W
  have h1 : rule.rhs.ProjsOK (projHitOK P.localContext.env E.hitHeads) := by
    have hr := hrule'
    rw [(P.generated.entry owner.val hi).rules_eq] at hr
    simp only [List.mem_map] at hr
    obtain ⟨blueprint, hmem, rfl⟩ := hr
    exact P.toCompletedRecursorConstruction.ruleRhsProjsOK (E.hitShapeInputs_of wf Hsources)
      W owner.val howner _ blueprint hmem
  -- registration of the projected structures
  obtain ⟨j, hj, hjrule⟩ := List.mem_iff_getElem.1 hrule'
  obtain ⟨X, Htr⟩ := P.ruleRhsTyped owner.val hi j hj
  rw [hjrule] at Htr
  have h2 := Htr.projsRegistered P.outVEnvWF.ordered trivial
  have hheadNames : (compilationRestoration sourceDecl aux').heads.map (·.auxiliary) =
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  refine (h1.and' h2).mono fun S ⟨hhit, info, hinfo⟩ hmem0 => ?_
  have hmem := D.restorableNames_subset D' S hmem0
  rw [P.installed.projections_eq, E.production.constructors.completed.contextVEnv] at hinfo
  rcases VEnv.addProjections_iff.mp hinfo with ⟨entry, hentry, rfl, -⟩ | hbase
  · simp only [VInductDecl.projectionEntries, List.mem_filterMap] at hentry
    obtain ⟨t, ht, hsome⟩ := hentry
    split at hsome
    · cases hsome
      simp only [Restoration.restorableNames, List.mem_append, hheadNames,
        compilationRestoration_recursors_fst, List.mem_map] at hmem
      rcases hmem with hmem | ⟨a, ha, hname⟩
      · exact hhit.1 (E.auxHeads_subset_hitHeads _ hmem)
      · obtain ⟨g, hg, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_l Haux a ha
        obtain ⟨t', ht', hexp⟩ := Lean4Lean.List.Forall₂.forall_exists_l Hexpansion g hg
        have h1 : t.name ∈ familyNames E.production.loweredDecl.types :=
          List.mem_flatMap.2 ⟨t, ht, List.mem_cons_self⟩
        have h2 : t.name ∈ E.production.loweredDecl.types.map (fun t => t.name.str "rec") := by
          refine List.mem_map.2 ⟨t', List.mem_of_mem_drop ht', ?_⟩
          rw [← hname, hev.auxiliary, ← hexp.name]
        exact (List.nodup_append.1 hnodup).2.2 _ h1 _ h2 rfl
    · cases hsome
  · rw [VEnv.addEliminators_projections,
      VEnv.addConstVals_projections_eq E.production.constructors.completed.core.ctorsAdded,
      VEnv.addConstVals_projections_eq E.production.constructors.completed.core.typesAdded,
      E.production_initialEnv] at hbase
    exact E.baseProjection_not_restorable wf hadded Haux Hexpansion hnodup hbase hmem

theorem NestedValidatedRunResult.LoweredRulesAvoid.of_cover
    {E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv}
    {heads L L₁ L₂ : List Name} (hcover : ∀ n ∈ L, n ∈ L₁ ∨ n ∈ L₂)
    (H₁ : E.LoweredRulesAvoid heads L₁) (H₂ : E.LoweredRulesAvoid heads L₂) :
    E.LoweredRulesAvoid heads L :=
  fun owner rec hfind rule hrule =>
    ⟨(H₁ owner rec hfind rule hrule).1.of_cover hcover (H₂ owner rec hfind rule hrule).1,
      (H₁ owner rec hfind rule hrule).2.of_cover hcover (H₂ owner rec hfind rule hrule).2⟩

/-- The auxiliary family names of a nested run: the lowered families after
the source families. -/
def NestedValidatedRunResult.auxFamilyNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) : List Name :=
  (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name)

/-- Every restorable name is an auxiliary family, auxiliary constructor or
lowered auxiliary recursor name. -/
theorem NestedValidatedRunResult.restorableNames_cover
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      n ∈ E.auxFamilyNames ∨ (n ∈ E.auxCtorNames ∨ n ∈ E.auxRecNames) := by
  obtain ⟨envTypes, generated, aux', hadded, -, Haux, Hexpansion, -, D', -⟩ :=
    E.restorationTablesRestoring wf Hsources
  intro n hn0
  have hn := D.restorableNames_subset D' n hn0
  simp only [Restoration.restorableNames, List.mem_append] at hn
  rcases hn with hhead | hrec
  · rw [compilationRestoration_heads_auxiliary,
      auxiliarySpecializations_headNames Haux Hexpansion] at hhead
    obtain ⟨t, ht, hmem⟩ := List.mem_flatMap.1 hhead
    rcases List.mem_cons.1 hmem with rfl | hctor
    · exact .inl (List.mem_map.2 ⟨t, ht, rfl⟩)
    · exact .inr (.inl (List.mem_flatMap.2 ⟨t, ht, hctor⟩))
  · rw [compilationRestoration_recursors_fst] at hrec
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hrec
    have haux : a.auxiliary ∈
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
      rw [← auxiliarySpecializations_names Haux Hexpansion]
      exact List.mem_map_of_mem ha
    obtain ⟨t, ht, hta⟩ := List.mem_map.1 haux
    exact .inr (.inr (List.mem_map.2 ⟨t, ht, by rw [hta]⟩))

/-- **Input-side avoidance of all restorable names, given the auxiliary
family names.** The auxiliary constructor names
(`loweredRulesAvoid_auxCtorNames`) and the lowered auxiliary recursor names
(`loweredRulesAvoid_auxRecNames`) are avoided unconditionally; the auxiliary
family names are the remaining hypothesis `HF`. -/
theorem NestedValidatedRunResult.loweredRulesAvoid_restorable_of_families
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) (heads : List Name)
    (HF : E.LoweredRulesAvoid heads E.auxFamilyNames) :
    E.LoweredRulesAvoid heads (compilationRestoration sourceDecl auxiliaries).restorableNames :=
  NestedValidatedRunResult.LoweredRulesAvoid.of_cover
    (L₂ := E.auxCtorNames ++ E.auxRecNames)
    (fun n hn => (E.restorableNames_cover wf Hsources D n hn).imp_right List.mem_append.2) HF
    (NestedValidatedRunResult.LoweredRulesAvoid.of_cover (fun _ h => List.mem_append.1 h)
      (E.loweredRulesAvoid_auxCtorNames wf Hsources heads)
      (E.loweredRulesAvoid_auxRecNames wf Hsources heads))

end RecNames

end VerifyInductive
end Lean4Lean
