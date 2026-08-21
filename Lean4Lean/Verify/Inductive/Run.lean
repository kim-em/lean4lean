import Lean4Lean.Verify.Inductive.Equation.Build

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Exact branch certificate for the production post-lowering pipeline. -/
inductive AddInductiveAfterLoweringResult
    (res : Lean4Lean.ElimNestedInductive.Result)
    (Installed : Environment → Prop)
    (Restored : Environment → Environment → Prop) :
    Environment → Prop
  | ordinary : res.aux2nested.size = 0 → Installed outEnv →
      AddInductiveAfterLoweringResult res Installed Restored outEnv
  | nested : res.aux2nested.size ≠ 0 → Installed loweredEnv →
      Restored loweredEnv outEnv →
      AddInductiveAfterLoweringResult res Installed Restored outEnv

/-- Compositional verifier for the exact ordinary/nested branch in
`Environment.addInductiveAfterLowering`. -/
theorem Environment.addInductiveAfterLowering.WF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) (res : Lean4Lean.ElimNestedInductive.Result)
    (Installed : Environment → Prop)
    (Restored : Environment → Environment → Prop)
    (Hrun : (AddInductive.run nparams res.types res.aux2nested.size
      { env, allowPrimitive, lparams, fuel,
        safety := if isUnsafe then .unsafe else .safe }).WF Installed)
    (Hrestore : ∀ loweredEnv, Installed loweredEnv →
      res.aux2nested.size ≠ 0 →
      (Environment.restoreNestedAfterInstall env loweredEnv lparams types
        (if isUnsafe then .unsafe else .safe) allowPrimitive fuel res).WF
          (Restored loweredEnv)) :
    (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
      allowPrimitive fuel res).WF
        (AddInductiveAfterLoweringResult res Installed Restored) := by
  unfold Environment.addInductiveAfterLowering
  exact Hrun.bind fun loweredEnv Hinstalled => by
    by_cases hzero : res.aux2nested.size = 0
    · simp only [hzero, ↓reduceIte]
      exact Except.WF.pure (.ordinary hzero Hinstalled)
    · simp only [hzero, ↓reduceIte]
      exact (Hrestore loweredEnv Hinstalled hzero).mono fun outEnv Hrestored =>
        .nested hzero Hinstalled Hrestored

/-- Successful nested restoration retains both the exact declaration-fold
trace and the independently specified auxiliary-witness validation. -/
structure RestoredAfterInstallResult
    (res : Lean4Lean.ElimNestedInductive.Result)
    (sourceEnv loweredEnv : Environment) (recNameMap : NameMap Name)
    (allIndNames : List Name) (types : List InductiveType)
    (auxRecNames : List Name) (Validated : Environment → Prop)
    (outEnv : Environment) : Prop where
  restoration : Nonempty (RestoredNestedDeclarationsResult res loweredEnv
    sourceEnv recNameMap allIndNames types auxRecNames ((), outEnv))
  validated : Validated outEnv

/-- Compose the verified declaration-restoration folds with the production
auxiliary validation pass. -/
theorem Environment.restoreNestedAfterInstall.WF
    (env loweredEnv : Environment) (lparams : List Name)
    (types : List InductiveType) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (res : Lean4Lean.ElimNestedInductive.Result)
    (Htypes : ∀ indType, indType ∈ types →
      ∃ oldInfo : InductiveVal,
        loweredEnv.find? indType.name = some (.inductInfo oldInfo) ∧
        (∀ ctorName, ctorName ∈ oldInfo.ctors →
          ∃ ctorInfo : ConstructorVal,
            loweredEnv.find? ctorName = some (.ctorInfo ctorInfo) ∧
            RestoreTelescope ctorInfo.type res.nparams) ∧
        ∃ recInfo : RecursorVal,
          loweredEnv.find? (Lean.mkRecName indType.name) =
            some (.recInfo recInfo) ∧
          RestoreTelescope recInfo.type res.nparams ∧
          ∀ rule ∈ recInfo.rules,
            RestoreTelescope rule.rhs res.nparams)
    (Haux : ∀ recName,
      recName ∈ (Lean4Lean.mkAuxRecNameMap loweredEnv types).1 →
      ∃ oldInfo : RecursorVal,
        loweredEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type res.nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs res.nparams)
    (Validated : Environment → Prop)
    (Hvalidate : ∀ restoredEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv env
        (Lean4Lean.mkAuxRecNameMap loweredEnv types).2 (types.map (·.name))
        types (Lean4Lean.mkAuxRecNameMap loweredEnv types).1
        ((), restoredEnv)) →
      (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
        res).WF fun _ => Validated restoredEnv) :
    (Environment.restoreNestedAfterInstall env loweredEnv lparams types safety
      allowPrimitive fuel res).WF fun outEnv =>
        RestoredAfterInstallResult res env loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
          (types.map (·.name)) types
          (Lean4Lean.mkAuxRecNameMap loweredEnv types).1 Validated outEnv := by
  let recNames := (Lean4Lean.mkAuxRecNameMap loweredEnv types).1
  let recNameMap := (Lean4Lean.mkAuxRecNameMap loweredEnv types).2
  let allIndNames := types.map (·.name)
  have Hdeclarations := restoreNestedDeclarations_refines res loweredEnv env
    recNameMap allIndNames allowPrimitive types recNames Htypes (by
      simpa [recNames] using Haux)
  have HrestoredEnv :
      ((·.2) <$> Lean4Lean.restoreNestedDeclarations res loweredEnv
        recNameMap allIndNames allowPrimitive types recNames env).WF
          fun restoredEnv => Nonempty (RestoredNestedDeclarationsResult res
            loweredEnv env recNameMap allIndNames types recNames
              ((), restoredEnv)) := by
    exact Hdeclarations.map fun restored Hrestored => by
      rcases restored with ⟨unit, restoredEnv⟩
      rcases unit with ⟨⟩
      exact Hrestored
  have Houtput :
      (((·.2) <$> Lean4Lean.restoreNestedDeclarations res loweredEnv
          recNameMap allIndNames allowPrimitive types recNames env).bind
        fun restoredEnv =>
          (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
            res).bind fun _ => Except.pure restoredEnv).WF
        (RestoredAfterInstallResult res env loweredEnv recNameMap allIndNames
          types recNames Validated) :=
    HrestoredEnv.bind fun restoredEnv Hrestored => by
      exact (Hvalidate restoredEnv (by
        simpa [recNames, recNameMap, allIndNames] using Hrestored)).bind
          fun _ Hvalidated => Except.WF.pure (show
            RestoredAfterInstallResult res env loweredEnv recNameMap
              allIndNames types recNames Validated restoredEnv from
                ⟨Hrestored, Hvalidated⟩)
  simpa [Environment.restoreNestedAfterInstall, recNames, recNameMap,
    allIndNames, StateT.run, bind, Except.bind, pure] using Houtput

/-- Complete outcome specification for an application already recognized as
nested: either an existing cache entry is reused without changing state, or a
certified batch for the entire mutual block is generated. -/
inductive RecognizedNestedReplacement
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (args : Array Expr)
    (value : InductiveVal) (state : Lean4Lean.ElimNestedInductive.State) :
    Option Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | cached (auxName : Name) :
      CachedNestedAux state.nestedAux
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract As
          |>.instantiateRev params) auxName →
      RecognizedNestedReplacement env lctx params As targetName levels args
        value state
        (some (mkAppRange (mkAppN (.const auxName state.lvls) As)
          value.numParams args.size args), state)
  | generated :
      MutualInductiveClosure env targetName value →
      GeneratedAuxiliaryBatch env lctx params As targetName levels
        value.numParams args none value.all state out →
      RecognizedNestedReplacement env lctx params As targetName levels args
        value state out

theorem replaceRecognizedNested_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (args : Array Expr)
    (value : InductiveVal) (state : Lean4Lean.ElimNestedInductive.State)
    (hargs : value.numParams ≤ args.size)
    (hsize : As.size = params.size)
    (hclosure : MutualInductiveClosure env targetName value) :
    (Lean4Lean.ElimNestedInductive.replaceRecognizedNested lctx params As
      (.const targetName levels) args value env state).WF fun out =>
        RecognizedNestedReplacement env lctx params As targetName levels args
          value state out := by
  unfold Lean4Lean.ElimNestedInductive.replaceRecognizedNested
  simp only [hargs, ↓reduceIte]
  refine nestedBind.WF
    (replaceNestedParams_state_refines params
      (mkAppRange (.const targetName levels) 0 value.numParams args) As
      env state hsize) ?_
  intro nested nextState hnested
  cases hnested
  simp only [get, bind, StateT.bind, ReaderT.bind]
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M Lean4Lean.ElimNestedInductive.State)
      env state) = Except.ok (state, state) := rfl
  rw [hget]
  simp only [Except.bind]
  cases hcache : Lean4Lean.ElimNestedInductive.findCachedAux?
      state.nestedAux
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract As
          |>.instantiateRev params) with
  | some auxName =>
    simp only [pure, ReaderT.pure, StateT.pure]
    exact Except.WF.pure (RecognizedNestedReplacement.cached auxName
      (findCachedAux?_refines state.nestedAux
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract As
          |>.instantiateRev params) auxName hcache))
  | none =>
    exact (generateAuxiliaries_refines env lctx params As targetName levels
      value.numParams args value state hsize hclosure.members
      hclosure.target).mono fun _ Hbatch =>
        RecognizedNestedReplacement.generated hclosure Hbatch

/-- Complete node-level result of nested replacement.  A non-candidate is
left untouched; every accepted candidate carries both the independent
recognition evidence and the cache-or-generation certificate. -/
inductive NestedReplacement
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (e : Expr) (state : Lean4Lean.ElimNestedInductive.State) :
    Option Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | unrecognized : NoNestedAppCandidate env state e →
      NestedReplacement env lctx params As e state (none, state)
  | recognized :
      NestedAppCandidate env state e value →
      e.getAppFn = .const targetName levels →
      RecognizedNestedReplacement env lctx params As targetName levels
        e.getAppArgs value state out →
      NestedReplacement env lctx params As e state out

theorem replaceIfNested_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (e : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : As.size = params.size)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.replaceIfNested lctx params As e env state).WF
      fun out => NestedReplacement env lctx params As e state out := by
  rw [Lean4Lean.ElimNestedInductive.replaceIfNested]
  refine nestedBind.WF
    (x := Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e)
    (P := fun recognized =>
      recognized.2 = state ∧
      (∀ value, recognized.1 = some value →
        NestedAppCandidate env state e value) ∧
      (recognized.1 = none → NoNestedAppCandidate env state e)) ?_ ?_
  · intro recognized hrecognized
    refine ⟨isNestedInductiveApp_preservesState e env state
        recognized hrecognized,
      isNestedInductiveApp_candidate e env state recognized hrecognized, ?_⟩
    intro hnone info Hcandidate
    have hcomplete := Hcandidate.recognized recognized hrecognized
    change recognized.1 = some info at hcomplete
    rw [hnone] at hcomplete
    cases hcomplete
  · intro recognized nextState hrecognized
    rcases hrecognized with ⟨hstate, hcandidate, hnone⟩
    simp only at hstate hcandidate hnone ⊢
    subst nextState
    cases recognized with
    | none =>
      exact Except.WF.pure (.unrecognized (hnone rfl))
    | some value =>
      have Hcandidate := hcandidate value rfl
      rcases Hcandidate.headFound with
        ⟨targetName, levels, hhead, hlookup⟩
      simp only
      rw [Expr.withApp_eq, hhead]
      exact (replaceRecognizedNested_refines env lctx params As targetName
        levels e.getAppArgs value state Hcandidate.parameters.arity hsize
        (hclosures targetName value hlookup)).mono fun _ Hresult =>
          .recognized Hcandidate hhead Hresult

theorem RecognizedNestedReplacement.resultSome
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out) : out.1.isSome = true := by
  cases H with
  | cached => simp
  | generated _ Hbatch => exact Hbatch.resultSome

theorem NestedReplacement.outcome
    (H : NestedReplacement env lctx params As e state out) :
    out = (none, state) ∨ ∃ output nextState, out = (some output, nextState) := by
  cases H with
  | unrecognized => exact Or.inl rfl
  | recognized Hcandidate hhead Hresult =>
    right
    have hsome := Hresult.resultSome
    cases h : out.1 with
    | none => simp [h] at hsome
    | some output => exact ⟨output, out.2, by cases out; simp_all⟩

theorem NestedReplacement.noCandidate
    (H : NestedReplacement env lctx params As e state (none, state)) :
    NoNestedAppCandidate env state e := by
  cases H with
  | unrecognized Hnone => exact Hnone
  | recognized Hcandidate hhead Hresult =>
    have hsome := Hresult.resultSome
    simp at hsome

/-- Stateful, top-down specification of `Expr.replaceM` for nested lowering.
A successful node replacement stops descent; otherwise children are processed
left-to-right with the exact intermediate states and update combinators used by
Lean's expression traversal. -/
inductive NestedExprReplacement
    (env : Environment) (lctx : LocalContext) (params As : Array Expr) :
    Expr → Lean4Lean.ElimNestedInductive.State →
      Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | hit : NestedReplacement env lctx params As input state
      (some output, nextState) →
      NestedExprReplacement env lctx params As input state (output, nextState)
  | bvar : NestedReplacement env lctx params As (.bvar i) state (none, state) →
      NestedExprReplacement env lctx params As (.bvar i) state (.bvar i, state)
  | fvar {fvarId : FVarId} :
      NestedReplacement env lctx params As (.fvar fvarId) state (none, state) →
      NestedExprReplacement env lctx params As (.fvar fvarId) state
        (.fvar fvarId, state)
  | mvar {mvarId : MVarId} :
      NestedReplacement env lctx params As (.mvar mvarId) state (none, state) →
      NestedExprReplacement env lctx params As (.mvar mvarId) state
        (.mvar mvarId, state)
  | sort : NestedReplacement env lctx params As (.sort level) state (none, state) →
      NestedExprReplacement env lctx params As (.sort level) state (.sort level, state)
  | const : NestedReplacement env lctx params As (.const name levels) state
      (none, state) →
      NestedExprReplacement env lctx params As (.const name levels) state
        (.const name levels, state)
  | lit : NestedReplacement env lctx params As (.lit literal) state (none, state) →
      NestedExprReplacement env lctx params As (.lit literal) state
        (.lit literal, state)
  | app : NestedReplacement env lctx params As (.app fn arg) state (none, state) →
      NestedExprReplacement env lctx params As fn state (fn', fnState) →
      NestedExprReplacement env lctx params As arg fnState (arg', outState) →
      NestedExprReplacement env lctx params As (.app fn arg) state
        (Expr.updateApp! (.app fn arg) fn' arg', outState)
  | lam : NestedReplacement env lctx params As (.lam name dom body bi) state
      (none, state) →
      NestedExprReplacement env lctx params As dom state (dom', domState) →
      NestedExprReplacement env lctx params As body domState (body', outState) →
      NestedExprReplacement env lctx params As (.lam name dom body bi) state
        (Expr.updateLambdaE! (.lam name dom body bi) dom' body', outState)
  | forallE : NestedReplacement env lctx params As
      (.forallE name dom body bi) state (none, state) →
      NestedExprReplacement env lctx params As dom state (dom', domState) →
      NestedExprReplacement env lctx params As body domState (body', outState) →
      NestedExprReplacement env lctx params As (.forallE name dom body bi) state
        (Expr.updateForallE! (.forallE name dom body bi) dom' body', outState)
  | letE : NestedReplacement env lctx params As
      (.letE name type value body nondep) state (none, state) →
      NestedExprReplacement env lctx params As type state (type', typeState) →
      NestedExprReplacement env lctx params As value typeState (value', valueState) →
      NestedExprReplacement env lctx params As body valueState (body', outState) →
      NestedExprReplacement env lctx params As (.letE name type value body nondep) state
        (Expr.updateLet! (.letE name type value body nondep)
          type' value' body' nondep, outState)
  | mdata : NestedReplacement env lctx params As (.mdata data body) state
      (none, state) →
      NestedExprReplacement env lctx params As body state (body', outState) →
      NestedExprReplacement env lctx params As (.mdata data body) state
        (Expr.updateMData! (.mdata data body) body', outState)
  | proj : NestedReplacement env lctx params As (.proj name idx body) state
      (none, state) →
      NestedExprReplacement env lctx params As body state (body', outState) →
      NestedExprReplacement env lctx params As (.proj name idx body) state
        (Expr.updateProj! (.proj name idx body) body', outState)

/-- Nested lowering only appends to `newTypes` while traversing expressions. -/
def NestedNewTypesLE (source target : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∃ suffix, target.newTypes.toList = source.newTypes.toList ++ suffix

/-- Nested-expression traversal also grows the `(nested expression, fresh
family name)` cache append-only. This is the operational source of the final
`aux2nested` map used by restoration. -/
def NestedAuxLE (source target : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∃ suffix, target.nestedAux.toList = source.nestedAux.toList ++ suffix

theorem NestedAuxLE.refl (state : Lean4Lean.ElimNestedInductive.State) :
    NestedAuxLE state state := ⟨[], by simp⟩

theorem NestedAuxLE.trans
    (H₁ : NestedAuxLE first middle) (H₂ : NestedAuxLE middle last) :
    NestedAuxLE first last := by
  rcases H₁ with ⟨xs, hxs⟩
  rcases H₂ with ⟨ys, hys⟩
  exact ⟨xs ++ ys, by simp [hys, hxs, List.append_assoc]⟩

theorem NestedAuxLE.mem
    (H : NestedAuxLE source target)
    (hentry : entry ∈ source.nestedAux) : entry ∈ target.nestedAux := by
  rcases H with ⟨suffix, hsuffix⟩
  have hsource : entry ∈ source.nestedAux.toList := by simpa using hentry
  have htarget : entry ∈ target.nestedAux.toList := by
    rw [hsuffix]
    exact List.mem_append_left suffix hsource
  simpa using htarget

private theorem nestedAuxFold_find_of_not_mem
    (entries : List (Expr × Name))
    (map : Std.TreeMap Name Expr Name.quickCmp)
    (hnot : name ∉ entries.map Prod.snd) :
    (entries.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1)
      map)[name]? = map[name]? := by
  induction entries generalizing map with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp only [List.foldl_cons]
    rw [ih _ hnot.2]
    rw [Std.TreeMap.getElem?_insert]
    split
    next heq =>
      have hname : entry.2 = name :=
        Std.LawfulEqCmp.compare_eq_iff_eq.mp heq
      exact False.elim (hnot.1 hname.symm)
    next => rfl

def NestedAuxMapFVarsIn (P : FVarId → Prop)
    (map : Std.TreeMap Name Expr Name.quickCmp) : Prop :=
  ∀ (name : Name) (nested : Expr),
    map[name]? = some nested → nested.FVarsIn P

/-- Every key in a restoration map belongs to the private namespace used by
the lowering-generated auxiliary families. -/
def NestedAuxMapNamesReserved
    (map : Std.TreeMap Name Expr Name.quickCmp) : Prop :=
  ∀ (name : Name) (nested : Expr), map[name]? = some nested →
    (`_nested).isPrefixOf name = true

def NestedAuxMapNamesFresh (env : Environment)
    (map : Std.TreeMap Name Expr Name.quickCmp) : Prop :=
  ∀ (name : Name) (nested : Expr), map[name]? = some nested →
    env.contains name = false

theorem NestedAuxMapNamesReserved.insert
    (Hmap : NestedAuxMapNamesReserved map)
    (Hname : (`_nested).isPrefixOf name = true) :
    NestedAuxMapNamesReserved (map.insert name nested) := by
  intro query value hfind
  rw [Std.TreeMap.getElem?_insert] at hfind
  split at hfind
  next hcmp =>
    cases hfind
    rw [← Std.LawfulEqCmp.eq_of_compare hcmp]
    exact Hname
  next => exact Hmap query value hfind

theorem NestedAuxMapNamesFresh.insert
    (Hmap : NestedAuxMapNamesFresh env map)
    (Hname : env.contains name = false) :
    NestedAuxMapNamesFresh env (map.insert name nested) := by
  intro query value hfind
  rw [Std.TreeMap.getElem?_insert] at hfind
  split at hfind
  next hcmp =>
    cases hfind
    rw [← Std.LawfulEqCmp.eq_of_compare hcmp]
    exact Hname
  next => exact Hmap query value hfind

theorem NestedAuxMapFVarsIn.insert
    (Hmap : NestedAuxMapFVarsIn P map) (Hnested : nested.FVarsIn P) :
    NestedAuxMapFVarsIn P (map.insert name nested) := by
  intro query value hfind
  rw [Std.TreeMap.getElem?_insert] at hfind
  split at hfind
  · cases hfind
    exact Hnested
  · exact Hmap query value hfind

theorem nestedAuxFold_fvarsIn
    (entries : List (Expr × Name))
    (Hentries : ∀ entry ∈ entries, entry.1.FVarsIn P)
    (Hmap : NestedAuxMapFVarsIn P map) :
    NestedAuxMapFVarsIn P
      (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        map) := by
  induction entries generalizing map with
  | nil => exact Hmap
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro tail htail
      exact Hentries tail (by simp [htail])
    · exact Hmap.insert (Hentries entry (by simp))

theorem nestedAuxFold_namesReserved
    (entries : List (Expr × Name))
    (Hentries : ∀ entry ∈ entries,
      (`_nested).isPrefixOf entry.2 = true)
    (Hmap : NestedAuxMapNamesReserved map) :
    NestedAuxMapNamesReserved
      (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        map) := by
  induction entries generalizing map with
  | nil => exact Hmap
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro tail htail
      exact Hentries tail (by simp [htail])
    · exact Hmap.insert (Hentries entry (by simp))

theorem nestedAuxFold_namesFresh
    (entries : List (Expr × Name))
    (Hentries : ∀ entry ∈ entries, env.contains entry.2 = false)
    (Hmap : NestedAuxMapNamesFresh env map) :
    NestedAuxMapNamesFresh env
      (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        map) := by
  induction entries generalizing map with
  | nil => exact Hmap
  | cons entry entries ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro tail htail
      exact Hentries tail (by simp [htail])
    · exact Hmap.insert (Hentries entry (by simp))

/-- Folding a cache with unique generated names retrieves the nested
expression paired with every cache entry. -/
theorem nestedAuxFold_find
    (entries : List (Expr × Name))
    (map : Std.TreeMap Name Expr Name.quickCmp)
    (hnodup : (entries.map Prod.snd).Nodup)
    (hentry : (nested, name) ∈ entries) :
    (entries.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1)
      map)[name]? = some nested := by
  induction entries generalizing map with
  | nil => simp at hentry
  | cons entry entries ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [List.mem_cons] at hentry
    simp only [List.foldl_cons]
    rcases hentry with hhead | htail
    · cases hhead
      rw [nestedAuxFold_find_of_not_mem entries _ hnodup.1]
      simp
    · have htailNodup : (entries.map Prod.snd).Nodup := hnodup.2
      have htailFind := ih (map.insert entry.2 entry.1) htailNodup htail
      simpa using htailFind

/-- A final restoration map faithfully represents every entry retained in a
nested-lowering state. This isolates the map property needed by local
lowering/restoration proofs from the particular fold that builds the map. -/
def NestedAuxMapModels (result : Lean4Lean.ElimNestedInductive.Result)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ nested name, (nested, name) ∈ state.nestedAux →
    result.aux2nested.find? name = some nested

theorem NestedNewTypesLE.refl (state : Lean4Lean.ElimNestedInductive.State) :
    NestedNewTypesLE state state := ⟨[], by simp⟩

theorem NestedNewTypesLE.trans
    (H₁ : NestedNewTypesLE first middle)
    (H₂ : NestedNewTypesLE middle last) : NestedNewTypesLE first last := by
  rcases H₁ with ⟨xs, hxs⟩
  rcases H₂ with ⟨ys, hys⟩
  exact ⟨xs ++ ys, by simp [hys, hxs, List.append_assoc]⟩

theorem NestedNewTypesLE.mem
    (H : NestedNewTypesLE source target)
    (hentry : entry ∈ source.newTypes) : entry ∈ target.newTypes := by
  rcases H with ⟨suffix, hsuffix⟩
  have hsource : entry ∈ source.newTypes.toList := by simpa using hentry
  have htarget : entry ∈ target.newTypes.toList := by
    rw [hsuffix]
    exact List.mem_append_left suffix hsource
  simpa using htarget

theorem NestedNewTypesLE.getElem
    (H : NestedNewTypesLE source target) (hi : i < source.newTypes.size) :
    ∃ htarget : i < target.newTypes.size,
      target.newTypes[i] = source.newTypes[i] := by
  rcases H with ⟨suffix, hsuffix⟩
  have htarget : i < target.newTypes.size := by
    have hsizes := congrArg List.length hsuffix
    have hlen : target.newTypes.size =
        source.newTypes.size + suffix.length := by simpa using hsizes
    rw [hlen]
    omega
  refine ⟨htarget, ?_⟩
  have hlist : target.newTypes.toList[i] = source.newTypes.toList[i] := by
    simpa [hsuffix, List.getElem_append, hi]
  simpa using hlist

theorem GeneratedAuxiliary.newTypesLE
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out) : NestedNewTypesLE state out.2 := by
  rcases H.generated with ⟨auxName, nextIdx, data, _, _, _, hstate⟩
  rw [hstate]
  exact ⟨[data.type], by simp⟩

theorem GeneratedAuxiliary.nestedAuxLE
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out) : NestedAuxLE state out.2 := by
  rcases H.generated with ⟨auxName, nextIdx, data, _, _, _, hstate⟩
  rw [hstate]
  exact ⟨[(data.nested, auxName)], by simp⟩

theorem GeneratedAuxiliary.namesWF
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstate⟩
  rcases Hfresh.index with ⟨index, hstart, hname, hnext⟩
  rw [hstate]
  have hnot : auxName ∉ state.nestedAux.toList.map Prod.snd := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨⟨nested, oldName⟩, hold, heq⟩
    change oldName = auxName at heq
    rcases Hstate.indexed nested oldName (by simpa using hold) with
      ⟨oldBase, oldIndex, holdName, holdIndex⟩
    have hsuffix : oldIndex = index := Hindex oldBase
      (`_nested ++ sourceName) oldIndex index (by
        rw [← holdName, ← hname]
        exact heq)
    omega
  constructor
  · simp only [Array.toList_push, List.map_append, List.map_singleton]
    apply List.nodup_append.mpr
    refine ⟨Hstate.nodup, by simp, ?_⟩
    intro oldName hold newName hnew
    simp only [List.mem_singleton] at hnew
    subst newName
    intro heq
    subst oldName
    exact hnot hold
  · intro nested name hentry
    simp only [Array.mem_push] at hentry
    rcases hentry with hold | hnew
    · rcases Hstate.indexed nested name hold with
        ⟨base, oldIndex, holdName, holdIndex⟩
      refine ⟨base, oldIndex, holdName, ?_⟩
      change oldIndex < nextIdx
      rw [hnext]
      omega
    · cases hnew
      refine ⟨`_nested ++ sourceName, index, hname, ?_⟩
      change index < nextIdx
      rw [hnext]
      omega
  · intro nested name hentry
    simp only [Array.mem_push] at hentry
    rcases hentry with hold | hnew
    · exact Hstate.reserved nested name hold
    · cases hnew
      rw [hname]
      exact nested_isPrefix_appendIndexAfter sourceName index

theorem GeneratedAuxiliary.namesFresh
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstate⟩
  rw [hstate]
  intro nested name hentry
  simp only [Array.mem_push] at hentry
  rcases hentry with hold | hnew
  · exact Hstate nested name hold
  · cases hnew
    exact Hfresh.fresh

theorem GeneratedAuxiliaryBatch.newTypesLE
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out) : NestedNewTypesLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hstep Htail ih => exact Hstep.newTypesLE.trans ih

theorem GeneratedAuxiliaryBatch.nestedAuxLE
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out) : NestedAuxLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hstep Htail ih => exact Hstep.nestedAuxLE.trans ih

theorem GeneratedAuxiliaryBatch.namesWF
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hstep Htail ih => exact ih (Hstep.namesWF Hindex Hstate)

theorem GeneratedAuxiliaryBatch.namesFresh
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hstep Htail ih => exact ih (Hstep.namesFresh Hstate)

/-- Every source family traversed by the mutual-generation loop has a
concrete auxiliary construction whose paired cache entry and lowered family
both survive in the batch's final state. -/
theorem GeneratedAuxiliaryBatch.generatedFor
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hsource : sourceName ∈ sourceNames) :
    ∃ (stepState : Lean4Lean.ElimNestedInductive.State)
        (sourceInfo : InductiveVal) (auxName : Name) (nextIdx : Nat)
        (data : Lean4Lean.ElimNestedInductive.AuxiliaryData),
      FreshNestedName env (`_nested ++ sourceName) stepState.nextIdx
        auxName nextIdx ∧
      BuiltAuxiliary env lctx params As levels nparams args sourceName auxName
        sourceInfo data ∧
      (data.nested, auxName) ∈ out.2.nestedAux ∧
      data.type ∈ out.2.newTypes := by
  induction H with
  | nil => simp at hsource
  | cons Hstep Htail ih =>
    simp only [List.mem_cons] at hsource
    rcases hsource with rfl | htail
    · rcases Hstep.generated with
        ⟨auxName, nextIdx, data, Hfresh, Hbuilt, _, hstep⟩
      refine ⟨_, _, auxName, nextIdx, data, Hfresh, Hbuilt, ?_, ?_⟩
      · apply Htail.nestedAuxLE.mem
        rw [hstep]
        simp
      · apply Htail.newTypesLE.mem
        rw [hstep]
        simp
    · exact ih htail

/-- If the target family does not occur in the remaining mutual-family
suffix, that suffix cannot replace the accumulated result. -/
theorem GeneratedAuxiliaryBatch.result_eq_of_target_not_mem
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hnot : targetName ∉ sourceNames) : out.1 = result := by
  induction H with
  | nil => rfl
  | @cons sourceName sourceInfo state step result sourceNames out Hstep Htail ih =>
    simp only [List.mem_cons, not_or] at hnot
    rcases Hstep.generated with
      ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstate⟩
    have hne : sourceName ≠ targetName := Ne.symm hnot.1
    have hstep : step.1 = none := by
      rw [hresult]
      simp [hne]
    have htail := ih hnot.2
    simpa [hstep] using htail

/-- With unique mutual-family names, the batch result is exactly the
auxiliary application generated at the unique target-family step. The same
fresh name remains paired with its source expression in the final cache. -/
theorem GeneratedAuxiliaryBatch.targetResult
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hnodup : sourceNames.Nodup)
    (htarget : targetName ∈ sourceNames) :
    ∃ (stepState : Lean4Lean.ElimNestedInductive.State)
        (sourceInfo : InductiveVal) (auxName : Name) (nextIdx : Nat)
        (data : Lean4Lean.ElimNestedInductive.AuxiliaryData),
      FreshNestedName env (`_nested ++ targetName) stepState.nextIdx
        auxName nextIdx ∧
      BuiltAuxiliary env lctx params As levels nparams args targetName auxName
        sourceInfo data ∧
      out.1 = some (mkAppRange
        (mkAppN (.const auxName stepState.lvls) As) nparams args.size args) ∧
      (data.nested, auxName) ∈ out.2.nestedAux ∧
      data.type ∈ out.2.newTypes := by
  induction H with
  | nil => simp at htarget
  | @cons sourceName sourceInfo state step result sourceNames out Hstep Htail ih =>
    simp only [List.nodup_cons] at hnodup
    simp only [List.mem_cons] at htarget
    rcases htarget with hhead | htail
    · subst sourceName
      rcases Hstep.generated with
        ⟨auxName, nextIdx, data, Hfresh, Hbuilt, hresult, hstepState⟩
      have hstepResult : step.1 = some (mkAppRange
          (mkAppN (.const auxName state.lvls) As) nparams args.size args) := by
        simpa using hresult
      have hfinal := Htail.result_eq_of_target_not_mem hnodup.1
      refine ⟨state, _, auxName, nextIdx, data, Hfresh, Hbuilt, ?_, ?_, ?_⟩
      · simpa [hstepResult] using hfinal
      · apply Htail.nestedAuxLE.mem
        rw [hstepState]
        simp
      · apply Htail.newTypesLE.mem
        rw [hstepState]
        simp
    · exact ih hnodup.2 htail

/-- The exact target result is already reversible by the map obtained from
folding the batch's final cache, provided the separately tracked generated
names are unique. -/
theorem GeneratedAuxiliaryBatch.targetResultLookup
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hsourceNames : sourceNames.Nodup)
    (htarget : targetName ∈ sourceNames)
    (hauxNames : (out.2.nestedAux.toList.map Prod.snd).Nodup) :
    ∃ (stepState : Lean4Lean.ElimNestedInductive.State)
        (sourceInfo : InductiveVal) (auxName : Name)
        (data : Lean4Lean.ElimNestedInductive.AuxiliaryData),
      BuiltAuxiliary env lctx params As levels nparams args targetName auxName
        sourceInfo data ∧
      out.1 = some (mkAppRange
        (mkAppN (.const auxName stepState.lvls) As) nparams args.size args) ∧
      (out.2.nestedAux.toList.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1)
        {})[auxName]? = some data.nested := by
  rcases H.targetResult hsourceNames htarget with
    ⟨stepState, sourceInfo, auxName, _nextIdx, data, _Hfresh, Hbuilt,
      hresult, hentry, _htype⟩
  exact ⟨stepState, sourceInfo, auxName, data, Hbuilt, hresult,
    nestedAuxFold_find out.2.nestedAux.toList {} hauxNames
      (by simpa using hentry)⟩

/-- Global map-model evidence turns the unique target step into the exact
`aux2nested` lookup used by restoration, even after later lowering has
appended more cache entries. -/
theorem GeneratedAuxiliaryBatch.targetResultMapped
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (hsourceNames : sourceNames.Nodup)
    (htarget : targetName ∈ sourceNames)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    ∃ (stepState : Lean4Lean.ElimNestedInductive.State)
        (sourceInfo : InductiveVal) (auxName : Name)
        (data : Lean4Lean.ElimNestedInductive.AuxiliaryData),
      BuiltAuxiliary env lctx params As levels nparams args targetName auxName
        sourceInfo data ∧
      out.1 = some (mkAppRange
        (mkAppN (.const auxName stepState.lvls) As) nparams args.size args) ∧
      finalResult.aux2nested.find? auxName = some data.nested := by
  rcases H.targetResult hsourceNames htarget with
    ⟨stepState, sourceInfo, auxName, _nextIdx, data, _Hfresh, Hbuilt,
      hresult, hentry, _htype⟩
  exact ⟨stepState, sourceInfo, auxName, data, Hbuilt, hresult,
    Hmap data.nested auxName (Hlater.mem hentry)⟩

/-- Both cache reuse and fresh mutual-family generation expose the same
restoration-facing fact: the returned auxiliary application is keyed in the
final map by the normalized source-family application it replaced. -/
theorem RecognizedNestedReplacement.finalMapping
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    ∃ auxName auxLevels nested lowered,
      out.1 = some lowered ∧
      lowered = mkAppRange (mkAppN (.const auxName auxLevels) As)
        value.numParams args.size args ∧
      (nested ==
        ((mkAppRange (.const targetName levels) 0 value.numParams args).abstract
          As).instantiateRev params) = true ∧
      finalResult.aux2nested.find? auxName = some nested := by
  cases H with
  | cached auxName Hcached =>
    rcases Hcached.entry with
      ⟨⟨found, foundName⟩, hentry, heq, hname⟩
    change foundName = auxName at hname
    rw [hname] at hentry
    refine ⟨auxName, state.lvls, found, _, rfl, rfl, heq, ?_⟩
    exact Hmap _ auxName (Hlater.mem hentry)
  | generated Hclosure Hbatch =>
    rcases Hbatch.targetResultMapped Hclosure.names Hclosure.target Hlater Hmap
      with ⟨stepState, sourceInfo, auxName, data, Hbuilt, hresult, hlookup⟩
    refine ⟨auxName, stepState.lvls, data.nested, _, hresult, rfl, ?_, hlookup⟩
    rw [Hbuilt.nested]
    simp

def NestedReplacementHasFinalMapping
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (input : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (lowered : Expr) (finalResult : Lean4Lean.ElimNestedInductive.Result) : Prop :=
    ∃ value targetName levels auxName auxLevels nested,
      NestedAppCandidate env state input value ∧
      input.getAppFn = .const targetName levels ∧
      lowered = mkAppRange (mkAppN (.const auxName auxLevels) As)
        value.numParams input.getAppArgs.size input.getAppArgs ∧
      (nested ==
        ((mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs).abstract As).instantiateRev params) = true ∧
      finalResult.aux2nested.find? auxName = some nested

/-- A mapped lowering hit introduces only its selected parameter variables;
all trailing arguments are inherited from the source application. -/
theorem NestedReplacementHasFinalMapping.outputFVarsIn
    (H : NestedReplacementHasFinalMapping env lctx params As input state
      lowered finalResult)
    (Hselection : LocalForallSelection lctx As)
    (Hinput : input.FVarIdsIn (· ∈ Hselection.fvars)) :
    lowered.FVarIdsIn (· ∈ Hselection.fvars) := by
  rcases H with
    ⟨value, targetName, levels, auxName, auxLevels, nested,
      Hcandidate, hhead, hlowered, hnested, hlookup⟩
  have HAs : ∀ arg ∈ As.toList,
      arg.FVarIdsIn (· ∈ Hselection.fvars) := by
    intro arg harg
    rw [Hselection.expressions] at harg
    rcases List.mem_map.mp harg with ⟨fv, hfv, rfl⟩
    simpa [Expr.FVarIdsIn] using hfv
  rw [hlowered]
  rw [Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
  apply Expr.FVarIdsIn.mkAppList.mpr
  constructor
  · rw [Expr.mkAppN_eq_mkAppList]
    exact Expr.FVarIdsIn.mkAppList.mpr
      ⟨by simp [Expr.FVarIdsIn], HAs⟩
  · intro arg harg
    apply Hinput.getAppArgsList
    rw [← Expr.getAppArgs_toList]
    exact List.mem_of_mem_drop harg

/-- A mapped lowering leaf after reopening its cached source application with
the parameter array chosen by restoration. -/
def NestedReplacementReopens
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (input : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (lowered : Expr) (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr) : Prop :=
  ∃ value targetName levels auxName auxLevels nested,
    NestedAppCandidate env state input value ∧
    input.getAppFn = .const targetName levels ∧
    lowered = mkAppRange (mkAppN (.const auxName auxLevels) As)
      value.numParams input.getAppArgs.size input.getAppArgs ∧
    finalResult.aux2nested.find? auxName = some nested ∧
    (((nested.abstract finalResult.params).instantiateRev restoreAs) ==
      ((mkAppRange (.const targetName levels) 0 value.numParams
        input.getAppArgs).abstract As).instantiateRev restoreAs) = true

/-- A reopened lowering hit is interpreted by the concrete family branch of
`restoreNestedNode`.  The auxiliary parameter prefix is discarded and the
reopened source-family prefix is reattached to the identically renamed
non-parameter arguments, yielding the renamed original application up to
Lean expression equivalence. -/
theorem NestedReplacementReopens.restoreNode
    (H : NestedReplacementReopens env lctx params As input state lowered
      finalResult restoreAs)
    (restoreEnv : Environment)
    (Hselection : LocalForallSelection lctx As)
    (hresultNParams : finalResult.nparams = As.size) :
    ∃ restored,
      finalResult.restoreNestedNode restoreEnv restoreAs {}
          (Expr.reopenParams lowered As restoreAs) = some restored ∧
      (restored == Expr.reopenParams input As restoreAs) = true := by
  rcases H with
    ⟨value, targetName, levels, auxName, auxLevels, nested,
      Hcandidate, hhead, hlowered, hlookup, hreopens⟩
  let R : Expr → Expr := fun e => Expr.reopenParams e As restoreAs
  let trailing : List Expr :=
    input.getAppArgsList.drop value.numParams |>.map R
  let paramPrefix : List Expr := As.toList.map R
  have hloweredReopened : R lowered =
      Expr.mkAppList (.const auxName auxLevels) (paramPrefix ++ trailing) := by
    rw [hlowered]
    rw [Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity]
    rw [Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append]
    change Expr.reopenParams _ As restoreAs = _
    rw [Expr.reopenParams_mkAppList Hselection.fvars
      Hselection.expressions]
    rw [Expr.reopenParams_const Hselection.fvars Hselection.expressions]
    simp [R, paramPrefix, trailing, Expr.getAppArgs_toList]
  have hfn : (R lowered).getAppFn = .const auxName auxLevels := by
    rw [hloweredReopened]
    exact Expr.getAppFn_mkAppList_const auxName auxLevels _
  have hargsList : (R lowered).getAppArgsList = paramPrefix ++ trailing := by
    rw [hloweredReopened]
    exact Expr.getAppArgsList_mkAppList_const auxName auxLevels _
  have hargs : (R lowered).getAppArgs = (paramPrefix ++ trailing).toArray := by
    rw [Expr.getAppArgs_eq, hargsList]
  have hprefixLength : paramPrefix.length = finalResult.nparams := by
    simp [paramPrefix, hresultNParams]
  have harity : finalResult.nparams ≤ (R lowered).getAppArgs.size := by
    rw [hargs]
    simp [hprefixLength]
  have hnode := restoreNestedNode_family_general finalResult restoreEnv
    restoreAs {}
    (R lowered) nested auxName auxLevels hfn (by rfl) hlookup harity
  have hrestored :
      mkAppRange ((nested.abstract finalResult.params).instantiateRev restoreAs)
          finalResult.nparams (R lowered).getAppArgs.size
          (R lowered).getAppArgs =
        Expr.mkAppList
          ((nested.abstract finalResult.params).instantiateRev restoreAs)
          trailing := by
    rw [Expr.mkAppRange_to_end _ _ _ harity, hargs]
    simp [hprefixLength]
  refine ⟨Expr.mkAppList
      ((nested.abstract finalResult.params).instantiateRev restoreAs)
      trailing, ?_, ?_⟩
  · rw [hrestored] at hnode
    simpa only [R] using hnode
  · have hprefixSource :
        R (mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs) =
          Expr.mkAppList (.const targetName levels)
            (input.getAppArgsList.take value.numParams |>.map R) := by
      rw [Expr.mkAppRange_from_zero _ _ _ Hcandidate.parameters.arity]
      change Expr.reopenParams _ As restoreAs = _
      rw [Expr.reopenParams_mkAppList Hselection.fvars
        Hselection.expressions]
      rw [Expr.reopenParams_const Hselection.fvars Hselection.expressions]
      simp [R, Expr.getAppArgs_toList]
    change (((nested.abstract finalResult.params).instantiateRev restoreAs) ==
      R (mkAppRange (.const targetName levels) 0 value.numParams
        input.getAppArgs)) = true at hreopens
    have happended := Expr.mkAppList_eqv hreopens trailing
    rw [hprefixSource] at happended
    have hinput : R input =
        Expr.mkAppList (.const targetName levels)
          (input.getAppArgsList.map R) :=
      Expr.reopenParams_of_getAppFn_const Hselection.fvars
        Hselection.expressions hhead
    rw [← Expr.mkAppList_append] at happended
    simp only [trailing] at happended
    rw [List.map_take, List.map_drop, List.take_append_drop] at happended
    simpa [hinput, trailing, R] using happended

/-- The final-map witness retained at a lowering hit is a left inverse for
the abstraction/reopening part of `restoreNestedNode`.  The only local
scoping premise is that abstracting the constructor-opening parameters has
removed all free variables; constructor lowering establishes that fact from
its closed source type. -/
theorem NestedReplacementHasFinalMapping.reopens
    (H : NestedReplacementHasFinalMapping env lctx params As input state
      lowered finalResult)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (hclosed : ∀ value targetName levels,
      NestedAppCandidate env state input value →
      input.getAppFn = .const targetName levels →
      FVarsIn (fun _ => False)
        ((mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs).abstract As)) :
    NestedReplacementReopens env lctx params As input state lowered
      finalResult restoreAs := by
  rcases H with
    ⟨value, targetName, levels, auxName, auxLevels, nested,
      Hcandidate, hhead, hlowered, hnested, hlookup⟩
  let base := (mkAppRange (.const targetName levels) 0 value.numParams
    input.getAppArgs).abstract As
  have habstract :
      (nested.abstract params) ==
        ((base.instantiateRev params).abstract params) := by
    rw [hparams, Expr.abstract_eq, Expr.abstract_eq]
    apply Expr.abstractList_eqv
    simpa [base, hparams] using hnested
  have heqv :
      ((nested.abstract finalResult.params).instantiateRev restoreAs) ==
        (((base.instantiateRev params).abstract params).instantiateRev
          restoreAs) := by
    rw [hresultParams, Expr.instantiateRev_eq, Expr.instantiate_eq,
      Expr.instantiateRev_eq, Expr.instantiate_eq]
    exact Expr.instantiateList_eqv habstract
  refine ⟨value, targetName, levels, auxName, auxLevels, nested, Hcandidate,
    hhead, hlowered, hlookup, ?_⟩
  have hfree : FVarsIn (fun fv => fv ∉ fvars) base :=
    (hclosed value targetName levels Hcandidate hhead).mono
      fun fv hfalse => False.elim hfalse
  have hcancel := hfree.reabstract_instantiateRev_fvarArray
    params restoreAs fvars hparams hnodup
  rw [hcancel] at heqv
  exact heqv

/-- A recognized nested application's source-family prefix becomes closed
once all constructor-opening free variables are abstracted. -/
theorem NestedAppCandidate.abstractedPrefixClosed
    (H : NestedAppCandidate env state input value)
    (Hselection : LocalForallSelection lctx As)
    (Hinput : FVarsIn (· ∈ Hselection.fvars) input)
    (hhead : input.getAppFn = .const targetName levels) :
    FVarsIn (fun _ => False)
      ((mkAppRange (.const targetName levels) 0 value.numParams
        input.getAppArgs).abstract As) := by
  apply FVarsIn.abstract_fvarArray_of Hselection.fvars As
    Hselection.expressions
  apply FVarsIn.mkAppRange_zero H.parameters.arity
  · have Hfn := Hinput.getAppFn
    rw [hhead] at Hfn
    exact Hfn
  · intro arg harg
    have harg' : arg ∈ input.getAppArgsList := by
      rw [← Expr.getAppArgs_toList]
      exact Array.mem_toList_iff.mpr harg
    exact (Hinput.getAppArgsList harg').mono fun fv hfv => Or.inl hfv

/-- Constructor-scoped specialization of `reopens`; the closedness premise
is derived from the source body's free-variable invariant. -/
theorem NestedReplacementHasFinalMapping.reopensOfFVars
    (H : NestedReplacementHasFinalMapping env lctx params As input state
      lowered finalResult)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hselection : LocalForallSelection lctx As)
    (Hinput : FVarsIn (· ∈ Hselection.fvars) input) :
    NestedReplacementReopens env lctx params As input state lowered
      finalResult restoreAs := by
  apply H.reopens hresultParams fvars hparams hnodup
  intro value targetName levels Hcandidate hhead
  exact Hcandidate.abstractedPrefixClosed Hselection Hinput hhead

/-- Successful node replacement retains both the independent recognition
certificate and the final restoration-map entry for the auxiliary family it
returns. This is the leaf case needed by the structural expression inverse. -/
theorem NestedReplacement.finalMapping
    (H : NestedReplacement env lctx params As input state
      (some lowered, nextState))
    (Hlater : NestedAuxLE nextState finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    NestedReplacementHasFinalMapping env lctx params As input state lowered
      finalResult := by
  cases H with
  | recognized Hcandidate hhead Hrecognized =>
    rcases Hrecognized.finalMapping Hlater Hmap with
      ⟨auxName, auxLevels, nested, replacement, hresult, hreplacement,
        hnested, hlookup⟩
    cases hresult
    exact ⟨_, _, _, auxName, auxLevels, nested,
      Hcandidate, hhead, hreplacement, hnested, hlookup⟩

/-- Structural expression-lowering relation whose successful leaves are
already connected to the final restoration map. Unlike the operational trace,
this relation forgets monadic control flow and retains exactly the semantic
information needed to interpret the lowered expression. -/
inductive NestedExprMapping
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (finalResult : Lean4Lean.ElimNestedInductive.Result) :
    Expr → Lean4Lean.ElimNestedInductive.State →
      Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | hit : NestedReplacementHasFinalMapping env lctx params As input state
      output finalResult →
      NestedExprMapping env lctx params As finalResult input state
        (output, nextState)
  | bvar : NestedReplacement env lctx params As (.bvar i) state (none, state) →
      NestedExprMapping env lctx params As finalResult (.bvar i) state
      (.bvar i, state)
  | fvar {fvarId : FVarId} :
      NestedReplacement env lctx params As (.fvar fvarId) state (none, state) →
      NestedExprMapping env lctx params As finalResult
      (.fvar fvarId) state (.fvar fvarId, state)
  | mvar {mvarId : MVarId} :
      NestedReplacement env lctx params As (.mvar mvarId) state (none, state) →
      NestedExprMapping env lctx params As finalResult
      (.mvar mvarId) state (.mvar mvarId, state)
  | sort : NestedReplacement env lctx params As (.sort level) state (none, state) →
      NestedExprMapping env lctx params As finalResult (.sort level) state
      (.sort level, state)
  | const : NestedReplacement env lctx params As (.const name levels) state
      (none, state) → NestedExprMapping env lctx params As finalResult
      (.const name levels) state (.const name levels, state)
  | lit : NestedReplacement env lctx params As (.lit literal) state (none, state) →
      NestedExprMapping env lctx params As finalResult (.lit literal) state
      (.lit literal, state)
  | app : NestedReplacement env lctx params As (.app fn arg) state (none, state) →
      NestedExprMapping env lctx params As finalResult fn state
      (fn', fnState) →
      NestedExprMapping env lctx params As finalResult arg fnState
        (arg', outState) →
      NestedExprMapping env lctx params As finalResult (.app fn arg) state
        (Expr.updateApp! (.app fn arg) fn' arg', outState)
  | lam : NestedReplacement env lctx params As (.lam name dom body bi) state
      (none, state) → NestedExprMapping env lctx params As finalResult dom state
      (dom', domState) →
      NestedExprMapping env lctx params As finalResult body domState
        (body', outState) →
      NestedExprMapping env lctx params As finalResult (.lam name dom body bi)
        state (Expr.updateLambdaE! (.lam name dom body bi) dom' body', outState)
  | forallE : NestedReplacement env lctx params As
      (.forallE name dom body bi) state (none, state) →
      NestedExprMapping env lctx params As finalResult dom state
      (dom', domState) →
      NestedExprMapping env lctx params As finalResult body domState
        (body', outState) →
      NestedExprMapping env lctx params As finalResult
        (.forallE name dom body bi) state
        (Expr.updateForallE! (.forallE name dom body bi) dom' body', outState)
  | letE : NestedReplacement env lctx params As
      (.letE name type value body nondep) state (none, state) →
      NestedExprMapping env lctx params As finalResult type state
      (type', typeState) →
      NestedExprMapping env lctx params As finalResult value typeState
        (value', valueState) →
      NestedExprMapping env lctx params As finalResult body valueState
        (body', outState) →
      NestedExprMapping env lctx params As finalResult
        (.letE name type value body nondep) state
        (Expr.updateLet! (.letE name type value body nondep)
          type' value' body' nondep, outState)
  | mdata : NestedReplacement env lctx params As (.mdata data body) state
      (none, state) → NestedExprMapping env lctx params As finalResult body state
      (body', outState) →
      NestedExprMapping env lctx params As finalResult (.mdata data body) state
        (Expr.updateMData! (.mdata data body) body', outState)
  | proj : NestedReplacement env lctx params As (.proj name idx body) state
      (none, state) → NestedExprMapping env lctx params As finalResult body state
      (body', outState) →
      NestedExprMapping env lctx params As finalResult (.proj name idx body) state
        (Expr.updateProj! (.proj name idx body) body', outState)

/-- Nested lowering preserves free-variable-ID scoping. Successful hits use
`outputFVarsIn`; structural misses inherit the property componentwise. -/
theorem NestedExprMapping.outputFVarIdsIn
    (H : NestedExprMapping env lctx params As finalResult input state out)
    (Hselection : LocalForallSelection lctx As)
    (Hinput : input.FVarIdsIn (· ∈ Hselection.fvars)) :
    out.1.FVarIdsIn (· ∈ Hselection.fvars) := by
  induction H with
  | hit Hnode => exact Hnode.outputFVarsIn Hselection Hinput
  | bvar | fvar | mvar | sort | const | lit => exact Hinput
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateApp!, Expr.FVarIdsIn] using
      And.intro (ihFn Hinput.1) (ihArg Hinput.2)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateLambdaE!, Expr.FVarIdsIn] using
      And.intro (ihDom Hinput.1) (ihBody Hinput.2)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateForallE!, Expr.FVarIdsIn] using
      And.intro (ihDom Hinput.1) (ihBody Hinput.2)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Expr.FVarIdsIn] at Hinput
    simpa [Expr.updateLet!, Expr.FVarIdsIn] using
      And.intro (ihType Hinput.1)
        (And.intro (ihValue Hinput.2.1) (ihBody Hinput.2.2))
  | mdata Hnode Hbody ihBody =>
    simpa [Expr.updateMData!, Expr.FVarIdsIn] using ihBody Hinput
  | proj Hnode Hbody ihBody =>
    simpa [Expr.updateProj!, Expr.FVarIdsIn] using ihBody Hinput

/-- Structural lowering map with every successful leaf upgraded to its
parameter-reopening certificate. -/
inductive NestedExprReopening
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr) :
    Expr → Lean4Lean.ElimNestedInductive.State →
      Expr × Lean4Lean.ElimNestedInductive.State → Prop
  | hit : NestedReplacementReopens env lctx params As input state output
      finalResult restoreAs →
      NestedExprReopening env lctx params As finalResult restoreAs input state
        (output, nextState)
  | bvar : NestedReplacement env lctx params As (.bvar i) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs
      (.bvar i) state (.bvar i, state)
  | fvar {fvarId : FVarId} :
      NestedReplacement env lctx params As (.fvar fvarId) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.fvar fvarId) state (.fvar fvarId, state)
  | mvar {mvarId : MVarId} :
      NestedReplacement env lctx params As (.mvar mvarId) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.mvar mvarId) state (.mvar mvarId, state)
  | sort : NestedReplacement env lctx params As (.sort level) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs
      (.sort level) state (.sort level, state)
  | const : NestedReplacement env lctx params As (.const name levels) state
      (none, state) → NestedExprReopening env lctx params As finalResult restoreAs
      (.const name levels) state (.const name levels, state)
  | lit : NestedReplacement env lctx params As (.lit literal) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs
      (.lit literal) state (.lit literal, state)
  | app : NestedReplacement env lctx params As (.app fn arg) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs fn state
      (fn', fnState) →
      NestedExprReopening env lctx params As finalResult restoreAs arg fnState
        (arg', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.app fn arg) state
        (Expr.updateApp! (.app fn arg) fn' arg', outState)
  | lam : NestedReplacement env lctx params As (.lam name dom body bi) state
      (none, state) → NestedExprReopening env lctx params As finalResult restoreAs dom state
      (dom', domState) →
      NestedExprReopening env lctx params As finalResult restoreAs body domState
        (body', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.lam name dom body bi) state
        (Expr.updateLambdaE! (.lam name dom body bi) dom' body', outState)
  | forallE : NestedReplacement env lctx params As
      (.forallE name dom body bi) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs dom
      state (dom', domState) →
      NestedExprReopening env lctx params As finalResult restoreAs body domState
        (body', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.forallE name dom body bi) state
        (Expr.updateForallE! (.forallE name dom body bi) dom' body', outState)
  | letE : NestedReplacement env lctx params As
      (.letE name type value body nondep) state (none, state) →
      NestedExprReopening env lctx params As finalResult restoreAs type state
      (type', typeState) →
      NestedExprReopening env lctx params As finalResult restoreAs value typeState
        (value', valueState) →
      NestedExprReopening env lctx params As finalResult restoreAs body valueState
        (body', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.letE name type value body nondep) state
        (Expr.updateLet! (.letE name type value body nondep)
          type' value' body' nondep, outState)
  | mdata : NestedReplacement env lctx params As (.mdata data body) state
      (none, state) → NestedExprReopening env lctx params As finalResult restoreAs body state
      (body', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.mdata data body) state
        (Expr.updateMData! (.mdata data body) body', outState)
  | proj : NestedReplacement env lctx params As (.proj name idx body) state
      (none, state) → NestedExprReopening env lctx params As finalResult restoreAs body state
      (body', outState) →
      NestedExprReopening env lctx params As finalResult restoreAs
        (.proj name idx body) state
        (Expr.updateProj! (.proj name idx body) body', outState)

/-- Lift a complete expression mapping to leafwise reopening.  Source
free-variable scoping is split structurally in exactly the same way as the
lowering traversal. -/
theorem NestedExprMapping.reopens
    (H : NestedExprMapping env lctx params As finalResult input state out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hselection : LocalForallSelection lctx As)
    (Hinput : FVarsIn (· ∈ Hselection.fvars) input) :
    NestedExprReopening env lctx params As finalResult restoreAs input state
      out := by
  induction H with
  | hit Hnode =>
    exact .hit (Hnode.reopensOfFVars hresultParams fvars hparams hnodup
      Hselection Hinput)
  | bvar Hnode => exact .bvar Hnode
  | fvar Hnode => exact .fvar Hnode
  | mvar Hnode => exact .mvar Hnode
  | sort Hnode => exact .sort Hnode
  | const Hnode => exact .const Hnode
  | lit Hnode => exact .lit Hnode
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .app Hnode (ihFn Hinput.1) (ihArg Hinput.2)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .lam Hnode (ihDom Hinput.1) (ihBody Hinput.2)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .forallE Hnode (ihDom Hinput.1) (ihBody Hinput.2)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact .letE Hnode (ihType Hinput.1) (ihValue Hinput.2.1)
      (ihBody Hinput.2.2)
  | mdata Hnode Hbody ihBody =>
    exact .mdata Hnode (ihBody Hinput)
  | proj Hnode Hbody ihBody =>
    exact .proj Hnode (ihBody Hinput)

/-- A structural lowering trace cannot introduce a constant application head
unless the root itself was recognized. In the application case, maximality
rules out a recognized function prefix whenever the parent has a certified
miss. -/
theorem NestedExprReopening.constHead_of_noCandidate
    (H : NestedExprReopening env lctx params As finalResult restoreAs input
      state out)
    (Hmiss : NoNestedAppCandidate env state input)
    (Hhead : out.1.getAppFn = .const name levels) :
    input.getAppFn = .const name levels := by
  induction H with
  | hit Hnode =>
    rcases Hnode with
      ⟨value, targetName, levels, auxName, auxLevels, nested,
        Hcandidate, hhead, hlowered, hlookup, hreopens⟩
    exact False.elim (Hmiss value Hcandidate)
  | bvar | fvar | mvar | sort | const | lit => exact Hhead
  | @app fn arg state fn' fnState arg' outState Hnode Hfn Harg ihFn ihArg =>
    have HfnMiss : NoNestedAppCandidate env state fn := by
      intro info Hcandidate
      exact Hmiss info (Hcandidate.app arg)
    apply ihFn HfnMiss
    simpa [Expr.getAppFn] using Hhead
  | lam => simp [Expr.getAppFn] at Hhead
  | forallE => simp [Expr.getAppFn] at Hhead
  | letE => simp [Expr.getAppFn] at Hhead
  | mdata => simp [Expr.getAppFn] at Hhead
  | proj => simp [Expr.getAppFn] at Hhead

/-- The constant-head reflection theorem remains true after the constructor
parameters have been renamed at an arbitrary binder depth. -/
theorem NestedExprReopening.reopenedConstHead_of_noCandidate
    (H : NestedExprReopening env lctx params As finalResult restoreAs input
      state out)
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (Hmiss : NoNestedAppCandidate env state input)
    (Hhead : (Expr.reopenFVarsAt out.1 fvars restoreFvars k).getAppFn =
      .const name levels) :
    input.getAppFn = .const name levels := by
  apply H.constHead_of_noCandidate Hmiss
  exact Expr.getAppFn_reopenFVarsAt_eq_const hnd hsize out.1 k Hhead

/-- At a structural lowering node, restoration must miss the node itself.
The proof uses recognition maximality for the lowered head and source-map
disjointness for the corresponding original constant. -/
theorem NestedExprReopening.restoreNode_none
    (H : NestedExprReopening env lctx params As finalResult targetAs input
      state out)
    (restoreEnv : Environment)
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (Hmiss : NoNestedAppCandidate env state input)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv input) (k : Nat) :
    finalResult.restoreNestedNode restoreEnv targetAs {}
      (Expr.reopenFVarsAt out.1 fvars restoreFvars k) = none := by
  generalize ht : Expr.reopenFVarsAt out.1 fvars restoreFvars k = t
  cases t with
  | const name levels =>
    have hsourceHead : input.getAppFn = .const name levels :=
      H.reopenedConstHead_of_noCandidate hnd hsize Hmiss (by
        rw [ht]
        rfl)
    have hdisjoint := Hsource.getAppFn hsourceHead
    have hrec : ({} : NameMap Name).find? name = none := rfl
    simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
      Expr.getAppFn, hrec, hdisjoint.1, hdisjoint.2]
  | app fn arg =>
    cases hhead : (Expr.app fn arg).getAppFn with
    | const name levels =>
      simp only [Expr.getAppFn] at hhead
      have hsourceHead : input.getAppFn = .const name levels :=
        H.reopenedConstHead_of_noCandidate hnd hsize Hmiss (by
          rw [ht]
          exact hhead)
      have hdisjoint := Hsource.getAppFn hsourceHead
      simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
        Expr.getAppFn, hhead, hdisjoint.1, hdisjoint.2]
    | bvar | fvar | mvar | sort | app | lam | forallE | letE | lit | mdata
        | proj =>
      simp only [Expr.getAppFn] at hhead
      simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
        Expr.getAppFn, hhead]
  | bvar | fvar | mvar | sort | lam | forallE | letE | lit | mdata | proj =>
    simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode,
      Expr.getAppFn]

/-- Restoring a completely lowered expression is a left inverse, up to Lean
expression equivalence, of the nested-expression traversal. The proof follows
the same top-down stopping rule as `Expr.replace`: hits restore immediately,
while certified misses recurse through the renamed children. -/
theorem NestedExprReopening.restore_eqv
    (H : NestedExprReopening env lctx params As finalResult targetAs input
      state out)
    (restoreEnv : Environment)
    (Hselection : LocalForallSelection lctx As)
    (hnd : Hselection.fvars.Nodup)
    (restoreFvars : List FVarId)
    (hrestore : targetAs = (restoreFvars.map Expr.fvar).toArray)
    (hsize : restoreFvars.length = Hselection.fvars.length)
    (hresultNParams : finalResult.nparams = As.size)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv input)
    (k : Nat) :
    ((Expr.reopenFVarsAt out.1 Hselection.fvars restoreFvars k).replace
        (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
      Expr.reopenFVarsAt input Hselection.fvars restoreFvars k) = true := by
  induction H generalizing k with
  | @hit hitInput hitState hitOutput nextState Hnode =>
    have hout := Expr.reopenFVarsAt_eq_reopenParams hnd hsize
      Hselection.expressions hrestore hitOutput k
    have hin := Expr.reopenFVarsAt_eq_reopenParams hnd hsize
      Hselection.expressions hrestore hitInput k
    rcases Hnode.restoreNode restoreEnv Hselection hresultNParams with
      ⟨restored, hrestored, heqv⟩
    rw [hout, hin]
    rw [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hrestored]
    exact heqv
  | bvar Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.bvar Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    rw [Expr.reopenFVarsAt_bvar hsize] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | fvar Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.fvar Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    rcases Expr.reopenFVarsAt_fvar_exists hnd hsize _ k with
      ⟨restored, hopen⟩
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @mvar stepState id Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.mvar Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.mvar id) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @sort level stepState Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.sort Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.sort level) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @const name levels stepState Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.const Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.const name levels) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @lit literal stepState Hnode =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.lit Hnode) restoreEnv hnd hsize
      Hnode.noCandidate Hsource k
    have hopen := Expr.reopenFVarsAt_of_abstract1_eq_self
      (e := Expr.lit literal) (by intro fv depth; simp [Expr.abstract1])
      (by simp [Expr.looseBVarRange']) Hselection.fvars restoreFvars k
    rw [hopen] at hnone ⊢
    simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, hnone]
  | @app fn arg stepState fn' fnState arg' outState Hnode Hfn Harg ihFn ihArg =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.app Hnode Hfn Harg) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    have hopen : R (Expr.updateApp! (.app fn arg) fn' arg') =
        .app (R fn') (R arg') := by
      simp [R, Expr.reopenFVarsAt]
    have hinput : R (.app fn arg) = .app (R fn) (R arg) := by
      simp [R, Expr.reopenFVarsAt]
    change ((R (Expr.updateApp! (.app fn arg) fn' arg')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R (.app fn arg)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R (Expr.updateApp! (.app fn arg) fn' arg')) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def]
    rw [hnone]
    have hfn := ihFn Hsource.1 k
    have harg := ihArg Hsource.2 k
    rw [Expr.replace_eq] at hfn harg
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R fn') == R fn) = true) at hfn
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R arg') == R arg) = true) at harg
    exact Expr.app_eqv hfn harg
  | @lam name dom body bi stepState dom' domState body' outState
      Hnode Hdom Hbody ihDom ihBody =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.lam Hnode Hdom Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R0 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    let R1 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars (k + 1)
    have hopen : R0 (Expr.updateLambdaE! (.lam name dom body bi) dom' body') =
        .lam name (R0 dom') (R1 body') bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    have hinput : R0 (.lam name dom body bi) =
        .lam name (R0 dom) (R1 body) bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    change ((R0 (Expr.updateLambdaE! (.lam name dom body bi) dom' body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R0 (.lam name dom body bi)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R0 (Expr.updateLambdaE! (.lam name dom body bi) dom' body')) = none
        at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hdom := ihDom Hsource.1 k
    have hbody := ihBody Hsource.2 (k + 1)
    rw [Expr.replace_eq] at hdom hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 dom') == R0 dom) = true) at hdom
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R1 body') == R1 body) = true) at hbody
    exact Expr.lam_eqv hdom hbody
  | @forallE name dom body bi stepState dom' domState body' outState
      Hnode Hdom Hbody ihDom ihBody =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.forallE Hnode Hdom Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R0 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    let R1 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars (k + 1)
    have hopen : R0 (Expr.updateForallE! (.forallE name dom body bi) dom' body') =
        .forallE name (R0 dom') (R1 body') bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    have hinput : R0 (.forallE name dom body bi) =
        .forallE name (R0 dom) (R1 body) bi := by
      simp [R0, R1, Expr.reopenFVarsAt]
    change ((R0 (Expr.updateForallE! (.forallE name dom body bi) dom' body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R0 (.forallE name dom body bi)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R0 (Expr.updateForallE! (.forallE name dom body bi) dom' body')) = none
        at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hdom := ihDom Hsource.1 k
    have hbody := ihBody Hsource.2 (k + 1)
    rw [Expr.replace_eq] at hdom hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 dom') == R0 dom) = true) at hdom
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R1 body') == R1 body) = true) at hbody
    exact Expr.forallE_eqv hdom hbody
  | @letE name type value body nondep stepState type' typeState value'
      valueState body' outState Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.letE Hnode Htype Hvalue Hbody) restoreEnv hnd hsize
        Hnode.noCandidate Hsource k
    let R0 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    let R1 : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars (k + 1)
    have hopen : R0 (Expr.updateLet! (.letE name type value body nondep)
        type' value' body' nondep) =
        .letE name (R0 type') (R0 value') (R1 body') nondep := by
      simp [R0, R1, Expr.reopenFVarsAt]
    have hinput : R0 (.letE name type value body nondep) =
        .letE name (R0 type) (R0 value) (R1 body) nondep := by
      simp [R0, R1, Expr.reopenFVarsAt]
    change ((R0 (Expr.updateLet! (.letE name type value body nondep)
      type' value' body' nondep)).replace
        (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
      R0 (.letE name type value body nondep)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R0 (Expr.updateLet! (.letE name type value body nondep)
        type' value' body' nondep)) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have htype := ihType Hsource.1 k
    have hvalue := ihValue Hsource.2.1 k
    have hbody := ihBody Hsource.2.2 (k + 1)
    rw [Expr.replace_eq] at htype hvalue hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 type') == R0 type) = true) at htype
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R0 value') == R0 value) = true) at hvalue
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R1 body') == R1 body) = true) at hbody
    exact Expr.letE_eqv htype hvalue hbody
  | @mdata data body stepState body' outState Hnode Hbody ihBody =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.mdata Hnode Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    have hopen : R (Expr.updateMData! (.mdata data body) body') =
        .mdata data (R body') := by simp [R, Expr.reopenFVarsAt]
    have hinput : R (.mdata data body) = .mdata data (R body) := by
      simp [R, Expr.reopenFVarsAt]
    change ((R (Expr.updateMData! (.mdata data body) body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R (.mdata data body)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R (Expr.updateMData! (.mdata data body) body')) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hbody := ihBody Hsource k
    rw [Expr.replace_eq] at hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R body') == R body) = true) at hbody
    exact Expr.mdata_eqv data hbody
  | @proj name idx body stepState body' outState Hnode Hbody ihBody =>
    have hnone := NestedExprReopening.restoreNode_none (targetAs := targetAs)
      (.proj Hnode Hbody) restoreEnv hnd hsize Hnode.noCandidate Hsource k
    let R : Expr → Expr := fun e =>
      Expr.reopenFVarsAt e Hselection.fvars restoreFvars k
    have hopen : R (Expr.updateProj! (.proj name idx body) body') =
        .proj name idx (R body') := by simp [R, Expr.reopenFVarsAt]
    have hinput : R (.proj name idx body) = .proj name idx (R body) := by
      simp [R, Expr.reopenFVarsAt]
    change ((R (Expr.updateProj! (.proj name idx body) body')).replace
      (finalResult.restoreNestedNode restoreEnv targetAs {}) ==
        R (.proj name idx body)) = true
    change finalResult.restoreNestedNode restoreEnv targetAs {}
      (R (Expr.updateProj! (.proj name idx body) body')) = none at hnone
    rw [hopen] at hnone
    rw [hopen, hinput, Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def,
      hnone]
    have hbody := ihBody Hsource k
    rw [Expr.replace_eq] at hbody
    change ((Expr.replaceNoCache
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (R body') == R body) = true) at hbody
    exact Expr.proj_eqv hbody

/-- Semantic form of the structural lowering left inverse.  Once the reopened
source expression has a canonical typed translation, restoring its lowered
image has the same translation and type.  This interprets arbitrary nested
applications (including trailing arguments) compositionally, rather than
classifying the concrete `restoreNestedNode` hit at the root. -/
theorem NestedExprReopening.restoredAbstractTypeTranslation
    (H : NestedExprReopening env lctx params As finalResult targetAs input
      state out)
    (restoreEnv : Environment)
    (Hselection : LocalForallSelection lctx As)
    (hnd : Hselection.fvars.Nodup)
    (restoreFvars : List FVarId)
    (hrestore : targetAs = (restoreFvars.map Expr.fvar).toArray)
    (hsize : restoreFvars.length = Hselection.fvars.length)
    (hresultNParams : finalResult.nparams = As.size)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv input)
    (k : Nat)
    (Htyped : Expr.AbstractTypeTranslation venv lparams Δ
      (Expr.reopenFVarsAt input Hselection.fvars restoreFvars k)) :
    Expr.AbstractTypeTranslation venv lparams Δ
      ((Expr.reopenFVarsAt out.1 Hselection.fvars restoreFvars k).replace
        (finalResult.restoreNestedNode restoreEnv targetAs {})) := by
  rcases Htyped with ⟨target, Htr, Htype⟩
  have Heqv := H.restore_eqv restoreEnv Hselection hnd restoreFvars hrestore
    hsize hresultNParams Hsource k
  exact ⟨target, Htr.eqv (BEq.symm Heqv), Htype⟩

/-- Relational form consumed directly by the restored-telescope fold.  The
`ExprReplacement` certificate identifies its output with the concrete
`Expr.replace` interpreted by `restoredAbstractTypeTranslation`. -/
theorem NestedExprReopening.replacementAbstractTypeTranslation
    (H : NestedExprReopening env lctx params As finalResult targetAs input
      state out)
    (restoreEnv : Environment)
    (Hselection : LocalForallSelection lctx As)
    (hnd : Hselection.fvars.Nodup)
    (restoreFvars : List FVarId)
    (hrestore : targetAs = (restoreFvars.map Expr.fvar).toArray)
    (hsize : restoreFvars.length = Hselection.fvars.length)
    (hresultNParams : finalResult.nparams = As.size)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv input)
    (k : Nat)
    (restored : Expr)
    (Hreplacement : ExprReplacement
      (finalResult.restoreNestedNode restoreEnv targetAs {})
      (Expr.reopenFVarsAt out.1 Hselection.fvars restoreFvars k) restored)
    (Htyped : Expr.AbstractTypeTranslation venv lparams Δ
      (Expr.reopenFVarsAt input Hselection.fvars restoreFvars k)) :
    Expr.AbstractTypeTranslation venv lparams Δ restored := by
  rw [Hreplacement.eq_replace]
  exact H.restoredAbstractTypeTranslation restoreEnv Hselection hnd
    restoreFvars hrestore hsize hresultNParams Hsource k Htyped

theorem RecognizedNestedReplacement.auxFVarsIn
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (HAs : LocalForallSelection lctx As)
    (hnparams : value.numParams ≤ args.size)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch =>
    exact Hbatch.auxFVarsIn HAs hnparams Hlevels Hargs Hparams Hstate

theorem NestedReplacement.auxFVarsIn
    (H : NestedReplacement env lctx params As e state out)
    (HAs : LocalForallSelection lctx As)
    (Hinput : e.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | @recognized value targetName levels out Hcandidate hhead Hresult =>
    apply Hresult.auxFVarsIn HAs Hcandidate.parameters.arity
    · have Hfn := Hinput.getAppFn
      rw [hhead] at Hfn
      simpa [Lean4Lean.FVarsIn] using Hfn
    · intro arg harg
      apply Hinput.getAppArgsList
      rw [← Expr.getAppArgs_toList]
      exact Array.mem_toList_iff.mpr harg
    · exact Hparams
    · exact Hstate

theorem RecognizedNestedReplacement.pendingNewTypesClosed
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch =>
    exact Hbatch.pendingNewTypesClosed Henv Hclosing Hlevels Hargs Hstate

theorem NestedReplacement.pendingNewTypesClosed
    (H : NestedReplacement env lctx params As e state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hinput : e.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | @recognized value targetName levels out Hcandidate hhead Hresult =>
    apply Hresult.pendingNewTypesClosed Henv Hclosing
    · have Hfn := Hinput.getAppFn
      rw [hhead] at Hfn
      simpa [Lean4Lean.FVarsIn] using Hfn
    · intro arg harg
      apply Hinput.getAppArgsList
      rw [← Expr.getAppArgs_toList]
      exact Array.mem_toList_iff.mpr harg
    · exact Hstate

theorem RecognizedNestedReplacement.newTypesLE
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out) : NestedNewTypesLE state out.2 := by
  cases H with
  | cached => exact .refl _
  | generated _ Hbatch => exact Hbatch.newTypesLE

theorem RecognizedNestedReplacement.nestedAuxLE
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out) : NestedAuxLE state out.2 := by
  cases H with
  | cached => exact .refl _
  | generated _ Hbatch => exact Hbatch.nestedAuxLE

theorem RecognizedNestedReplacement.namesWF
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch => exact Hbatch.namesWF Hindex Hstate

theorem RecognizedNestedReplacement.namesFresh
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  cases H with
  | cached => exact Hstate
  | generated _ Hbatch => exact Hbatch.namesFresh Hstate

theorem NestedReplacement.newTypesLE
    (H : NestedReplacement env lctx params As e state out) :
    NestedNewTypesLE state out.2 := by
  cases H with
  | unrecognized => exact .refl _
  | recognized _ _ Hresult => exact Hresult.newTypesLE

theorem NestedReplacement.nestedAuxLE
    (H : NestedReplacement env lctx params As e state out) :
    NestedAuxLE state out.2 := by
  cases H with
  | unrecognized => exact .refl _
  | recognized _ _ Hresult => exact Hresult.nestedAuxLE

theorem NestedReplacement.namesWF
    (H : NestedReplacement env lctx params As e state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | recognized _ _ Hresult => exact Hresult.namesWF Hindex Hstate

theorem NestedReplacement.namesFresh
    (H : NestedReplacement env lctx params As e state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  cases H with
  | unrecognized => exact Hstate
  | recognized _ _ Hresult => exact Hresult.namesFresh Hstate

theorem NestedExprReplacement.newTypesLE
    (H : NestedExprReplacement env lctx params As e state out) :
    NestedNewTypesLE state out.2 := by
  induction H with
  | hit Hnode => exact Hnode.newTypesLE
  | bvar | fvar | mvar | sort | const | lit => exact .refl _
  | app Hnode _ _ ihFn ihArg =>
    exact Hnode.newTypesLE.trans (ihFn.trans ihArg)
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    exact Hnode.newTypesLE.trans (ihDom.trans ihBody)
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    exact Hnode.newTypesLE.trans (ihType.trans (ihValue.trans ihBody))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody =>
    exact Hnode.newTypesLE.trans ihBody

theorem NestedExprReplacement.nestedAuxLE
    (H : NestedExprReplacement env lctx params As e state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | hit Hnode => exact Hnode.nestedAuxLE
  | bvar | fvar | mvar | sort | const | lit => exact .refl _
  | app Hnode _ _ ihFn ihArg =>
    exact Hnode.nestedAuxLE.trans (ihFn.trans ihArg)
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    exact Hnode.nestedAuxLE.trans (ihDom.trans ihBody)
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    exact Hnode.nestedAuxLE.trans (ihType.trans (ihValue.trans ihBody))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody =>
    exact Hnode.nestedAuxLE.trans ihBody

theorem NestedExprReplacement.namesWF
    (H : NestedExprReplacement env lctx params As e state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | hit Hnode => exact Hnode.namesWF Hindex Hstate
  | bvar | fvar | mvar | sort | const | lit => exact Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    exact ihArg (ihFn (Hnode.namesWF Hindex Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody =>
    exact ihBody (ihDom (Hnode.namesWF Hindex Hstate))
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    exact ihBody (ihDom (Hnode.namesWF Hindex Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    exact ihBody (ihValue (ihType (Hnode.namesWF Hindex Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    exact ihBody (Hnode.namesWF Hindex Hstate)

theorem NestedExprReplacement.namesFresh
    (H : NestedExprReplacement env lctx params As e state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | hit Hnode => exact Hnode.namesFresh Hstate
  | bvar | fvar | mvar | sort | const | lit => exact Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    exact ihArg (ihFn (Hnode.namesFresh Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody
      | forallE Hnode Hdom Hbody ihDom ihBody =>
    exact ihBody (ihDom (Hnode.namesFresh Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    exact ihBody (ihValue (ihType (Hnode.namesFresh Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    exact ihBody (Hnode.namesFresh Hstate)

theorem NestedExprReplacement.pendingNewTypesClosed
    (H : NestedExprReplacement env lctx params As e state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hinput : e.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  induction H with
  | hit Hnode =>
    exact Hnode.pendingNewTypesClosed Henv Hclosing Hinput Hstate
  | bvar Hnode | fvar Hnode | mvar Hnode | sort Hnode | const Hnode
      | lit Hnode =>
    exact Hnode.pendingNewTypesClosed Henv Hclosing Hinput Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihArg Hinput.2
      (ihFn Hinput.1
        (Hnode.pendingNewTypesClosed Henv Hclosing
          ⟨Hinput.1, Hinput.2⟩ Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody
      | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2
      (ihDom Hinput.1
        (Hnode.pendingNewTypesClosed Henv Hclosing
          ⟨Hinput.1, Hinput.2⟩ Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2.2
      (ihValue Hinput.2.1
        (ihType Hinput.1
          (Hnode.pendingNewTypesClosed Henv Hclosing
            ⟨Hinput.1, Hinput.2.1, Hinput.2.2⟩ Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    exact ihBody Hinput
      (Hnode.pendingNewTypesClosed Henv Hclosing Hinput Hstate)

theorem NestedExprReplacement.auxFVarsIn
    (H : NestedExprReplacement env lctx params As e state out)
    (HAs : LocalForallSelection lctx As)
    (Hinput : e.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  induction H generalizing P with
  | hit Hnode => exact Hnode.auxFVarsIn HAs Hinput Hparams Hstate
  | bvar Hnode | fvar Hnode | mvar Hnode | sort Hnode | const Hnode
      | lit Hnode =>
    exact Hnode.auxFVarsIn HAs Hinput Hparams Hstate
  | app Hnode Hfn Harg ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihArg Hinput.2 Hparams
      (ihFn Hinput.1 Hparams
        (Hnode.auxFVarsIn HAs Hinput Hparams Hstate))
  | lam Hnode Hdom Hbody ihDom ihBody
      | forallE Hnode Hdom Hbody ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2 Hparams
      (ihDom Hinput.1 Hparams
        (Hnode.auxFVarsIn HAs Hinput Hparams Hstate))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2.2 Hparams
      (ihValue Hinput.2.1 Hparams
        (ihType Hinput.1 Hparams
          (Hnode.auxFVarsIn HAs Hinput Hparams Hstate)))
  | mdata Hnode Hbody ihBody | proj Hnode Hbody ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput Hparams
      (Hnode.auxFVarsIn HAs Hinput Hparams Hstate)

theorem NestedExprReplacement.finalMapping
    (H : NestedExprReplacement env lctx params As input state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    NestedExprMapping env lctx params As finalResult input state out := by
  induction H generalizing finalState with
  | hit Hnode => exact .hit (Hnode.finalMapping Hlater Hmap)
  | bvar Hnode => exact .bvar Hnode
  | fvar Hnode => exact .fvar Hnode
  | mvar Hnode => exact .mvar Hnode
  | sort Hnode => exact .sort Hnode
  | const Hnode => exact .const Hnode
  | lit Hnode => exact .lit Hnode
  | app Hnode Hfn Harg ihFn ihArg =>
    exact .app Hnode (ihFn (Harg.nestedAuxLE.trans Hlater) Hmap)
      (ihArg Hlater Hmap)
  | lam Hnode Hdom Hbody ihDom ihBody =>
    exact .lam Hnode (ihDom (Hbody.nestedAuxLE.trans Hlater) Hmap)
      (ihBody Hlater Hmap)
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    exact .forallE Hnode (ihDom (Hbody.nestedAuxLE.trans Hlater) Hmap)
      (ihBody Hlater Hmap)
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    exact .letE Hnode
      (ihType (Hvalue.nestedAuxLE.trans
        (Hbody.nestedAuxLE.trans Hlater)) Hmap)
      (ihValue (Hbody.nestedAuxLE.trans Hlater) Hmap)
      (ihBody Hlater Hmap)
  | mdata Hnode Hbody ihBody => exact .mdata Hnode (ihBody Hlater Hmap)
  | proj Hnode Hbody ihBody => exact .proj Hnode (ihBody Hlater Hmap)

theorem replaceAllNested_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (e : Expr) (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : As.size = params.size)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.replaceAllNested lctx params As e env state).WF
      fun out => NestedExprReplacement env lctx params As e state out := by
  induction e generalizing state with
  | bvar i =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.bvar i)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.bvar Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | fvar id =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.fvar id)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.fvar Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | mvar id =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.mvar id)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.mvar Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | sort level =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As (.sort level)
      state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.sort Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | const name levels =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.const name levels) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.const Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | lit literal =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.lit literal) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone; exact Except.WF.pure (.lit Hnode)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | app fn arg ihFn ihArg =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.app fn arg) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihFn state) ?_
      intro fn' fnState Hfn
      refine nestedBind.WF (ihArg fnState) ?_
      intro arg' outState Harg
      exact Except.WF.pure (.app Hnode Hfn Harg)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | lam name dom body bi ihDom ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.lam name dom body bi) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihDom state) ?_
      intro dom' domState Hdom
      refine nestedBind.WF (ihBody domState) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.lam Hnode Hdom Hbody)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | forallE name dom body bi ihDom ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.forallE name dom body bi) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihDom state) ?_
      intro dom' domState Hdom
      refine nestedBind.WF (ihBody domState) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.forallE Hnode Hdom Hbody)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | letE name type value body nondep ihType ihValue ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.letE name type value body nondep) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihType state) ?_
      intro type' typeState Htype
      refine nestedBind.WF (ihValue typeState) ?_
      intro value' valueState Hvalue
      refine nestedBind.WF (ihBody valueState) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.letE Hnode Htype Hvalue Hbody)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | mdata data body ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.mdata data body) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihBody state) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.mdata Hnode Hbody)
    · cases hsome; exact Except.WF.pure (.hit Hnode)
  | proj name idx body ihBody =>
    simp only [Lean4Lean.ElimNestedInductive.replaceAllNested,
      Expr.replaceM, Expr.replaceNoCacheT]
    refine nestedBind.WF (replaceIfNested_refines env lctx params As
      (.proj name idx body) state hsize hclosures) ?_
    intro replacement nextState Hnode
    rcases Hnode.outcome with hnone | ⟨output, finalState, hsome⟩
    · cases hnone
      refine nestedBind.WF (ihBody state) ?_
      intro body' outState Hbody
      exact Except.WF.pure (.proj Hnode Hbody)
    · cases hsome; exact Except.WF.pure (.hit Hnode)

/-- Any successful replacement is rooted in an occurrence satisfying the
independent recognition contract. This prefix theorem intentionally leaves
cache reuse and fresh auxiliary generation to separate certificates. -/
theorem replaceIfNested_recognized
    (lctx : LocalContext) (params As : Array Expr) (e : Expr)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.replaceIfNested
      lctx params As e env state).WF fun out =>
        out.1.isSome → ∃ info, NestedAppCandidate env state e info := by
  rw [Lean4Lean.ElimNestedInductive.replaceIfNested]
  refine nestedBind.WF
    (x := Lean4Lean.ElimNestedInductive.isNestedInductiveApp? e)
    (P := fun recognized =>
      recognized.2 = state ∧ ∀ info, recognized.1 = some info →
        NestedAppCandidate env state e info) ?_ ?_
  · intro recognized hrecognized
    exact ⟨isNestedInductiveApp_preservesState e env state
        recognized hrecognized,
      isNestedInductiveApp_candidate e env state recognized hrecognized⟩
  · intro recognized nextState hrecognized
    rcases hrecognized with ⟨hstate, hcandidate⟩
    cases hstate
    cases recognized with
    | none =>
      exact Except.WF.pure (by simp)
    | some info =>
      intro out _ hout
      exact ⟨info, hcandidate info rfl⟩

/-- Structural contract for one constructor after nested lowering.  It
records the exact source telescope opened by the executable pass, the arity
check performed before rebuilding it, and the fact that lowering changes
only the constructor type.  The node-level replacement semantics are exposed
separately by `replaceIfNested_recognized`. -/
structure LoweredConstructorShape
    (nparams : Nat) (source target : Constructor) : Prop where
  name : target.name = source.name
  rebuilt : ∃ lctx tail As lowered,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    ∃ _ : LocalForallSelection lctx As,
      As.size = nparams ∧ target.type = lctx.mkForall As lowered

theorem LoweredConstructorShape.targetRestoreTelescope
    (H : LoweredConstructorShape nparams source target) :
    RestoreTelescope target.type nparams := by
  rcases H.rebuilt with
    ⟨lctx, tail, As, lowered, Hopening, Hselection, hsize, htype⟩
  rw [htype, ← hsize]
  exact (Hselection.forallTelescope lowered).restorePrefix (Nat.le_refl _)

inductive LoweredConstructorShapes (nparams : Nat) :
    List Constructor → List Constructor → Prop
  | nil : LoweredConstructorShapes nparams [] []
  | cons : LoweredConstructorShape nparams source target →
      LoweredConstructorShapes nparams sources targets →
      LoweredConstructorShapes nparams (source :: sources) (target :: targets)

theorem ElimNestedInductive.lowerConstructor.shape
    (params : Array Expr) (nparams : Nat) (ctor : Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams ctor
      env state).WF fun out => LoweredConstructorShape nparams ctor out.1 := by
  unfold Lean4Lean.ElimNestedInductive.lowerConstructor
  apply ElimNestedInductive.withParams.refinesSelected
  intro lctx tail As openedState Hopening _Hctx Hselection _hnodup _hnewTypes
    _hnestedAux _hnextIdx
  have hsize : As.size = nparams := Hopening.initial_size
  simp only [hsize, beq_self_eq_true, if_true]
  refine nestedBind.WF
    (x := Lean4Lean.ElimNestedInductive.replaceAllNested lctx params As tail)
    (P := fun _ => True) ?_ ?_
  · intro _ _
    trivial
  · intro lowered nextState _
    exact Except.WF.pure
      ⟨rfl, lctx, tail, As, lowered, Hopening, Hselection, hsize, rfl⟩

/-- Semantic constructor-lowering certificate.  In addition to the rebuilt
telescope shape, it records the complete stateful nested-expression
translation from the opened source tail to the installed constructor type. -/
structure LoweredConstructorTranslation
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  translated : ∃ lctx tail As lowered openedState,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    lctx.WF ∧
    ∃ Hselection : LocalForallSelection lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      NestedExprReplacement env lctx params As tail openedState
        (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered

theorem LoweredConstructorTranslation.targetRestoreTelescope
    (H : LoweredConstructorTranslation env params nparams source state out) :
    RestoreTelescope out.1.type nparams := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      _hnodup, hopenedTypes, _hopenedAux, _hopenedNext, hsize, Hreplace, htype⟩
  rw [htype, ← hsize]
  exact (Hselection.forallTelescope lowered).restorePrefix (Nat.le_refl _)

theorem LoweredConstructorTranslation.newTypesLE
    (H : LoweredConstructorTranslation env params nparams source state out) :
    NestedNewTypesLE state out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, hopenedTypes, _, _,
      _, Hreplace, _⟩
  rcases Hreplace.newTypesLE with ⟨suffix, hsuffix⟩
  exact ⟨suffix, by simpa [hopenedTypes] using hsuffix⟩

theorem LoweredConstructorTranslation.nestedAuxLE
    (H : LoweredConstructorTranslation env params nparams source state out) :
    NestedAuxLE state out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux, _, _,
      Hreplace, _⟩
  rcases Hreplace.nestedAuxLE with ⟨suffix, hsuffix⟩
  exact ⟨suffix, by simpa [hopenedAux] using hsuffix⟩

theorem LoweredConstructorTranslation.namesWF
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux,
      hopenedNext, _, Hreplace, _⟩
  exact Hreplace.namesWF Hindex
    (Hstate.ofCacheCounterEq hopenedAux hopenedNext)

theorem LoweredConstructorTranslation.namesFresh
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _, _, _, _, _, hopenedAux,
      _, _, Hreplace, _⟩
  exact Hreplace.namesFresh (Hstate.ofCacheEq hopenedAux)

theorem LoweredConstructorTranslation.auxFVarsIn
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hsource : source.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      _hnodup, _hopenedTypes, hopenedAux, _hopenedNext, _hsize, Hreplace,
      _htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun _ hfalse => False.elim hfalse)
  have Hinput : tail.FVarsIn
      (fun fv => fv ∈ Hselection.fvars ∨ P fv) :=
    Htail.mono fun _ hfv => Or.inl hfv
  have Hopened : NestedAuxFVarsIn P openedState := by
    intro nested name hentry
    apply Hstate nested name
    rwa [hopenedAux] at hentry
  exact Hreplace.auxFVarsIn Hselection Hinput Hparams Hopened

/-- Constructor lowering interpreted against the final restoration map. The
opened source telescope and rebuilt target telescope are retained verbatim,
while the body traversal is promoted from operational replacement to the
semantic `NestedExprMapping` relation. -/
structure LoweredConstructorMapping
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  mapped : ∃ lctx tail As lowered openedState,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    lctx.WF ∧
    ∃ Hselection : LocalForallSelection lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      NestedExprMapping env lctx params As finalResult tail openedState
        (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered

/-- Constructor lowering with its expression mapping upgraded pointwise to
reopening under a restoration parameter array. -/
structure LoweredConstructorReopening
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr)
    (source : Constructor) (state : Lean4Lean.ElimNestedInductive.State)
    (out : Constructor × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  reopened : ∃ lctx tail As lowered openedState,
    NestedParamOpening {} #[] source.type nparams lctx tail As ∧
    ∃ Hselection : LocalForallSelection lctx As,
      Hselection.fvars.Nodup ∧
      openedState.newTypes = state.newTypes ∧
      openedState.nestedAux = state.nestedAux ∧
      openedState.nextIdx = state.nextIdx ∧
      As.size = nparams ∧
      NestedExprReopening env lctx params As finalResult restoreAs tail
        openedState (lowered, out.2) ∧
      out.1.type = lctx.mkForall As lowered

/-- A mapped lowered constructor type contains no free-variable IDs: the
translated body remains scoped by the copied source parameters, and the
rebuilt forall telescope closes exactly those parameters. -/
theorem LoweredConstructorMapping.targetFVarIdsClosed
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (Hsource : source.type.FVarsIn fun _ => False) :
    out.1.type.FVarIdsIn fun _ => False := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun fv hfalse => False.elim hfalse)
  have Hlowered : lowered.FVarIdsIn (· ∈ Hselection.fvars) :=
    Hmapping.outputFVarIdsIn Hselection (FVarsIn_to_FVarIdsIn Htail)
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  rw [htype]
  exact Hopening.toRestoreParamOpening.root_mkForall_fvarIdsClosed hlctxWF
    Htelescope (FVarsIn_to_FVarIdsIn Hsource) Hselection Hlowered

/-- Source and lowered constructor types have exactly the same retained
forall prefix; lowering changes only the residual constructor body. -/
theorem LoweredConstructorMapping.sourceTargetSameForallPrefix
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (Hsource : source.type.FVarsIn fun _ => False) :
    Expr.SameForallPrefix nparams source.type out.1.type := by
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  rcases Hopening.toRestoreParamOpening.forall_rebuilding_data hlctxWF
      Htelescope with
    ⟨decls, _hlctx, hparams, _hlength, _hdeclNodup, _hfind, hrebuild⟩
  have hids : Hselection.fvars = decls.map (fun d => d.fvarId) := by
    have harr : (Hselection.fvars.map Expr.fvar).toArray =
        ((decls.map (fun d => d.fvarId)).map Expr.fvar).toArray := by
      rw [← Hselection.expressions]
      apply Array.toList_inj.mp
      simpa [Function.comp_def] using hparams
    have hlist : Hselection.fvars.map Expr.fvar =
        (decls.map (fun d => d.fvarId)).map Expr.fvar := by
      simpa using congrArg Array.toList harr
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist
  have hsourceFold :
      Hselection.fvars.foldr
          (fun fv result =>
            LocalContext.mkBindingList1 false lctx [] fv
              (result.abstract1 fv)) tail = source.type := by
    have hclosed := FVarsIn_to_FVarIdsIn Hsource
    have havoid : source.type.FVarIdsIn
        (fun fv => fv ∉ decls.map (fun d => d.fvarId)) :=
      hclosed.mono fun fv hfalse => False.elim hfalse
    simpa [hids] using hrebuild havoid
  have htargetFold : lctx.mkForall As lowered =
      Hselection.fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1 false lctx [] fv
            (result.abstract1 fv)) lowered := by
    calc
      lctx.mkForall As lowered =
          lctx.mkForall (Hselection.fvars.map Expr.fvar).toArray lowered :=
        congrArg (fun xs => lctx.mkForall xs lowered) Hselection.expressions
      _ = _ := by
        rw [LocalContext.mkForall, LocalContext.mkBinding_eq]
        apply LocalContext.mkBindingList_eq_fold
        · intro fv hfv
          rcases Hselection.declarations fv hfv with
            ⟨index, name, type, bi, kind, hfind⟩
          exact ⟨.cdecl index fv name type bi kind, hfind⟩
        · exact hnodupAs
  have hsame := LocalContext.sameForallPrefix_fold
    Hselection.declarations tail lowered
  have hlen : Hselection.fvars.length = nparams := by
    have := congrArg Array.size Hselection.expressions
    simpa [hsize] using this.symm
  rw [hlen] at hsame
  rw [hsourceFold, ← htargetFold, ← htype] at hsame
  exact hsame

theorem LoweredConstructorMapping.reopens
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hsource : source.type.FVarsIn fun _ => False) :
    LoweredConstructorReopening env params nparams finalResult restoreAs source
      state out := by
  refine ⟨H.name, ?_⟩
  rcases H.mapped with
    ⟨lctx, tail, As, lowered, openedState, Hopening, _hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hmapping, htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun fv hfalse => False.elim hfalse)
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize,
    Hmapping.reopens hresultParams fvars hparams hnodup Hselection Htail,
    htype⟩

/-- Opening the lowered constructor with restoration's fresh parameters
produces the lowering body renamed from its original parameter selection to
the concrete restoration array. -/
theorem LoweredConstructorReopening.restoreTail
    (H : LoweredConstructorReopening env params nparams finalResult targetAs
      source state out)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (restoredTail : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs restoredTail) :
    ∃ lctx tail As lowered openedState,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧
        openedState.newTypes = state.newTypes ∧
        openedState.nestedAux = state.nestedAux ∧
        openedState.nextIdx = state.nextIdx ∧
        As.size = nparams ∧
        NestedExprReopening env lctx params As finalResult targetAs tail
          openedState (lowered, out.2) ∧
        out.1.type = lctx.mkForall As lowered ∧
        restoredTail = (lowered.abstract As).instantiateRev restoreAs := by
  rcases H.reopened with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening, htype⟩
  have Htelescope := Hselection.forallTelescope lowered
  rw [hsize, ← htype] at Htelescope
  have htail := Hrestore.forallResidual Htelescope
  have habstract : lowered.abstract As =
      lowered.abstractList Hselection.fvars :=
    calc
      lowered.abstract As = lowered.abstract
          (Hselection.fvars.map Expr.fvar).toArray :=
        congrArg lowered.abstract Hselection.expressions
      _ = lowered.abstractList Hselection.fvars :=
        Expr.abstract_eq lowered Hselection.fvars
  refine ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening, htype,
    ?_⟩
  simpa [habstract] using htail

/-- The body exposed by restoration is the original constructor body with
the restoration parameters substituted for lowering's fresh parameters.
This is the constructor-scoped inverse theorem: it combines the exact two
telescope traversals with the structural inverse for nested replacement. -/
theorem LoweredConstructorReopening.restoreTail_inverse
    (H : LoweredConstructorReopening env params nparams finalResult targetAs
      source state out)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (restoredTail : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs restoredTail)
    (restoreEnv : Environment)
    (htargetAs : targetAs = restoreAs)
    (hresultNParams : finalResult.nparams = nparams)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv source.type) :
    ∃ lctx tail As lowered openedState,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧
        openedState.newTypes = state.newTypes ∧
        openedState.nestedAux = state.nestedAux ∧
        openedState.nextIdx = state.nextIdx ∧
        As.size = nparams ∧
        NestedExprReopening env lctx params As finalResult targetAs tail
          openedState (lowered, out.2) ∧
        out.1.type = lctx.mkForall As lowered ∧
        restoredTail = (lowered.abstract As).instantiateRev restoreAs ∧
        ((restoredTail.replace
            (finalResult.restoreNestedNode restoreEnv restoreAs {})) ==
          Expr.reopenParams tail As restoreAs) = true := by
  rcases H.restoreTail restoreLctx restoreAs restoredTail Hrestore with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening,
      htype, hrestoredTail⟩
  rcases Hrestore.params_fvars_extension with
    ⟨restoreFvars, hrestoreList, hrestoreLength⟩
  have hrestoreArray :
      restoreAs = (restoreFvars.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa using hrestoreList
  have hselectionLength : Hselection.fvars.length = As.size := by
    simpa using (congrArg Array.size Hselection.expressions).symm
  have hrestoreSize :
      restoreFvars.length = Hselection.fvars.length := by
    rw [hrestoreLength, hselectionLength, hsize]
  have hresultSize : finalResult.nparams = As.size := by
    rw [hresultNParams, hsize]
  have HtailSource : RestoreSourceDisjoint finalResult restoreEnv tail :=
    Hopening.tailRestoreSourceDisjoint Hsource
  have hinverse := Hreopening.restore_eqv restoreEnv Hselection hnodupAs
    restoreFvars
    (by simpa [htargetAs] using hrestoreArray) hrestoreSize hresultSize
    HtailSource 0
  have hloweredOpen := Expr.reopenFVarsAt_eq_reopenParams hnodupAs
    hrestoreSize Hselection.expressions hrestoreArray lowered 0
  have hsourceOpen := Expr.reopenFVarsAt_eq_reopenParams hnodupAs
    hrestoreSize Hselection.expressions hrestoreArray tail 0
  have hrestoredOpen :
      restoredTail = Expr.reopenParams lowered As restoreAs := by
    simpa [Expr.reopenParams] using hrestoredTail
  rw [htargetAs, hloweredOpen, hsourceOpen, ← hrestoredOpen] at hinverse
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreopening,
    htype, hrestoredTail, hinverse⟩

/-- Operational constructor restoration consumes a mapped lowering body and
produces the correspondingly renamed source body.  Unlike
`restoreTail_inverse`, this theorem starts from the mapping certificate
available before restoration chooses its fresh variables and concludes about
the `restoredBody` retained by `NestedRestoration`. -/
theorem LoweredConstructorMapping.restoredBody_inverse
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (openedBody restoredBody : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs openedBody)
    (restoreEnv : Environment)
    (Hbody : ExprReplacement
      (finalResult.restoreNestedNode restoreEnv restoreAs {}) openedBody
        restoredBody)
    (hresultNParams : finalResult.nparams = nparams)
    (Hsource : RestoreSourceDisjoint finalResult restoreEnv source.type) :
    ∃ lctx tail As,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧ As.size = nparams ∧
        (restoredBody == Expr.reopenParams tail As restoreAs) = true := by
  have Hreopening : LoweredConstructorReopening env params nparams finalResult
      restoreAs source state out :=
    H.reopens hresultParams paramFvars hparams hnodup HsourceClosed
  rcases Hreopening.restoreTail_inverse restoreLctx restoreAs openedBody
      Hrestore restoreEnv rfl hresultNParams Hsource with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hselection,
      hnodupAs, _hopenedTypes, _hopenedAux, _hopenedNext, hsize,
      _Hreopening, _htype, _hopenedBody, hinverse⟩
  have hrestoredInverse :
      (restoredBody == Expr.reopenParams tail As restoreAs) = true := by
    rw [Hbody.eq_replace]
    exact hinverse
  exact ⟨lctx, tail, As, Hopening, Hselection, hnodupAs, hsize,
    hrestoredInverse⟩

theorem LoweredConstructorMapping.restoredBody_inverseOfSyntax
    (H : LoweredConstructorMapping env params nparams finalResult source state
      out)
    (hresultParams : finalResult.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved finalResult restoreEnv)
    (restoreLctx : LocalContext) (restoreAs : Array Expr)
    (openedBody restoredBody : Expr)
    (Hrestore : RestoreParamOpening {} #[] out.1.type nparams restoreLctx
      restoreAs openedBody)
    (Hbody : ExprReplacement
      (finalResult.restoreNestedNode restoreEnv restoreAs {}) openedBody
        restoredBody)
    (hresultNParams : finalResult.nparams = nparams) :
    ∃ lctx tail As,
      NestedParamOpening {} #[] source.type nparams lctx tail As ∧
      ∃ Hselection : LocalForallSelection lctx As,
        Hselection.fvars.Nodup ∧ As.size = nparams ∧
        (restoredBody == Expr.reopenParams tail As restoreAs) = true :=
  H.restoredBody_inverse hresultParams paramFvars hparams hnodup
    Hsyntax.closed restoreLctx restoreAs openedBody restoredBody Hrestore
    restoreEnv Hbody hresultNParams
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved)

/-- A whole operational `NestedRestoration` of a lowered constructor, with
its restored body related back to the independently checked source
constructor body.  The outer telescope equations are retained explicitly;
the next abstraction layer can therefore prove alpha-equivalence without
replaying either executable traversal. -/
structure ConstructorRestorationBodyInverse
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (nparams : Nat) (source lowered : Constructor) (restoredType : Expr) where
  restoreLctx : LocalContext
  restoreAs : Array Expr
  openedBody : Expr
  restoredBody : Expr
  loweredOpening : RestoreParamOpening {} #[] lowered.type nparams
    restoreLctx restoreAs openedBody
  restoreLctxWF : restoreLctx.WF
  restoreSelection : LocalForallSelection restoreLctx restoreAs
  restoreNodup : restoreSelection.fvars.Nodup
  bodyRestoration : ExprReplacement
    (result.restoreNestedNode env restoreAs {}) openedBody restoredBody
  output : restoredType = if lowered.type.isForall then
    restoreLctx.mkForall restoreAs restoredBody
    else restoreLctx.mkLambda restoreAs restoredBody
  sourceLctx : LocalContext
  sourceTail : Expr
  sourceAs : Array Expr
  sourceClosed : source.type.FVarsIn fun _ => False
  loweredFVarIdsClosed : lowered.type.FVarIdsIn fun _ => False
  sourceLoweredPrefix :
    Expr.SameForallPrefix nparams source.type lowered.type
  sourceOpening : NestedParamOpening {} #[] source.type nparams sourceLctx
    sourceTail sourceAs
  sourceSelection : LocalForallSelection sourceLctx sourceAs
  sourceNodup : sourceSelection.fvars.Nodup
  sourceArity : sourceAs.size = nparams
  bodyInverse :
    (restoredBody == Expr.reopenParams sourceTail sourceAs restoreAs) = true

/-- Whole-constructor restoration inverse stated at its semantic boundary.
This form does not assume any naming convention for generated auxiliary
constructors; callers may establish source disjointness from typing and
freshness instead. -/
theorem LoweredConstructorMapping.nestedRestoration_inverse
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : NestedRestoration result restoreEnv {} out.1.type
      restoredType) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 restoredType) := by
  rcases Hrestored with
    ⟨restoreLctx, restoreAs, openedBody, restoredBody, Hopening,
      Hbody, houtput⟩
  rcases Hopening.2 with ⟨hrestoreLctxWF, HrestoreSelection,
    hrestoreNodup⟩
  have Hopening' := Hopening.1
  rw [hresultNParams] at Hopening'
  rcases H.restoredBody_inverse hresultParams paramFvars hparams hnodup
      HsourceClosed restoreLctx restoreAs openedBody restoredBody Hopening'
      restoreEnv Hbody hresultNParams HsourceDisjoint with
    ⟨sourceLctx, sourceTail, sourceAs, HsourceOpening, Hselection,
      hsourceNodup, hsourceArity, hinverse⟩
  exact ⟨{
    restoreLctx := restoreLctx
    restoreAs := restoreAs
    openedBody := openedBody
    restoredBody := restoredBody
    loweredOpening := Hopening'
    restoreLctxWF := hrestoreLctxWF
    restoreSelection := HrestoreSelection
    restoreNodup := hrestoreNodup
    bodyRestoration := Hbody
    output := houtput
    sourceLctx := sourceLctx
    sourceTail := sourceTail
    sourceAs := sourceAs
    sourceClosed := HsourceClosed
    loweredFVarIdsClosed := H.targetFVarIdsClosed HsourceClosed
    sourceLoweredPrefix := H.sourceTargetSameForallPrefix HsourceClosed
    sourceOpening := HsourceOpening
    sourceSelection := Hselection
    sourceNodup := hsourceNodup
    sourceArity := hsourceArity
    bodyInverse := hinverse }⟩

theorem LoweredConstructorMapping.nestedRestoration_inverseOfSyntax
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved result restoreEnv)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : NestedRestoration result restoreEnv {} out.1.type
      restoredType) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 restoredType) := by
  exact H.nestedRestoration_inverse hresultParams paramFvars hparams hnodup
    Hsyntax.closed restoreEnv
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved) hresultNParams
    Hrestored

/-- Eliminate the source-opening free variables from the body inverse.  The
restored body is the ordinary residual of the original constructor telescope,
instantiated only with restoration's fresh parameter array. -/
theorem ConstructorRestorationBodyInverse.restoredBody_residual
    (H : ConstructorRestorationBodyInverse result env nparams source lowered
      restoredType) :
    ∃ residual,
      Expr.ForallTelescope source.type nparams residual ∧
      (H.restoredBody == residual.instantiateRev H.restoreAs) = true := by
  rcases H.sourceOpening.forallTelescope with ⟨residual, Htelescope⟩
  have htail : H.sourceTail = residual.instantiateRev H.sourceAs :=
    H.sourceOpening.toRestoreParamOpening.forallResidual Htelescope
  have hfree : residual.FVarsIn
      (fun fv => fv ∉ H.sourceSelection.fvars) :=
    (Htelescope.resultFVarsIn H.sourceClosed).mono fun fv hfalse =>
      False.elim hfalse
  have hcancel := hfree.reabstract_instantiateRev_fvarArray H.sourceAs
    H.restoreAs H.sourceSelection.fvars H.sourceSelection.expressions
    H.sourceNodup
  have hopen : Expr.reopenParams H.sourceTail H.sourceAs H.restoreAs =
      residual.instantiateRev H.restoreAs := by
    rw [htail]
    simpa [Expr.reopenParams] using hcancel
  have hinverse := H.bodyInverse
  rw [hopen] at hinverse
  exact ⟨residual, Htelescope, hinverse⟩

/-- Whole-constructor inverse: rebuilding the restored body under the copied
parameter telescope yields a constructor type equivalent to the independent
source constructor type. -/
theorem ConstructorRestorationBodyInverse.restoredType_eqv_source
    (H : ConstructorRestorationBodyInverse result env nparams source lowered
      restoredType) :
    (restoredType == source.type) = true := by
  rcases H.sourceLoweredPrefix.transferRestoreOpening H.loweredOpening with
    ⟨sourceOpened, HsourceRestore⟩
  rcases H.restoredBody_residual with
    ⟨residual, Htelescope, hbodyResidual⟩
  have hsourceOpened :
      sourceOpened = residual.instantiateRev H.restoreAs :=
    HsourceRestore.forallResidual Htelescope
  have hbodyOpened : (H.restoredBody == sourceOpened) = true := by
    rw [hsourceOpened]
    exact hbodyResidual
  have hclosedSource : source.type.FVarIdsIn fun _ => False :=
    FVarsIn_to_FVarIdsIn H.sourceClosed
  have hsourceRebuild :
      H.restoreLctx.mkForall H.restoreAs sourceOpened = source.type :=
    HsourceRestore.root_mkForall_tail H.restoreLctxWF Htelescope hclosedSource
  have hwrapped := H.restoreSelection.mkForall_eqv H.restoreNodup hbodyOpened
  rw [hsourceRebuild] at hwrapped
  have houtput : restoredType =
      H.restoreLctx.mkForall H.restoreAs H.restoredBody := by
    refine H.output.trans ?_
    by_cases hzero : nparams = 0
    · have hsize : H.restoreAs.size = 0 :=
        H.loweredOpening.initial_size.trans hzero
      have hempty : H.restoreAs = #[] :=
        Array.eq_empty_of_size_eq_zero hsize
      rw [hempty]
      split
      · rfl
      · rw [LocalContext.mkForall, LocalContext.mkLambda]
        rw [show (#[] : Array Expr) =
            (([] : List FVarId).map Expr.fvar).toArray from rfl,
          LocalContext.mkBinding_eq, LocalContext.mkBinding_eq]
        simp only [LocalContext.mkBindingList_nil]
    · have hpos : 0 < nparams := Nat.pos_of_ne_zero hzero
      have hisForall :=
        H.sourceLoweredPrefix.target_isForall_of_pos hpos
      simp [hisForall]
  rw [houtput]
  exact hwrapped

/-- Metadata-facing form of the constructor inverse.  Installation exposes a
`ConstructorVal`, while lowering is indexed by the corresponding
`Constructor`; the explicit type equality is the only alignment fact needed
to connect the two verified traces. -/
theorem LoweredConstructorMapping.constructorRestoration_inverse
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 newInfo.type) := by
  apply H.nestedRestoration_inverse hresultParams paramFvars hparams hnodup
    HsourceClosed restoreEnv HsourceDisjoint hresultNParams
  simpa [htype] using Hrestored.type

theorem LoweredConstructorMapping.constructorRestoration_inverseOfSyntax
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved result restoreEnv)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type) :
    Nonempty (ConstructorRestorationBodyInverse result restoreEnv nparams source
      out.1 newInfo.type) := by
  apply H.nestedRestoration_inverseOfSyntax hresultParams paramFvars hparams
    hnodup Hsyntax restoreEnv Hreserved hresultNParams
  simpa [htype] using Hrestored.type

/-- Transport source translation across constructor restoration using exact
semantic disjointness, without imposing a namespace convention on generated
constructor names. -/
theorem LoweredConstructorMapping.restoredType_translation
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type)
    (Hsource : TrExprS venv oldInfo.levelParams [] source.type targetType) :
    TrExprS venv oldInfo.levelParams [] newInfo.type targetType := by
  rcases H.constructorRestoration_inverse hresultParams paramFvars hparams
      hnodup HsourceClosed restoreEnv HsourceDisjoint hresultNParams Hrestored
      htype with
    ⟨Hinverse⟩
  apply Hsource.eqv
  simpa [beq_comm] using Hinverse.restoredType_eqv_source

/-- Transport a source constructor's abstract translation across lowering and
restoration.  This is the semantic premise needed by constructor installation;
unlike translation of the lowered constructor, it is obtained from the
independent pre-lowering source type. -/
theorem LoweredConstructorMapping.restoredType_translationOfSyntax
    (H : LoweredConstructorMapping env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (restoreEnv : Environment)
    (Hreserved : RestoreNamesReserved result restoreEnv)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type)
    (Hsource : TrExprS venv oldInfo.levelParams [] source.type targetType) :
    TrExprS venv oldInfo.levelParams [] newInfo.type targetType := by
  exact H.restoredType_translation hresultParams paramFvars hparams hnodup
    Hsyntax.closed restoreEnv
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved) hresultNParams
    Hrestored htype Hsource

/-- Install a restored constructor from its independent source translation
and exact semantic disjointness from the generated auxiliary declarations. -/
theorem RestoredConstructorStep.installationOfDisjoint
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (HsourceDisjoint : RestoreSourceDisjoint result loweredEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (Huvars : Hstep.oldInfo.levelParams.length = constructor.uvars)
    (Hname : Hstep.oldInfo.name = constructor.name)
    (Hsource : TrExprS sourceVEnv Hstep.oldInfo.levelParams [] source.type
      constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfMetadata Hvalid constructor Hsafety Huvars Hname
  · exact Hmapping.restoredType_translation hresultParams paramFvars
      hparams hnodup HsourceClosed loweredEnv HsourceDisjoint hresultNParams
      Hstep.restored.restoration htype Hsource
  · exact Hwf

/-- Source-declaration specialization of `installationOfDisjoint`.  A single
`TrSourceConst` supplies the abstract constructor used both by the source
`TrInductDeclCore` and by the exact restored installation trace. -/
theorem RestoredConstructorStep.installationOfSource
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (HsourceDisjoint : RestoreSourceDisjoint result loweredEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (hlevels : Hstep.oldInfo.levelParams = lparams)
    (hname : Hstep.oldInfo.name = source.name)
    (Hsource : TrSourceConst sourceVEnv lparams source.name source.type
      constructor) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfDisjoint Hmapping hresultParams paramFvars hparams
    hnodup HsourceClosed HsourceDisjoint hresultNParams htype Hvalid
    constructor Hsafety
  · rw [hlevels]
    exact Hsource.uvars.symm
  · exact hname.trans Hsource.name.symm
  · simpa [hlevels] using Hsource.type
  · exact Hsource.wf

/-- Preferred source-syntax installation endpoint. Auxiliary family names are
reserved by the lowering cache, while auxiliary constructor names need only
be fresh in the abstract source environment; no constructor namespace
convention is assumed. -/
theorem RestoredConstructorStep.installationOfFresh
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv sourceVEnv)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (Huvars : Hstep.oldInfo.levelParams.length = constructor.uvars)
    (Hname : Hstep.oldInfo.name = constructor.name)
    (Hsource : TrExprS sourceVEnv Hstep.oldInfo.levelParams [] source.type
      constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfDisjoint Hmapping hresultParams paramFvars hparams
    hnodup Hsyntax.closed
  · exact Hsyntax.noNestedAux.restoreSourceDisjointOfFresh
      Hsource.constantsDefined Hfamilies Hconstructors
  · exact hresultNParams
  · exact htype
  · exact Hvalid
  · exact Hsafety
  · exact Huvars
  · exact Hname
  · exact Hsource
  · exact Hwf

/-- Preferred end-to-end constructor endpoint.  Fresh-cache lowering gives
the semantic restoration disjointness, while the independent source
translation is reused unchanged by declaration formation and installation. -/
theorem RestoredConstructorStep.installationOfFreshSource
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv sourceVEnv)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
    (hlevels : Hstep.oldInfo.levelParams = lparams)
    (hname : Hstep.oldInfo.name = source.name)
    (Hsource : TrSourceConst sourceVEnv lparams source.name source.type
      constructor) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfSource Hmapping hresultParams paramFvars hparams
    hnodup Hsyntax.closed
  · exact Hsyntax.noNestedAux.restoreSourceDisjointOfFresh
      Hsource.type.constantsDefined Hfamilies Hconstructors
  · exact hresultNParams
  · exact htype
  · exact Hvalid
  · exact Hsafety
  · exact hlevels
  · exact hname
  · exact Hsource

/-- Namespace-based convenience specialization of
`installationOfDisjoint`.  The semantic endpoint above is the preferred path
for arbitrary kernel constructor names. -/
theorem RestoredConstructorStep.installationOfSyntax
    (Hstep : RestoredConstructorStep result loweredEnv ctorName
      sourceProdEnv targetProdEnv)
    (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
      source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (Hsyntax : SourceConstructorSyntax source)
    (Hreserved : RestoreNamesReserved result loweredEnv)
    (hresultNParams : result.nparams = nparams)
    (htype : Hstep.oldInfo.type = out.1.type)
    (Hvalid : CheckingEnv safety sourceProdEnv sourceVEnv)
    (constructor : VConstVal)
    (Hold : TrConstVal safety sourceVEnv
      (.ctorInfo Hstep.oldInfo) constructor)
    (Hsource : TrExprS sourceVEnv Hstep.oldInfo.levelParams [] source.type
      constructor.type)
    (Hwf : constructor.toVConstant.WF sourceVEnv) :
    ∃ targetVEnv,
      Nonempty (RestoredConstructorInstallationSemantics safety Hstep
        sourceVEnv targetVEnv) := by
  apply Hstep.installationOfDisjoint Hmapping hresultParams paramFvars hparams
    hnodup Hsyntax.closed
    (Hsyntax.noNestedAux.restoreSourceDisjoint Hreserved) hresultNParams htype
    Hvalid constructor
  · exact Hold.1.1
  · simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal] using
      Hold.1.2.1
  · simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using Hold.2
  · exact Hsource
  · exact Hwf

theorem LoweredConstructorTranslation.finalMapping
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    LoweredConstructorMapping env params nparams finalResult source state out := by
  refine ⟨H.name, ?_⟩
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
      hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize, Hreplace, htype⟩
  exact ⟨lctx, tail, As, lowered, openedState, Hopening, hlctxWF, Hselection,
    hnodupAs, hopenedTypes, hopenedAux, hopenedNext, hsize,
    Hreplace.finalMapping Hlater Hmap, htype⟩

theorem ElimNestedInductive.lowerConstructor.translation
    (params : Array Expr) (nparams : Nat) (ctor : Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams ctor
      env state).WF fun out =>
        LoweredConstructorTranslation env params nparams ctor state out := by
  unfold Lean4Lean.ElimNestedInductive.lowerConstructor
  apply ElimNestedInductive.withParams.refinesSelected
  intro lctx tail As openedState Hopening Hctx Hselection hnodup hopenedTypes
    hopenedAux hopenedNext
  have hsize : As.size = nparams := Hopening.initial_size
  simp only [hsize, beq_self_eq_true, if_true]
  have hsubst : As.size = params.size := by omega
  refine nestedBind.WF
    (replaceAllNested_refines env lctx params As tail openedState
      hsubst hclosures) ?_
  intro lowered outState Hlowered
  exact Except.WF.pure
    ⟨rfl, lctx, tail, As, lowered, openedState, Hopening, Hctx.wf, Hselection,
      hnodup, hopenedTypes, hopenedAux, hopenedNext, hsize, Hlowered, rfl⟩

theorem ElimNestedInductive.lowerConstructor.translationPending
    (params : Array Expr) (nparams : Nat) (ctor : Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hctor : ctor.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams ctor
      env state).WF fun out =>
        LoweredConstructorTranslation env params nparams ctor state out ∧
        PendingNewTypesClosed cursor out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerConstructor
  apply ElimNestedInductive.withParams.refinesClosing (Htype := Hctor)
  intro lctx tail As openedState Hopening Hclosing Htail hopenedTypes
    hopenedAux hopenedNext
  have hsize : As.size = nparams := Hopening.initial_size
  simp only [hsize, beq_self_eq_true, if_true]
  have hsubst : As.size = params.size := by omega
  refine nestedBind.WF
    (replaceAllNested_refines env lctx params As tail openedState
      hsubst hclosures) ?_
  intro lowered outState Hlowered
  have HopenedPending : PendingNewTypesClosed cursor openedState := by
    intro j hcursor hj
    have hjState : j < state.newTypes.size := by
      simpa [hopenedTypes] using hj
    have hvalue : openedState.newTypes[j] = state.newTypes[j] := by
      have heq := congrArg
        (fun xs : Array InductiveType => xs[j]!) hopenedTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hj, hjState] using heq
    rw [hvalue]
    exact Hstate j hcursor hjState
  exact Except.WF.pure ⟨
    ⟨rfl, lctx, tail, As, lowered, openedState, Hopening,
      Hclosing.binding.wf, Hclosing.selection, Hclosing.nodup,
      hopenedTypes, hopenedAux, hopenedNext, hsize,
      Hlowered, rfl⟩,
    Hlowered.pendingNewTypesClosed Henv Hclosing Htail HopenedPending⟩

/-- Stateful positional correspondence for an entire constructor list. -/
inductive LoweredConstructorTranslations
    (env : Environment) (params : Array Expr) (nparams : Nat) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : LoweredConstructorTranslations env params nparams [] state ([], state)
  | cons : LoweredConstructorTranslation env params nparams source state step →
      LoweredConstructorTranslations env params nparams sources step.2 out →
      LoweredConstructorTranslations env params nparams (source :: sources)
        state (step.1 :: out.1, out.2)

theorem LoweredConstructorTranslations.newTypesLE
    (H : LoweredConstructorTranslations env params nparams sources state out) :
    NestedNewTypesLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hhead Htail ih => exact Hhead.newTypesLE.trans ih

theorem LoweredConstructorTranslations.nestedAuxLE
    (H : LoweredConstructorTranslations env params nparams sources state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | nil => exact .refl _
  | cons Hhead Htail ih => exact Hhead.nestedAuxLE.trans ih

theorem LoweredConstructorTranslations.namesWF
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih => exact ih (Hhead.namesWF Hindex Hstate)

theorem LoweredConstructorTranslations.namesFresh
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih => exact ih (Hhead.namesFresh Hstate)

theorem LoweredConstructorTranslations.auxFVarsIn
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  induction H with
  | nil => exact Hstate
  | cons Hhead Htail ih =>
    apply ih
    · intro source hsource
      exact Hsources source (by simp [hsource])
    · exact Hhead.auxFVarsIn (Hsources _ (by simp)) Hparams Hstate

inductive LoweredConstructorMappings
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : LoweredConstructorMappings env params nparams finalResult [] state
      ([], state)
  | cons : LoweredConstructorMapping env params nparams finalResult source
      state step →
      LoweredConstructorMappings env params nparams finalResult sources step.2
        out →
      LoweredConstructorMappings env params nparams finalResult
        (source :: sources) state (step.1 :: out.1, out.2)

theorem LoweredConstructorMappings.length
    (H : LoweredConstructorMappings env params nparams finalResult sources
      state out) : out.1.length = sources.length := by
  induction H with
  | nil => rfl
  | cons Hhead Htail ih => simp [ih]

/-- Positional projection of the state-threaded constructor mapping.  Both
the source and target list lookups are retained, so subsequent restoration
folds can align their metadata without a name-based uniqueness assumption. -/
theorem LoweredConstructorMappings.mappingAt
    (H : LoweredConstructorMappings env params nparams finalResult sources
      state out) (i : Nat) (hi : i < sources.length) :
    ∃ source target before after,
      sources[i]? = some source ∧
      out.1[i]? = some target ∧
      LoweredConstructorMapping env params nparams finalResult source before
        (target, after) := by
  induction H generalizing i with
  | nil => simp at hi
  | @cons source state step sources out Hhead Htail ih =>
    cases i with
    | zero => exact ⟨source, step.1, state, step.2, by simp, by simp, Hhead⟩
    | succ i =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      rcases ih i hi with
        ⟨tailSource, tailTarget, before, after, hsource, htarget, Hmapping⟩
      exact ⟨tailSource, tailTarget, before, after, by simpa, by simpa,
        Hmapping⟩

/-- Lockstep alignment of the state-threaded constructor lowering relation
with the exact operational restoration fold.  The production lookup theorem
has already identified the `oldInfo.type` read at every step with that step's
positionally corresponding lowered constructor type. -/
inductive RestoredConstructorMappingTrace
    (result : Lean4Lean.ElimNestedInductive.Result)
    (mappingEnv loweredEnv : Environment) (params : Array Expr)
    (nparams : Nat) (safety : DefinitionSafety) (lparams : List Name) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor → Lean4Lean.ElimNestedInductive.State →
      Environment → Environment → Prop
  | nil (state : Lean4Lean.ElimNestedInductive.State)
      (sourceProdEnv : Environment) :
      RestoredConstructorMappingTrace result mappingEnv loweredEnv params
        nparams safety lparams [] state [] state sourceProdEnv sourceProdEnv
  | cons
      (Hmapping : LoweredConstructorMapping mappingEnv params nparams result
        source state (target, nextState))
      (Hstep : RestoredConstructorStep result loweredEnv target.name
        sourceProdEnv middleProdEnv)
      (hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
      (hlevels : Hstep.oldInfo.levelParams = lparams)
      (hname : Hstep.oldInfo.name = target.name)
      (htype : Hstep.oldInfo.type = target.type)
      (Hrest : RestoredConstructorMappingTrace result mappingEnv loweredEnv params
        nparams safety lparams sources nextState targets finalState
          middleProdEnv targetProdEnv) :
      RestoredConstructorMappingTrace result mappingEnv loweredEnv params nparams
        safety lparams (source :: sources) state (target :: targets) finalState
          sourceProdEnv targetProdEnv

/-- Build the lockstep constructor trace from verified lowered installation.
The only list premise is that all mapped targets belong to the installed
owner; in the family specialization this is immediate because `targets` is
that owner's constructor list. -/
theorem RestoredConstructorMappingTrace.ofInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hprod : RecursorPhasesResult R loweredEnv)
    (howner : owner ∈ indTypes.toList)
    (Hmapping : LoweredConstructorMappings mappingEnv params nparams result
      sources state (targets, finalState))
    (Htrace : StateForMTrace (RestoredConstructorStep result loweredEnv)
      (targets.map (fun ctor => ctor.name)) sourceProdEnv targetProdEnv)
    (Htargets : ∀ target ∈ targets, target ∈ owner.ctors) :
    RestoredConstructorMappingTrace result mappingEnv loweredEnv params nparams
      c.safety c.lparams sources state targets finalState sourceProdEnv
        targetProdEnv := by
  cases Hmapping with
  | nil =>
    cases Htrace
    exact .nil _ _
  | cons Hhead Htail =>
    cases Htrace with
    | cons Hstep Hsteps =>
      have Hmetadata := Hstep.metadataOfInstalled Hprod howner
        (Htargets _ (by simp)) rfl
      apply RestoredConstructorMappingTrace.cons Hhead Hstep
      · exact Hmetadata.1
      · exact Hmetadata.2.1
      · exact Hmetadata.2.2
      · exact Hstep.oldType_eq_ofInstalled Hprod howner
          (Htargets _ (by simp)) rfl
      · apply RestoredConstructorMappingTrace.ofInstalled Hprod howner
          Htail Hsteps
        intro target htarget
        exact Htargets target (by simp [htarget])

/-- Interpret the proof-independent lowering/restoration trace against the
independently translated source constructors.  This is the constructor-list
implementation/specification bridge: every executable restoration step is
shown to translate the same abstract constructor that appears in the source
inductive specification. -/
theorem RestoredConstructorMappingTrace.sourceSemantics
    (H : RestoredConstructorMappingTrace result mappingEnv loweredEnv params
      nparams safety lparams sources state targets finalState sourceProdEnv
        targetProdEnv)
    (Hsources : List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv lparams source.name source.type constructor)
      sources constructors)
    (Hsyntax : SourceConstructorSyntaxes sources)
    (Hdisjoint : ∀ source ∈ sources,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (hresultNParams : result.nparams = nparams) :
    RestoredSourceConstructorTrace lparams safety canonicalEnv
      (targets.map (fun ctor => ctor.name)) sourceProdEnv targetProdEnv
        sources constructors := by
  induction H generalizing constructors with
  | nil =>
    cases Hsources
    exact .nil _
  | @cons source state target nextState sourceProdEnv middleProdEnv sources
      finalState targets targetProdEnv Hmapping Hstep hsafety hlevels hname
      htype Hrest ih =>
    cases Hsources with
    | cons Hsource Hsources =>
      rename_i vctor vconstructors
      cases Hsyntax with
      | cons HsourceSyntax Hsyntax =>
        have HsourceType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            source.type vctor.type := by
          simpa [hlevels] using Hsource.type
        have HrestoredType : TrExprS canonicalEnv Hstep.oldInfo.levelParams []
            Hstep.restored.newInfo.type vctor.type :=
          Hmapping.restoredType_translation hresultParams paramFvars hparams
            hnodup HsourceSyntax.closed loweredEnv
            (Hdisjoint source (by simp)) hresultNParams
            Hstep.restored.restoration htype HsourceType
        have Htranslated : TrConstVal safety canonicalEnv
            (.ctorInfo Hstep.restored.newInfo) vctor :=
          Hstep.restored.restoration.translatedOfMetadata hsafety (by
            rw [hlevels]
            exact Hsource.uvars.symm) (by
            exact (hname.trans Hmapping.name).trans Hsource.name.symm)
            HrestoredType
        apply RestoredSourceConstructorTrace.cons Hstep
          { constructor := vctor
            sourceTranslation := Hsource
            restoredTranslation := Htranslated }
        apply ih Hsources Hsyntax
        intro tail htail
        exact Hdisjoint tail (by simp [htail])

inductive LoweredConstructorReopenings
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor × Lean4Lean.ElimNestedInductive.State → Prop
  | nil : LoweredConstructorReopenings env params nparams finalResult restoreAs
      [] state ([], state)
  | cons : LoweredConstructorReopening env params nparams finalResult restoreAs
      source state step →
      LoweredConstructorReopenings env params nparams finalResult restoreAs
        sources step.2 out →
      LoweredConstructorReopenings env params nparams finalResult restoreAs
        (source :: sources) state (step.1 :: out.1, out.2)

theorem LoweredConstructorMappings.reopens
    (H : LoweredConstructorMappings env params nparams finalResult sources
      state out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False) :
    LoweredConstructorReopenings env params nparams finalResult restoreAs
      sources state out := by
  induction H with
  | nil => exact .nil
  | cons Hhead Htail ih =>
    apply LoweredConstructorReopenings.cons
    · exact Hhead.reopens hresultParams fvars hparams hnodup
        (Hsources _ (by simp))
    · apply ih
      intro source hsource
      exact Hsources source (by simp [hsource])

theorem LoweredConstructorTranslations.finalMapping
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    LoweredConstructorMappings env params nparams finalResult sources state out := by
  induction H generalizing finalState with
  | nil => exact .nil
  | cons Hhead Htail ih =>
    exact .cons
      (Hhead.finalMapping (Htail.nestedAuxLE.trans Hlater) Hmap)
      (ih Hlater Hmap)

theorem LoweredConstructorTranslations.targetsRestoreTelescope
    (H : LoweredConstructorTranslations env params nparams sources state out) :
    ∀ ctor ∈ out.1, RestoreTelescope ctor.type nparams := by
  induction H with
  | nil => simp
  | cons Hhead Htail ih =>
    intro ctor hctor
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | htail
    · exact Hhead.targetRestoreTelescope
    · exact ih ctor htail

theorem ElimNestedInductive.lowerConstructors.translations
    (params : Array Expr) (nparams : Nat) (ctors : List Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (ctors.mapM (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams)
      env state).WF fun out =>
        LoweredConstructorTranslations env params nparams ctors state out := by
  induction ctors generalizing state with
  | nil => exact Except.WF.pure .nil
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine nestedBind.WF
      (ElimNestedInductive.lowerConstructor.translation params nparams ctor
        env state hparams hclosures) ?_
    intro lowered nextState Hlowered
    refine nestedBind.WF (ih nextState) ?_
    intro loweredTail finalState Htail
    exact Except.WF.pure (.cons Hlowered Htail)

theorem ElimNestedInductive.lowerConstructors.translationsPending
    (params : Array Expr) (nparams : Nat) (ctors : List Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hctors : ∀ ctor ∈ ctors, ctor.type.FVarsIn fun _ => False)
    (Hstate : PendingNewTypesClosed cursor state) :
    (ctors.mapM (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams)
      env state).WF fun out =>
        LoweredConstructorTranslations env params nparams ctors state out ∧
        PendingNewTypesClosed cursor out.2 := by
  induction ctors generalizing state with
  | nil => exact Except.WF.pure ⟨.nil, Hstate⟩
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine nestedBind.WF
      (ElimNestedInductive.lowerConstructor.translationPending params nparams
        ctor env state hparams hclosures Henv (Hctors ctor (by simp)) Hstate) ?_
    intro lowered nextState Hlowered
    refine nestedBind.WF (ih nextState
      (fun tail htail => Hctors tail (by simp [htail])) Hlowered.2) ?_
    intro loweredTail finalState Htail
    exact Except.WF.pure ⟨.cons Hlowered.1 Htail.1, Htail.2⟩

theorem ElimNestedInductive.lowerConstructors.shapes
    (params : Array Expr) (nparams : Nat) (ctors : List Constructor)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (ctors.mapM
      (Lean4Lean.ElimNestedInductive.lowerConstructor params nparams)
      env state).WF fun out =>
        LoweredConstructorShapes nparams ctors out.1 := by
  induction ctors generalizing state with
  | nil => exact Except.WF.pure .nil
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    refine nestedBind.WF
      (ElimNestedInductive.lowerConstructor.shape
        params nparams ctor env state) ?_
    intro lowered nextState Hlowered
    refine nestedBind.WF (ih nextState) ?_
    intro loweredTail finalState Htail
    exact Except.WF.pure (.cons Hlowered Htail)

/-- Family-level lowering preserves the family header verbatim and changes
only its positionally corresponding constructor types. -/
structure LoweredInductiveShape
    (nparams : Nat) (source target : InductiveType) : Prop where
  name : target.name = source.name
  type : target.type = source.type
  constructors : LoweredConstructorShapes nparams source.ctors target.ctors

theorem ElimNestedInductive.lowerInductive.shape
    (params : Array Expr) (nparams : Nat) (indType : InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.lowerInductive params nparams indType
      env state).WF fun out => LoweredInductiveShape nparams indType out.1 := by
  unfold Lean4Lean.ElimNestedInductive.lowerInductive
  refine nestedBind.WF
    (ElimNestedInductive.lowerConstructors.shapes
      params nparams indType.ctors env state) ?_
  intro ctors nextState Hctors
  exact Except.WF.pure ⟨rfl, rfl, Hctors⟩

/-- Family-level semantic lowering: headers are preserved and the constructor
list carries the full state-threaded nested-expression translation. -/
structure LoweredInductiveTranslation
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : LoweredConstructorTranslations env params nparams source.ctors
    state (out.1.ctors, out.2)

structure LoweredInductiveMapping
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : LoweredConstructorMappings env params nparams finalResult
    source.ctors state (out.1.ctors, out.2)

structure LoweredInductiveReopening
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalResult : Lean4Lean.ElimNestedInductive.Result)
    (restoreAs : Array Expr)
    (source : InductiveType) (state : Lean4Lean.ElimNestedInductive.State)
    (out : InductiveType × Lean4Lean.ElimNestedInductive.State) : Prop where
  name : out.1.name = source.name
  type : out.1.type = source.type
  constructors : LoweredConstructorReopenings env params nparams finalResult
    restoreAs source.ctors state (out.1.ctors, out.2)

theorem LoweredInductiveMapping.reopens
    (H : LoweredInductiveMapping env params nparams finalResult source state out)
    (hresultParams : finalResult.params = params)
    (fvars : List FVarId)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hnodup : fvars.Nodup)
    (Hsource : ∀ ctor ∈ source.ctors,
      ctor.type.FVarsIn fun _ => False) :
    LoweredInductiveReopening env params nparams finalResult restoreAs source
      state out :=
  ⟨H.name, H.type,
    H.constructors.reopens hresultParams fvars hparams hnodup Hsource⟩

theorem LoweredInductiveTranslation.newTypesLE
    (H : LoweredInductiveTranslation env params nparams source state out) :
    NestedNewTypesLE state out.2 := H.constructors.newTypesLE

theorem LoweredInductiveTranslation.nestedAuxLE
    (H : LoweredInductiveTranslation env params nparams source state out) :
    NestedAuxLE state out.2 := H.constructors.nestedAuxLE

theorem LoweredInductiveTranslation.namesWF
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 :=
  H.constructors.namesWF Hindex Hstate

theorem LoweredInductiveTranslation.namesFresh
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 :=
  H.constructors.namesFresh Hstate

theorem LoweredInductiveTranslation.auxFVarsIn
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hsource : ∀ ctor ∈ source.ctors,
      ctor.type.FVarsIn fun _ => False)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 :=
  H.constructors.auxFVarsIn Hsource Hparams Hstate

theorem LoweredInductiveTranslation.finalMapping
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hlater : NestedAuxLE out.2 finalState)
    (Hmap : NestedAuxMapModels finalResult finalState) :
    LoweredInductiveMapping env params nparams finalResult source state out :=
  ⟨H.name, H.type, H.constructors.finalMapping Hlater Hmap⟩

theorem LoweredInductiveTranslation.targetRestoreTelescope
    (H : LoweredInductiveTranslation env params nparams source state out) :
    ∀ ctor ∈ out.1.ctors, RestoreTelescope ctor.type nparams :=
  H.constructors.targetsRestoreTelescope

def RestorableInductiveType (nparams : Nat) (type : InductiveType) : Prop :=
  ∀ ctor ∈ type.ctors, RestoreTelescope ctor.type nparams

def RestorableNewTypesPrefix (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ j, j < i → (hj : j < state.newTypes.size) →
    RestorableInductiveType nparams state.newTypes[j]

theorem RestorableNewTypesPrefix.zero
    (state : Lean4Lean.ElimNestedInductive.State) :
    RestorableNewTypesPrefix nparams 0 state := by
  intro j hj
  omega

def NewTypeNamePresent (state : Lean4Lean.ElimNestedInductive.State)
    (name : Name) : Prop :=
  ∃ type ∈ state.newTypes.toList, type.name = name

theorem ElimNestedInductive.lowerInductive.translation
    (params : Array Expr) (nparams : Nat) (indType : InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.lowerInductive params nparams indType
      env state).WF fun out =>
        LoweredInductiveTranslation env params nparams indType state out := by
  unfold Lean4Lean.ElimNestedInductive.lowerInductive
  refine nestedBind.WF
    (ElimNestedInductive.lowerConstructors.translations params nparams
      indType.ctors env state hparams hclosures) ?_
  intro ctors nextState Hctors
  exact Except.WF.pure ⟨rfl, rfl, Hctors⟩

theorem ElimNestedInductive.lowerInductive.translationPending
    (params : Array Expr) (nparams : Nat) (indType : InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsource : InductiveConstructorsClosed indType)
    (Hstate : PendingNewTypesClosed cursor state) :
    (Lean4Lean.ElimNestedInductive.lowerInductive params nparams indType
      env state).WF fun out =>
        LoweredInductiveTranslation env params nparams indType state out ∧
        PendingNewTypesClosed cursor out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerInductive
  refine nestedBind.WF
    (ElimNestedInductive.lowerConstructors.translationsPending params nparams
      indType.ctors env state hparams hclosures Henv Hsource Hstate) ?_
  intro ctors nextState Hctors
  exact Except.WF.pure ⟨⟨rfl, rfl, Hctors.1⟩, Hctors.2⟩

/-- Semantic state transition for a dynamic lowering-queue iteration. -/
inductive LowerNextTranslation
    (env : Environment) (params : Array Expr) (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) :
    Option InductiveType × Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LowerNextTranslation env params nparams i state (none, state)
  | step (hidx : i < state.newTypes.size)
      (Hlowered : LoweredInductiveTranslation env params nparams
        state.newTypes[i] state (target, loweredState)) :
      LowerNextTranslation env params nparams i state
        (some state.newTypes[i], { loweredState with
          newTypes := loweredState.newTypes.set! i target })

theorem LowerNextTranslation.restorablePrefix
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (Hprefix : RestorableNewTypesPrefix nparams i state) :
    RestorableNewTypesPrefix nparams (i + 1) nextState := by
  cases H with
  | step hidx Hlowered =>
    rename_i target loweredState
    have Hle := Hlowered.newTypesLE
    have hiLowered := (Hle.getElem hidx).choose
    intro j hj hjNext
    have hjLowered : j < loweredState.newTypes.size := by
      simpa [Array.size_set!] using hjNext
    by_cases hji : j = i
    · subst j
      change RestorableInductiveType nparams
        (loweredState.newTypes.set! i target)[i]
      simpa [Array.getElem_setIfInBounds, hiLowered,
        RestorableInductiveType] using Hlowered.targetRestoreTelescope
    · have hjlt : j < i := by omega
      rcases Hle.getElem (show j < state.newTypes.size by omega) with
        ⟨hjInLowered, hsame⟩
      change RestorableInductiveType nparams
        (loweredState.newTypes.set! i target)[j]
      rw [show (loweredState.newTypes.set! i target)[j] =
          loweredState.newTypes[j] by
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjInLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact hget]
      rw [hsame]
      exact Hprefix j hjlt _

theorem LowerNextTranslation.nestedAuxLE
    (H : LowerNextTranslation env params nparams i state out) :
    NestedAuxLE state out.2 := by
  cases H with
  | done => exact .refl _
  | step _ Hlowered => exact Hlowered.nestedAuxLE

theorem LowerNextTranslation.namesWF
    (H : LowerNextTranslation env params nparams i state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  cases H with
  | done => exact Hstate
  | step _ Hlowered =>
    exact (Hlowered.namesWF Hindex Hstate).ofCacheCounterEq rfl rfl

theorem LowerNextTranslation.namesFresh
    (H : LowerNextTranslation env params nparams i state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  cases H with
  | done => exact Hstate
  | step _ Hlowered => exact (Hlowered.namesFresh Hstate).ofCacheEq rfl

theorem LowerNextTranslation.preservesTypeName
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (Hname : NewTypeNamePresent state name) :
    NewTypeNamePresent nextState name := by
  cases H with
  | step hidx Hlowered =>
    rename_i target loweredState
    rcases Hname with ⟨type, htype, hname⟩
    rcases List.mem_iff_getElem.mp htype with ⟨j, hj, htypeEq⟩
    have hjState : j < state.newTypes.size := by simpa using hj
    rcases Hlowered.newTypesLE.getElem hjState with
      ⟨hjLowered, hpreserved⟩
    have hjNext : j < (loweredState.newTypes.set! i target).size := by
      simpa [Array.size_set!] using hjLowered
    let finalType := (loweredState.newTypes.set! i target)[j]
    refine ⟨finalType, by
      exact List.getElem_mem hjNext, ?_⟩
    by_cases hji : j = i
    · subst j
      have hset : finalType = target := by
        simp [finalType, Array.getElem_setIfInBounds, hjLowered]
      rw [hset, Hlowered.name]
      have hsource : state.newTypes[i] = type := by
        simpa using htypeEq
      rw [hsource]
      exact hname
    · have hset : finalType = loweredState.newTypes[j] := by
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact hget
      rw [hset, hpreserved]
      have : state.newTypes[j] = type := by simpa using htypeEq
      rw [this]
      exact hname

/-- A queue step changes only its selected slot. Auxiliary discovery may
append new families before that slot is overwritten, but every distinct
pre-existing index retains its exact family record. -/
theorem LowerNextTranslation.getElem_ne
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (hj : j < state.newTypes.size) (hne : j ≠ i) :
    ∃ hjNext : j < nextState.newTypes.size,
      nextState.newTypes[j] = state.newTypes[j] := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    rcases Hlowered.newTypesLE.getElem hj with
      ⟨hjLowered, hsame⟩
    have hjNext : j <
        ({ loweredState with
          newTypes := loweredState.newTypes.set! i target }).newTypes.size := by
      simpa [Array.size_set!] using hjLowered
    refine ⟨hjNext, ?_⟩
    change (loweredState.newTypes.set! i target)[j] = state.newTypes[j]
    have hget := Array.getElem_setIfInBounds
      (xs := loweredState.newTypes) (i := i) (a := target)
      (j := j) hjLowered
    rw [if_neg (fun h : i = j => hne h.symm)] at hget
    simpa [Array.set!] using hget.trans hsame

/-- The selected queue slot contains the just-lowered target after the step,
even when lowering appended auxiliary families along the way. -/
theorem LowerNextTranslation.getElem_selected
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState)) (hi : i < state.newTypes.size) :
    ∃ target loweredState,
      LoweredInductiveTranslation env params nparams
        state.newTypes[i] state
        (target, loweredState) ∧
      nextState.nestedAux = loweredState.nestedAux ∧
      ∃ hiNext : i < nextState.newTypes.size,
        nextState.newTypes[i] = target := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    have hiLowered := Hlowered.newTypesLE.getElem hi |>.choose
    have hiNext : i <
        ({ loweredState with
          newTypes := loweredState.newTypes.set! i target }).newTypes.size := by
      simpa [Array.size_set!] using hiLowered
    refine ⟨target, loweredState, Hlowered, rfl, hiNext, ?_⟩
    change (loweredState.newTypes.set! i target)[i] = target
    simp [Array.getElem_setIfInBounds, hiLowered]

theorem ElimNestedInductive.lowerNext.translation
    (params : Array Expr) (nparams i : Nat)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.lowerNext params nparams i env state).WF
      fun out => LowerNextTranslation env params nparams i state out := by
  unfold Lean4Lean.ElimNestedInductive.lowerNext
  simp only [get, bind, StateT.bind, ReaderT.bind]
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M Lean4Lean.ElimNestedInductive.State)
      env state) = Except.ok (state, state) := rfl
  rw [hget]
  simp only [Except.bind]
  by_cases hidx : i < state.newTypes.size
  · rw [dif_pos hidx]
    refine nestedBind.WF
      (ElimNestedInductive.lowerInductive.translation params nparams
        state.newTypes[i] env state hparams hclosures) ?_
    intro target loweredState Htarget
    simp only [modify, StateT.modifyGet, pure, StateT.pure, ReaderT.pure,
      bind, StateT.bind, ReaderT.bind]
    exact Except.WF.pure (.step hidx Htarget)
  · rw [dif_neg hidx]
    exact Except.WF.pure (.done (Nat.le_of_not_gt hidx))

theorem ElimNestedInductive.lowerNext.translationPending
    (params : Array Expr) (nparams i : Nat)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hstate : PendingNewTypesClosed i state) :
    (Lean4Lean.ElimNestedInductive.lowerNext params nparams i env state).WF
      fun out =>
        LowerNextTranslation env params nparams i state out ∧
        PendingNewTypesClosed (i + 1) out.2 := by
  unfold Lean4Lean.ElimNestedInductive.lowerNext
  simp only [get, bind, StateT.bind, ReaderT.bind]
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M Lean4Lean.ElimNestedInductive.State)
      env state) = Except.ok (state, state) := rfl
  rw [hget]
  simp only [Except.bind]
  by_cases hidx : i < state.newTypes.size
  · rw [dif_pos hidx]
    refine nestedBind.WF
      (ElimNestedInductive.lowerInductive.translationPending params nparams
        state.newTypes[i] env state hparams hclosures Henv
        (Hstate i (Nat.le_refl _) hidx) Hstate) ?_
    intro target loweredState Htarget
    simp only [modify, StateT.modifyGet, pure, StateT.pure, ReaderT.pure,
      bind, StateT.bind, ReaderT.bind]
    have HnextPending : PendingNewTypesClosed (i + 1)
        { loweredState with
          newTypes := loweredState.newTypes.set! i target } := by
      intro j hcursor hj
      have hjLowered : j < loweredState.newTypes.size := by
        simpa [Array.size_set!] using hj
      have hne : j ≠ i := by omega
      have hvalue := Array.getElem_setIfInBounds
        (xs := loweredState.newTypes) (i := i) (a := target)
        (j := j) hjLowered
      rw [if_neg (fun heq : i = j => hne heq.symm)] at hvalue
      change InductiveConstructorsClosed
        (loweredState.newTypes.set! i target)[j]
      rw [show (loweredState.newTypes.set! i target)[j] =
        loweredState.newTypes[j] by simpa [Array.set!] using hvalue]
      exact Htarget.2 j (by omega) hjLowered
    exact Except.WF.pure ⟨.step hidx Htarget.1, HnextPending⟩
  · rw [dif_neg hidx]
    exact Except.WF.pure ⟨.done (Nat.le_of_not_gt hidx),
      fun j hcursor hj => Hstate j (by omega) hj⟩

/-- Complete semantic trace of the dynamically growing lowering queue.  The
queue stops only once the index reaches the then-current array size; each
preceding step contains the semantic family translation, including any new
auxiliary families appended while processing it. -/
inductive LoweringQueueTrace
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) : Nat → Nat →
      Lean4Lean.ElimNestedInductive.State →
      Lean4Lean.ElimNestedInductive.Result ×
        Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LoweringQueueTrace env params nparams lctx i (fuel + 1) state
        ({ state with
          nparams := params.size
          lctx
          params
          aux2nested := state.nestedAux.foldl
            (fun map (nested, name) => map.insert name nested) {}
          types := state.newTypes.toList }, state)
  | step :
      LowerNextTranslation env params nparams i state (some source, nextState) →
      LoweringQueueTrace env params nparams lctx (i + 1) fuel nextState out →
      LoweringQueueTrace env params nparams lctx i (fuel + 1) state out

theorem LoweringQueueTrace.resultContext
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    out.1.lctx = lctx ∧ out.1.params = params := by
  induction H with
  | done => exact ⟨rfl, rfl⟩
  | step _ _ ih => exact ih

theorem LoweringQueueTrace.resultNParams
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    out.1.nparams = params.size := by
  induction H with
  | done => rfl
  | step _ _ ih => exact ih

theorem LoweringQueueTrace.resultAuxMap
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    out.1.aux2nested = out.2.nestedAux.foldl
      (fun map (entry : Expr × Name) => map.insert entry.2 entry.1) {} := by
  induction H with
  | done => rfl
  | step _ _ ih => exact ih

theorem LoweringQueueTrace.resultNestedAuxLE
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    NestedAuxLE state out.2 := by
  induction H with
  | done => exact .refl _
  | step Hnext _ ih => exact Hnext.nestedAuxLE.trans ih

theorem LoweringQueueTrace.resultNamesWF
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF state) : NestedAuxNamesWF out.2 := by
  induction H with
  | done => exact Hstate
  | step Hnext Htail ih => exact ih (Hnext.namesWF Hindex Hstate)

theorem LoweringQueueTrace.resultNamesFresh
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hstate : NestedAuxNamesFresh env state) :
    NestedAuxNamesFresh env out.2 := by
  induction H with
  | done => exact Hstate
  | step Hnext Htail ih => exact ih (Hnext.namesFresh Hstate)

/-- Once an index lies strictly behind the queue cursor, later lowering
steps preserve the exact family stored there through to the final result. -/
theorem LoweringQueueTrace.getElem_before
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (hj : j < i) (hbound : j < state.newTypes.size) :
    out.1.types[j]? = some state.newTypes[j] := by
  induction H with
  | done =>
    simp only
    rw [List.getElem?_eq_getElem (by simpa using hbound)]
    rfl
  | step Hnext Htail ih =>
    rcases Hnext.getElem_ne hbound (by omega) with
      ⟨hnextBound, hsame⟩
    simpa [hsame] using ih (by omega) hnextBound

/-- Every not-yet-processed family within the current queue has a unique
future lowering step. The theorem retains that exact semantic translation
and identifies its target at the same index in the final result list. -/
theorem LoweringQueueTrace.translationAt
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (hij : i ≤ j) (hj : j < state.newTypes.size) :
    ∃ stepState target loweredState,
      LoweredInductiveTranslation env params nparams state.newTypes[j]
        stepState (target, loweredState) ∧
      out.1.types[j]? = some target ∧
      NestedAuxLE loweredState out.2 := by
  revert j
  induction H with
  | done hdone =>
    intro j hij hj
    omega
  | @step iStep stateStep sourceStep nextStateStep fuelStep outStep
      Hnext Htail ih =>
    intro j hij hj
    by_cases hji : j = iStep
    · subst j
      rcases Hnext.getElem_selected hj with
        ⟨target, loweredState, Htranslated, hnextAux, hiNext, htarget⟩
      refine ⟨stateStep, target, loweredState, Htranslated, ?_, ?_⟩
      have hfinal := Htail.getElem_before (j := iStep) (by omega) hiNext
      simpa [htarget] using hfinal
      rcases Htail.resultNestedAuxLE with ⟨suffix, hsuffix⟩
      exact ⟨suffix, by simpa [hnextAux] using hsuffix⟩
    · have hij' : iStep + 1 ≤ j := by omega
      rcases Hnext.getElem_ne hj hji with ⟨hjNext, hsame⟩
      rcases ih hij' hjNext with
        ⟨stepState, target, loweredState, Htranslated, hfinal, Haux⟩
      rw [hsame] at Htranslated
      exact ⟨stepState, target, loweredState, Htranslated, hfinal, Haux⟩

theorem LoweringQueueTrace.resultRestorable
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hprefix : RestorableNewTypesPrefix nparams i state) :
    ∀ type ∈ out.1.types, RestorableInductiveType nparams type := by
  induction H with
  | @done iDone fuelDone stateDone hbound =>
    intro type htype
    simp only at htype
    rcases List.mem_iff_getElem.mp htype with ⟨j, hj, rfl⟩
    apply Hprefix j
    · have hjSize : j < stateDone.newTypes.size := by simpa using hj
      omega
  | step Hnext Htail ih =>
    exact ih (Hnext.restorablePrefix Hprefix)

theorem LoweringQueueTrace.preservesTypeName
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hname : NewTypeNamePresent state name) :
    ∃ type ∈ out.1.types, type.name = name := by
  induction H with
  | done => simpa [NewTypeNamePresent] using Hname
  | step Hnext Htail ih => exact ih (Hnext.preservesTypeName Hname)

private theorem loweringQueueLoop_refines
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) (i fuel : Nat)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.run.loop nparams lctx params i fuel
      env state).WF fun out =>
        LoweringQueueTrace env params nparams lctx i fuel state out := by
  induction fuel generalizing i state with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [Lean4Lean.ElimNestedInductive.run.loop]
    refine nestedBind.WF
      (ElimNestedInductive.lowerNext.translation params nparams i env state
        hparams hclosures) ?_
    intro next nextState Hnext
    cases Hnext with
    | done hbound =>
      simp only [pure, ReaderT.pure, StateT.pure]
      exact Except.WF.pure (.done hbound)
    | step hidx Hlowered =>
      exact (ih (i := i + 1) (state := _)).mono fun _ Htail =>
        LoweringQueueTrace.step (LowerNextTranslation.step hidx Hlowered) Htail

/-- The dynamic queue invariant used by auxiliary validation. Every pending
family has closed constructor types, so processing it preserves the cache
free-variable invariant and proves every newly appended family closed before
the cursor can reach it. -/
private theorem loweringQueueLoop_refinesClosed
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (lctx : LocalContext) (i fuel : Nat)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hparams : params.size = nparams)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hpending : PendingNewTypesClosed i state)
    (Hcache : NestedAuxFVarsIn P state) :
    (Lean4Lean.ElimNestedInductive.run.loop nparams lctx params i fuel
      env state).WF fun out =>
        LoweringQueueTrace env params nparams lctx i fuel state out ∧
        NestedAuxFVarsIn P out.2 := by
  induction fuel generalizing i state with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [Lean4Lean.ElimNestedInductive.run.loop]
    refine nestedBind.WF
      (ElimNestedInductive.lowerNext.translationPending params nparams i env
        state hparams hclosures Henv Hpending) ?_
    intro next nextState Hnext
    rcases Hnext with ⟨Htranslation, HpendingNext⟩
    cases Htranslation with
    | done hbound =>
      simp only [pure, ReaderT.pure, StateT.pure]
      exact Except.WF.pure ⟨.done hbound, Hcache⟩
    | step hidx Hlowered =>
      rename_i target loweredState
      have HcacheNext : NestedAuxFVarsIn P
          { loweredState with
            newTypes := loweredState.newTypes.set! i target } := by
        have HcacheLower := Hlowered.auxFVarsIn
          (Hpending i (Nat.le_refl _) hidx) Hparams Hcache
        intro nested name hentry
        exact HcacheLower nested name hentry
      exact (ih (i := i + 1)
        (state := { loweredState with
          newTypes := loweredState.newTypes.set! i target })
        HpendingNext HcacheNext).mono fun _ Htail =>
          ⟨LoweringQueueTrace.step (.step hidx Hlowered) Htail.1,
            Htail.2⟩

/-- End-to-end semantic certificate for nested lowering from the source
parameter telescope through the complete dynamic family queue. -/
structure NestedLoweringRun
    (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (initialState : Lean4Lean.ElimNestedInductive.State)
    (out : Lean4Lean.ElimNestedInductive.Result ×
      Lean4Lean.ElimNestedInductive.State) : Prop where
  source : ∃ first rest tail paramsState lctx params,
    types = first :: rest ∧
    NestedParamOpening {} #[] first.type nparams
      lctx tail params ∧
    paramsState.newTypes = initialState.newTypes ∧
    paramsState.nestedAux = initialState.nestedAux ∧
    paramsState.nextIdx = initialState.nextIdx ∧
    NestedBindingContextWF lctx paramsState.ngen ∧
    Nonempty (LocalForallSelection lctx params) ∧
    LoweringQueueTrace env params nparams lctx 0 fuel
      paramsState out

theorem NestedLoweringRun.resultRestorable
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    ∀ type ∈ out.1.types, RestorableInductiveType nparams type := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultRestorable (.zero paramsState)

theorem NestedLoweringRun.resultNParams
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.nparams = nparams := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, Hopening, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultNParams.trans Hopening.initial_size

theorem NestedLoweringRun.resultParamsSize
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.params.size = nparams := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, Hopening, _, _, _, _, _, Hqueue⟩
  rw [Hqueue.resultContext.2]
  exact Hopening.initial_size

/-- The final restoration context is exactly the source parameter selection
opened before the dynamic lowering queue starts. -/
theorem NestedLoweringRun.resultContextSelection
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    Nonempty (LocalForallSelection out.1.lctx out.1.params) := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _,
      _Hctx, Hselection, Hqueue⟩
  rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
  rw [hlctx, hparams]
  exact Hselection

theorem NestedLoweringRun.resultContextWF
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.lctx.WF := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, Hctx,
      _Hselection, Hqueue⟩
  rw [Hqueue.resultContext.1]
  exact Hctx.wf

/-- Lowering stores common parameters in source binder order, whereas its
local context (and therefore every `MLCtx.vlctx`) stores free variables in
most-recent-first order. -/
theorem NestedLoweringRun.resultParams_reverse_fvars
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.params.toList.reverse = out.1.lctx.fvars.map Expr.fvar := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      _hnewTypes, _hnestedAux, _hnextIdx, _Hctx, _Hselection, Hqueue⟩
  rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
  rw [hlctx, hparams]
  exact Hopening.toRestoreParamOpening.root_params_reverse_fvars

/-- Any retained selection of the final parameter array lists exactly the
same free variables as the returned local context, in binder order rather
than the context's most-recent-first order. -/
theorem NestedLoweringRun.resultSelection_reverse_fvars
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (selection : LocalForallSelection out.1.lctx out.1.params) :
    selection.fvars.reverse = out.1.lctx.fvars := by
  have hparams := H.resultParams_reverse_fvars
  have hselected : out.1.params.toList =
      selection.fvars.map Expr.fvar := by
    calc
      out.1.params.toList =
          (selection.fvars.map Expr.fvar).toArray.toList :=
        congrArg Array.toList selection.expressions
      _ = selection.fvars.map Expr.fvar := by simp
  rw [hselected, ← List.map_reverse] at hparams
  exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hparams

/-- The executable auxiliary checks can be closed over lowering's retained
parameter telescope.  This removes the concrete free-variable names from the
semantic certificate before restoration reopens the same telescope with its
own fresh names. -/
theorem NestedLoweringRun.closeValidatedNestedAuxiliaries
    (H : NestedLoweringRun sourceEnv fuel nparams types initialState
      (res, finalState))
    (henv : venv.WF)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (Hvalidated : ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res) :
    ClosedValidatedNestedAuxiliaries venv lparams res := by
  have hfull : mlctx.fvarRevList mlctx.length (Nat.le_refl _) =
      mlctx.vlctx.fvars := mlctx.fvarRevList_all
  have hparams : res.params.toList.reverse =
      (mlctx.fvarRevList mlctx.length (Nat.le_refl _)).map Expr.fvar := by
    rw [hfull, ← hmlctx.tr.fvars_eq, hlctx]
    exact H.resultParams_reverse_fvars
  intro name e hfind
  rcases Hvalidated name e hfind with
    ⟨ty, e', ty', ⟨_hfvars, Hexpr, _Htype, _Htyping⟩, HisType⟩
  have Hclosed := hmlctx.mkForall_trS henv Hexpr HisType
    mlctx.length (Nat.le_refl _)
  rw [mlctx.dropN_all] at Hclosed
  have hconcrete : res.lctx.mkForall res.params e =
      mlctx.mkForall mlctx.length (Nat.le_refl _) e := by
    rw [← hlctx]
    exact hmlctx.mkForall_eq mlctx.length (Nat.le_refl _) hparams
  refine ⟨mlctx.mkForall' mlctx.length (Nat.le_refl _) e', ?_⟩
  rw [hconcrete]
  exact Hclosed

/-- Fully name-independent auxiliary semantics retained after validation:
the lowering-selected production variables are abstracted into the canonical
de-Bruijn parameter context before restoration is inspected. -/
theorem NestedLoweringRun.validatedAuxiliaryResidualTranslations
    (H : NestedLoweringRun sourceEnv fuel nparams types initialState
      (res, finalState))
    (henv : venv.WF)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (Hvalidated : ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res) :
    ∃ selection : LocalForallSelection res.lctx res.params,
      ClosedNestedAuxiliaryTranslations venv lparams res selection := by
  rcases H.resultContextSelection with ⟨selection⟩
  exact ⟨selection,
    (H.closeValidatedNestedAuxiliaries henv mlctx hmlctx hlctx Hvalidated
      ).residualTranslations henv selection⟩

theorem NestedLoweringRun.resultParamsFVarsIn
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    ∀ e ∈ out.1.params, e.FVarsIn (· ∈ out.1.lctx.fvars) := by
  rcases H.resultContextSelection with ⟨Hselection⟩
  exact Hselection.fvarsIn H.resultContextWF

theorem NestedLoweringRun.resultAuxMap
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    out.1.aux2nested = out.2.nestedAux.foldl
      (fun map (entry : Expr × Name) => map.insert entry.2 entry.1) {} := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, _, _, _, _, Hqueue⟩
  exact Hqueue.resultAuxMap

theorem NestedLoweringRun.resultAuxFVarsIn
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hcache : NestedAuxFVarsIn P out.2) :
    NestedAuxMapFVarsIn P
      (show Std.TreeMap Name Expr Name.quickCmp from out.1.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapFVarsIn P
    (out.2.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_fvarsIn out.2.nestedAux.toList
  · intro entry hentry
    exact Hcache entry.1 entry.2 (by simpa using hentry)
  · unfold NestedAuxMapFVarsIn
    intro name nested hfind
    simp at hfind

theorem NestedLoweringRun.resultAuxNamesReserved
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Hnames : NestedAuxNamesWF finalState) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapNamesReserved
    (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_namesReserved finalState.nestedAux.toList
  · intro entry hentry
    exact Hnames.reserved entry.1 entry.2 (by simpa using hentry)
  · intro name nested hfind
    simp at hfind

theorem NestedLoweringRun.resultAuxNamesFresh
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Hnames : NestedAuxNamesFresh env finalState) :
    NestedAuxMapNamesFresh env
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) := by
  rw [H.resultAuxMap]
  change NestedAuxMapNamesFresh env
    (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})
  rw [← Array.foldl_toList]
  apply nestedAuxFold_namesFresh finalState.nestedAux.toList
  · intro entry hentry
    exact Hnames entry.1 entry.2 (by simpa using hentry)
  · intro name nested hfind
    simp at hfind

theorem NestedLoweringRun.validateNestedAuxiliariesWF
    (H : NestedLoweringRun sourceEnv loweringFuel nparams sourceTypes
      initialState (res, finalState))
    (hvalid : CheckingEnv.Valid safety restoredEnv venv)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv)
    (Hcache : NestedAuxFVarsIn (· ∈ mlctx.vlctx.fvars) finalState) :
    (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
      res).WF fun _ =>
        ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res := by
  apply validateNestedAuxiliaries.WF hvalid mlctx hmlctx hlctx hfresh
  intro name nested hfind
  exact H.resultAuxFVarsIn Hcache name nested hfind

/-- Under the separately stated fresh-name invariant, every final cache entry
is retrieved exactly by the production `aux2nested` map. -/
theorem NestedLoweringRun.resultAuxLookup
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hnodup : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hentry : (nested, name) ∈ finalState.nestedAux) :
    result.aux2nested.find? name = some nested := by
  rw [H.resultAuxMap]
  change (finalState.nestedAux.foldl
    (fun (map : Std.TreeMap Name Expr Name.quickCmp)
      (entry : Expr × Name) => map.insert entry.2 entry.1)
    {})[name]? = some nested
  rw [← Array.foldl_toList]
  exact nestedAuxFold_find finalState.nestedAux.toList {} hnodup
    (by simpa using hentry)

theorem NestedLoweringRun.resultAuxMapModels
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hnodup : (finalState.nestedAux.toList.map Prod.snd).Nodup) :
    NestedAuxMapModels result finalState := by
  intro nested name hentry
  exact H.resultAuxLookup hnodup hentry

theorem NestedLoweringRun.resultNestedAuxLE
    (H : NestedLoweringRun env fuel nparams types initialState out) :
    NestedAuxLE initialState out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _hnewTypes,
      hinitialAux, _hinitialNext, _Hctx, _Hselection, Hqueue⟩
  rcases Hqueue.resultNestedAuxLE with ⟨suffix, hsuffix⟩
  exact ⟨suffix, by simpa [hinitialAux] using hsuffix⟩

theorem NestedLoweringRun.resultNamesWF
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (Hstate : NestedAuxNamesWF initialState) : NestedAuxNamesWF out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, hinitialAux,
      hinitialNext, _Hctx, _Hselection, Hqueue⟩
  exact Hqueue.resultNamesWF Hindex
    (Hstate.ofCacheCounterEq hinitialAux hinitialNext)

theorem NestedLoweringRun.resultNamesFresh
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hstate : NestedAuxNamesFresh env initialState) :
    NestedAuxNamesFresh env out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, _, hinitialAux,
      _hinitialNext, _Hctx, _Hselection, Hqueue⟩
  exact Hqueue.resultNamesFresh (Hstate.ofCacheEq hinitialAux)

theorem NestedLoweringRun.resultFamilyNamesFreshOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hwf : env.constants.WF)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxFamiliesFresh result env := by
  have Hnames := H.resultNamesFresh
    (NestedAuxNamesFresh.empty env initialState hempty)
  have Hmap := H.resultAuxNamesFresh Hnames
  intro name nested hfind
  exact find?_none_of_contains_false hwf (Hmap name nested hfind)

/-- End-to-end freshness bridge for restoration: lowering proves auxiliary
families fresh in the production source, and lockstep installation turns that
into abstract freshness for every constructor recognized through those
families. -/
theorem NestedLoweringRun.restoreAuxConstructorsFreshOfInstallation
    (H : NestedLoweringRun sourceProdEnv fuel nparams types initialState
      (result, finalState))
    (Hinstall : AddConstants safety sourceProdEnv sourceVEnv entries
      loweredEnv loweredVEnv)
    (hwf : sourceProdEnv.constants.WF)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv :=
  Hinstall.restoreAuxConstructorsFresh hwf Howners
    (H.resultFamilyNamesFreshOfEmpty hwf hempty)

theorem NestedLoweringRun.resultNamesNodupOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hindex : AppendIndexAfterIndexFaithful)
    (hempty : initialState.nestedAux = #[]) :
    (out.2.nestedAux.toList.map Prod.snd).Nodup :=
  (H.resultNamesWF Hindex (NestedAuxNamesWF.empty initialState hempty)).nodup

theorem NestedLoweringRun.resultFamilyNamesReservedOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Hindex : AppendIndexAfterIndexFaithful)
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) :=
  H.resultAuxNamesReserved
    (H.resultNamesWF Hindex (NestedAuxNamesWF.empty initialState hempty))

theorem NestedLoweringRun.resultFamilyNamesReservedFresh
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapNamesReserved
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested) :=
  H.resultFamilyNamesReservedOfEmpty appendIndexAfterIndexFaithful hempty

theorem NestedLoweringRun.resultAuxMapModelsOfEmpty
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Hindex : AppendIndexAfterIndexFaithful)
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapModels result finalState :=
  H.resultAuxMapModels (H.resultNamesNodupOfEmpty Hindex hempty)

theorem NestedLoweringRun.resultAuxMapModelsFresh
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxMapModels result finalState :=
  H.resultAuxMapModelsOfEmpty appendIndexAfterIndexFaithful hempty

/-- Positional lowering witness for any family present in the initial queue.
Unlike name preservation, this exposes the complete constructor-expression
translation performed at that family's actual dynamic queue step. -/
theorem NestedLoweringRun.translationAtInitial
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveTranslation env params nparams
        initialState.newTypes[j] stepState (target, loweredState) ∧
      out.1.types[j]? = some target ∧
      NestedAuxLE loweredState out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _Hctx, _Hselection, Hqueue⟩
  have hjParams : j < paramsState.newTypes.size := by
    simpa [hinitial] using hj
  rcases Hqueue.translationAt (Nat.zero_le j) hjParams with
    ⟨stepState, target, loweredState, Htranslated, htarget, Haux⟩
  have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
    have heq := congrArg
      (fun xs : Array InductiveType => xs[j]!) hinitial
    simpa [Array.getElem!_eq_getD, Array.getD, hjParams, hj] using heq
  rw [hvalue] at Htranslated
  exact ⟨params, stepState, target, loweredState,
    Hopening.initial_size, Htranslated, htarget, Haux⟩

/-- Once final cache-name uniqueness is supplied, every initially declared
family has a positional lowering certificate whose constructor bodies are
all interpreted by the actual final restoration map. -/
theorem NestedLoweringRun.finalMappingAtInitial
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hauxNames : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result
        initialState.newTypes[j] stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.translationAtInitial hj with
    ⟨params, stepState, target, loweredState, hparams, Htranslated,
      htarget, Hlater⟩
  exact ⟨params, stepState, target, loweredState, hparams,
    Htranslated.finalMapping Hlater (H.resultAuxMapModels hauxNames), htarget⟩

/-- Parameter-aligned form of `finalMappingAtInitial`.  The expression
mapping for each source family is performed with exactly the parameter array
stored in the final restoration record, rather than merely with an array of
the same size.  This identity is what later lets restoration cancel the
abstraction performed when a nested application was cached. -/
theorem NestedLoweringRun.finalMappingAtInitialAligned
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hauxNames : (finalState.nestedAux.toList.map Prod.snd).Nodup)
    (hj : j < initialState.newTypes.size) :
    ∃ params stepState target loweredState,
      result.params = params ∧
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result
        initialState.newTypes[j] stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _Hctx, _Hselection, Hqueue⟩
  have hjParams : j < paramsState.newTypes.size := by
    simpa [hinitial] using hj
  rcases Hqueue.translationAt (Nat.zero_le j) hjParams with
    ⟨stepState, target, loweredState, Htranslated, htarget, Hlater⟩
  have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
    have heq := congrArg
      (fun xs : Array InductiveType => xs[j]!) hinitial
    simpa [Array.getElem!_eq_getD, Array.getD, hjParams, hj] using heq
  rw [hvalue] at Htranslated
  exact ⟨params, stepState, target, loweredState,
    Hqueue.resultContext.2, Hopening.initial_size,
    Htranslated.finalMapping Hlater (H.resultAuxMapModels hauxNames), htarget⟩

theorem NestedLoweringRun.preservesInitialTypeName
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Hname : NewTypeNamePresent initialState name) :
    ∃ type ∈ out.1.types, type.name = name := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _, _, hnewTypes,
      _hnewAux, _hnextIdx, _Hctx, _Hselection, Hqueue⟩
  apply Hqueue.preservesTypeName
  unfold NewTypeNamePresent at Hname ⊢
  rwa [hnewTypes]

theorem ElimNestedInductive.run.translation
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun out => NestedLoweringRun env fuel nparams types state out := by
  cases types with
  | nil => exact Except.WF.throw
  | cons first rest =>
    unfold Lean4Lean.ElimNestedInductive.run
    apply ElimNestedInductive.withParams.refinesSelected
    intro lctx tail params paramsState Hopening Hctx Hselection _hnodup hnewTypes
      hnestedAux hnextIdx
    have hparams : params.size = nparams := Hopening.initial_size
    exact (loweringQueueLoop_refines env params nparams lctx 0 fuel paramsState
      hparams hclosures).mono fun _ Hqueue =>
        ⟨⟨first, rest, tail, paramsState, lctx, params,
          rfl, Hopening, hnewTypes, hnestedAux, hnextIdx, Hctx,
          ⟨Hselection⟩, Hqueue⟩⟩

/-- The final restoration parameter array is an ordered array of distinct
free variables. -/
def NestedResultParamsNodup
    (result : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∃ fvars : List FVarId,
    result.params = (fvars.map Expr.fvar).toArray ∧ fvars.Nodup

/-- End-to-end queue safety from the executable source checks.  This closes
the dynamic-generation loop: source constructors are closed, every generated
auxiliary constructor is re-closed over the verified parameter context, and
therefore every final cache witness is open only over the retained result
context. -/
theorem ElimNestedInductive.run.translationClosed
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitial : state.newTypes = types.toArray)
    (hempty : state.nestedAux = #[]) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun out =>
        NestedLoweringRun env fuel nparams types state out ∧
        NestedAuxFVarsIn (· ∈ out.1.lctx.fvars) out.2 ∧
        NestedResultParamsNodup out.1 := by
  cases types with
  | nil => exact Except.WF.throw
  | cons first rest =>
    unfold Lean4Lean.ElimNestedInductive.run
    apply ElimNestedInductive.withParams.refinesClosing
      (Htype := Hsources.typeClosed (by simp))
    intro lctx tail params paramsState Hopening Hclosing Htail hnewTypes
      hnestedAux hnextIdx
    have hparams : params.size = nparams := Hopening.initial_size
    have Hparams : ∀ param ∈ params,
        param.FVarsIn (· ∈ lctx.fvars) :=
      Hclosing.selection.fvarsIn Hclosing.binding.wf
    have Hpending : PendingNewTypesClosed 0 paramsState := by
      intro j _hj hj
      have hjState : j < state.newTypes.size := by
        simpa [hnewTypes] using hj
      have hvalue : paramsState.newTypes[j] = state.newTypes[j] := by
        have heq := congrArg
          (fun xs : Array InductiveType => xs[j]!) hnewTypes
        simpa [Array.getElem!_eq_getD, Array.getD, hj, hjState] using heq
      rw [hvalue]
      have hmember : state.newTypes[j] ∈ first :: rest := by
        have hmemState : state.newTypes[j] ∈ state.newTypes :=
          Array.getElem_mem hjState
        simpa [hinitial] using hmemState
      exact Hsources.constructorsClosed hmember
    have Hcache : NestedAuxFVarsIn (· ∈ lctx.fvars) paramsState := by
      intro nested name hentry
      rw [hnestedAux, hempty] at hentry
      simp at hentry
    exact (loweringQueueLoop_refinesClosed env params nparams lctx 0 fuel
      paramsState hparams hclosures Henv Hparams Hpending Hcache).mono
        fun _ Hqueue => by
          refine ⟨⟨⟨first, rest, tail, paramsState, lctx, params,
            rfl, Hopening, hnewTypes, hnestedAux, hnextIdx,
            Hclosing.binding, ⟨Hclosing.selection⟩, Hqueue.1⟩⟩, ?_, ?_⟩
          · rw [Hqueue.1.resultContext.1]
            exact Hqueue.2
          · exact ⟨Hclosing.selection.fvars,
              Hqueue.1.resultContext.2.trans Hclosing.selection.expressions,
              Hclosing.nodup⟩

/-- Exact state transition for one iteration of the dynamic lowering queue.
The successful case retains the source family selected before lowering, while
allowing `lowerInductive` to append freshly discovered auxiliary families
before the selected slot is overwritten. -/
inductive LowerNextResult (params : Array Expr) (nparams i : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) :
    Option InductiveType → Lean4Lean.ElimNestedInductive.State → Prop
  | done (hbound : state.newTypes.size ≤ i) :
      LowerNextResult params nparams i state none state
  | step {target : InductiveType}
      {loweredState : Lean4Lean.ElimNestedInductive.State}
      (hidx : i < state.newTypes.size)
      (shape : LoweredInductiveShape nparams state.newTypes[i] target) :
      LowerNextResult params nparams i state (some state.newTypes[i])
        { loweredState with
          newTypes := loweredState.newTypes.set! i target }

theorem ElimNestedInductive.lowerNext.refines
    (params : Array Expr) (nparams i : Nat)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.lowerNext params nparams i env state).WF
      fun out => LowerNextResult params nparams i state out.1 out.2 := by
  intro out hout
  unfold Lean4Lean.ElimNestedInductive.lowerNext at hout
  simp only [get, bind, StateT.bind, ReaderT.bind, pure] at hout
  have hget : ((getThe Lean4Lean.ElimNestedInductive.State :
      Lean4Lean.ElimNestedInductive.M
        Lean4Lean.ElimNestedInductive.State) env state) =
      Except.ok (state, state) := rfl
  rw [hget] at hout
  simp only [Except.bind] at hout
  by_cases hidx : i < state.newTypes.size
  · rw [dif_pos hidx] at hout
    change ((Lean4Lean.ElimNestedInductive.lowerInductive
      params nparams state.newTypes[i] env state).bind fun lowered =>
        Except.ok (some state.newTypes[i],
          { lowered.2 with
            newTypes := lowered.2.newTypes.set! i lowered.1 })) =
      Except.ok out at hout
    cases hlower : Lean4Lean.ElimNestedInductive.lowerInductive
        params nparams state.newTypes[i] env state with
    | error err =>
      rw [hlower] at hout
      contradiction
    | ok lowered =>
      rw [hlower] at hout
      simp at hout
      cases hout
      exact .step hidx
        (ElimNestedInductive.lowerInductive.shape
          params nparams state.newTypes[i] env state lowered hlower)
  · rw [dif_neg hidx] at hout
    cases hout
    exact .done (Nat.le_of_not_gt hidx)

/-- The first branch of nested lowering rejects an empty source block. This
is the operational origin of the nonemptiness premise later used to recover
`SourceWF` from `TrInductDeclCore`. -/
theorem ElimNestedInductive.run.source_nonempty
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun _ => types ≠ [] := by
  intro out hout
  cases types with
  | nil =>
    change Except.error _ = Except.ok out at hout
    contradiction
  | cons type types =>
    simp

/-- A successful lowering run carries the exact common-parameter opening of
the first source header into the restoration data returned in `Result`. -/
theorem ElimNestedInductive.run.parameterOpening
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State) :
    (Lean4Lean.ElimNestedInductive.run fuel nparams types env state).WF
      fun out => ∃ first rest tail,
        types = first :: rest ∧
        NestedParamOpening {} #[] first.type nparams
          out.1.lctx tail out.1.params ∧
        out.1.nparams = nparams := by
  cases types with
  | nil => exact Except.WF.throw
  | cons first rest =>
    unfold Lean4Lean.ElimNestedInductive.run
    apply ElimNestedInductive.withParams.refines
    intro lctx tail params outState Hopening
    have loopWF : ∀ remaining i currentState,
        (Lean4Lean.ElimNestedInductive.run.loop nparams lctx params i
          remaining env currentState).WF fun out => ∃ first' rest' tail',
            first :: rest = first' :: rest' ∧
            NestedParamOpening {} #[] first'.type nparams
              out.1.lctx tail' out.1.params ∧
            out.1.nparams = nparams := by
      intro remaining
      induction remaining with
      | zero => intro i currentState; exact Except.WF.throw
      | succ remaining ih =>
        intro i currentState
        simp only [Lean4Lean.ElimNestedInductive.run.loop]
        exact (ElimNestedInductive.lowerNext.refines
          params nparams i env currentState).bind fun next Hnext => by
            rcases next with ⟨next, nextState⟩
            cases Hnext with
            | done hbound =>
              exact Except.WF.pure ⟨first, rest, tail, rfl, Hopening,
                Hopening.initial_size⟩
            | step hidx Hshape =>
              exact ih (i + 1) _
    exact loopWF fuel 0 outState

/-- Projection of the complete lowering trace through the `StateT.run'` used
by `Environment.addInductive`. -/
def NestedLoweringResult
    (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (initialState : Lean4Lean.ElimNestedInductive.State)
    (result : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∃ finalState, NestedLoweringRun env fuel nparams types initialState
    (result, finalState)

/-- Lowering result with the dynamic-queue closure argument discharged.  The
final cache predicate is stated against the exact local context returned in
the executable restoration record. -/
def NestedLoweringResultClosed
    (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (initialState : Lean4Lean.ElimNestedInductive.State)
    (result : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∃ finalState,
    NestedLoweringRun env fuel nparams types initialState
      (result, finalState) ∧
    NestedAuxFVarsIn (· ∈ result.lctx.fvars) finalState ∧
    NestedResultParamsNodup result

/-- Closed lowering scopes every auxiliary witness by any retained
binder-order selection of the result parameters. -/
theorem NestedLoweringResultClosed.auxFVarsInSelection
    (H : NestedLoweringResultClosed env fuel nparams types initialState result)
    (selection : LocalForallSelection result.lctx result.params) :
    ∀ name e, result.aux2nested.find? name = some e →
      e.FVarsIn (· ∈ selection.fvars) := by
  rcases H with ⟨finalState, Hrun, Hcache, _Hparams⟩
  have Hmap := Hrun.resultAuxFVarsIn Hcache
  have hcontext := Hrun.resultSelection_reverse_fvars selection
  intro name e hfind
  exact (Hmap name e hfind).mono fun fv hfv => by
    rw [← hcontext] at hfv
    exact List.mem_reverse.mp hfv

/-- Canonical semantic interpretation of the head expression inserted by an
auxiliary-family restoration hit, after restoration's fresh parameters are
closed again.  Both its parameter arity and its translation follow from the
validated auxiliary certificate; no concrete free-variable identity remains. -/
theorem NestedLoweringResultClosed.auxiliaryRestorationHeadTranslation
    (H : NestedLoweringResultClosed env fuel nparams types initialState result)
    (selection : LocalForallSelection result.lctx result.params)
    (Htranslations : ClosedNestedAuxiliaryTranslations venv lparams result
      selection)
    (name : Name) (e : Expr)
    (hfind : result.aux2nested.find? name = some e)
    (restoreSelection : LocalForallSelection restoreLctx restoreAs)
    (hrestoreNodup : restoreSelection.fvars.Nodup) :
    ∃ domains target,
      domains.length = result.params.size ∧
      TrExprS venv lparams (abstractForallContext domains [])
        (((e.abstract result.params).instantiateRev restoreAs).abstract
          restoreAs) target ∧
      venv.IsType lparams.length
        (abstractForallContext domains []).toCtx target := by
  rcases Htranslations name e hfind with ⟨Haux⟩
  have Hscope := H.auxFVarsInSelection selection name e hfind
  have halpha := Haux.restorationAlpha Hscope restoreSelection hrestoreNodup
  refine ⟨Haux.domains, Haux.residualTarget, Haux.arity, ?_,
    Haux.residualType⟩
  rw [halpha]
  exact Haux.residual

theorem NestedLoweringResultClosed.toResult
    (H : NestedLoweringResultClosed env fuel nparams types initialState result) :
    NestedLoweringResult env fuel nparams types initialState result := by
  rcases H with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  exact ⟨finalState, Hrun⟩

theorem NestedLoweringResultClosed.resultParamsNodup
    (H : NestedLoweringResultClosed env fuel nparams types initialState result) :
    NestedResultParamsNodup result := by
  rcases H with ⟨_finalState, _Hrun, _Hcache, Hparams⟩
  exact Hparams

theorem NestedLoweringResultClosed.selectionNodup
    (H : NestedLoweringResultClosed env fuel nparams types initialState result)
    (selection : LocalForallSelection result.lctx result.params) :
    selection.fvars.Nodup := by
  rcases H.resultParamsNodup with ⟨fvars, hparams, hnodup⟩
  have harrays : (selection.fvars.map Expr.fvar).toArray =
      (fvars.map Expr.fvar).toArray := by
    rw [← selection.expressions, ← hparams]
  have hlists : selection.fvars.map Expr.fvar =
      fvars.map Expr.fvar := by
    simpa using congrArg Array.toList harrays
  have heq : selection.fvars = fvars :=
    (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlists
  rw [heq]
  exact hnodup

theorem NestedLoweringResultClosed.resultParamsSize
    (H : NestedLoweringResultClosed env fuel nparams types initialState result) :
    result.params.size = result.nparams := by
  rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
  exact Hrun.resultParamsSize.trans Hrun.resultNParams.symm

/-- Actual operational restoration openings satisfy the arbitrary-depth
alpha law for every validated auxiliary hit. -/
theorem NestedRestorationOpening.auxiliaryAlphaAt
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (name : Name) (hfind : result.aux2nested.find? name = some e)
    (k : Nat) :
    ((e.abstract result.params).instantiateRev Hopen.params).abstractList
        Hopen.selection.fvars k =
      e.abstractList selection.fvars k := by
  have Hscope := Hlower.auxFVarsInSelection selection name e hfind
  have hsize : Hopen.selection.fvars.length = selection.fvars.length := by
    rw [Hopen.selectionLength, ← selection.size]
  exact Haux.restorationAlphaAt Hscope (Hlower.selectionNodup selection)
    Hopen.selection Hopen.selectionNodup hsize k

/-- A concrete family head inserted by operational restoration has the
validated auxiliary translation in the abstract context extended by the
recursor binders beneath which the hit occurs. -/
theorem NestedRestorationOpening.auxiliaryTranslationUnder
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.Ordered)
    (name : Name) (hfind : result.aux2nested.find? name = some e)
    (suffixDomains : List VExpr) :
    TrExprS venv lparams
      (abstractForallContext suffixDomains
        (abstractForallContext Haux.domains []))
      (((e.abstract result.params).instantiateRev Hopen.params).abstractList
        Hopen.selection.fvars suffixDomains.length)
      (Haux.residualTarget.liftN suffixDomains.length 0) := by
  rw [Hopen.auxiliaryAlphaAt Hlower selection Haux name hfind
    suffixDomains.length]
  exact Haux.residualUnder henv (Hlower.selectionNodup selection)
    suffixDomains

/-- Typed form of `auxiliaryTranslationUnder`, packaging the translation and
the abstract domain-type proof needed by the enclosing restored telescope. -/
theorem NestedRestorationOpening.auxiliaryTypedUnder
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.Ordered)
    (name : Name) (hfind : result.aux2nested.find? name = some e)
    (suffixDomains : List VExpr) :
    TrExprS venv lparams
        (abstractForallContext suffixDomains
          (abstractForallContext Haux.domains []))
        (((e.abstract result.params).instantiateRev Hopen.params).abstractList
          Hopen.selection.fvars suffixDomains.length)
        (Haux.residualTarget.liftN suffixDomains.length 0) ∧
      venv.IsType lparams.length
        (abstractForallContext suffixDomains
          (abstractForallContext Haux.domains [])).toCtx
        (Haux.residualTarget.liftN suffixDomains.length 0) := by
  exact ⟨Hopen.auxiliaryTranslationUnder Hlower selection Haux henv name
    hfind suffixDomains, Haux.residualTypeUnder henv suffixDomains⟩

/-- Interpret a complete restoration hit on an auxiliary-family application
which has exactly the common-parameter arguments.  The executable output is
identified with the validated reopened witness, then translated and typed in
the exact current suffix context. -/
theorem NestedRestorationOpening.exactFamilyHitTypedUnder
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.Ordered)
    (family : Name) (levels : List Level)
    (hfind : result.aux2nested.find? family = some e)
    (hrec : auxRec.find? family = none)
    (t restored : Expr)
    (hhead : t.getAppFn = .const family levels)
    (hargs : t.getAppArgs.size = result.nparams)
    (Hhit : result.restoreNestedNode prodEnv Hopen.params auxRec t =
      some restored)
    (suffixDomains : List VExpr) :
    TrExprS venv lparams
        (abstractForallContext suffixDomains
          (abstractForallContext Haux.domains []))
        (restored.abstractList Hopen.selection.fvars suffixDomains.length)
        (Haux.residualTarget.liftN suffixDomains.length 0) ∧
      venv.IsType lparams.length
        (abstractForallContext suffixDomains
          (abstractForallContext Haux.domains [])).toCtx
        (Haux.residualTarget.liftN suffixDomains.length 0) := by
  have Hexact := restoreNestedNode_family_exactParams result prodEnv
    Hopen.params auxRec t e family levels hhead hrec hfind hargs
  have hrestored : restored =
      (e.abstract result.params).instantiateRev Hopen.params :=
    Option.some.inj (Hhit.symm.trans Hexact)
  subst restored
  exact Hopen.auxiliaryTypedUnder Hlower selection Haux henv family hfind
    suffixDomains

theorem NestedRestorationOpening.exactFamilyHitAbstractTypeTranslation
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.Ordered)
    (family : Name) (levels : List Level)
    (hfind : result.aux2nested.find? family = some e)
    (hrec : auxRec.find? family = none)
    (t restored : Expr)
    (hhead : t.getAppFn = .const family levels)
    (hargs : t.getAppArgs.size = result.nparams)
    (Hhit : result.restoreNestedNode prodEnv Hopen.params auxRec t =
      some restored)
    (suffixDomains : List VExpr) :
    Expr.AbstractTypeTranslation venv lparams
      (abstractForallContext suffixDomains
        (abstractForallContext Haux.domains []))
      (restored.abstractList Hopen.selection.fvars suffixDomains.length) := by
  rcases Hopen.exactFamilyHitTypedUnder Hlower selection Haux henv family
      levels hfind hrec t restored hhead hargs Hhit suffixDomains with
    ⟨Htr, Htype⟩
  exact ⟨_, Htr, Htype⟩

/-- Context-normalized form of the exact-family interpreter.  The semantic
common-parameter domains are the initial prefix of the restored recursor;
`suffixDomains` are precisely the binders already traversed by the suffix
telescope fold. -/
theorem NestedRestorationOpening.exactFamilyHitAbstractTypeTranslationAtPrefix
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.Ordered)
    (family : Name) (levels : List Level)
    (hfind : result.aux2nested.find? family = some e)
    (hrec : auxRec.find? family = none)
    (t restored : Expr)
    (hhead : t.getAppFn = .const family levels)
    (hargs : t.getAppArgs.size = result.nparams)
    (Hhit : result.restoreNestedNode prodEnv Hopen.params auxRec t =
      some restored)
    (suffixDomains : List VExpr) :
    Expr.AbstractTypeTranslation venv lparams
      (abstractForallContext (Haux.domains ++ suffixDomains) [])
      (restored.abstractList Hopen.selection.fvars suffixDomains.length) := by
  simpa only [abstractForallContext_append] using
    Hopen.exactFamilyHitAbstractTypeTranslation Hlower selection Haux henv
      family levels hfind hrec t restored hhead hargs Hhit suffixDomains

/-- Lookup-driven form used by a recursor-domain callback.  Validation of all
cached auxiliaries supplies the particular closed translation selected by the
same `aux2nested` lookup that triggered the executable restoration hit. -/
theorem NestedRestorationOpening.exactFamilyHitOfTranslationsAtPrefix
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Htranslations : ClosedNestedAuxiliaryTranslations venv lparams result
      selection)
    (henv : venv.Ordered)
    (family : Name) (levels : List Level) (e : Expr)
    (hfind : result.aux2nested.find? family = some e)
    (hrec : auxRec.find? family = none)
    (t restored : Expr)
    (hhead : t.getAppFn = .const family levels)
    (hargs : t.getAppArgs.size = result.nparams)
    (Hhit : result.restoreNestedNode prodEnv Hopen.params auxRec t =
      some restored)
    (suffixDomains : List VExpr) :
    ∃ parameterDomains,
      parameterDomains.length = result.params.size ∧
      Expr.AbstractTypeTranslation venv lparams
        (abstractForallContext (parameterDomains ++ suffixDomains) [])
        (restored.abstractList Hopen.selection.fvars
          suffixDomains.length) := by
  rcases Htranslations family e hfind with ⟨Haux⟩
  exact ⟨Haux.domains, Haux.arity,
    Hopen.exactFamilyHitAbstractTypeTranslationAtPrefix Hlower selection Haux
      henv family levels hfind hrec t restored hhead hargs Hhit
      suffixDomains⟩

theorem NestedLoweringResultClosed.validateNestedAuxiliariesWF
    (H : NestedLoweringResultClosed sourceEnv loweringFuel nparams sourceTypes
      initialState res)
    (hvalid : CheckingEnv.Valid safety restoredEnv venv)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv) :
    (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
      res).WF fun _ =>
        ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res := by
  rcases H with ⟨finalState, Hrun, Hcache, _Hparams⟩
  apply Hrun.validateNestedAuxiliariesWF hvalid mlctx hmlctx hlctx hfresh
  have hfvars : res.lctx.fvars = mlctx.vlctx.fvars := by
    rw [← hlctx, hmlctx.tr.fvars_eq]
  intro nested name hentry
  simpa [hfvars] using Hcache nested name hentry

theorem NestedLoweringResult.resultRestorable
    (H : NestedLoweringResult env fuel nparams types initialState result) :
    ∀ type ∈ result.types, RestorableInductiveType nparams type := by
  rcases H with ⟨finalState, Hrun⟩
  exact Hrun.resultRestorable

theorem NestedLoweringResult.resultNParams
    (H : NestedLoweringResult env fuel nparams types initialState result) :
    result.nparams = nparams := by
  rcases H with ⟨finalState, Hrun⟩
  exact Hrun.resultNParams

theorem NestedLoweringResult.resultAuxMap
    (H : NestedLoweringResult env fuel nparams types initialState result) :
    ∃ finalState,
      NestedLoweringRun env fuel nparams types initialState
        (result, finalState) ∧
      result.aux2nested = finalState.nestedAux.foldl
        (fun map (entry : Expr × Name) => map.insert entry.2 entry.1) {} := by
  rcases H with ⟨finalState, Hrun⟩
  exact ⟨finalState, Hrun, Hrun.resultAuxMap⟩

theorem NestedLoweringResult.resultNestedAuxLE
    (H : NestedLoweringResult env fuel nparams types initialState result) :
    ∃ finalState,
      NestedLoweringRun env fuel nparams types initialState
        (result, finalState) ∧
      NestedAuxLE initialState finalState := by
  rcases H with ⟨finalState, Hrun⟩
  exact ⟨finalState, Hrun, Hrun.resultNestedAuxLE⟩

theorem NestedLoweringResult.sourceTranslationAt
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveTranslation env params nparams sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target ∧
      ∃ finalState,
        NestedLoweringRun env fuel nparams sourceTypes
          { initialState with newTypes := sourceTypes.toArray }
          (result, finalState) ∧
        NestedAuxLE loweredState finalState := by
  rcases H with ⟨finalState, Hrun⟩
  have hjInitial : j <
      ({ initialState with
        newTypes := sourceTypes.toArray }).newTypes.size := by
    simpa using hj
  rcases Hrun.translationAtInitial hjInitial with
    ⟨params, stepState, target, loweredState, hparams, Htranslated,
      htarget, Haux⟩
  exact ⟨params, stepState, target, loweredState, hparams,
    by simpa using Htranslated, htarget, finalState, Hrun, Haux⟩

/-- End-to-end source-family mapping, with the one still-unproved production
fresh-name obligation exposed at the final cache boundary rather than hidden
inside the semantic certificate. -/
theorem NestedLoweringResult.sourceFinalMappingAt
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hj : j < sourceTypes.length) :
    ∃ finalState,
      NestedLoweringRun env fuel nparams sourceTypes
        { initialState with newTypes := sourceTypes.toArray }
        (result, finalState) ∧
      ((finalState.nestedAux.toList.map Prod.snd).Nodup →
        ∃ params stepState target loweredState,
          params.size = nparams ∧
          LoweredInductiveMapping env params nparams result sourceTypes[j]
            stepState (target, loweredState) ∧
          result.types[j]? = some target) := by
  rcases H with ⟨finalState, Hrun⟩
  refine ⟨finalState, Hrun, ?_⟩
  intro hauxNames
  have hjInitial : j <
      ({ initialState with
        newTypes := sourceTypes.toArray }).newTypes.size := by
    simpa using hj
  rcases Hrun.finalMappingAtInitial hauxNames hjInitial with
    ⟨params, stepState, target, loweredState, hparams, Hmapped, htarget⟩
  exact ⟨params, stepState, target, loweredState, hparams,
    by simpa using Hmapped, htarget⟩

/-- The source-family mapping with cache uniqueness discharged from the empty
production cache and the isolated suffix-index primitive law. -/
theorem NestedLoweringResult.sourceFinalMappingAtOfIndexFaithful
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hindex : AppendIndexAfterIndexFaithful)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.sourceFinalMappingAt hj with ⟨finalState, Hrun, Hmapped⟩
  apply Hmapped
  apply Hrun.resultNamesNodupOfEmpty Hindex
  simpa using hempty

theorem NestedLoweringResult.sourceFinalMappingAtFresh
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target :=
  H.sourceFinalMappingAtOfIndexFaithful appendIndexAfterIndexFaithful hempty hj

/-- Fresh-cache source mapping with the lowering parameters identified with
the parameters retained by the production restoration record. -/
theorem NestedLoweringResult.sourceFinalMappingAtFreshAligned
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      result.params = params ∧
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H with ⟨finalState, Hrun⟩
  have hjInitial : j <
      ({ initialState with
        newTypes := sourceTypes.toArray }).newTypes.size := by
    simpa using hj
  apply Hrun.finalMappingAtInitialAligned _ hjInitial
  apply Hrun.resultNamesNodupOfEmpty appendIndexAfterIndexFaithful
  simpa using hempty

/-- Every original family retains its positional slot in the expanded
lowering result, so the original mutual block is no longer than that result. -/
theorem NestedLoweringResult.sourceTypes_length_le
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result) :
    sourceTypes.length ≤ result.types.length := by
  by_contra hle
  have hj : result.types.length < sourceTypes.length := Nat.lt_of_not_ge hle
  rcases H.sourceTranslationAt (j := result.types.length) hj with
    ⟨_params, _stepState, _target, _loweredState, _hparams, _Htranslation,
      htarget, _finalState, _Hrun, _Haux⟩
  exact (Nat.lt_irrefl result.types.length)
    (_root_.getElem?_eq_some_iff.mp htarget).1

/-- Lowering preserves the constructor count of every original family and
only appends auxiliary families.  Consequently the source constructor batch
is a cardinality prefix of the expanded lowered batch. -/
theorem NestedLoweringResult.sourceOwnedConstructors_length_le
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[]) :
    (Lean4Lean.VerifyInductive.ownedConstructors sourceTypes).length ≤
      (Lean4Lean.VerifyInductive.ownedConstructors result.types).length := by
  have htypes := H.sourceTypes_length_le
  have hprefix :
      (result.types.take sourceTypes.length).map
          (fun type => type.ctors.length) =
        sourceTypes.map (fun type => type.ctors.length) := by
    apply List.ext_getElem
    · simp [List.length_take, htypes]
    · intro i hresult hsource
      rw [List.getElem_map, List.getElem_take, List.getElem_map]
      rcases H.sourceFinalMappingAtFresh hempty (j := i) (by simpa using hsource)
          with ⟨_params, _stepState, target, _loweredState, _hparams,
            Hmapping, htarget⟩
      obtain ⟨hiResult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
      rw [htargetEq]
      exact Hmapping.constructors.length
  have hsplit := congrArg
    (fun types : List InductiveType =>
      (types.map (fun type => type.ctors.length)).sum)
    (List.take_append_drop sourceTypes.length result.types)
  simp only [List.map_append, List.sum_append] at hsplit
  rw [hprefix] at hsplit
  simp only [Lean4Lean.VerifyInductive.ownedConstructors,
    List.length_flatMap, List.length_map]
  omega

/-- Transport an installed lowered recursor shape to its original source
family.  Lowering and the two declaration translations discharge owner/name,
universe, parameter, and prefix-cardinality compatibility; only equality of
the independently recovered source/lowered index counts remains explicit. -/
theorem VInductDecl.NestedRecursorShape.toSourceOfLowering
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (Hsource : TrInductDeclCore sourceVEnv lparams nparams sourceTypes
      isUnsafe sourceDecl sourceEnvTypes sourceEnvCtors)
    (Hexpanded : TrInductDeclCore expandedVEnv lparams nparams result.types
      isUnsafe loweredDecl expandedEnvTypes expandedEnvCtors)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hsourceDecl : familyIdx < sourceDecl.types.length)
    (hloweredDecl : familyIdx < loweredDecl.types.length)
    {recursor : VConstVal}
    (Hshape : loweredDecl.NestedRecursorShape
      (loweredDecl.types[familyIdx]'hloweredDecl) recursor)
    (hindices : (sourceDecl.types[familyIdx]'hsourceDecl).numIndices =
      (loweredDecl.types[familyIdx]'hloweredDecl).numIndices) :
    Nonempty (sourceDecl.NestedRecursorShape
      (sourceDecl.types[familyIdx]'hsourceDecl) recursor) := by
  rcases Hlower.sourceFinalMappingAtFresh hempty hfamily with
    ⟨_params, _stepState, target, _loweredState, _hparams, Hmapping,
      htarget⟩
  obtain ⟨hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hsource familyIdx hfamily hsourceDecl
  have HexpandedType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hexpanded familyIdx hresult hloweredDecl
  have hloweredOwnerName :
      (loweredDecl.types[familyIdx]'hloweredDecl).name =
        sourceTypes[familyIdx].name := by
    exact HexpandedType.header.name.trans <| by
      simpa [htargetEq] using Hmapping.name
  have hsourceOwnerName :
      (sourceDecl.types[familyIdx]'hsourceDecl).name =
        sourceTypes[familyIdx].name := HsourceType.header.name
  have hshapeIdx : Hshape.ownerIdx = familyIdx := by
    exact Lean4Lean.VerifyInductive.VInductDecl.NestedRecursorShape.ownerIdx_eq_of_name
      Hshape familyIdx hloweredDecl Hshape.name
        (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup Hexpanded)
  refine ⟨Hshape.ofCompatible ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [hshapeIdx] using hsourceDecl
  · simpa [hshapeIdx]
  · rw [Hshape.name]
    simp only [VInductDecl.recursorName_eq_mkRecName]
    exact congrArg Lean.mkRecName (hloweredOwnerName.trans hsourceOwnerName.symm)
  · have huvars := Hshape.uvars
    rw [Hexpanded.uvars] at huvars
    rw [Hsource.uvars]
    exact huvars
  · exact Hsource.nparams.trans Hexpanded.nparams.symm
  · calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := Hlower.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hexpanded
      _ ≤ Hshape.motives.length := Hshape.source_motives
  · calc
      sourceDecl.ownedConstructors.length =
          (Lean4Lean.VerifyInductive.ownedConstructors sourceTypes).length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          Hsource).symm
      _ ≤ (Lean4Lean.VerifyInductive.ownedConstructors result.types).length :=
        Hlower.sourceOwnedConstructors_length_le hempty
      _ = loweredDecl.ownedConstructors.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          Hexpanded
      _ ≤ Hshape.minors.length := Hshape.source_minors
  · exact hindices

/-- Closed-lowering specialization of the aligned source mapping.  It
exposes the exact duplicate-free free-variable presentation of the final
parameter array needed by abstraction/instantiation cancellation. -/
theorem NestedLoweringResultClosed.sourceFinalMappingAtFreshAligned
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ fvars : List FVarId, ∃ stepState target loweredState,
      result.params = (fvars.map Expr.fvar).toArray ∧
      fvars.Nodup ∧
      result.params.size = nparams ∧
      LoweredInductiveMapping env result.params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.resultParamsNodup with ⟨fvars, hresultParams, hnodup⟩
  rcases H.toResult.sourceFinalMappingAtFreshAligned hempty hj with
    ⟨params, stepState, target, loweredState, hparams, hsize,
      Hmapping, htarget⟩
  rw [← hparams] at Hmapping
  exact ⟨fvars, stepState, target, loweredState, hresultParams, hnodup,
    by simpa [hparams] using hsize, Hmapping, htarget⟩

/-- Original family headers need no semantic restoration: lowering preserves
them verbatim, so the positional translation proved for the lowered block is
already the independently checked translation of the corresponding source
header.  This theorem deliberately uses the list position fixed by the
lowering trace, rather than recovering the owner by name. -/
theorem NestedLoweringResultClosed.sourceHeaderTranslationAtFresh
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (Hcore : TrInductDeclCore sourceVEnv lparams nparams result.types
      isUnsafe decl envTypes envCtors)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    ∃ hdecl : familyIdx < decl.types.length,
      TrSourceConst sourceVEnv lparams sourceTypes[familyIdx].name
        sourceTypes[familyIdx].type
        (decl.types[familyIdx]'hdecl).toVConstVal := by
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hsourceCore, htargetEq⟩ :=
    _root_.getElem?_eq_some_iff.mp htarget
  have hdecl : familyIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hcore]
    exact hsourceCore
  have Hheader :=
    (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hcore familyIdx
      hsourceCore hdecl).header
  refine ⟨hdecl, ?_⟩
  rw [← Hmapping.name, ← Hmapping.type]
  simpa [htargetEq] using Hheader

/-- End-to-end positional constructor mapping for an original source family.
This is the alignment consumed by restoration: it identifies the exact
lowered constructor at the same family and constructor indices while retaining
the final parameter presentation needed by the expression inverse. -/
theorem NestedLoweringResultClosed.sourceConstructorMappingAtFreshAligned
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (familyIdx ctorIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hctor : ctorIdx < sourceTypes[familyIdx].ctors.length) :
    ∃ fvars : List FVarId, ∃ target sourceCtor targetCtor before after,
      result.params = (fvars.map Expr.fvar).toArray ∧
      fvars.Nodup ∧
      result.params.size = nparams ∧
      SourceConstructorSyntax sourceTypes[familyIdx].ctors[ctorIdx] ∧
      sourceTypes[familyIdx].ctors[ctorIdx]? = some sourceCtor ∧
      target.ctors[ctorIdx]? = some targetCtor ∧
      LoweredConstructorMapping env result.params nparams result sourceCtor
        before (targetCtor, after) ∧
      result.types[familyIdx]? = some target := by
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨fvars, stepState, target, loweredState, hparams, hnodup, hsize,
      Hmapping, htarget⟩
  rcases Hmapping.constructors.mappingAt ctorIdx hctor with
    ⟨sourceCtor, targetCtor, before, after, hsourceCtor, htargetCtor,
      HctorMapping⟩
  exact ⟨fvars, target, sourceCtor, targetCtor, before, after, hparams,
    hnodup, hsize,
    (Hsources.getElem familyIdx hfamily).constructors.getElem ctorIdx hctor,
    hsourceCtor, htargetCtor, HctorMapping, htarget⟩

/-- End-to-end alignment of one original source family's lowering with the
exact constructor-restoration fold selected by production.  All concrete
`oldInfo.type = lowered.type` facts are consequences of the verified lowered
installation; the returned certificate retains only the genuinely semantic
source-to-abstract constructor work for the next layer. -/
theorem NestedLoweringResultClosed.sourceConstructorRestorationTraceAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) :
    ∃ fvars : List FVarId, ∃ stepState target loweredState,
      result.params = (fvars.map Expr.fvar).toArray ∧
      fvars.Nodup ∧
      result.params.size = nparams ∧
      result.types[familyIdx]? = some target ∧
      Hstep.oldInfo.ctors = target.ctors.map (fun ctor => ctor.name) ∧
      ∃ Hmappings : LoweredConstructorMappings loweredSourceEnv result.params
          nparams result sourceTypes[familyIdx].ctors stepState
            (target.ctors, loweredState),
        ∃ Htrace : StateForMTrace
          (RestoredConstructorStep result loweredEnv)
          (target.ctors.map (fun ctor => ctor.name))
          Hstep.restored.headerEnv Hstep.restored.constructorEnv,
          RestoredConstructorMappingTrace result loweredSourceEnv loweredEnv
            result.params nparams c.safety c.lparams
              sourceTypes[familyIdx].ctors stepState target.ctors loweredState
              Hstep.restored.headerEnv Hstep.restored.constructorEnv := by
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨fvars, stepState, target, loweredState, hparams, hnodup, hsize,
      Hmapping, htarget⟩
  have htargetMem : target ∈ result.types.toArray.toList := by
    simpa using List.mem_of_getElem? htarget
  have hctorNames : Hstep.oldInfo.ctors =
      target.ctors.map (fun ctor => ctor.name) :=
    Hstep.oldConstructors_eq_ofInstalled Hc Hprod htargetMem
      Hmapping.name.symm
  have Htrace : StateForMTrace
      (RestoredConstructorStep result loweredEnv)
      (target.ctors.map (fun ctor => ctor.name)) Hstep.restored.headerEnv
        Hstep.restored.constructorEnv := by
    rw [← hctorNames]
    exact Hstep.restored.constructors
  have Haligned := RestoredConstructorMappingTrace.ofInstalled Hprod
    htargetMem Hmapping.constructors Htrace (by
      intro targetCtor htargetCtor
      exact htargetCtor)
  exact ⟨fvars, stepState, target, loweredState, hparams, hnodup, hsize,
    htarget, hctorNames, Hmapping.constructors, Htrace, Haligned⟩

/-- Production restoration never renames the primary recursor of an
original mutual-family member.  Original families occupy positions strictly
before the auxiliary suffix from which `mkAuxRecNameMap` is built, and the
installed mutual-family metadata proves that these positions are distinct. -/
theorem NestedLoweringResultClosed.sourceRecursorUnmappedAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.find?
      (Lean.mkRecName sourceTypes[familyIdx].name) = none := by
  rcases H with ⟨finalState, Hrun, Hcache, Hparams⟩
  rcases Hrun.source with
    ⟨main, rest, tail, paramsState, lctx, params, hsource, Hopening,
      hinitial, hinitialAux, hinitialNext, Hctx, Hselection, Hqueue⟩
  subst sourceTypes
  have Hclosed : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      (main :: rest)
      { initialState with newTypes := (main :: rest).toArray } result :=
    ⟨finalState, Hrun, Hcache, Hparams⟩
  rcases Hclosed.sourceFinalMappingAtFreshAligned hempty (j := 0) (by simp) with
    ⟨_mainFVars, _mainState, mainTarget, _mainLoweredState, _mainParams,
      _mainNodup, _mainSize, Hmain, hmainTarget⟩
  have hmainMem : mainTarget ∈ result.types.toArray.toList := by
    simpa using List.mem_of_getElem? hmainTarget
  rcases Hprod.findSourceHeader Hc hmainMem with
    ⟨mainInfo, hmainFind, _hmainCtors, hall⟩
  have hmainFind' :
      loweredEnv.find? main.name = some (.inductInfo mainInfo) := by
    have hmainName : mainTarget.name = main.name := by
      simpa using Hmain.name
    rw [← hmainName]
    exact hmainFind
  apply mkAuxRecNameMap_recMap_find_none main rest loweredEnv mainInfo
    hmainFind'
  intro hquery
  rcases List.mem_map.mp hquery with ⟨suffixName, hsuffix, hrecName⟩
  have hsuffixName : suffixName = (main :: rest)[familyIdx].name :=
    mkRecName_injective (hrecName.trans rfl)
  rcases List.mem_drop_iff_getElem.mp hsuffix with
    ⟨suffixIdx, hsuffixBound, hsuffixGet⟩
  rcases Hclosed.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_familyFVars, _familyState, familyTarget, _familyLoweredState,
      _familyParams, _familyNodup, _familySize, Hfamily, hfamilyTarget⟩
  have hfamilyInfo : mainInfo.all[familyIdx]? =
      some (main :: rest)[familyIdx].name := by
    rw [hall]
    rw [List.getElem?_map, hfamilyTarget]
    simp only [Option.map_some, Option.some.injEq]
    exact Hfamily.name
  have hsuffixInfo :
      mainInfo.all[(main :: rest).length + suffixIdx]? =
        some (main :: rest)[familyIdx].name := by
    exact _root_.getElem?_eq_some_iff.mpr
      ⟨by omega, hsuffixGet.trans hsuffixName⟩
  have hfamilyResultBound : familyIdx < result.types.length :=
    (_root_.getElem?_eq_some_iff.mp hfamilyTarget).1
  have hindexEq : familyIdx = (main :: rest).length + suffixIdx :=
    (List.getElem?_inj (l := mainInfo.all)
      (i := familyIdx) (j := (main :: rest).length + suffixIdx)
      (by simpa [hall] using hfamilyResultBound)
      (Hprod.closed main.name mainInfo hmainFind').names).mp
      (hfamilyInfo.trans hsuffixInfo.symm)
  omega

/-- Interpret one source family's exact constructor-restoration fold using
the independently checked source constructor translations.  Fresh generated
names turn the syntactic no-auxiliary condition into the semantic
disjointness required by the lowering/restoration inverse. -/
theorem NestedLoweringResultClosed.sourceConstructorSemanticsAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv canonicalEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hfamily : familyIdx < sourceTypes.length)
    (Htranslations : List.Forall₂ (fun source constructor =>
      TrSourceConst canonicalEnv c.lparams source.name source.type constructor)
      sourceTypes[familyIdx].ctors constructors)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv canonicalEnv)
    (hempty : initialState.nestedAux = #[])
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) :
    RestoredSourceConstructorTrace c.lparams c.safety canonicalEnv
      Hstep.oldInfo.ctors Hstep.restored.headerEnv
        Hstep.restored.constructorEnv sourceTypes[familyIdx].ctors
          constructors := by
  rcases H.sourceConstructorRestorationTraceAtFresh Hc Hprod hempty
      familyIdx hfamily Hstep with
    ⟨fvars, stepState, target, loweredState, hparams, hnodup, _hsize,
      htarget, hctorNames, Hmappings, Htrace, Haligned⟩
  have Hsyntax := (Hsources.getElem familyIdx hfamily).constructors
  have Hsemantic := Haligned.sourceSemantics Htranslations Hsyntax (by
    intro source hsource
    have HsourceTranslation :=
      Lean4Lean.List.Forall₂.forall_exists_l Htranslations source hsource
    rcases HsourceTranslation with ⟨constructor, _hconstructor, Hsource⟩
    exact (Hsyntax.of_mem hsource).noNestedAux
      |>.restoreSourceDisjointOfFresh Hsource.type.constantsDefined Hfamilies
        Hconstructors) rfl fvars hparams hnodup H.toResult.resultNParams
  simpa [hctorNames] using Hsemantic

/-- Realize one restored primary recursor from the one irreducibly semantic
fact about it: translation of its restored concrete type in the canonical
source environment. Source translation, shared metadata materialization,
lowering, and the generated recursor certificate determine every remaining
name, universe, and telescope-cardinality premise. -/
theorem NestedLoweringResultClosed.sourcePrimaryRecursorRealizationAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hdecl : familyIdx < sourceDecl.types.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv)
    (targetType : VExpr)
    (Htype : TrExprS envCtors Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type targetType) :
    ∃ recursor, Nonempty (SourcePrimaryRecursorRealization sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor envCtors
      recursor) := by
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hresultIdx, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have howner : familyIdx < result.types.toArray.size := by
    simpa using hresultIdx
  have hrecInfo : familyIdx < Hprod.recInfos.size := by
    simpa [Hprod.generated.length] using hentry
  have hloweredDecl : familyIdx < loweredDecl.types.length := by
    simpa [Hprod.cardinality.records] using hrecInfo
  have hdeclLength : sourceDecl.types.length ≤ loweredDecl.types.length := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := H.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
  have hindices : (sourceDecl.types[familyIdx]'hdecl).numIndices =
      Hprod.recInfos[familyIdx]!.indices.size := by
    exact (Hmetadata.numIndices hdeclLength familyIdx hdecl hloweredDecl).trans
      (Hprod.cardinality.indices familyIdx hrecInfo).symm
  have hsourceName : result.types.toArray[familyIdx]!.name =
      sourceTypes[familyIdx].name := by
    have harray : result.types.toArray[familyIdx]! = target := by
      simp [Array.getElem!_eq_getD, Array.getD, howner, hresultIdx,
        htargetEq]
    rw [harray, Hmapping.name]
  have holdRecName : Lean.mkRecName sourceTypes[familyIdx].name =
      Lean.mkRecName result.types.toArray[familyIdx]!.name :=
    congrArg Lean.mkRecName hsourceName.symm
  let recursor : VConstVal := {
    name := sourceDecl.recursorName (sourceDecl.types[familyIdx]'hdecl)
    uvars := Hstep.restored.recursor.oldInfo.levelParams.length
    type := targetType }
  have huvars : recursor.uvars = sourceDecl.uvars ∨
      recursor.uvars = sourceDecl.uvars + 1 := by
    exact Hprod.restoredPrimaryRecursorUvars familyIdx hentry
      Hstep.restored.recursor holdRecName sourceDecl Hsource.uvars
  have hmotives : sourceDecl.types.length ≤
      (Hprod.recInfos.map (·.motive)).size := by
    calc
      sourceDecl.types.length = sourceTypes.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource).symm
      _ ≤ result.types.length := H.toResult.sourceTypes_length_le
      _ = loweredDecl.types.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core
      _ = Hprod.recInfos.size := Hprod.cardinality.records.symm
      _ = (Hprod.recInfos.map (·.motive)).size := by simp
  have hminors : sourceDecl.ownedConstructors.length ≤
      (Hprod.recInfos.flatMap (·.minors)).size := by
    calc
      sourceDecl.ownedConstructors.length =
          (Lean4Lean.VerifyInductive.ownedConstructors sourceTypes).length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          Hsource).symm
      _ ≤ (Lean4Lean.VerifyInductive.ownedConstructors result.types).length :=
        H.toResult.sourceOwnedConstructors_length_le hempty
      _ = loweredDecl.ownedConstructors.length :=
        Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length
          R.core
      _ = (Hprod.recInfos.flatMap (·.minors)).size :=
        Hprod.cardinality.minors.symm
  refine ⟨recursor, ⟨Hprod.restoredSourcePrimaryRecursorRealization
    familyIdx hentry Hstep.restored.recursor holdRecName sourceDecl hdecl
    recursor envCtors rfl huvars rfl H.toResult.resultNParams
    (Hsource.nparams.trans H.toResult.resultNParams.symm) hmotives hminors
    hindices ?_⟩⟩
  simpa [recursor] using Htype

/-- Binder-explicit form of `sourcePrimaryRecursorRealizationAtFresh`.
This is the preferred boundary for the pending nested-restoration transport:
the caller must provide the exact typed restored telescope, rather than an
opaque translation of the whole expression. -/
theorem NestedLoweringResultClosed.sourcePrimaryRecursorRealizationAtFreshOfTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hdecl : familyIdx < sourceDecl.types.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv)
    (targetType : VExpr)
    (Htype : Expr.ForallTelescopeTypeTranslation envCtors
      Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type
      (result.nparams + (Hprod.recInfos.map (·.motive)).size +
        (Hprod.recInfos.flatMap (·.minors)).size +
        Hprod.recInfos[familyIdx]!.indices.size + 1)
      targetType) :
    ∃ recursor, Nonempty (SourcePrimaryRecursorRealization sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor envCtors
      recursor) :=
  H.sourcePrimaryRecursorRealizationAtFresh Hprod Hsource Hmetadata hempty
    familyIdx hfamily hdecl hentry Hstep targetType Htype.translation

/-- Package one original family into the payload consumed by whole-mutual
semantic-trace assembly.  Header and constructor semantics come from the
independent source translation. The source-recursion payload is explicitly
indexed by the original declaration, while the installed expanded declaration
is used only to recover production safety metadata and name preservation. -/
theorem NestedLoweringResultClosed.sourceInductiveSemanticsAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hdecl : familyIdx < sourceDecl.types.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hsource : TrInductiveType sourceVEnv envTypes c.lparams
      sourceTypes[familyIdx] (sourceDecl.types[familyIdx]'hdecl))
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv)
    (HsourceRec : SourcePrimaryRecursorSemantics sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) envCtors)
    (Hrefine : RestoredPrimaryRecursorRefinement Hstep.restored.recursor
      envCtors HsourceRec.recursor) :
    Nonempty (RestoredSourceInductiveSemantics sourceDecl c.lparams c.safety
      sourceVEnv envTypes envCtors Hstep) := by
  rcases H.sourceFinalMappingAtFreshAligned hempty hfamily with
    ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, htarget⟩
  obtain ⟨hresultIdx, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
  have howner : familyIdx < result.types.toArray.size := by simpa using hresultIdx
  have hsourceName : result.types.toArray[familyIdx]!.name =
      sourceTypes[familyIdx].name := by
    have harray : result.types.toArray[familyIdx]! = target := by
      simp [Array.getElem!_eq_getD, Array.getD, howner, hresultIdx,
        htargetEq]
    rw [harray, Hmapping.name]
  have HctorSemantics := H.sourceConstructorSemanticsAtFresh Hc Hprod
    Hsources hfamily Hsource.ctors Hfamilies Hconstructors hempty Hstep
  have hrestoredName : Hstep.restored.recursor.restored.newRecName =
      Lean.mkRecName sourceTypes[familyIdx].name := by
    have hunmapped := H.sourceRecursorUnmappedAtFresh Hc Hprod hempty
      familyIdx hfamily
    rw [Hstep.restored.recursor.restored.mappedName]
    apply Std.TreeMap.getD_eq_fallback_of_contains_eq_false
    change Std.TreeMap.contains
      (show Std.TreeMap Name Name Name.quickCmp from
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2)
        (Lean.mkRecName sourceTypes[familyIdx].name) = false
    rw [Std.TreeMap.contains_eq_isSome_getElem?]
    change ((Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.find?
      (Lean.mkRecName sourceTypes[familyIdx].name)).isSome = false
    rw [hunmapped]
    rfl
  have Hmetadata := Hprod.restoredPrimaryRecursorMetadata familyIdx hentry
    Hstep.restored.recursor (congrArg Lean.mkRecName hsourceName.symm)
  have hownerName : (sourceDecl.types[familyIdx]'hdecl).name =
      sourceTypes[familyIdx].name := by
    simpa using Hsource.header.name
  have HrecName : HsourceRec.recursor.name =
      Hstep.restored.recursor.restored.newRecName := by
    exact HsourceRec.name.trans <| by
      simpa only [VInductDecl.recursorName_eq_mkRecName] using
        (congrArg Lean.mkRecName hownerName).trans hrestoredName.symm
  have HrecWF : HsourceRec.recursor.toVConstant.WF envCtors := by
    exact HsourceRec.isType
  have HrecSemantics : RestoredPrimaryRecursorSemantics sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) c.safety
      Hstep.restored.recursor envCtors := {
    recursor := HsourceRec.recursor
    safety_le := Hmetadata.1
    uvars := Hrefine.uvars
    type := Hrefine.type
    name := HrecName
    wf := HrecWF
    shape := HsourceRec.shape }
  exact ⟨{
    owner := sourceDecl.types[familyIdx]'hdecl
    header := Hsource.header
    constructors := HctorSemantics
    recursor := HrecSemantics }⟩

/-- Assemble the independent source declaration semantics over the exact
production mutual-restoration trace. The lowered and source declarations are
separate indices, which is essential when nested lowering appends auxiliary
families. The two per-family inputs expose the precise verification boundary:
independent source-recursion semantics and executable-to-source refinement.
Headers, constructors, production metadata, and all list/state ordering are
derived here. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (HsourceRecursors : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (_hentry : familyIdx < Hprod.entries.length),
      Nonempty (SourcePrimaryRecursorSemantics sourceDecl
        (sourceDecl.types[familyIdx]'hdecl) envCtors))
    (HrecursorRefinements : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget)
      (HsourceRec : SourcePrimaryRecursorSemantics sourceDecl
        (sourceDecl.types[familyIdx]'hdecl) envCtors),
      RestoredPrimaryRecursorRefinement Hstep.restored.recursor envCtors
        HsourceRec.recursor) :
    ∃ owners recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety sourceVEnv
        envTypes envCtors Hrestored.inductives owners recursors := by
  apply Hrestored.inductives.sourceInductiveSemanticTrace
  intro indType stepSource stepTarget Hstep hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨familyIdx, hfamily, heq⟩
  subst indType
  have hdecl : familyIdx < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  rcases H.toResult.sourceFinalMappingAtFresh hempty hfamily with
    ⟨_mappingParams, _mappingState, _mappingTarget, _mappingLowered,
      _mappingSize, _mapping, htarget⟩
  have hresult : familyIdx < result.types.length :=
    (_root_.getElem?_eq_some_iff.mp htarget).1
  have hentry : familyIdx < Hprod.entries.length := by
    rw [Hprod.generated.length, Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hresult
  rcases HsourceRecursors familyIdx hfamily hdecl hentry with
    ⟨HsourceRec⟩
  exact H.sourceInductiveSemanticsAtFresh Hc Hprod Hsources hempty
    familyIdx hfamily hdecl hentry
    (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource familyIdx
      hfamily hdecl) Hfamilies Hconstructors Hstep
    HsourceRec
    (HrecursorRefinements familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep HsourceRec)

/-- Joint recursor-realization form of `sourceSemanticTraceAtFresh`.  This is
the preferred executable/specification boundary: each operational restoration
step must produce one source semantic witness together with a refinement of
that very same recursor, rather than satisfying two independently quantified
callbacks. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceAtFreshOfRealizations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (Hrealizations : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget),
      ∃ recursor, Nonempty (SourcePrimaryRecursorRealization sourceDecl
        (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor envCtors
        recursor)) :
    ∃ owners recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes envCtors Hrestored.inductives owners recursors := by
  apply Hrestored.inductives.sourceInductiveSemanticTrace
  intro indType stepSource stepTarget Hstep hmem
  rcases List.mem_iff_getElem.mp hmem with ⟨familyIdx, hfamily, heq⟩
  subst indType
  have hdecl : familyIdx < sourceDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  rcases H.toResult.sourceFinalMappingAtFresh hempty hfamily with
    ⟨_mappingParams, _mappingState, _mappingTarget, _mappingLowered,
      _mappingSize, _mapping, htarget⟩
  have hresult : familyIdx < result.types.length :=
    (_root_.getElem?_eq_some_iff.mp htarget).1
  have hentry : familyIdx < Hprod.entries.length := by
    rw [Hprod.generated.length, Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hresult
  rcases Hrealizations familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep with ⟨recursor, ⟨Hrealization⟩⟩
  have Hrefinement := Hrealization.refinement
  rw [← Hrealization.recursor_eq] at Hrefinement
  exact H.sourceInductiveSemanticsAtFresh Hc Hprod Hsources hempty
    familyIdx hfamily hdecl hentry
    (Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource familyIdx
      hfamily hdecl) Hfamilies Hconstructors Hstep
    Hrealization.source Hrefinement

/-- Whole-mutual source semantics with the callback surface reduced to the
canonical translation of each restored concrete primary-recursor type.
Source/lowered index arities are derived once from their shared materialized
metadata prefix; every other realization field follows from the verified
lowering and recursor phases. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceAtFreshOfTranslatedTypes
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (HtranslatedTypes : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget),
      ∃ targetType,
        TrExprS envCtors Hstep.restored.recursor.oldInfo.levelParams []
          Hstep.restored.recursor.restored.newInfo.type targetType) :
    ∃ owners recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes envCtors Hrestored.inductives owners recursors := by
  apply H.sourceSemanticTraceAtFreshOfRealizations Hc Hprod Hsources Hsource
    Hfamilies Hconstructors hempty Hrestored
  intro familyIdx hfamily hdecl hentry stepSource stepTarget Hstep
  rcases HtranslatedTypes familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep with ⟨targetType, Htype⟩
  exact H.sourcePrimaryRecursorRealizationAtFresh Hprod Hsource Hmetadata
    hempty familyIdx hfamily hdecl hentry Hstep targetType Htype

/-- Preferred whole-mutual boundary for canonical restored recursor typing.
The remaining family-wise obligation is decomposed at every forall binder and
already includes typehood of every domain and the final result. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceAtFreshOfTelescopeTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result loweredEnv envTypes)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv
      loweredSourceEnv (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
      allIndNames sourceTypes auxRecNames out)
    (HtelescopeTypes : ∀ familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget),
      ∃ targetType, Expr.ForallTelescopeTypeTranslation envCtors
        Hstep.restored.recursor.oldInfo.levelParams []
        Hstep.restored.recursor.restored.newInfo.type
        (result.nparams + (Hprod.recInfos.map (·.motive)).size +
          (Hprod.recInfos.flatMap (·.minors)).size +
          Hprod.recInfos[familyIdx]!.indices.size + 1)
        targetType) :
    ∃ owners recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes envCtors Hrestored.inductives owners recursors := by
  apply H.sourceSemanticTraceAtFreshOfRealizations Hc Hprod Hsources Hsource
    Hfamilies Hconstructors hempty Hrestored
  intro familyIdx hfamily hdecl hentry stepSource stepTarget Hstep
  rcases HtelescopeTypes familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep with ⟨targetType, Htype⟩
  exact H.sourcePrimaryRecursorRealizationAtFreshOfTelescope Hprod Hsource
    Hmetadata hempty familyIdx hfamily hdecl hentry Hstep targetType Htype

theorem NestedLoweringResult.sourceTypeName
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams types
      { initialState with newTypes := types.toArray } result)
    (hsource : source ∈ types) :
    ∃ lowered ∈ result.types, lowered.name = source.name := by
  rcases H with ⟨finalState, Hrun⟩
  apply Hrun.preservesInitialTypeName
  exact ⟨source, by simpa using hsource, rfl⟩

/-- Specialize `restorationSources` from the installed lowered family list
back to each original source family, using the lowering trace for name
preservation and target constructor telescopes. -/
theorem RecursorPhasesResult.restorationSourcesOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorPhasesResult R outEnv)
    (Hlower : NestedLoweringResult prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res) :
    ∀ owner, owner ∈ sourceTypes →
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
  have Hlowered := H.restorationSources Hc (by
    intro lowered hlowered ctor hctor
    apply Hlower.resultRestorable lowered (by simpa using hlowered)
    exact hctor)
  intro owner howner
  rcases Hlower.sourceTypeName howner with
    ⟨lowered, hlowered, hname⟩
  simpa [hname] using Hlowered lowered (by simpa using hlowered)

/-- Every auxiliary recursor selected by the production restoration map is
the installed recursor of one of the dynamically generated lowered families.
Consequently its type and every rule RHS satisfy the telescope discipline
required by restoration. -/
theorem RecursorPhasesResult.auxRestorationSourcesOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorPhasesResult R outEnv)
    (Hlower : NestedLoweringResult prodEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res) :
    ∀ recName,
      recName ∈ (Lean4Lean.mkAuxRecNameMap outEnv sourceTypes).1 →
      ∃ oldInfo : RecursorVal,
        outEnv.find? recName = some (.recInfo oldInfo) ∧
        RestoreTelescope oldInfo.type nparams ∧
        ∀ rule ∈ oldInfo.rules,
          RestoreTelescope rule.rhs nparams := by
  rcases Hlower with ⟨finalState, Hrun⟩
  rcases Hrun.source with
    ⟨main, rest, tail, paramsState, lctx, params, hsource, Hopening,
      hinitial, _hinitialAux, _hinitialNext, _Hctx, _Hselection, Hqueue⟩
  subst sourceTypes
  have Hrestorable := H.restorationSources Hc (by
    intro lowered hlowered ctor hctor
    apply Hrun.resultRestorable lowered (by simpa using hlowered)
    exact hctor)
  have hmainPresent :
      NewTypeNamePresent
        { initialState with newTypes := (main :: rest).toArray } main.name :=
    ⟨main, by simp, rfl⟩
  rcases Hrun.preservesInitialTypeName hmainPresent with
    ⟨loweredMain, hloweredMain, hmainName⟩
  rcases H.findSourceHeader Hc (by simpa using hloweredMain) with
    ⟨mainInfo, hmainFind, _hctors, hall⟩
  have hmainFind' :
      outEnv.find? main.name = some (.inductInfo mainInfo) := by
    simpa [hmainName] using hmainFind
  have hall' :
      mainInfo.all = res.types.map (fun type => type.name) := by
    simpa using hall
  intro recName hrecName
  rcases mkAuxRecNameMap_recNames_mem main rest outEnv mainInfo hmainFind'
      hrecName with ⟨familyName, hfamilyName, rfl⟩
  rw [hall'] at hfamilyName
  rcases List.mem_map.mp hfamilyName with
    ⟨family, hfamily, rfl⟩
  rcases Hrestorable family (by simpa using hfamily) with
    ⟨_oldIndInfo, _hindFind, _hctors, recInfo, hrecFind, hrecType,
      hrecRules⟩
  exact ⟨recInfo, hrecFind, hrecType, hrecRules⟩

/-- End-to-end verifier for production nested restoration after a verified
lowered installation. Both declaration-source arguments are now consequences
of lowering and installation; only the subsequent auxiliary type-checking
pass remains parameterized by its own semantic postcondition. -/
theorem Environment.restoreNestedAfterInstall.ofLoweringWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorPhasesResult R loweredEnv)
    (Hlower : NestedLoweringResult sourceProdEnv loweringFuel nparams
      sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res)
    (lparams : List Name) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (Validated : Environment → Prop)
    (Hvalidate : ∀ restoredEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv sourceProdEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) sourceTypes
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
        ((), restoredEnv)) →
      (Lean4Lean.validateNestedAuxiliaries restoredEnv lparams safety fuel
        res).WF fun _ => Validated restoredEnv) :
    (Environment.restoreNestedAfterInstall sourceProdEnv loweredEnv lparams
      sourceTypes safety allowPrimitive fuel res).WF fun outEnv =>
        RestoredAfterInstallResult res sourceProdEnv loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
          Validated outEnv := by
  have hnparams : res.nparams = nparams := Hlower.resultNParams
  apply Environment.restoreNestedAfterInstall.WF sourceProdEnv loweredEnv
    lparams sourceTypes safety allowPrimitive fuel res
  · intro owner howner
    simpa [hnparams] using
      H.restorationSourcesOfLowering Hc Hlower owner howner
  · intro recName hrecName
    simpa [hnparams] using
      H.auxRestorationSourcesOfLowering Hc Hlower recName hrecName
  · exact Hvalidate

/-- Closed-lowering specialization of `ofLoweringWF`.  The final auxiliary
validation pass is no longer a semantic callback: every witness in the
production `aux2nested` map is known to be scoped by the exact local context
returned by lowering, so the ordinary type-checker soundness theorem applies
directly in the restored environment. -/
theorem Environment.restoreNestedAfterInstall.ofLoweringClosedWF
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : RecursorPhasesResult R loweredEnv)
    (Hlower : NestedLoweringResultClosed sourceProdEnv loweringFuel nparams
      sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res)
    (lparams : List Name) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (venv : VEnv)
    (hvalid : ∀ restoredEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv sourceProdEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) sourceTypes
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
        ((), restoredEnv)) →
      CheckingEnv.Valid safety restoredEnv venv)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv) :
    (Environment.restoreNestedAfterInstall sourceProdEnv loweredEnv lparams
      sourceTypes safety allowPrimitive fuel res).WF fun outEnv =>
        RestoredAfterInstallResult res sourceProdEnv loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
          (fun _ =>
            ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res ∧
            ∃ selection : LocalForallSelection res.lctx res.params,
              ClosedNestedAuxiliaryTranslations venv lparams res selection)
          outEnv := by
  apply Environment.restoreNestedAfterInstall.ofLoweringWF Hc H
    Hlower.toResult lparams safety allowPrimitive fuel
    (fun _ =>
      ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res ∧
      ∃ selection : LocalForallSelection res.lctx res.params,
        ClosedNestedAuxiliaryTranslations venv lparams res selection)
  intro restoredEnv Hrestoration
  have Hvalid := hvalid restoredEnv Hrestoration
  refine (Hlower.validateNestedAuxiliariesWF Hvalid mlctx hmlctx hlctx
    hfresh).mono fun _ Hvalidated => ⟨Hvalidated, ?_⟩
  rcases Hlower with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  exact Hrun.validatedAuxiliaryResidualTranslations Hvalid.tr.wf
    mlctx hmlctx hlctx Hvalidated

theorem ElimNestedInductive.run'.translation
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env) :
    ((Lean4Lean.ElimNestedInductive.run fuel nparams types env).run'
      state).WF (NestedLoweringResult env fuel nparams types state) := by
  have Hrun := ElimNestedInductive.run.translation fuel nparams types env state
    hclosures
  have Hprojected := Hrun.map fun out Hout =>
    show NestedLoweringResult env fuel nparams types state out.1 from
      ⟨out.2, Hout⟩
  simpa [StateT.run'] using Hprojected

theorem ElimNestedInductive.run'.translationClosed
    (fuel nparams : Nat) (types : List InductiveType)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitial : state.newTypes = types.toArray)
    (hempty : state.nestedAux = #[]) :
    ((Lean4Lean.ElimNestedInductive.run fuel nparams types env).run'
      state).WF (NestedLoweringResultClosed env fuel nparams types state) := by
  have Hrun := ElimNestedInductive.run.translationClosed fuel nparams types env
    state hclosures Henv Hsources hinitial hempty
  have Hprojected := Hrun.map fun out Hout =>
    show NestedLoweringResultClosed env fuel nparams types state out.1 from
      ⟨out.2, Hout.1, Hout.2.1, Hout.2.2⟩
  simpa [StateT.run'] using Hprojected

/-- Exact outer composition for `Environment.addInductive`, retaining both
the source-syntax checks and the complete lowering trace for the continuation.
These are independent inputs to the later source-WF and nested-compilation
proofs, so neither is intentionally discarded here. -/
theorem Environment.addInductive.checkedLoweringWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig)
    (hclosures : MutualInductivesClosed env)
    (Q : Environment → Prop)
    (Hfinish : ∀ res,
      SourceSyntaxChecks types →
      NestedLoweringResult env fuel.inductiveFuel nparams types
        { lvls := lparams.map .param, newTypes := types.toArray } res →
      (Environment.addInductiveAfterLowering env lparams nparams types
        isUnsafe allowPrimitive fuel res).WF Q) :
    (Environment.addInductive env lparams nparams types isUnsafe
      allowPrimitive fuel).WF Q := by
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hlowering := ElimNestedInductive.run'.translation fuel.inductiveFuel
    nparams types env
    { lvls := lparams.map .param, newTypes := types.toArray } hclosures
  have Hcombined := Hsources.bind fun _ Hsource =>
    Hlowering.bind fun res Hres => Hfinish res Hsource Hres
  simpa [Environment.addInductive] using Hcombined

/-- Strengthened outer composition used by the soundness proof.  Unlike the
compatibility theorem above, this result discharges dynamic auxiliary-family
closedness and the final cache scoping invariant from the source checks and
the verified production environment. -/
theorem Environment.addInductive.checkedLoweringClosedWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig)
    (hclosures : MutualInductivesClosed env)
    (Henv : EnvironmentTypesClosed env)
    (Q : Environment → Prop)
    (Hfinish : ∀ res,
      SourceSyntaxChecks types →
      NestedLoweringResultClosed env fuel.inductiveFuel nparams types
        { lvls := lparams.map .param, newTypes := types.toArray } res →
      (Environment.addInductiveAfterLowering env lparams nparams types
        isUnsafe allowPrimitive fuel res).WF Q) :
    (Environment.addInductive env lparams nparams types isUnsafe
      allowPrimitive fuel).WF Q := by
  have Hsources : (Lean4Lean.checkInductiveSources env types).WF
      fun _ => SourceSyntaxChecks types :=
    checkInductiveSources_refines env types
  have Hcombined := Hsources.bind fun _ Hsource =>
    (ElimNestedInductive.run'.translationClosed fuel.inductiveFuel nparams
      types env { lvls := lparams.map .param, newTypes := types.toArray }
      hclosures Henv Hsource rfl rfl).bind fun res Hres =>
        Hfinish res Hsource Hres
  simpa [Environment.addInductive] using Hcombined

/-- Compatibility projection of `checkedLoweringWF` for clients whose final
postcondition does not depend on the retained source-syntax certificate. -/
theorem Environment.addInductive.loweringWF
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig)
    (hclosures : MutualInductivesClosed env)
    (Q : Environment → Prop)
    (Hfinish : ∀ res,
      NestedLoweringResult env fuel.inductiveFuel nparams types
        { lvls := lparams.map .param, newTypes := types.toArray } res →
      (Environment.addInductiveAfterLowering env lparams nparams types
        isUnsafe allowPrimitive fuel res).WF Q) :
    (Environment.addInductive env lparams nparams types isUnsafe
      allowPrimitive fuel).WF Q := by
  apply Environment.addInductive.checkedLoweringWF env lparams nparams types
    isUnsafe allowPrimitive fuel hclosures Q
  intro res _Hsource Hlower
  exact Hfinish res Hlower

/-- Reference formulation of the executable header-checking prefix. Keeping
the closure check in the statement is important: it is what turns the
type-checker's context-relative result into a source declaration judgment. -/
def checkHeader (env : Environment) (safety : DefinitionSafety)
    (lparams : List Name) (fuel : FuelConfig) (name : Name) (type : Expr) :
    Except Exception Expr := do
  env.checkNoMVarNoFVar name type
  TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType type)

theorem checkHeader.WF
    (hvalid : CheckingEnv.Valid safety env venv) :
    (checkHeader env safety lparams fuel name type).WF (fun checkedType =>
      ∃ type' checkedType',
        TrTyping venv lparams [] type checkedType type' checkedType') := by
  unfold checkHeader
  have hno : (env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := env) (name := name) h
  exact hno.bind fun _ hclosed =>
    checkType_closed.WF (lparams := lparams) (fuel := fuel) hvalid hclosed

end VerifyInductive
end Lean4Lean
