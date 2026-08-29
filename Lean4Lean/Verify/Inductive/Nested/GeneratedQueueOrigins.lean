import Lean4Lean.Verify.Inductive.Nested.LoweringTrace

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Positional provenance for generated queue families

`SourceFamilyOrigin` intentionally forgets the queue position at which an
origin was established.  Formation needs a stronger fact: every final slot
strictly after the initial source block was produced by an actual auxiliary
generation step.  We retain that fact as a queue invariant rather than infer
it from equality of family values.
-/

/-- Reverse positional provenance for the append-only auxiliary cache.  Every
cache entry is paired with the generated-family queue slot that introduced its
fresh name.  The slot's family may later be lowered in place, but family-level
lowering preserves its name, so the position remains stable throughout the
queue run. -/
structure NestedAuxFamilyPositions
    (initialSize : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop where
  size : initialSize ≤ state.newTypes.size
  position : ∀ nested auxName, (nested, auxName) ∈ state.nestedAux →
    ∃ j, ∃ hj : j < state.newTypes.size,
      initialSize ≤ j ∧ state.newTypes[j].name = auxName

theorem GeneratedAuxiliary.familyPositions
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hpositions : NestedAuxFamilyPositions initialSize state) :
    NestedAuxFamilyPositions initialSize out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, _Hfresh, Hbuilt, _hresult, hstate⟩
  rw [hstate]
  constructor
  · simp only [Array.size_push]
    exact Nat.le_trans Hpositions.size (Nat.le_succ _)
  · intro nested name hentry
    simp only [Array.mem_push] at hentry
    rcases hentry with hold | hnew
    · rcases Hpositions.position nested name hold with
        ⟨j, hj, hinitial, hname⟩
      refine ⟨j, ?_, hinitial, ?_⟩
      · simp only [Array.size_push]
        omega
      simpa [Array.getElem_push, hj] using hname
    · cases hnew
      refine ⟨state.newTypes.size, by simp, Hpositions.size, ?_⟩
      simpa [Array.getElem_push] using Hbuilt.name

theorem GeneratedAuxiliaryBatch.familyPositions
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hpositions : NestedAuxFamilyPositions initialSize state) :
    NestedAuxFamilyPositions initialSize out.2 := by
  induction H with
  | nil => exact Hpositions
  | cons Hstep Htail ih => exact ih (Hstep.familyPositions Hpositions)

theorem RecognizedNestedReplacement.familyPositions
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (Hpositions : NestedAuxFamilyPositions initialSize state) :
    NestedAuxFamilyPositions initialSize out.2 := by
  cases H with
  | cached => exact Hpositions
  | generated _ Hbatch => exact Hbatch.familyPositions Hpositions

theorem NestedReplacement.familyPositions
    (H : NestedReplacement env lctx params As input state out)
    (Hpositions : NestedAuxFamilyPositions initialSize state) :
    NestedAuxFamilyPositions initialSize out.2 := by
  cases H with
  | unrecognized => exact Hpositions
  | recognized _ _ Hrecognized =>
    exact Hrecognized.familyPositions Hpositions

theorem NestedExprReplacement.familyPositions
    (H : NestedExprReplacement env lctx params As input state out)
    (Hpositions : NestedAuxFamilyPositions initialSize state) :
    NestedAuxFamilyPositions initialSize out.2 := by
  induction H with
  | hit Hnode => exact Hnode.familyPositions Hpositions
  | bvar | fvar | mvar | sort | const | lit => exact Hpositions
  | app Hnode _ _ ihFn ihArg =>
    exact ihArg (ihFn (Hnode.familyPositions Hpositions))
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    exact ihBody (ihDom (Hnode.familyPositions Hpositions))
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    exact ihBody (ihValue (ihType (Hnode.familyPositions Hpositions)))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody =>
    exact ihBody (Hnode.familyPositions Hpositions)

theorem LoweredConstructorTranslation.familyPositions
    (H : LoweredConstructorTranslation env params nparams source state out)
    (Hpositions : NestedAuxFamilyPositions initialSize state) :
    NestedAuxFamilyPositions initialSize out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, _Hopening, _Hbinding,
      _Hselection, _hnodup, hopenedTypes, hopenedAux, _hopenedNext, _hsize,
      Hreplace, _htype⟩
  have Hopened : NestedAuxFamilyPositions initialSize openedState := by
    constructor
    · simpa [hopenedTypes] using Hpositions.size
    · intro nested name hentry
      have hentryState : (nested, name) ∈ state.nestedAux := by
        simpa [hopenedAux] using hentry
      rcases Hpositions.position nested name hentryState with
        ⟨j, hj, hinitial, hname⟩
      refine ⟨j, ?_, hinitial, ?_⟩
      · simpa [hopenedTypes] using hj
      · simpa [hopenedTypes] using hname
  exact Hreplace.familyPositions Hopened

theorem LoweredConstructorTranslations.familyPositions
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (Hpositions : NestedAuxFamilyPositions initialSize state) :
    NestedAuxFamilyPositions initialSize out.2 := by
  induction H with
  | nil => exact Hpositions
  | cons Hhead Htail ih => exact ih (Hhead.familyPositions Hpositions)

theorem LoweredInductiveTranslation.familyPositions
    (H : LoweredInductiveTranslation env params nparams source state out)
    (Hpositions : NestedAuxFamilyPositions initialSize state) :
    NestedAuxFamilyPositions initialSize out.2 :=
  H.constructors.familyPositions Hpositions

/-- Every pending queue slot in the generated suffix carries the exact
`GeneratedFamilyWitness` that appended it. -/
def PendingGeneratedFamilyOrigins
    (env : Environment) (params : Array Expr) (initialSize cursor : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ j, initialSize ≤ j → cursor ≤ j →
    (hj : j < state.newTypes.size) →
    Nonempty (GeneratedFamilyWitness env params state.nestedAux
      state.newTypes[j])

theorem GeneratedAuxiliary.pendingGeneratedFamilyOrigins
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Hselection : LocalForallSelection lctx As)
    (hselectionNodup : Hselection.fvars.Nodup)
    (Hclosing : NestedClosingContext lctx As ngen)
    (hnparams : nparams ≤ args.size)
    (hsourceParams : nparams = sourceInfo.numParams)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args, arg.FVarsIn (· ∈ Hselection.fvars))
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, _Hfresh, Hbuilt, _hresult, hstate⟩
  rw [hstate]
  intro j hinitial hcursor hj
  simp only [Array.size_push] at hj
  by_cases hold : j < state.newTypes.size
  · rcases Horigins j hinitial hcursor hold with ⟨Horigin⟩
    refine ⟨{ Horigin with
      family_eq := by
        simpa [Array.getElem_push, hold] using Horigin.family_eq
      cached := by
        simp only [Array.mem_push]
        exact Or.inl Horigin.cached }⟩
  · have heq : j = state.newTypes.size := by omega
    subst j
    exact ⟨{
      lctx := lctx
      As := As
      levels := levels
      nestedNParams := nparams
      sourceNumParams := hsourceParams
      args := args
      argsArity := hnparams
      sourceName := sourceName
      auxName := auxName
      sourceInfo := sourceInfo
      data := data
      selection := Hselection
      selectionNodup := hselectionNodup
      ngen := ngen
      closing := Hclosing
      levelsNoMVars := Hlevels
      argsFVars := Hargs
      built := Hbuilt
      family_eq := by simp [Array.getElem_push]
      cached := by simp }⟩

theorem GeneratedAuxiliaryBatch.pendingGeneratedFamilyOrigins
    (H : GeneratedAuxiliaryBatch env lctx params As targetName levels nparams
      args result sourceNames state out)
    (Hselection : LocalForallSelection lctx As)
    (hselectionNodup : Hselection.fvars.Nodup)
    (Hclosing : NestedClosingContext lctx As ngen)
    (hnparams : nparams ≤ args.size)
    (hclosures : MutualInductivesClosed env)
    (triggerInfo : InductiveVal)
    (htrigger : env.find? targetName = some (.inductInfo triggerInfo))
    (hsourceNames : ∀ sourceName ∈ sourceNames,
      sourceName ∈ triggerInfo.all)
    (hnparamsTrigger : nparams = triggerInfo.numParams)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args, arg.FVarsIn (· ∈ Hselection.fvars))
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  induction H with
  | nil => exact Horigins
  | cons Hstep Htail ih =>
    have Hclosure := hclosures targetName triggerInfo htrigger
    rcases Hstep.generated with
      ⟨_auxName, _nextIdx, _data, _Hfresh, Hbuilt, _hresult, _hstate⟩
    have hmemberParams := Hclosure.parameters _ _
      (hsourceNames _ (by simp)) Hbuilt.lookup
    have hstepParams : nparams = _ :=
      hnparamsTrigger.trans hmemberParams.symm
    exact ih
      (fun sourceName hsource => hsourceNames sourceName (by simp [hsource]))
      (Hstep.pendingGeneratedFamilyOrigins Hselection
        hselectionNodup Hclosing hnparams hstepParams Hlevels Hargs Horigins)

theorem RecognizedNestedReplacement.pendingGeneratedFamilyOrigins
    (H : RecognizedNestedReplacement env lctx params As targetName levels args
      value state out)
    (Hselection : LocalForallSelection lctx As)
    (hselectionNodup : Hselection.fvars.Nodup)
    (Hclosing : NestedClosingContext lctx As ngen)
    (hnparams : value.numParams ≤ args.size)
    (hclosures : MutualInductivesClosed env)
    (htrigger : env.find? targetName = some (.inductInfo value))
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args, arg.FVarsIn (· ∈ Hselection.fvars))
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  cases H with
  | cached => exact Horigins
  | generated _ Hbatch =>
    exact Hbatch.pendingGeneratedFamilyOrigins Hselection hselectionNodup
      Hclosing hnparams hclosures value htrigger (by simp) rfl Hlevels Hargs
      Horigins

theorem NestedReplacement.pendingGeneratedFamilyOrigins
    (H : NestedReplacement env lctx params As e state out)
    (Hselection : LocalForallSelection lctx As)
    (hselectionNodup : Hselection.fvars.Nodup)
    (Hclosing : NestedClosingContext lctx As ngen)
    (hclosures : MutualInductivesClosed env)
    (Hinput : e.FVarsIn (· ∈ Hselection.fvars))
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  cases H with
  | unrecognized => exact Horigins
  | recognized Hcandidate hhead Hresult =>
    exact Hresult.pendingGeneratedFamilyOrigins Hselection hselectionNodup
      Hclosing Hcandidate.parameters.arity hclosures (by
        rcases Hcandidate.headFound with ⟨fn, levels, hfn, hfind⟩
        rw [hhead] at hfn
        injection hfn with hname _
        simpa [hname] using hfind) (by
        have Hfn := Hinput.getAppFn
        rw [hhead] at Hfn
        simpa [Lean4Lean.FVarsIn] using Hfn) (by
        intro arg harg
        apply Hinput.getAppArgsList
        rw [← Expr.getAppArgs_toList]
        exact Array.mem_toList_iff.mpr harg) Horigins

theorem NestedExprReplacement.pendingGeneratedFamilyOrigins
    (H : NestedExprReplacement env lctx params As e state out)
    (Hselection : LocalForallSelection lctx As)
    (hselectionNodup : Hselection.fvars.Nodup)
    (Hclosing : NestedClosingContext lctx As ngen)
    (hclosures : MutualInductivesClosed env)
    (Hinput : e.FVarsIn (· ∈ Hselection.fvars))
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  induction H with
  | hit Hnode =>
    exact Hnode.pendingGeneratedFamilyOrigins Hselection hselectionNodup
      Hclosing hclosures Hinput Horigins
  | bvar | fvar | mvar | sort | const | lit => exact Horigins
  | app Hnode _ _ ihFn ihArg =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihArg Hinput.2 (ihFn Hinput.1
      (Hnode.pendingGeneratedFamilyOrigins Hselection hselectionNodup Hclosing
        hclosures Hinput Horigins))
  | lam Hnode _ _ ihDom ihBody | forallE Hnode _ _ ihDom ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2 (ihDom Hinput.1
      (Hnode.pendingGeneratedFamilyOrigins Hselection hselectionNodup Hclosing
        hclosures Hinput Horigins))
  | letE Hnode _ _ _ ihType ihValue ihBody =>
    simp only [Lean4Lean.FVarsIn] at Hinput
    exact ihBody Hinput.2.2 (ihValue Hinput.2.1 (ihType Hinput.1
      (Hnode.pendingGeneratedFamilyOrigins Hselection hselectionNodup Hclosing
        hclosures Hinput Horigins)))
  | mdata Hnode _ ihBody | proj Hnode _ ihBody =>
    exact ihBody Hinput (Hnode.pendingGeneratedFamilyOrigins Hselection
      hselectionNodup Hclosing hclosures Hinput Horigins)

theorem LoweredConstructorTranslation.pendingGeneratedFamilyOrigins
    (H : LoweredConstructorTranslation env params nparams source state out)
    (hclosures : MutualInductivesClosed env)
    (Hsource : source.type.FVarsIn fun _ => False)
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  rcases H.translated with
    ⟨lctx, tail, As, lowered, openedState, Hopening, Hbinding,
      Hselection, hnodup, hopenedTypes, hopenedAux, _hopenedNext, _hsize,
      Hreplace, _htype⟩
  have Htail : tail.FVarsIn (· ∈ Hselection.fvars) :=
    Hopening.tailFVarsIn Hselection
      (Hsource.mono fun _ hfalse => False.elim hfalse)
  have Hopened : PendingGeneratedFamilyOrigins env params initialSize cursor
      openedState := by
    intro j hinitial hcursor hj
    have hjState : j < state.newTypes.size := by
      simpa [hopenedTypes] using hj
    rcases Horigins j hinitial hcursor hjState with ⟨Horigin⟩
    exact ⟨by simpa [hopenedTypes, hopenedAux] using Horigin⟩
  have Hclosing : NestedClosingContext lctx As openedState.ngen :=
    Hopening.closingContext Hbinding Hselection hnodup Hsource
  exact Hreplace.pendingGeneratedFamilyOrigins Hselection hnodup Hclosing
    hclosures Htail Hopened

theorem LoweredConstructorTranslations.pendingGeneratedFamilyOrigins
    (H : LoweredConstructorTranslations env params nparams sources state out)
    (hclosures : MutualInductivesClosed env)
    (Hsources : ∀ source ∈ sources,
      source.type.FVarsIn fun _ => False)
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 := by
  induction H with
  | nil => exact Horigins
  | cons Hhead Htail ih =>
    exact ih (fun source hsource => Hsources source (by simp [hsource]))
      (Hhead.pendingGeneratedFamilyOrigins hclosures
        (Hsources _ (by simp)) Horigins)

theorem LoweredInductiveTranslation.pendingGeneratedFamilyOrigins
    (H : LoweredInductiveTranslation env params nparams source state out)
    (hclosures : MutualInductivesClosed env)
    (Hsource : InductiveConstructorsClosed source)
    (Horigins : PendingGeneratedFamilyOrigins env params initialSize cursor
      state) :
    PendingGeneratedFamilyOrigins env params initialSize cursor out.2 :=
  H.constructors.pendingGeneratedFamilyOrigins hclosures Hsource Horigins

/-- Complete lowering provenance for a dynamically generated final slot. -/
structure FinalLoweredGeneratedFamilyOrigin
    (env : Environment) (params : Array Expr) (nparams : Nat)
    (finalState : Lean4Lean.ElimNestedInductive.State)
    (target : InductiveType) where
  source : InductiveType
  generated : GeneratedFamilyWitness env params finalState.nestedAux source
  stepState : Lean4Lean.ElimNestedInductive.State
  loweredState : Lean4Lean.ElimNestedInductive.State
  lowered : LoweredInductiveTranslation env params nparams source stepState
    (target, loweredState)
  later : NestedAuxLE loweredState finalState

def FinalLoweredGeneratedFamilyOrigin.mono
    (H : FinalLoweredGeneratedFamilyOrigin env params nparams state target)
    (Haux : NestedAuxLE state nextState) :
    FinalLoweredGeneratedFamilyOrigin env params nparams nextState target :=
  { H with
    generated := { H.generated with cached := Haux.mem H.generated.cached }
    later := H.later.trans Haux }

/-- Generated provenance split at the dynamic queue cursor. -/
structure LoweringQueueGeneratedOrigins
    (env : Environment) (params : Array Expr) (nparams initialSize cursor : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop where
  processed : ∀ j, initialSize ≤ j →
    (hj : j < state.newTypes.size) → j < cursor →
    Nonempty (FinalLoweredGeneratedFamilyOrigin env params nparams state
      state.newTypes[j])
  pending : PendingGeneratedFamilyOrigins env params initialSize cursor state

theorem LowerNextTranslation.familyPositions
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (Hpositions : NestedAuxFamilyPositions initialSize state) :
    NestedAuxFamilyPositions initialSize nextState := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    have HloweredPositions := Hlowered.familyPositions Hpositions
    have Hle := Hlowered.newTypesLE
    have hiLowered := (Hle.getElem hi).choose
    constructor
    · simpa [Array.size_set!] using HloweredPositions.size
    · intro nested name hentry
      rcases HloweredPositions.position nested name hentry with
        ⟨j, hj, hinitial, hname⟩
      have hjNext : j < (loweredState.newTypes.set! i target).size := by
        simpa [Array.size_set!] using hj
      refine ⟨j, hjNext, hinitial, ?_⟩
      by_cases hji : j = i
      · subst j
        have hsource : loweredState.newTypes[i] = state.newTypes[i] :=
          (Hle.getElem hi).choose_spec
        have htargetName : target.name = loweredState.newTypes[i].name := by
          rw [Hlowered.name, hsource]
        calc
          (loweredState.newTypes.set! i target)[i].name = target.name := by
            simp [Array.getElem_setIfInBounds, hiLowered]
          _ = loweredState.newTypes[i].name := htargetName
          _ = name := hname
      · have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hj
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        simpa [Array.set!, hget] using hname

theorem LowerNextTranslation.generatedFamilyOrigins
    (H : LowerNextTranslation env params nparams i state
      (some source, nextState))
    (Hpending : PendingNewTypesClosed i state)
    (hclosures : MutualInductivesClosed env)
    (Horigins : LoweringQueueGeneratedOrigins env params nparams initialSize i
      state) :
    LoweringQueueGeneratedOrigins env params nparams initialSize (i + 1)
      nextState := by
  cases H with
  | step hi Hlowered =>
    rename_i target loweredState
    have Hle := Hlowered.newTypesLE
    have Haux := Hlowered.nestedAuxLE
    have HsetAux : NestedAuxLE loweredState
        { loweredState with
          newTypes := loweredState.newTypes.set! i target } :=
      ⟨[], by simp⟩
    have hiLowered := (Hle.getElem hi).choose
    have HpendingOrigins := Hlowered.pendingGeneratedFamilyOrigins
      hclosures (Hpending i (Nat.le_refl _) hi) Horigins.pending
    constructor
    · intro j hinitial hjNext hjProcessed
      by_cases hji : j = i
      · subst j
        rcases Horigins.pending i hinitial (Nat.le_refl _) hi with
          ⟨Hsource⟩
        let Hfinal : FinalLoweredGeneratedFamilyOrigin env params nparams
            { loweredState with
              newTypes := loweredState.newTypes.set! i target } target := {
          source := state.newTypes[i]
          generated := { Hsource with cached := Haux.mem Hsource.cached }
          stepState := state
          loweredState := loweredState
          lowered := Hlowered
          later := HsetAux }
        exact ⟨by
          simpa [Array.getElem_setIfInBounds, hiLowered] using Hfinal⟩
      · have hjOld : j < i := by omega
        have hjState : j < state.newTypes.size := by omega
        rcases Horigins.processed j hinitial hjState hjOld with ⟨Hprocessed⟩
        rcases Hle.getElem hjState with ⟨hjLowered, hsame⟩
        have Hprocessed' := Hprocessed.mono (Haux.trans HsetAux)
        have hget := Array.getElem_setIfInBounds
          (xs := loweredState.newTypes) (i := i) (a := target)
          (j := j) hjLowered
        rw [if_neg (fun h : i = j => hji h.symm)] at hget
        exact ⟨by simpa [Array.set!, hget, hsame] using Hprocessed'⟩
    · intro j hinitial hjCursor hjNext
      have hjLowered : j < loweredState.newTypes.size := by
        simpa [Array.size_set!] using hjNext
      rcases HpendingOrigins j hinitial (by omega) hjLowered with ⟨Hsource⟩
      have hji : j ≠ i := by omega
      have hget := Array.getElem_setIfInBounds
        (xs := loweredState.newTypes) (i := i) (a := target)
        (j := j) hjLowered
      rw [if_neg (fun h : i = j => hji h.symm)] at hget
      exact ⟨by simpa [Array.set!, hget] using Hsource⟩

/-- Every generated final result slot has exact source-generation and
lowering provenance. -/
theorem LoweringQueueTrace.finalGeneratedFamilyOriginAt
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hpending : PendingNewTypesClosed i state)
    (Horigins : LoweringQueueGeneratedOrigins env params nparams initialSize i
      state)
    (hinitial : initialSize ≤ j)
    (hj : j < out.1.types.length) :
    Nonempty (FinalLoweredGeneratedFamilyOrigin env params nparams out.2
      out.1.types[j]) := by
  induction H with
  | @done iDone fuelDone stateDone hbound =>
    have hjState : j < stateDone.newTypes.size := by simpa using hj
    exact Horigins.processed j hinitial hjState (by omega)
  | step Hnext Htail ih =>
    exact ih (Hnext.pendingNewTypesClosed Henv Hpending)
      (Hnext.generatedFamilyOrigins Hpending hclosures Horigins) hj

theorem LoweringQueueTrace.familyPositions
    (H : LoweringQueueTrace env params nparams lctx i fuel state out)
    (Hpositions : NestedAuxFamilyPositions initialSize state) :
    NestedAuxFamilyPositions initialSize out.2 := by
  induction H with
  | done => exact Hpositions
  | step Hnext Htail ih => exact ih (Hnext.familyPositions Hpositions)

theorem LoweringQueueTrace.resultTypes
    (H : LoweringQueueTrace env params nparams lctx i fuel state out) :
    out.1.types = out.2.newTypes.toList := by
  induction H with
  | done => rfl
  | step _ _ ih => exact ih

/-- End-to-end generated-suffix provenance, indexed by the exact final result
position. -/
theorem NestedLoweringRun.finalGeneratedFamilyOriginAt
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitialTypes : initialState.newTypes = types.toArray)
    (hsuffix : initialState.newTypes.size ≤ j)
    (hj : j < out.1.types.length) :
    Nonempty (FinalLoweredGeneratedFamilyOrigin env out.1.params nparams
      out.2 out.1.types[j]) := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, _Hopening,
      hnewTypes, _hnestedAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have Horigins : LoweringQueueGeneratedOrigins env params nparams
      initialState.newTypes.size 0 paramsState := by
    constructor
    · intro j _hinitial _hj hjProcessed
      omega
    · intro j hinitial _hcursor hj
      have hjInitial : j < initialState.newTypes.size := by
        simpa [hnewTypes] using hj
      omega
  have Hpending : PendingNewTypesClosed 0 paramsState := by
    intro j _hj hjState
    have hjInitial : j < initialState.newTypes.size := by
      simpa [hnewTypes] using hjState
    have hmember : initialState.newTypes[j] ∈ types := by
      have hmemInitial : initialState.newTypes[j] ∈ initialState.newTypes :=
        Array.getElem_mem hjInitial
      simpa [hinitialTypes] using hmemInitial
    have hvalue : paramsState.newTypes[j] = initialState.newTypes[j] := by
      have heq := congrArg (fun xs : Array InductiveType => xs[j]!) hnewTypes
      simpa [Array.getElem!_eq_getD, Array.getD, hjState, hjInitial] using heq
    rw [hvalue]
    exact Hsources.constructorsClosed hmember
  have Hfinal := Hqueue.finalGeneratedFamilyOriginAt Henv hclosures Hpending Horigins
    hsuffix hj
  rw [Hqueue.resultContext.2]
  exact Hfinal

/-- Every final auxiliary-cache entry points back to a concrete generated
suffix slot.  This is derived from the paired cache/queue pushes of the
executable lowering trace, rather than assumed as a semantic provider. -/
theorem NestedLoweringRun.finalAuxFamilyPosition
    (H : NestedLoweringRun env fuel nparams types initialState out)
    (hempty : initialState.nestedAux = #[]) :
    NestedAuxFamilyPositions initialState.newTypes.size out.2 := by
  rcases H.source with
    ⟨first, rest, tail, paramsState, lctx, params, _htypes, _Hopening,
      hnewTypes, hinitialAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have Hinitial : NestedAuxFamilyPositions initialState.newTypes.size
      paramsState := by
    constructor
    · simpa [hnewTypes]
    · intro nested name hentry
      have : (nested, name) ∈ initialState.nestedAux := by
        simpa [hinitialAux] using hentry
      simp [hempty] at this
  exact Hqueue.familyPositions Hinitial

/-- Exact generated-family provenance recovered from a final cache entry.
The cache's fresh-name invariant makes the positional generated witness agree
with the queried nested expression, including for a hit that reused an entry
created earlier in the lowering traversal. -/
structure FinalCachedGeneratedFamilyOrigin
    (env : Environment) (params : Array Expr) (nparams initialSize : Nat)
    (finalState : Lean4Lean.ElimNestedInductive.State)
    (nested : Expr) (auxName : Name) where
  j : Nat
  hj : j < finalState.newTypes.size
  generatedSuffix : initialSize ≤ j
  origin : FinalLoweredGeneratedFamilyOrigin env params nparams finalState
    finalState.newTypes[j]
  nested_eq : origin.generated.data.nested = nested
  auxName_eq : origin.generated.auxName = auxName

/-- The executable result map contains no entries other than those retained
in the final lowering cache.  This reverse direction is what lets a local
replacement hit rejoin the generated-family queue provenance carried by the
whole lowering run. -/
theorem NestedLoweringRun.finalCacheEntryOfResultLookup
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (hlookup : result.aux2nested.find? auxName = some nested) :
    (nested, auxName) ∈ finalState.nestedAux := by
  rw [H.resultAuxMap] at hlookup
  change (finalState.nestedAux.foldl
    (fun (map : Std.TreeMap Name Expr Name.quickCmp)
      (entry : Expr × Name) => map.insert entry.2 entry.1)
    {})[auxName]? = some nested at hlookup
  rw [← Array.foldl_toList] at hlookup
  simpa using nestedAuxFold_find_mem finalState.nestedAux.toList hlookup

theorem NestedLoweringRun.finalCachedGeneratedFamilyOrigin
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitialTypes : initialState.newTypes = types.toArray)
    (hempty : initialState.nestedAux = #[])
    (hentry : (nested, auxName) ∈ finalState.nestedAux) :
    Nonempty (FinalCachedGeneratedFamilyOrigin env result.params nparams
      initialState.newTypes.size finalState nested auxName) := by
  rcases (H.finalAuxFamilyPosition hempty).position nested auxName hentry with
    ⟨j, hj, hinitial, hname⟩
  rcases H.source with
    ⟨_first, _rest, _tail, _paramsState, _lctx, _params, _htypes,
      _Hopening, _hnewTypes, _hinitialAux, _hnextIdx, _hprefix, _Hctx, _Hselection,
      Hqueue⟩
  have hjResult : j < result.types.length := by
    rw [Hqueue.resultTypes]
    simpa using hj
  rcases H.finalGeneratedFamilyOriginAt Henv hclosures Hsources hinitialTypes hinitial
    hjResult with ⟨Horigin⟩
  have hfamily : result.types[j] = finalState.newTypes[j] := by
    have harr : result.types.toArray = finalState.newTypes := by
      simpa using congrArg List.toArray Hqueue.resultTypes
    have hget := congrArg
      (fun xs : Array InductiveType => xs[j]!) harr
    have hleft : result.types.toArray[j]! = result.types[j] := by
      simp [Array.getElem!_eq_getD, Array.getD, hjResult]
    have hright : finalState.newTypes[j]! = finalState.newTypes[j] := by
      simp [Array.getElem!_eq_getD, Array.getD, hj]
    exact hleft.symm.trans (hget.trans hright)
  have HoriginFinal : FinalLoweredGeneratedFamilyOrigin env result.params
      nparams finalState finalState.newTypes[j] := by
    simpa [hfamily] using Horigin
  have hauxName : HoriginFinal.generated.auxName = auxName := by
    calc
      HoriginFinal.generated.auxName = HoriginFinal.generated.data.type.name :=
        HoriginFinal.generated.built.name.symm
      _ = HoriginFinal.source.name :=
        congrArg InductiveType.name HoriginFinal.generated.family_eq.symm
      _ = finalState.newTypes[j].name := HoriginFinal.lowered.name.symm
      _ = auxName := hname
  have hgeneratedEntry :
      (HoriginFinal.generated.data.nested, auxName) ∈
        finalState.nestedAux := by
    simpa [hauxName] using HoriginFinal.generated.cached
  have hnodup := H.resultNamesNodupOfEmpty hempty
  have hfind := nestedAuxFold_find finalState.nestedAux.toList
    ({} : Std.TreeMap Name Expr Name.quickCmp) hnodup
    (by simpa using hentry)
  have hfindGenerated := nestedAuxFold_find finalState.nestedAux.toList
    ({} : Std.TreeMap Name Expr Name.quickCmp) hnodup
    (by simpa using hgeneratedEntry)
  have hnested : HoriginFinal.generated.data.nested = nested := by
    rw [hfind] at hfindGenerated
    exact Option.some.inj hfindGenerated.symm
  exact ⟨{
    j := j
    hj := hj
    generatedSuffix := hinitial
    origin := HoriginFinal
    nested_eq := hnested
    auxName_eq := hauxName }⟩

/-- Map-facing form of `finalCachedGeneratedFamilyOrigin`.  Replacement
traces expose an exact production-map lookup; both cache hits and newly
generated hits can therefore recover their concrete generated suffix slot
without any caller-supplied correspondence. -/
theorem NestedLoweringRun.finalCachedGeneratedFamilyOriginOfLookup
    (H : NestedLoweringRun env fuel nparams types initialState
      (result, finalState))
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitialTypes : initialState.newTypes = types.toArray)
    (hempty : initialState.nestedAux = #[])
    (hlookup : result.aux2nested.find? auxName = some nested) :
    Nonempty (FinalCachedGeneratedFamilyOrigin env result.params nparams
      initialState.newTypes.size finalState nested auxName) :=
  H.finalCachedGeneratedFamilyOrigin Henv hclosures Hsources hinitialTypes hempty
    (H.finalCacheEntryOfResultLookup hlookup)

/-- Every successful expression-lowering hit in an exact run rejoins the
generated queue at one concrete suffix slot.  This packages the operational
application data together with the derived queue origin, so subsequent
formation projection never has to assume a cache/generated correspondence. -/
theorem NestedReplacementFinalTrace.finalGeneratedFamilyOrigin
    (H : NestedReplacementFinalTrace env lctx result.params As input state
      lowered nextState result traceFinalState)
    (Hrun : NestedLoweringRun env fuel nparams types initialState
      (result, runFinalState))
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitialTypes : initialState.newTypes = types.toArray)
    (hempty : initialState.nestedAux = #[]) :
    ∃ value targetName levels auxName auxLevels nested,
      NestedAppCandidate env state input value ∧
      input.getAppFn = .const targetName levels ∧
      lowered = mkAppRange (mkAppN (.const auxName auxLevels) As)
        value.numParams input.getAppArgs.size input.getAppArgs ∧
      (nested ==
        ((mkAppRange (.const targetName levels) 0 value.numParams
          input.getAppArgs).abstract As).instantiateRev result.params) = true ∧
      Nonempty (FinalCachedGeneratedFamilyOrigin env result.params nparams
        initialState.newTypes.size runFinalState nested auxName) := by
  rcases H.mapping with
    ⟨value, targetName, levels, auxName, auxLevels, nested, Hcandidate,
      _hauxLevels, hhead, hlowered, hnested, hlookup⟩
  exact ⟨value, targetName, levels, auxName, auxLevels, nested, Hcandidate,
    hhead, hlowered, hnested,
    Hrun.finalCachedGeneratedFamilyOriginOfLookup Henv hclosures Hsources hinitialTypes
      hempty hlookup⟩

theorem FinalLoweredGeneratedFamilyOrigin.finalMapping
    (H : FinalLoweredGeneratedFamilyOrigin env params nparams finalState
      target)
    (Hmap : NestedAuxMapModels result finalState) :
    LoweredInductiveMapping env params nparams result H.source H.stepState
      (target, H.loweredState) :=
  H.lowered.finalMapping H.later Hmap

end VerifyInductive
end Lean4Lean
