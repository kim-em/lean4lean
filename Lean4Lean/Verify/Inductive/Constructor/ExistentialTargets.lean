import Lean4Lean.Verify.Inductive.Constructor.Positivity
import Lean4Lean.Verify.Inductive.Header.Existential
import Lean4Lean.Verify.Inductive.Header.RawMaterialization

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Ordered raw abstract constructor targets for one source family.  This is
the constructor-side counterpart of `CheckedSourceHeaderAccumulator`: target
constants are outputs of the executable closed-type checks, not inputs
chosen by a declaration skeleton. -/
structure CheckedSourceConstructorAccumulator (env : VEnv) (Us : List Name)
    (sources : List Constructor) where
  targets : List VConstVal
  translations : List.Forall₂
    (fun source target =>
      TrSourceConstRaw env Us source.name source.type target)
    sources targets

namespace CheckedSourceConstructorAccumulator

def empty (env : VEnv) (Us : List Name) :
    CheckedSourceConstructorAccumulator env Us [] where
  targets := []
  translations := .nil

def snoc (H : CheckedSourceConstructorAccumulator env Us sources)
    (source : Constructor) (target : VConstVal)
    (Htarget : TrSourceConstRaw env Us source.name source.type target) :
    CheckedSourceConstructorAccumulator env Us (sources ++ [source]) where
  targets := H.targets ++ [target]
  translations := Lean4Lean.VerifyInductive.List.Forall₂.append'
    H.translations (.cons Htarget .nil)

end CheckedSourceConstructorAccumulator

/-- Two-dimensional, source-aligned raw constructor targets for a prefix of
the mutual family list. -/
structure CheckedSourceConstructorRows (env : VEnv) (Us : List Name)
    (sources : List InductiveType) where
  targets : List (List VConstVal)
  translations : List.Forall₂
    (fun source targets => List.Forall₂
      (fun ctor target =>
        TrSourceConstRaw env Us ctor.name ctor.type target)
      source.ctors targets)
    sources targets

namespace CheckedSourceConstructorRows

def empty (env : VEnv) (Us : List Name) :
    CheckedSourceConstructorRows env Us [] where
  targets := []
  translations := .nil

def snoc (H : CheckedSourceConstructorRows env Us sources)
    (source : InductiveType)
    (row : CheckedSourceConstructorAccumulator env Us source.ctors) :
    CheckedSourceConstructorRows env Us (sources ++ [source]) where
  targets := H.targets ++ [row.targets]
  translations := Lean4Lean.VerifyInductive.List.Forall₂.append'
    H.translations (.cons row.translations .nil)

end CheckedSourceConstructorRows

/-- Assemble metadata-free family targets from independently accumulated
header constants and constructor rows. -/
def assembleInductiveSkeletonTypes (headers : List VConstVal)
    (constructors : List (List VConstVal)) : List VInductiveTypeSkeleton :=
  List.zipWith (fun header ctors => {
    toVConstVal := header
    ctors := ctors }) headers constructors

theorem assembleInductiveSkeletonTypes_translated
    {sources : List InductiveType} {headers : List VConstVal}
    {constructors : List (List VConstVal)}
    (Hheaders : List.Forall₂
      (fun source target =>
        TrSourceConst env Us source.name source.type target)
      sources headers)
    (Hconstructors : List.Forall₂
      (fun source targets => List.Forall₂
        (fun ctor target =>
          TrSourceConstRaw envTypes Us ctor.name ctor.type target)
        source.ctors targets)
      sources constructors) :
    List.Forall₂ (TrInductiveTypeSkeletonHeaders env envTypes Us)
      sources (assembleInductiveSkeletonTypes headers constructors) := by
  induction Hheaders generalizing constructors with
  | nil =>
      cases Hconstructors
      exact .nil
  | cons Hheader Hheaders ih =>
      cases Hconstructors with
      | cons Hctors Hconstructors =>
        exact .cons ⟨Hheader, Hctors⟩ (ih Hconstructors)

theorem assembleInductiveSkeletonTypes_headers
    {sources : List InductiveType} {headers : List VConstVal}
    {constructors : List (List VConstVal)}
    (Hheaders : List.Forall₂
      (fun source target =>
        TrSourceConst env Us source.name source.type target)
      sources headers)
    (Hconstructors : List.Forall₂
      (fun source targets => List.Forall₂
        (fun ctor target =>
          TrSourceConstRaw envTypes Us ctor.name ctor.type target)
        source.ctors targets)
      sources constructors) :
    (assembleInductiveSkeletonTypes headers constructors).map
      VInductiveTypeSkeleton.toVConstVal = headers := by
  have hlength : constructors.length = headers.length := by
    rw [← Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hconstructors,
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hheaders]
  have go : ∀ (hs : List VConstVal) (cs : List (List VConstVal)),
      cs.length = hs.length →
      (assembleInductiveSkeletonTypes hs cs).map
        VInductiveTypeSkeleton.toVConstVal = hs := by
    intro hs
    induction hs with
    | nil =>
        intro cs hlen
        have : cs = [] := List.eq_nil_of_length_eq_zero hlen
        subst cs
        rfl
    | cons header headers ih =>
        intro cs hlen
        cases cs with
        | nil => simp at hlen
        | cons ctors constructors =>
          have hlen' : constructors.length = headers.length := by
            simpa using Nat.succ.inj hlen
          change header ::
            (assembleInductiveSkeletonTypes headers constructors).map
              VInductiveTypeSkeleton.toVConstVal = header :: headers
          rw [ih constructors hlen']
  exact go headers constructors hlength

/-- The two skeleton-free executable accumulators determine the complete
metadata-free declaration translation.  The only remaining input is the
successful abstract header installation, which belongs to the declaration
boundary rather than either syntax traversal. -/
theorem TrInductDeclSkeletonHeaders.ofExistentialTargets
    {sources : List InductiveType}
    (Hheaders : MaterializedSourceHeaderAccumulator env Us sources)
    (Hconstructors : CheckedSourceConstructorRows envTypes Us sources)
    (nparams : Nat) (isUnsafe : Bool)
    (htypesAdded : env.addConstVals Hheaders.targets = some envTypes) :
    ∃ skeleton : VInductDeclSkeleton,
      TrInductDeclSkeletonHeaders env Us nparams sources isUnsafe skeleton
        envTypes := by
  let skeleton : VInductDeclSkeleton := {
    uvars := Us.length
    nparams := nparams
    types := assembleInductiveSkeletonTypes Hheaders.targets
      Hconstructors.targets
    isUnsafe := isUnsafe }
  refine ⟨skeleton, {
    uvars := rfl
    nparams := rfl
    isUnsafe := rfl
    typesAdded := ?_
    types := assembleInductiveSkeletonTypes_translated
      Hheaders.translations Hconstructors.translations }⟩
  change env.addConstVals
    ((assembleInductiveSkeletonTypes Hheaders.targets
      Hconstructors.targets).map
        VInductiveTypeSkeleton.toVConstVal) = some envTypes
  rw [assembleInductiveSkeletonTypes_headers Hheaders.translations
    Hconstructors.translations]
  exact htypesAdded

namespace checkConstructors.loopCtors

/-- One constructor iteration extends an existentially built raw-target row.
The semantic `loopCtor` proof remains with the caller, but its target
translation is now the one produced by this very `checkClosedType` call. -/
theorem stepPrefix.accumulatesRawTargets
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {isUnsafe : Bool} {targetIdx ctorIdx : Nat}
    {ctors : List Constructor} {foundCtors : NameSet}
    {sources : List Constructor} {Q : Unit → Prop}
    (Hc : ContextWF c)
    (Hprefix : CheckedSourceConstructorAccumulator
      Hc.venv c.lparams sources)
    (hidx : ctorIdx < ctors.length)
    (Hloop : ∀ checkedType,
      (Hchecked : CheckedSourceHeaderTranslation Hc
        ctors[ctorIdx].name ctors[ctorIdx].type checkedType) →
      CheckedSourceConstructorAccumulator Hc.venv c.lparams
        (sources ++ [ctors[ctorIdx]]) →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
          (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
            ctors (ctorIdx + 1)
            (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtors, dif_pos hidx]
  cases hfresh : foundCtors.contains ctors[ctorIdx].name with
  | true =>
      simp only [hfresh, ↓reduceIte]
      exact Except.WF.throw
  | false =>
      rw [if_neg (by simpa using hfresh)]
      change (AddInductive.checkClosedType ctors[ctorIdx].name
        ctors[ctorIdx].type c >>= fun _ => ((do
          let _ ← readThe AddInductive.Context
          AddInductive.checkConstructors.loopCtor stats isUnsafe
            ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
            c.fuel.inductiveFuel
          AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
            ctors (ctorIdx + 1)
            (foundCtors.insert ctors[ctorIdx].name)) :
          AddInductive.M Unit) c).WF Q
      exact (checkClosedType.rawSourceTranslationWF Hc).bind
        fun checkedType hchecked => by
          rcases hchecked with ⟨Hchecked⟩
          change ((read : AddInductive.M AddInductive.Context) c >>= fun c' =>
            ((AddInductive.checkConstructors.loopCtor stats isUnsafe
                ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
                c'.fuel.inductiveFuel >>= fun _ =>
              AddInductive.checkConstructors.loopCtors stats isUnsafe
                targetIdx ctors (ctorIdx + 1)
                (foundCtors.insert ctors[ctorIdx].name)) :
              AddInductive.M Unit) c).WF Q
          have hread : ((read : AddInductive.M AddInductive.Context) c).WF
              (fun c' => c' = c) := by
            intro c' h
            cases h
            rfl
          refine hread.bind fun c' hc' => ?_
          subst c'
          exact (Hloop checkedType Hchecked
            (Hprefix.snoc ctors[ctorIdx] Hchecked.target
              Hchecked.source)).bind fun _ hnext => hnext

/-- Traverse one complete constructor list while existentially retaining its
raw abstract targets in exact source order. -/
theorem accumulatesRawTargets
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {isUnsafe : Bool} {targetIdx ctorIdx : Nat}
    {ctors : List Constructor} {foundCtors : NameSet}
    {Q : Unit → Prop}
    (Hc : ContextWF c)
    (Hprefix : CheckedSourceConstructorAccumulator Hc.venv c.lparams
      (ctors.take ctorIdx))
    (Hcheck : ∀ i (hi : i < ctors.length) checkedType,
      (Hchecked : CheckedSourceHeaderTranslation Hc
        ctors[i].name ctors[i].type checkedType) →
      ∀ (R : Unit → Prop), R () →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[i].name targetIdx ctors[i].type 0
        c.fuel.inductiveFuel c).WF R)
    (Hfinish : CheckedSourceConstructorAccumulator Hc.venv c.lparams
      ctors → Q ()) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  by_cases hidx : ctorIdx < ctors.length
  · apply stepPrefix.accumulatesRawTargets
      (stats := stats) (isUnsafe := isUnsafe) (targetIdx := targetIdx)
      (foundCtors := foundCtors) (Q := Q) Hc Hprefix hidx
    intro checkedType Hchecked Hprefix'
    have Hnext : CheckedSourceConstructorAccumulator Hc.venv c.lparams
        (ctors.take (ctorIdx + 1)) := by
      rw [List.take_succ_eq_append_getElem hidx]
      exact Hprefix'
    apply Hcheck ctorIdx hidx checkedType Hchecked
    exact accumulatesRawTargets Hc Hnext Hcheck Hfinish
  · apply result.WF (Q := Q) hidx
    have htake : ctors.take ctorIdx = ctors :=
      List.take_of_length_le (Nat.le_of_not_gt hidx)
    exact Hfinish (by simpa [htake] using Hprefix)
termination_by ctors.length - ctorIdx

end checkConstructors.loopCtors

namespace checkConstructors.loopTypes

/-- Traverse the complete mutual constructor matrix without a caller-chosen
constructor skeleton.  Each row is generated by the corresponding
`checkClosedType` calls and the result preserves the production's family and
constructor order exactly. -/
theorem accumulatesRawTargets
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {isUnsafe : Bool} {indTypes : Array InductiveType}
    {targetIdx : Nat} {Q : Unit → Prop}
    (Hc : ContextWF c)
    (Hrows : CheckedSourceConstructorRows Hc.venv c.lparams
      (indTypes.toList.take targetIdx))
    (Hcheck : ∀ familyIdx (hfamily : familyIdx < indTypes.size)
      ctorIdx (hctor : ctorIdx < indTypes[familyIdx].ctors.length)
      checkedType,
      (Hchecked : CheckedSourceHeaderTranslation Hc
        indTypes[familyIdx].ctors[ctorIdx].name
        indTypes[familyIdx].ctors[ctorIdx].type checkedType) →
      ∀ (R : Unit → Prop), R () →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        indTypes[familyIdx].ctors[ctorIdx].name familyIdx
        indTypes[familyIdx].ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF R)
    (Hfinish : CheckedSourceConstructorRows Hc.venv c.lparams
      indTypes.toList → Q ()) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  by_cases hidx : targetIdx < indTypes.size
  · apply step.WF (Q := Q) hidx
    apply checkConstructors.loopCtors.accumulatesRawTargets
      (stats := stats) (isUnsafe := isUnsafe) (targetIdx := targetIdx)
      (ctors := indTypes[targetIdx].ctors) (ctorIdx := 0)
      (foundCtors := {})
      (Q := fun _ =>
        (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
          (targetIdx + 1) c).WF Q)
      Hc (by
        change CheckedSourceConstructorAccumulator Hc.venv c.lparams []
        exact CheckedSourceConstructorAccumulator.empty Hc.venv c.lparams)
    · intro ctorIdx hctor checkedType Hchecked R hR
      exact Hcheck targetIdx hidx ctorIdx hctor checkedType Hchecked R hR
    · intro Hrow
      have Hrows' : CheckedSourceConstructorRows Hc.venv c.lparams
          (indTypes.toList.take (targetIdx + 1)) := by
        rw [List.take_succ_eq_append_getElem (by simpa using hidx)]
        exact Hrows.snoc indTypes[targetIdx] Hrow
      exact accumulatesRawTargets Hc Hrows' Hcheck Hfinish
  · apply result.WF (Q := Q) hidx
    have htake : indTypes.toList.take targetIdx = indTypes.toList :=
      List.take_of_length_le (by simpa using Nat.le_of_not_gt hidx)
    exact Hfinish (by simpa [htake] using Hrows)
termination_by indTypes.size - targetIdx

end checkConstructors.loopTypes

end VerifyInductive
end Lean4Lean
