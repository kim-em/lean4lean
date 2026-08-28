import Lean4Lean.Verify.Inductive.Header.ExistentialFold

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Ordered abstract header targets after the executable telescope/result
checks have supplied the formation evidence deliberately absent from
`CheckedSourceHeaderAccumulator`. -/
structure MaterializedSourceHeaderAccumulator (env : VEnv) (Us : List Name)
    (sources : List InductiveType) where
  targets : List VConstVal
  translations : List.Forall₂
    (fun source target =>
      TrSourceConst env Us source.name source.type target)
    sources targets

namespace MaterializedSourceHeaderAccumulator

def empty (env : VEnv) (Us : List Name) :
    MaterializedSourceHeaderAccumulator env Us [] where
  targets := []
  translations := .nil

def snoc (H : MaterializedSourceHeaderAccumulator env Us sources)
    (source : InductiveType) (target : VConstVal)
    (Htarget : TrSourceConst env Us source.name source.type target) :
    MaterializedSourceHeaderAccumulator env Us (sources ++ [source]) where
  targets := H.targets ++ [target]
  translations := Lean4Lean.VerifyInductive.List.Forall₂.append'
    H.translations (.cons Htarget .nil)

def raw (H : MaterializedSourceHeaderAccumulator env Us sources) :
    CheckedSourceHeaderAccumulator env Us sources where
  targets := H.targets
  translations := Lean4Lean.List.Forall₂.imp
    (fun _ _ h => h.raw) H.translations

@[simp] theorem empty_targets : (empty env Us).targets = [] := rfl

@[simp] theorem snoc_targets
    (H : MaterializedSourceHeaderAccumulator env Us sources)
    (Htarget : TrSourceConst env Us source.name source.type target) :
    (H.snoc source target Htarget).targets = H.targets ++ [target] := rfl

end MaterializedSourceHeaderAccumulator

/-- Exact loop-indexed view of the fully formed mutual-header prefix. -/
structure MaterializedSourceHeaderTraversal (env : VEnv) (Us : List Name)
    (indTypes : Array InductiveType) (dIdx : Nat) where
  accumulator : MaterializedSourceHeaderAccumulator env Us
    (indTypes.toList.take dIdx)

namespace MaterializedSourceHeaderTraversal

def empty (env : VEnv) (Us : List Name) (indTypes : Array InductiveType) :
    MaterializedSourceHeaderTraversal env Us indTypes 0 where
  accumulator := MaterializedSourceHeaderAccumulator.empty env Us

def next (H : MaterializedSourceHeaderTraversal env Us indTypes dIdx)
    (hidx : dIdx < indTypes.size) (target : VConstVal)
    (Htarget : TrSourceConst env Us indTypes[dIdx].name
      indTypes[dIdx].type target) :
    MaterializedSourceHeaderTraversal env Us indTypes (dIdx + 1) where
  accumulator := by
    rw [List.take_succ_eq_append_getElem (by simpa using hidx)]
    exact H.accumulator.snoc indTypes[dIdx] target Htarget

def complete (H : MaterializedSourceHeaderTraversal env Us indTypes dIdx)
    (hdone : indTypes.size ≤ dIdx) :
    MaterializedSourceHeaderAccumulator env Us indTypes.toList := by
  have htake : indTypes.toList.take dIdx = indTypes.toList :=
    List.take_of_length_le (by simpa using hdone)
  rw [← htake]
  exact H.accumulator

def raw (H : MaterializedSourceHeaderTraversal env Us indTypes dIdx) :
    CheckedSourceHeaderTraversal env Us indTypes dIdx where
  accumulator := H.accumulator.raw

end MaterializedSourceHeaderTraversal

namespace TrSourceConstRaw

/-- Upgrade a raw source translation once an independently checked,
definitionally equal presentation is known to be a type. -/
theorem checkedOfDefEqType
    (H : TrSourceConstRaw env Us name type target)
    (henv : env.WF)
    (hdefeq : env.IsDefEqU Us.length [] target.type normalized)
    (hnormalized : env.IsType Us.length [] normalized) :
    TrSourceConst env Us name type target := by
  refine {
    uvars := H.uvars
    name := H.name
    type := H.type
    wf := ?_ }
  change env.IsType target.uvars [] target.type
  rw [H.uvars]
  exact hnormalized.defeqU_l henv (by trivial) hdefeq.symm

/-- A strict translation of a syntactic forall carries exactly the domain
and codomain `IsType` witnesses needed to discharge raw header formation. -/
theorem checkedOfForallTranslation
    (H : TrSourceConstRaw env Us name type target)
    (henv : env.WF)
    (hdefeq : env.IsDefEqU Us.length [] target.type normalized)
    (hforall : TrExprS env Us [] (.forallE binderName domain body binderInfo)
      normalized) :
    TrSourceConst env Us name type target := by
  cases hforall with
  | forallE hdomain hbody _ _ =>
    exact checkedOfDefEqType H henv hdefeq
      (VEnv.IsType.forallE hdomain hbody)

end TrSourceConstRaw

namespace checkInductiveTypes.loopType

/-- The source-only telescope accumulated by `loopType` is sufficient to
recover well-formedness of the original abstract header once `ensureSort`
has checked its terminal result.  In particular, this step needs no
caller-provided well-formed header skeleton. -/
theorem HeaderTelescopeLoopCertificate.checkedSource
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    {root current exprType : VExpr} {i nindices : Nat}
    (H : HeaderTelescopeLoopCertificate Hc root current i nindices)
    (Hsource : TrSourceConstRaw Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hheader : Hc.venv.IsDefEq c.lparams.length []
      target.type root exprType)
    (hcurrent : Hc.venv.IsType c.lparams.length
      Hc.mlctx.vlctx.toCtx current) :
    TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal := by
  have hsemanticCurrent : Hc.venv.IsType c.lparams.length
      (H.indices.reverse ++ H.params.reverse) current :=
    hcurrent.defeqDFC Hc.checking.tr.wf.ordered
      (H.telescope.context.symm Hc.checking.tr.wf.ordered)
  have hwrapped : Hc.venv.IsType c.lparams.length []
      (VExpr.wrapForalls (H.params ++ H.indices) current) :=
    VEnv.IsType.wrapForalls (by
      simpa [List.reverse_append] using H.telescope.context.isType)
      (by simpa [List.reverse_append] using hsemanticCurrent)
  have hroot : Hc.venv.IsType c.lparams.length [] root := by
    simpa [H.telescope.rebuild] using hwrapped
  have htarget : Hc.venv.IsType c.lparams.length [] target.type :=
    hroot.defeqU_l Hc.checking.tr.wf (by trivial) hheader.toU.symm
  exact {
    uvars := Hsource.uvars
    name := Hsource.name
    type := Hsource.type
    wf := by
      change Hc.venv.IsType target.uvars [] target.type
      rw [Hsource.uvars]
      exact htarget }

/-- `ensureSort` supplies the terminal `IsType` premise needed by
`checkedSource`; the translated result universe remains available to the
outer header fold as semantic metadata. -/
theorem HeaderTelescopeLoopCertificate.checkedSourceOfSort
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : InductiveType} {target : VInductiveTypeSkeleton}
    {root current exprType : VExpr} {i nindices : Nat}
    (H : HeaderTelescopeLoopCertificate Hc root current i nindices)
    (Hsource : TrSourceConstRaw Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hheader : Hc.venv.IsDefEq c.lparams.length []
      target.type root exprType)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort resultSort) current) :
    ∃ resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel ∧
      TrSourceConst Hc.venv c.lparams source.name source.type
        target.toVConstVal := by
  rcases TrExpr.sort_result Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx hsort with
    ⟨resultLevel, hofLevel, hcurrent⟩
  exact ⟨resultLevel, hofLevel,
    H.checkedSource Hsource hheader ⟨_, hcurrent.hasType.1⟩⟩

end checkInductiveTypes.loopType

namespace checkInductiveTypes.loopInd

/-- At the terminal `loopType` continuation, `ensureSort` proves the
contextual translation of the closed source header is a type.  Weakening the
raw empty-context target into that runtime context, using translation
uniqueness, and then inverting the weakening recovers target well-formedness
in the original environment.  This is the non-forall/zero-remaining-arity
half of raw header materialization. -/
theorem CheckedSourceHeaderTranslation.checkedTerminal
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : InductiveType} {checkedType : Expr}
    (H : CheckedSourceHeaderTranslation Hc source.name source.type
      checkedType)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort resultSort) H.runtimeTarget) :
    ∃ resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel ∧
      TrSourceConst Hc.venv c.lparams source.name source.type H.target := by
  rcases TrExpr.sort_result Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx hsort with
    ⟨resultLevel, hofLevel, hruntimeSorted⟩
  have hruntimeType : Hc.venv.IsType c.lparams.length
      Hc.mlctx.vlctx.toCtx H.runtimeTarget :=
    ⟨_, hruntimeSorted.hasType.1⟩
  let W : VLCtx.FVLift [] Hc.mlctx.vlctx 0
      Hc.mlctx.vlctx.toCtx.length 0 :=
    VLCtx.FVLift.from_nil Hc.mlctx.noBV
  have htargetWeak := H.source.type.weakFV
    Hc.checking.tr.wf.ordered W Hc.mlctx_wf.tr.wf
  have hruntimeTarget := H.typing.2.1.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) htargetWeak
  have htargetLifted : Hc.venv.IsType c.lparams.length
      Hc.mlctx.vlctx.toCtx
      (H.target.type.liftN Hc.mlctx.vlctx.toCtx.length 0) :=
    hruntimeType.defeqU_l Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx hruntimeTarget
  have htargetType : Hc.venv.IsType c.lparams.length [] H.target.type :=
    (VEnv.IsType.weakN_iff Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx W.toCtx).1 htargetLifted
  refine ⟨resultLevel, hofLevel, {
    uvars := H.source.uvars
    name := H.source.name
    type := H.source.type
    wf := ?_ }⟩
  change Hc.venv.IsType H.target.uvars [] H.target.type
  rw [H.source.uvars]
  exact htargetType

/-- A forall-headed first normal form is already type-valued by strict
translation, so its raw existential target can initialize the existing
header-synthesis recursion without assuming a skeleton from the caller. -/
theorem CheckedSourceHeaderTranslation.checkedFirstForall
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : InductiveType} {checkedType : Expr}
    (H : CheckedSourceHeaderTranslation Hc source.name source.type
      checkedType)
    (hctx : Hc.mlctx.vlctx = [])
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.forallE binderName domain body binderInfo) H.runtimeTarget) :
    TrSourceConst Hc.venv c.lparams source.name source.type H.target := by
  let target : VInductiveTypeSkeleton := {
    toVConstVal := H.target
    ctors := [] }
  rcases initialHeaderNormalization Hc hctx
      (target := target) H.source H.typing hnormalized with
    ⟨normalized, _exprType, hforall, hdefeq⟩
  have hforall' : TrExprS Hc.venv c.lparams []
      (.forallE binderName domain body binderInfo) normalized := by
    simpa [hctx] using hforall
  exact Lean4Lean.VerifyInductive.TrSourceConstRaw.checkedOfForallTranslation
    H.source Hc.checking.tr.wf
    hdefeq.toU hforall'

/-- Later forall-headed normal forms are first narrowed to the empty source
scope; their strict translation then upgrades the corresponding raw target
without importing ambient indices from earlier mutual headers. -/
theorem CheckedSourceHeaderTranslation.checkedLaterForall
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : InductiveType} {checkedType : Expr}
    (H : CheckedSourceHeaderTranslation Hc source.name source.type
      checkedType)
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.forallE binderName domain body binderInfo) H.runtimeTarget)
    (hfvars : FVarsIn (fun _ => False)
      (.forallE binderName domain body binderInfo)) :
    TrSourceConst Hc.venv c.lparams source.name source.type H.target := by
  let target : VInductiveTypeSkeleton := {
    toVConstVal := H.target
    ctors := [] }
  rcases initialLaterHeaderDefEqOfTranslation Hc
      (target := target) H.source H.typing.2.1 hnormalized hfvars with
    ⟨normalized, hforall, hdefeq⟩
  exact Lean4Lean.VerifyInductive.TrSourceConstRaw.checkedOfForallTranslation
    H.source Hc.checking.tr.wf
    hdefeq hforall

end checkInductiveTypes.loopInd
end VerifyInductive
end Lean4Lean
