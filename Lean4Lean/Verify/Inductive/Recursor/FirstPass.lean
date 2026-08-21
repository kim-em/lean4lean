import Lean4Lean.Verify.Inductive.Recursor.Origins

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

namespace mkRecInfos.loopArgs1

/-- Canonical abstract variables for indices retained in source binder order
inside a context that stores the most recently opened index first. -/
def canonicalIndexVars (n : Nat) : List VExpr :=
  (List.range n).reverse.map .bvar

@[simp] theorem canonicalIndexVars_zero : canonicalIndexVars 0 = [] := rfl

@[simp] theorem canonicalIndexVars_succ (n : Nat) :
    (canonicalIndexVars n).map (fun target => target.liftN 1 0) ++
      [.bvar 0] = canonicalIndexVars (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show canonicalIndexVars (n + 1) =
        .bvar n :: canonicalIndexVars n by
      simp [canonicalIndexVars, List.range_succ]]
    simp only [List.map_cons, VExpr.liftN, Nat.zero_le, ↓reduceIte,
      List.cons_append]
    rw [ih]
    simp [canonicalIndexVars, List.range_succ]

/-- Common parameters beneath `n` index binders followed by those index
variables are exactly the canonical variables for the whole header. -/
theorem VInductDecl.paramVars_append_canonicalIndexVars
    (decl : VInductDecl) (n : Nat) :
    decl.paramVars n ++ canonicalIndexVars n =
      canonicalIndexVars (decl.nparams + n) := by
  unfold VInductDecl.paramVars canonicalIndexVars
  rw [Nat.add_comm decl.nparams n, List.range_add,
    List.reverse_append, List.map_append]
  simp [Function.comp_def, Nat.add_comm]

/-- All independently checked inputs needed to replay one source family
header during recursor construction.  The family index is retained in the
package, so parameter/index arities cannot be borrowed from another member
of a mutual block. -/
structure CheckedRecursorHeaderAt
    (Hc : ContextWF c) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (depth : Nat) (source : InductiveType)
    (familyIdx : Nat) where
  target : VInductiveType
  targetAt : decl.types[familyIdx]? = some target
  materialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
    Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth
  sourceTranslation : TrSourceConst Hc.venv c.lparams source.name
    source.type target.toVConstVal
  targetLookup : Hc.venv.constants target.name = some target.toVConstant
  lparamsNodup : c.lparams.Nodup

/-- The semantic family header seen by generated recursor code.  Small
elimination keeps the checked header unchanged.  Large elimination shifts
the header's abstract universe indices under the fresh leading recursor
parameter; its stored declaration arity is intentionally not changed. -/
def CheckedRecursorHeaderAt.recursorTargetSkeleton
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    VInductiveTypeSkeleton :=
  match elimLevel with
  | .zero => H.target.toSkeleton
  | .param _ =>
    { H.target.toSkeleton with
      type := H.target.type.instL
        (VLevel.prependShift c.lparams.length) }
  | .succ _ | .max _ _ | .imax _ _ | .mvar _ => False.elim Helim

/-- Common header parameters after the optional leading recursor universe is
introduced.  Term-variable indices are unchanged; only universe indices in
their domain types move. -/
def CheckedRecursorHeaderAt.recursorParams
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    List VExpr :=
  match elimLevel with
  | .zero => H.materialized.headers.params
  | .param _ => H.materialized.headers.params.map
      (VExpr.instL (VLevel.prependShift c.lparams.length))
  | .succ _ | .max _ _ | .imax _ _ | .mvar _ => False.elim Helim

/-- The independently specified common parameters remain definitionally
equal to the exact cached executable suffix after universe rebasing. -/
theorem CheckedRecursorHeaderAt.recursorParamsContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    let R := Hc.toAdmissibleRecursorContextWF Helim
    let Hsuffix := H.materialized.parameterSuffix.toRecursorContext Helim
    VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx := by
  dsimp only
  cases elimLevel with
  | zero => exact H.materialized.paramsContext
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    change VEnv.IsDefEqCtx Hc.venv (fresh :: c.lparams).length []
      (H.materialized.headers.params.map (VExpr.instL shift)).reverse
      (H.materialized.parameterScope.instL shift).toCtx
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    have hctx := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.instL hshift
      H.materialized.paramsContext
    simpa only [CheckedRecursorHeaderAt.recursorParams,
      List.map_reverse, List.map_nil, TypeChecker.MLCtx.prependLevelParam_vlctx,
      VLCtx.instL_toCtx, shift] using hctx
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Expose the next family-local parameter from the independent `TypeShape`
after shifting it beneath the optional fresh recursor universe parameter. -/
theorem CheckedRecursorHeaderAt.recursorNextParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    (hi : i < decl.nparams) :
    ∃ (ownParams : List VExpr)
        (expectedDomain expectedBody targetType : VExpr),
      ownParams.length = decl.nparams ∧
      ownParams[i]? = some expectedDomain ∧
      VEnv.IsDefEqCtx Hc.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams).length []
        (H.recursorParams Helim).reverse ownParams.reverse ∧
      Hc.venv.IsDefEq
        (AddInductive.getRecLevelParams elimLevel c.lparams).length []
        (H.recursorTargetSkeleton Helim).type
        (VExpr.wrapForalls (ownParams.take i)
          (.forallE expectedDomain expectedBody)) targetType := by
  have hshape : decl.TypeShape Hc.venv
      H.materialized.headers.params H.target :=
    H.materialized.headers.typeShapes H.target
      (List.mem_of_getElem? H.targetAt)
  cases elimLevel with
  | zero =>
    simpa [AddInductive.getRecLevelParams,
      CheckedRecursorHeaderAt.recursorParams,
      CheckedRecursorHeaderAt.recursorTargetSkeleton,
      VInductDecl.ParamsDefEq, VInductiveType.toSkeleton,
      H.materialized.uvars] using
      VInductDecl.TypeShape.nextParameter hshape hi
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    change ∃ (ownParams : List VExpr)
        (expectedDomain expectedBody targetType : VExpr),
      ownParams.length = decl.nparams ∧
      ownParams[i]? = some expectedDomain ∧
      VEnv.IsDefEqCtx Hc.venv (fresh :: c.lparams).length []
        (H.materialized.headers.params.map
          (VExpr.instL shift)).reverse ownParams.reverse ∧
      Hc.venv.IsDefEq (fresh :: c.lparams).length []
        (H.target.type.instL shift)
        (VExpr.wrapForalls (ownParams.take i)
          (.forallE expectedDomain expectedBody)) targetType
    rcases VInductDecl.TypeShape.nextParameter hshape hi with
      ⟨ownParams, expectedDomain, expectedBody, targetType,
        hlength, hget, hown, hpresentation⟩
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    let ownParams' := ownParams.map (VExpr.instL shift)
    let expectedDomain' := expectedDomain.instL shift
    let expectedBody' := expectedBody.instL shift
    let targetType' := targetType.instL shift
    refine ⟨ownParams', expectedDomain', expectedBody', targetType',
      ?_, ?_, ?_, ?_⟩
    · simp [ownParams', hlength]
    · simp [ownParams', expectedDomain', hget]
    · have hown' :=
        Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.instL hshift hown
      simpa only [CheckedRecursorHeaderAt.recursorParams,
        ownParams', List.map_reverse, List.map_nil, shift] using hown'
    · have hpresentation' := hpresentation.instL hshift
      have instL_wrapForalls (domains : List VExpr) (result : VExpr) :
          (VExpr.wrapForalls domains result).instL shift =
            VExpr.wrapForalls (domains.map (VExpr.instL shift))
              (result.instL shift) := by
        induction domains with
        | nil => rfl
        | cons domain domains ih =>
          change VExpr.forallE (domain.instL shift)
              ((VExpr.wrapForalls domains result).instL shift) =
            VExpr.forallE (domain.instL shift)
              (VExpr.wrapForalls (domains.map (VExpr.instL shift))
                (result.instL shift))
          exact congrArg (VExpr.forallE (domain.instL shift)) ih
      simpa only [CheckedRecursorHeaderAt.recursorTargetSkeleton,
        ownParams', expectedDomain', expectedBody', targetType',
        List.map_nil, List.map_take, List.map_reverse,
        VExpr.instL, instL_wrapForalls] using hpresentation'
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The next domain exposed by independent rebased header synthesis is the
exact cached parameter declaration selected in the current recursor context.
No successful executable `isDefEq` result is used to establish the match. -/
theorem CheckedRecursorHeaderAt.recursorCurrentDomainDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {c' : AddInductive.Context}
    {R : RecursorContextWF c'
      (AddInductive.getRecLevelParams elimLevel c.lparams)}
    {Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {currentDomain currentBody : VExpr}
    (Hscope : RecursorLaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) Hscope.older
        (.forallE currentDomain currentBody) i 0)
    (hi : i < stats.params.size)
    (henv : R.venv = Hc.venv)
    (hctx : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx) :
    R.venv.IsDefEqU
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      Hscope.older.toCtx currentDomain Hscope.paramType := by
  have hparameterCount : stats.params.size = decl.nparams := by
    have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      H.materialized.narrowParams
    simpa [VInductDecl.paramVars] using hlength
  have hiDecl : i < decl.nparams := by
    rw [← hparameterCount]
    exact hi
  rcases H.recursorNextParameter Helim hiDecl with
    ⟨ownParams, expectedDomain, expectedBody, targetType,
      hownLength, hget, hown, hpresentation⟩
  have hiOwn : i < ownParams.length := by omega
  have hexpected : expectedDomain = ownParams[i] := by
    have hget' : some ownParams[i] = some expectedDomain := by
      simpa [List.getElem?_eq_getElem hiOwn] using hget
    exact (Option.some.inj hget').symm
  have hindices : Hsynthesis.indices = [] :=
    List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
  have hprefixLength : Hsynthesis.params.length =
      (ownParams.take i).length := by
    rw [Hsynthesis.parameterCount, List.length_take]
    omega
  have hpresentationR : R.venv.IsDefEq
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (H.recursorTargetSkeleton Helim).type
      (VExpr.wrapForalls (ownParams.take i)
        (.forallE expectedDomain expectedBody)) targetType := by
    simpa [henv] using hpresentation
  rcases Hsynthesis.nextDomainDefEq R.checking.tr.wf hindices
      hprefixLength hpresentationR with ⟨nextLevel, hnext⟩
  have hscopeCtx : Hscope.older.toCtx = Hsynthesis.params.reverse := by
    simpa [hindices] using Hsynthesis.scopeCtx
  have hnext' : R.venv.IsDefEq
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      Hscope.older.toCtx currentDomain expectedDomain (.sort nextLevel) := by
    rw [hscopeCtx]
    exact hnext
  have hparamsLength : (H.recursorParams Helim).length =
      stats.params.size := by
    have hctxLength := H.materialized.paramsContext.length_eq
    have hcachedCtx :=
      checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
        H.materialized.cachedScope
    have hcachedLength :=
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
        H.materialized.cachedScope
    have hbaseLength : H.materialized.headers.params.length =
        stats.params.size := by
      calc
        H.materialized.headers.params.length =
            H.materialized.headers.params.reverse.length := by simp
        _ = H.materialized.parameterScope.toCtx.length := hctxLength
        _ = H.materialized.parameterScope.length := hcachedCtx
        _ = stats.params.size := by simpa using hcachedLength.symm
    cases elimLevel with
    | zero => simpa [CheckedRecursorHeaderAt.recursorParams]
        using hbaseLength
    | param fresh => simpa [CheckedRecursorHeaderAt.recursorParams]
        using hbaseLength
    | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
      simp [AddInductive.AdmissibleElimLevel] at Helim
  have hownR : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (H.recursorParams Helim).reverse ownParams.reverse := by
    simpa [henv] using hown
  rcases Hscope.ownParameterDefEq hi hparamsLength hctx hownR with
    ⟨cachedLevel, hcached⟩
  have hcached' : R.venv.IsDefEq
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      Hscope.older.toCtx expectedDomain Hscope.paramType
      (.sort cachedLevel) := by
    simpa [hexpected] using hcached
  exact ⟨_, hnext'.trans_r R.checking.tr.wf
    (Hscope.lift.wf R.checking.tr.wf R.mlctx_wf.tr.wf).1.toCtx
    hcached'⟩

@[simp] theorem CheckedRecursorHeaderAt.recursorTargetSkeleton_zero
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams (.zero)) :
    H.recursorTargetSkeleton Helim = H.target.toSkeleton := rfl

/-- The closed concrete source header translates to the rebased semantic
header under the exact universe list assigned to generated recursors. -/
theorem CheckedRecursorHeaderAt.recursorSourceTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    TrExprS Hc.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) []
      source.type (H.recursorTargetSkeleton Helim).type := by
  cases elimLevel with
  | zero => exact H.sourceTranslation.type
  | param fresh =>
    change TrExprS Hc.venv (fresh :: c.lparams) [] source.type
      (H.target.type.instL (VLevel.prependShift c.lparams.length))
    simpa [VLCtx.instL] using H.sourceTranslation.type.prependLevelParam
      Hc.checking.tr.wf (by trivial) Helim
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The rebased semantic header remains a type in the recursor universe
context. -/
theorem CheckedRecursorHeaderAt.recursorTargetType
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    Hc.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (H.recursorTargetSkeleton Helim).type := by
  have htarget : Hc.venv.IsType c.lparams.length [] H.target.type := by
    have htyped := H.sourceTranslation.wf
    change Hc.venv.IsType H.target.uvars [] H.target.type at htyped
    rwa [H.sourceTranslation.uvars] at htyped
  cases elimLevel with
  | zero => exact htarget
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    exact htarget.instL hshift
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Normalize a later mutual-family header in the actual generated recursor
context and restart independent narrow synthesis in the empty closed scope.
This is the first operational step that remains valid after earlier major and
motive frames have introduced the fresh large-elimination universe. -/
theorem CheckedRecursorHeaderAt.startRecursorHeaderSemantics
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {c' : AddInductive.Context}
    (R : RecursorContextWF c'
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    (henv : R.venv = Hc.venv)
    (hwhnf : WhnfLParamsCompat) :
    ((monadLift (TypeChecker.whnf source.type) :
        AddInductive.M Expr) c').WF fun normalized =>
      FVarsBelow R.mlctx.vlctx source.type normalized ∧
      ∃ normalizedTarget,
        TrExprS R.venv
          (AddInductive.getRecLevelParams elimLevel c.lparams) []
          normalized normalizedTarget ∧
        Nonempty
          (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
            R.venv
            (AddInductive.getRecLevelParams elimLevel c.lparams)
            (H.recursorTargetSkeleton Helim) [] normalizedTarget 0 0) := by
  let recLparams :=
    AddInductive.getRecLevelParams elimLevel c.lparams
  have htarget : TrExprS R.venv recLparams [] source.type
      (H.recursorTargetSkeleton Helim).type := by
    simpa [recLparams, henv] using H.recursorSourceTranslation Helim
  have htargetType : R.venv.IsType recLparams.length []
      (H.recursorTargetSkeleton Helim).type := by
    simpa [recLparams, henv] using H.recursorTargetType Helim
  let W : VLCtx.FVLift [] R.mlctx.vlctx 0
      R.mlctx.vlctx.toCtx.length 0 :=
    VLCtx.FVLift.from_nil R.mlctx.noBV
  have hsource := htarget.weakFV R.checking.tr.wf.ordered W
    R.mlctx_wf.tr.wf
  have hnormalize := whnfInRecursorContext.scopeWF hwhnf R hsource
  exact hnormalize.mono fun normalized hnormalized => by
    have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
      htarget.fvarsIn.mono fun fv hfv => by
        simpa [VLCtx.fvars] using hfv
    have hfalseUpSet : IsFVarUpSet (fun _ => False) R.mlctx.vlctx := by
      have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
        R.mlctx.vlctx (by simpa using R.mlctx_wf.tr.wf)
      simpa [VLCtx.fvars] using hsuffix
    have hnormalizedNoFVars : FVarsIn (fun _ => False) normalized :=
      hnormalized.1 _ hfalseUpSet hsourceNoFVars
    rcases R.initialClosedHeaderDefEq htarget hsource hnormalized.2
        hnormalizedNoFVars with
      ⟨normalizedTarget, hnormalizedTarget, hheader⟩
    have hnormalizedType : R.venv.IsType recLparams.length []
        normalizedTarget :=
      htargetType.defeqU_l R.checking.tr.wf (by trivial) hheader
    rcases htargetType with ⟨targetLevel, htargetHasType⟩
    have hheaderTyped := hheader.of_l R.checking.tr.wf (by trivial)
      htargetHasType
    exact ⟨hnormalized.1, normalizedTarget, hnormalizedTarget,
      ⟨checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.empty
        ⟨targetLevel, htargetHasType⟩ hnormalizedType hheaderTyped⟩⟩

theorem CheckedRecursorHeaderAt.target_mem
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx) :
    H.target ∈ decl.types :=
  List.mem_of_getElem? H.targetAt

theorem CheckedRecursorHeaderAt.shape
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx) :
    decl.TypeShape Hc.venv H.materialized.headers.params H.target :=
  H.materialized.headers.typeShapes H.target H.target_mem

theorem CheckedRecursorHeaderAt.parameterCount
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx) :
    stats.params.size = decl.nparams := by
  have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
    H.materialized.narrowParams
  simpa [VInductDecl.paramVars] using hlength

def CheckedRecursorHeaderAt.parameterSuffix
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx) :
    checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth :=
  H.materialized.parameterSuffix

/-- Preserve a selected family header after one verified recursor-frame
declaration is added to the ambient executable context. -/
def CheckedRecursorHeaderAt.withAmbient
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
    CheckedRecursorHeaderAt Hc' stats decl (depth + 1) source familyIdx := by
  dsimp only
  exact {
    target := H.target
    targetAt := H.targetAt
    materialized := H.materialized.withAmbient
      (name := name) (bi := bi) htr hty
    sourceTranslation := H.sourceTranslation
    targetLookup := H.targetLookup
    lparamsNodup := H.lparamsNodup }

theorem CheckedRecursorHeaderAt.paramsContext
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx) :
    VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      H.materialized.headers.params.reverse
      H.parameterSuffix.parameterDecls.toCtx := by
  exact H.materialized.paramsContext

theorem CheckedRecursorHeaderAt.indexCount
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx) :
    stats.nindices[familyIdx]? = some H.target.numIndices := by
  have htargetBound : familyIdx < decl.types.length :=
    List.getElem?_eq_some_iff.mp H.targetAt |>.1
  have hstatsLength : stats.nindices.size = decl.types.length := by
    simpa using congrArg List.length H.materialized.indices
  have hstatsBound : familyIdx < stats.nindices.size := by omega
  rw [Array.getElem?_eq_getElem hstatsBound]
  have hentry := congrArg (fun values => values[familyIdx]?)
    H.materialized.indices
  simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hstatsBound,
    List.getElem?_map, H.targetAt, Option.map_some] at hentry
  exact hentry

def CheckedRecursorHeaderAt.abstractLevels
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx) :
    List VLevel :=
  c.lparams.map fun name => .param (c.lparams.idxOf name)

theorem CheckedRecursorHeaderAt.abstractLevels_eq_params
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx) :
    H.abstractLevels = VLevel.params c.lparams.length := by
  apply List.ext_getElem
  · simp [CheckedRecursorHeaderAt.abstractLevels, VLevel.params]
  · intro i hleft hright
    have hi : i < c.lparams.length := by
      simpa [VLevel.params] using hright
    simp [CheckedRecursorHeaderAt.abstractLevels, VLevel.params,
      H.lparamsNodup.idxOf_getElem i hi]

theorem CheckedRecursorHeaderAt.targetType_inst_abstractLevels
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx) :
    H.target.type.instL H.abstractLevels = H.target.type := by
  rw [H.abstractLevels_eq_params, ← H.sourceTranslation.uvars]
  have htyped := Classical.choose_spec H.sourceTranslation.wf
  exact (htyped.levelWF (by trivial)).1.instL_id

/-- Universe arguments of the installed family constant as seen from the
generated recursor.  Large elimination inserts one fresh leading universe,
so every original declaration argument is shifted by one slot. -/
def CheckedRecursorHeaderAt.recursorAbstractLevels
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    List VLevel :=
  match elimLevel with
  | .zero => H.abstractLevels
  | .param _ => H.abstractLevels.map
      (VLevel.inst (VLevel.prependShift c.lparams.length))
  | .succ _ | .max _ _ | .imax _ _ | .mvar _ => False.elim Helim

theorem CheckedRecursorHeaderAt.recursorAbstractLevels_length
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    (H.recursorAbstractLevels Helim).length = H.target.uvars := by
  cases elimLevel with
  | zero =>
    simp [CheckedRecursorHeaderAt.recursorAbstractLevels,
      H.abstractLevels_eq_params, H.sourceTranslation.uvars]
  | param fresh =>
    simp [CheckedRecursorHeaderAt.recursorAbstractLevels,
      H.abstractLevels_eq_params, H.sourceTranslation.uvars]
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem CheckedRecursorHeaderAt.recursorAbstractLevels_wf
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    ∀ level ∈ H.recursorAbstractLevels Helim,
      level.WF
        (AddInductive.getRecLevelParams elimLevel c.lparams).length := by
  cases elimLevel with
  | zero =>
    intro level hlevel
    rw [CheckedRecursorHeaderAt.recursorAbstractLevels,
      H.abstractLevels_eq_params] at hlevel
    exact VLevel.params_wf hlevel
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    rw [CheckedRecursorHeaderAt.recursorAbstractLevels]
    intro level hlevel
    rw [List.mem_map] at hlevel
    rcases hlevel with ⟨sourceLevel, hsourceLevel, rfl⟩
    exact VLevel.WF.inst hshift
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The installed family constant at its concrete translated universe
arguments has the original abstract header type. -/
theorem CheckedRecursorHeaderAt.constHasType
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx) :
    Hc.venv.HasType c.lparams.length []
      (.const H.target.name H.abstractLevels) H.target.type := by
  have hlevels : ∀ level ∈ H.abstractLevels,
      level.WF c.lparams.length := by
    rw [H.abstractLevels_eq_params]
    exact VLevel.params_wf
  have hlength : H.abstractLevels.length = H.target.uvars := by
    rw [H.abstractLevels_eq_params, VLevel.params_length,
      H.sourceTranslation.uvars]
  have hconst := VEnv.HasType.const (Γ := []) H.targetLookup hlevels hlength
  simpa [H.targetType_inst_abstractLevels] using hconst

/-- The family constant remains typed after the optional recursor-universe
shift, independently of how many earlier mutual frames are in the local
context. -/
theorem CheckedRecursorHeaderAt.recursorConstHasType
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    (henv : R.venv = Hc.venv) :
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (.const H.target.name (H.recursorAbstractLevels Helim))
      (H.recursorTargetSkeleton Helim).type := by
  cases elimLevel with
  | zero =>
    simpa [CheckedRecursorHeaderAt.recursorAbstractLevels,
      CheckedRecursorHeaderAt.recursorTargetSkeleton,
      AddInductive.getRecLevelParams, VInductiveType.toSkeleton, henv] using
      H.constHasType
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    have htyped := H.constHasType.instL hshift
    simpa [CheckedRecursorHeaderAt.recursorAbstractLevels,
      CheckedRecursorHeaderAt.recursorTargetSkeleton,
      AddInductive.getRecLevelParams, VExpr.instL, shift, henv] using
      htyped
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- The concrete family constant retained in the mutable statistics translates
to the independently installed abstract family constant, with exactly the
universe arguments produced from the declaration's level parameters. -/
theorem CheckedRecursorHeaderAt.indConstTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    {c' : AddInductive.Context} {Hc' : ContextWF c'} {scope : VLCtx}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams
      scope stats decl appDepth)
    (henv : Hc'.venv = Hc.venv)
    (hlparams : c'.lparams = c.lparams) :
    TrExprS Hc'.venv c'.lparams scope stats.indConsts[familyIdx]!
      (.const H.target.name H.abstractLevels) := by
  have hbound : familyIdx < decl.types.length :=
    List.getElem?_eq_some_iff.mp H.targetAt |>.1
  have htarget : decl.types[familyIdx] = H.target := by
    have htargetAt := H.targetAt
    rw [List.getElem?_eq_getElem hbound] at htargetAt
    exact Option.some.inj htargetAt
  have hconst := Hstats.indConstAt hbound
  have hsource : stats.indConsts[familyIdx]! =
      .const H.target.name stats.levels := by
    simp [Array.getElem!_eq_getD, hconst, htarget]
  rw [hsource]
  have htr : TrExprS Hc.venv c.lparams scope
      (.const H.target.name stats.levels)
      (.const H.target.name H.abstractLevels) := by
    apply TrExprS.const H.targetLookup H.materialized.levelTranslation
    have hlevels := Hstats.levels
    have huvars := H.materialized.uvars
    have htargetUvars := H.sourceTranslation.uvars
    omega
  simpa [henv, hlparams] using htr

/-- Recursor-universe analogue of `indConstTranslation`.  It selects the
same executable family constant but translates its universe arguments after
the optional fresh leading recursor parameter. -/
theorem CheckedRecursorHeaderAt.recursorIndConstTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx}
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl appDepth)
    (henv : R.venv = Hc.venv) :
    TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope
      stats.indConsts[familyIdx]!
      (.const H.target.name (H.recursorAbstractLevels Helim)) := by
  have hbound : familyIdx < decl.types.length :=
    List.getElem?_eq_some_iff.mp H.targetAt |>.1
  have htarget : decl.types[familyIdx] = H.target := by
    have htargetAt := H.targetAt
    rw [List.getElem?_eq_getElem hbound] at htargetAt
    exact Option.some.inj htargetAt
  have hconst : stats.indConsts[familyIdx]? =
      some (.const decl.types[familyIdx].name stats.levels) := by
    rw [Hstats.consts.exact]
    simp [hbound]
  have hsource : stats.indConsts[familyIdx]! =
      .const H.target.name stats.levels := by
    simp [Array.getElem!_eq_getD, hconst, htarget]
  rw [hsource]
  have hlevels : stats.levels.mapM
      (VLevel.ofLevel
        (AddInductive.getRecLevelParams elimLevel c.lparams)) =
      some (H.recursorAbstractLevels Helim) := by
    cases elimLevel with
    | zero =>
      simpa [CheckedRecursorHeaderAt.recursorAbstractLevels,
        CheckedRecursorHeaderAt.abstractLevels,
        AddInductive.getRecLevelParams] using
        H.materialized.levelTranslation
    | param fresh =>
      have hshifted := VLevel.mapM_ofLevel_fresh_cons Helim
        H.materialized.levelTranslation
      simpa [CheckedRecursorHeaderAt.recursorAbstractLevels,
        CheckedRecursorHeaderAt.abstractLevels,
        AddInductive.getRecLevelParams] using hshifted
    | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
      simp [AddInductive.AdmissibleElimLevel] at Helim
  apply TrExprS.const (by simpa [henv] using H.targetLookup) hlevels
  have hlevelsLength := Hstats.levels
  have huvars := H.materialized.uvars
  have htargetUvars := H.sourceTranslation.uvars
  omega

/-- The executable arity guard identifies the completed replay with this
family's independently materialized index arity.  Keeping all three equalities
at this boundary avoids recovering them separately when constructing the
major premise and motive telescope. -/
theorem CheckedRecursorHeaderAt.completedIndexCount
    {c' : AddInductive.Context} {Hc' : ContextWF c'}
    {indices : Array Expr} {indexTargets : List VExpr} {nindices : Nat}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Hindices : List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true) :
    indices.size = H.target.numIndices ∧
      indexTargets.length = H.target.numIndices ∧
      nindices = H.target.numIndices := by
  have htranslated : indices.size = indexTargets.length := by
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hindices
  have hguard : indices.size = stats.nindices[familyIdx]! := by
    simpa using harity
  have hfamily : stats.nindices[familyIdx]! = H.target.numIndices := by
    simp [Array.getElem!_eq_getD, H.indexCount]
  omega

theorem CheckedRecursorHeaderAt.completedIndexVars
    {c' : AddInductive.Context} {Hc' : ContextWF c'}
    {indices : Array Expr} {indexTargets : List VExpr} {nindices : Nat}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Hindices : List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true) :
    indexTargets = canonicalIndexVars H.target.numIndices := by
  rcases H.completedIndexCount Hindices hreplay harity with
    ⟨_concrete, _abstract, hnindices⟩
  simpa [hnindices] using hcanonical

/-- At the successful family-local arity guard, the two executable application
spines translate pointwise to the exact parameter variables at the current
ambient depth followed by the canonical index variables. -/
theorem CheckedRecursorHeaderAt.completedArguments
    {c' : AddInductive.Context} {Hc' : ContextWF c'}
    {indices : Array Expr} {indexTargets : List VExpr} {nindices : Nat}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams
      Hc'.mlctx.vlctx stats decl (depth + nindices))
    (Hindices : List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true) :
    List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
      (stats.params.toList ++ indices.toList)
      (decl.paramVars (depth + H.target.numIndices) ++
        canonicalIndexVars H.target.numIndices) := by
  rcases H.completedIndexCount Hindices hreplay harity with
    ⟨_concrete, _abstract, hnindices⟩
  have Hall :=
    Lean4Lean.VerifyInductive.List.Forall₂.append' Hstats.params Hindices
  simpa [hnindices, hcanonical] using Hall

/-- The same completed executable argument spine in the independently
synthesized parameter/index scope.  At narrow depth `numIndices`, common
parameter variables followed by index variables collapse to the canonical
variables for the entire family header. -/
theorem CheckedRecursorHeaderAt.completedNarrowArguments
    {c' : AddInductive.Context} {Hc' : ContextWF c'}
    {scope : VLCtx} {indices : Array Expr} {indexTargets : List VExpr}
    {nindices : Nat}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams
      scope stats decl nindices)
    (Hindices : List.Forall₂ (TrExprS Hc'.venv c'.lparams scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true) :
    List.Forall₂ (TrExprS Hc'.venv c'.lparams scope)
      (stats.params.toList ++ indices.toList)
      (canonicalIndexVars (decl.nparams + H.target.numIndices)) := by
  have htranslated : indices.size = indexTargets.length := by
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hindices
  have hguard : indices.size = stats.nindices[familyIdx]! := by
    simpa using harity
  have hfamily : stats.nindices[familyIdx]! = H.target.numIndices := by
    simp [Array.getElem!_eq_getD, H.indexCount]
  have hnindices : nindices = H.target.numIndices := by omega
  have Hall :=
    Lean4Lean.VerifyInductive.List.Forall₂.append' Hstats.params Hindices
  rw [hcanonical, VInductDecl.paramVars_append_canonicalIndexVars] at Hall
  simpa [hnindices, H.parameterCount] using Hall

/-- Applying the independently installed family constant to the canonical
variables of the completed synthesized header yields its residual type in the
exact narrow replay scope. -/
theorem CheckedRecursorHeaderAt.canonicalFamilyApplication
    {c : AddInductive.Context} {Hc : ContextWF c}
    {c' : AddInductive.Context} {Hc' : ContextWF c'}
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc'.venv c'.lparams H.target.toSkeleton scope narrowTarget
        stats.params.size nindices)
    (henv : Hc'.venv = Hc.venv)
    (hlparams : c'.lparams = c.lparams)
    (hnindices : nindices = H.target.numIndices) :
    Hc'.venv.HasType c'.lparams.length scope.toCtx
      (VExpr.mkApps (.const H.target.name H.abstractLevels)
        (canonicalIndexVars (decl.nparams + H.target.numIndices)))
      narrowTarget := by
  have hhead : Hc'.venv.HasType c'.lparams.length []
      (.const H.target.name H.abstractLevels) H.target.type := by
    simpa [henv, hlparams] using H.constHasType
  have hheadTelescope : Hc'.venv.HasType c'.lparams.length []
      (.const H.target.name H.abstractLevels)
      (VExpr.wrapForalls (Hsynthesis.params ++ Hsynthesis.indices)
        narrowTarget) := by
    apply hhead.defeqU_r Hc'.checking.tr.wf (by trivial)
    exact ⟨Hsynthesis.exprType, by
      simpa [VInductiveType.toSkeleton] using Hsynthesis.header⟩
  have happ := VEnv.HasType.mkApps_wrapForalls_canonical
    Hc'.checking.tr.wf.ordered hheadTelescope
  have hparamCount : Hsynthesis.params.length = decl.nparams := by
    rw [Hsynthesis.parameterCount, H.parameterCount]
  have hindexCount : Hsynthesis.indices.length = H.target.numIndices := by
    rw [Hsynthesis.indexCount, hnindices]
  simpa [List.reverse_append, Hsynthesis.scopeCtx, hparamCount,
    hindexCount, canonicalIndexVars, VExpr.liftN, ← List.map_reverse] using happ

/-- At the successful family arity guard, the exact executable type used for
the major premise strictly translates in the independent replay scope to the
canonical abstract family application, and that application has the residual
header type. -/
theorem CheckedRecursorHeaderAt.completedNarrowFamilyApplication
    {c : AddInductive.Context} {Hc : ContextWF c}
    {c' : AddInductive.Context} {Hc' : ContextWF c'}
    {scope : VLCtx} {type : VExpr}
    {indices : Array Expr} {indexTargets : List VExpr} {nindices : Nat}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc'.venv c'.lparams H.target.toSkeleton scope type
        stats.params.size nindices)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams
      scope stats decl nindices)
    (Hindices : List.Forall₂ (TrExprS Hc'.venv c'.lparams scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true)
    (henv : Hc'.venv = Hc.venv)
    (hlparams : c'.lparams = c.lparams) :
    TrExprS Hc'.venv c'.lparams scope
      (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params) indices)
      (VExpr.mkApps (.const H.target.name H.abstractLevels)
        (canonicalIndexVars (decl.nparams + H.target.numIndices))) ∧
    Hc'.venv.HasType c'.lparams.length scope.toCtx
      (VExpr.mkApps (.const H.target.name H.abstractLevels)
        (canonicalIndexVars (decl.nparams + H.target.numIndices))) type ∧
    Hc'.venv.IsType c'.lparams.length scope.toCtx
      (VExpr.mkApps (.const H.target.name H.abstractLevels)
        (canonicalIndexVars (decl.nparams + H.target.numIndices))) := by
  have htranslated : indices.size = indexTargets.length := by
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hindices
  have hguard : indices.size = stats.nindices[familyIdx]! := by
    simpa using harity
  have hfamily : stats.nindices[familyIdx]! = H.target.numIndices := by
    simp [Array.getElem!_eq_getD, H.indexCount]
  have hnindices : nindices = H.target.numIndices := by omega
  have hargs := H.completedNarrowArguments Hstats Hindices hreplay
    hcanonical harity
  have hhead := H.indConstTranslation Hstats henv hlparams
  have happ := H.canonicalFamilyApplication Hsynthesis henv hlparams hnindices
  have huvars : H.target.uvars = decl.uvars := by
    rw [H.sourceTranslation.uvars, H.materialized.uvars]
  have htargetWF : H.target.toVConstant.WF Hc'.venv := by
    simpa [henv] using H.sourceTranslation.wf
  have hshape : decl.TypeShape Hc'.venv
      H.materialized.headers.params H.target := by
    simpa [henv] using H.shape
  rcases typeShape_forallAritySort huvars Hc'.checking.tr.wf htargetWF
      hshape with
    ⟨functionType, typeLevel, hfunctionType, hfunctionShape⟩
  have hlevelsWF : ∀ level ∈ H.abstractLevels,
      level.WF c'.lparams.length := by
    rw [H.abstractLevels_eq_params, hlparams]
    exact VLevel.params_wf
  have hlevelsLength : H.abstractLevels.length = H.target.uvars := by
    rw [H.abstractLevels_eq_params, VLevel.params_length,
      H.sourceTranslation.uvars]
  have hfunctionTypeInst := hfunctionType.instL hlevelsWF
  have hlookup : Hc'.venv.constants H.target.name =
      some H.target.toVConstant := by
    simpa [henv] using H.targetLookup
  have hconstBase := VEnv.HasType.const (env := Hc'.venv)
    (U := c'.lparams.length) (Γ := scope.toCtx) hlookup
    hlevelsWF hlevelsLength
  have hconstType : Hc'.venv.HasType c'.lparams.length scope.toCtx
      (.const H.target.name H.abstractLevels)
      (functionType.instL H.abstractLevels) := by
    have hfunctionTypeInst' : Hc'.venv.IsDefEq c'.lparams.length []
        (H.target.type.instL H.abstractLevels)
        (functionType.instL H.abstractLevels)
        (.sort (typeLevel.inst H.abstractLevels)) := by
      simpa [henv, hlparams, VExpr.instL] using hfunctionTypeInst
    exact (hfunctionTypeInst'.weak0 Hc'.checking.tr.wf.ordered).defeq hconstBase
  have happType : Hc'.venv.IsType c'.lparams.length scope.toCtx
      (VExpr.mkApps (.const H.target.name H.abstractLevels)
        (canonicalIndexVars (decl.nparams + H.target.numIndices))) := by
    apply VEnv.HasType.mkApps_isType Hc'.checking.tr.wf
      Hsynthesis.scopeWF.toCtx hconstType
    · simpa [canonicalIndexVars] using
        hfunctionShape.instL H.abstractLevels
    · exact ⟨type, happ⟩
  have htr : TrExprS Hc'.venv c'.lparams scope
      (Expr.mkAppList stats.indConsts[familyIdx]!
        (stats.params.toList ++ indices.toList))
      (VExpr.mkApps (.const H.target.name H.abstractLevels)
        (canonicalIndexVars (decl.nparams + H.target.numIndices))) :=
    checkPositivityStep.TrExprS.mkAppList Hc'.checking.tr.wf.ordered
      Hsynthesis.scopeWF.toCtx hhead hargs ⟨_, happ⟩
  refine ⟨?_, happ, happType⟩
  simpa [Expr.mkAppN_eq_mkAppList, Expr.mkAppList_append] using htr

/-- The exact executable family application used for the major premise has a
well-formed annotation-consumed interpretation in the actual reader context.
The independent family shape establishes typehood in the narrow header scope;
the recorded scope embedding and annotation compatibility are used only at
the executable boundary. -/
theorem CheckedRecursorHeaderAt.completedMajorDomain
    {c : AddInductive.Context} {Hc : ContextWF c}
    {c' : AddInductive.Context} {Hc' : ContextWF c'}
    {scope : VLCtx} {type : VExpr}
    {indices : Array Expr} {indexTargets : List VExpr}
    {nindices : Nat}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc'.venv c'.lparams H.target.toSkeleton scope type
        stats.params.size nindices)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc'.venv c'.lparams scope Hc'.mlctx.vlctx)
    (Hindices : List.Forall₂ (TrExprS Hc'.venv c'.lparams scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true)
    (henv : Hc'.venv = Hc.venv)
    (hlparams : c'.lparams = c.lparams)
    (hconsume : ConsumeTypeAnnotationsCompat) :
    ∃ sourceTarget consumedTarget,
      Hc'.ConsumedDomain
        (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params) indices)
        sourceTarget consumedTarget := by
  rcases H.completedNarrowFamilyApplication Hsynthesis Hstats Hindices
      hreplay hcanonical harity henv hlparams with
    ⟨hnarrow, _happ, hnarrowType⟩
  rcases Hruntime.transportType Hc'.checking.tr.wf hnarrow hnarrowType with
    ⟨sourceTarget, hsource, hsourceType⟩
  rcases hconsume c' Hc' hsource hsourceType with
    ⟨consumedTarget, Hconsumed⟩
  exact ⟨sourceTarget, consumedTarget, Hconsumed⟩

/-- Completed executable arguments in the independently synthesized scope,
interpreted under the recursor universe list. -/
theorem CheckedRecursorHeaderAt.completedRecursorNarrowArguments
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {indices : Array Expr} {indexTargets : List VExpr}
    {nindices : Nat}
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hindices : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true) :
    List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      (stats.params.toList ++ indices.toList)
      (canonicalIndexVars (decl.nparams + H.target.numIndices)) := by
  have htranslated : indices.size = indexTargets.length := by
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hindices
  have hguard : indices.size = stats.nindices[familyIdx]! := by
    simpa using harity
  have hfamily : stats.nindices[familyIdx]! = H.target.numIndices := by
    simp [Array.getElem!_eq_getD, H.indexCount]
  have hnindices : nindices = H.target.numIndices := by omega
  have Hall :=
    Lean4Lean.VerifyInductive.List.Forall₂.append' Hstats.params Hindices
  rw [hcanonical, VInductDecl.paramVars_append_canonicalIndexVars] at Hall
  simpa [hnindices, H.parameterCount] using Hall

/-- Applying the installed family constant to the canonical variables of a
rebased completed header yields its residual synthesized type. -/
theorem CheckedRecursorHeaderAt.recursorCanonicalFamilyPrefix
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (henv : R.venv = Hc.venv) :
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      Hsynthesis.params.reverse
      (VExpr.mkApps
        ((VExpr.const H.target.name (H.recursorAbstractLevels Helim)).liftN
          Hsynthesis.params.length 0)
        (recursorCanonicalVars Hsynthesis.params.length))
      (VExpr.wrapForalls Hsynthesis.indices narrowTarget) := by
  have hhead := H.recursorConstHasType Helim R henv
  have hheadTelescope : R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (.const H.target.name (H.recursorAbstractLevels Helim))
      (VExpr.wrapForalls (Hsynthesis.params ++ Hsynthesis.indices)
        narrowTarget) := by
    apply hhead.defeqU_r R.checking.tr.wf (by trivial)
    exact ⟨Hsynthesis.exprType, Hsynthesis.header⟩
  simpa [recursorCanonicalVars] using
    VEnv.HasType.mkApps_wrapForalls_prefix_canonical
      R.checking.tr.wf.ordered hheadTelescope

/-- The canonical family prefix remains typed after reopening the exact
index scope; both the prefix and its residual index telescope are shifted
beneath those ambient index variables. -/
theorem CheckedRecursorHeaderAt.recursorCanonicalFamilyPrefixAtScope
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (henv : R.venv = Hc.venv) :
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      ((VExpr.mkApps
        ((VExpr.const H.target.name (H.recursorAbstractLevels Helim)).liftN
          Hsynthesis.params.length 0)
        (recursorCanonicalVars Hsynthesis.params.length)).liftN
          Hsynthesis.indices.length 0)
      ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
        Hsynthesis.indices.length 0) := by
  have hprefix := H.recursorCanonicalFamilyPrefix Helim R Hsynthesis henv
  have hweakened := hprefix.weakN R.checking.tr.wf.ordered
    (Ctx.LiftN.zero Hsynthesis.indices.reverse)
  simpa [Hsynthesis.scopeCtx, List.reverse_append] using hweakened

/-- The concrete family prefix, before its indices are applied, translates
to the canonical parameter application in the completed narrow replay scope.
This is the translation counterpart of
`recursorCanonicalFamilyPrefixAtScope`. -/
theorem CheckedRecursorHeaderAt.recursorNarrowFamilyPrefixTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (henv : R.venv = Hc.venv) :
    let family := VExpr.mkApps
      (.const H.target.name (H.recursorAbstractLevels Helim))
      (decl.paramVars nindices)
    TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams) scope
        (mkAppN stats.indConsts[familyIdx]! stats.params) family ∧
      R.venv.HasType
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        scope.toCtx family
          ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
            nindices 0) := by
  dsimp only
  have hcanonical := H.recursorCanonicalFamilyPrefixAtScope Helim R
    Hsynthesis henv
  have hparamCount : Hsynthesis.params.length = decl.nparams := by
    rw [Hsynthesis.parameterCount, H.parameterCount]
  have hindexCount : Hsynthesis.indices.length = nindices :=
    Hsynthesis.indexCount
  have hfamilyType : R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (decl.paramVars nindices))
      ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
        nindices 0) := by
    simpa [recursorCanonicalVars, VInductDecl.paramVars, hparamCount,
      hindexCount, VExpr.liftN_mkApps, VExpr.liftN,
      ← List.map_reverse, Function.comp_def, Nat.add_comm] using hcanonical
  have hhead := H.recursorIndConstTranslation Helim R Hstats henv
  have htranslated := checkPositivityStep.TrExprS.mkAppList
    R.checking.tr.wf.ordered Hsynthesis.scopeWF.toCtx hhead Hstats.params
    (show VExpr.WF R.venv
        (AddInductive.getRecLevelParams elimLevel c.lparams).length
        scope.toCtx
        (VExpr.mkApps
          (.const H.target.name (H.recursorAbstractLevels Helim))
          (decl.paramVars nindices)) from ⟨_, hfamilyType⟩)
  exact ⟨by
    simpa [Expr.mkAppN_eq_mkAppList] using htranslated, hfamilyType⟩

/-- Transport the canonical narrow family-prefix typing into the executable
index context and identify its term with the prefix retained in the motive
frame.  Strict equality is available because the concrete constant/free-
variable application has unique translation. -/
theorem CheckedRecursorHeaderAt.completedRecursorFamilyPrefixTyping
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    {indices : Array Expr}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (henv : R.venv = Hc.venv)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    let familyType :=
      ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
        nindices 0).lift' Hruntime.shift
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      R.mlctx.vlctx.toCtx Hframe.familyTarget familyType := by
  dsimp only
  rcases H.recursorNarrowFamilyPrefixTranslation Helim R Hsynthesis Hstats
      henv with ⟨Hfamily, HfamilyType⟩
  have HfamilyWeak : TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hruntime.expanded
      (mkAppN stats.indConsts[familyIdx]! stats.params)
      ((VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (decl.paramVars nindices)).lift' Hruntime.shift) := by
    simpa using Hfamily.weakFV' R.checking.tr.wf.ordered Hruntime.lift
      Hruntime.context.wf
  have HtypeWeak := HfamilyType.weak' R.checking.tr.wf.ordered
    Hruntime.lift.toCtx
  have HtypeRuntime := HtypeWeak.defeqDFC R.checking.tr.wf.ordered
    Hruntime.context.defeqCtx
  have HfamilyEqU : R.venv.IsDefEqU
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      R.mlctx.vlctx.toCtx
      ((VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (decl.paramVars nindices)).lift' (Hruntime.shift.consN 0))
      Hframe.familyTarget := by
    have Heq := HfamilyWeak.uniq R.checking.tr.wf
      Hruntime.context Hframe.familyTr
    exact Heq.defeqDFC R.checking.tr.wf.ordered Hruntime.context.defeqCtx
  exact HtypeRuntime.defeqU_l R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx HfamilyEqU

/-- The canonical narrow family prefix and the prefix retained by the
executable motive frame are not merely definitionally equal.  Their source
is syntax-directed and the narrow/runtime contexts have the same declaration
spine, so translation uniqueness identifies the terms strictly. -/
theorem CheckedRecursorHeaderAt.completedRecursorFamilyPrefixEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    {indices : Array Expr}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (henv : R.venv = Hc.venv)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    (VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (decl.paramVars nindices)).lift' Hruntime.shift =
      Hframe.familyTarget := by
  rcases H.recursorNarrowFamilyPrefixTranslation Helim R Hsynthesis Hstats
      henv with ⟨Hfamily, _HfamilyType⟩
  have HfamilyWeak : TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hruntime.expanded
      (mkAppN stats.indConsts[familyIdx]! stats.params)
      ((VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (decl.paramVars nindices)).lift' Hruntime.shift) := by
    simpa using Hfamily.weakFV' R.checking.tr.wf.ordered Hruntime.lift
      Hruntime.context.wf
  exact TrExprS.unique'
    (Lean4Lean.VerifyInductive.VLCtx.IsDefEq.toIsUniqueCtx_ofOnlyLams
      Hruntime.context R.onlyLams)
    (Hstats.familyPrefixUnique familyIdx
      (List.getElem?_eq_some_iff.mp H.targetAt).1)
    HfamilyWeak Hframe.familyTr

/-- The index arguments recovered from the executable major application are
exactly the weakened canonical variables of the independent narrow replay.
The source array contains only retained free variables, so the same
cross-context uniqueness argument applies pointwise. -/
theorem CheckedRecursorHeaderAt.completedRecursorIndexTargetsEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    {indices : Array Expr} {indexTargets : List VExpr}
    (_Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (Hindices : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      indices.toList indexTargets)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (Hbound : BoundFVarArray current indices)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    (canonicalIndexVars nindices).map (fun target =>
        target.lift' Hruntime.shift) = Hframe.familyIndexTargets := by
  have Hweak : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      Hruntime.expanded) indices.toList
      (indexTargets.map fun target => target.lift' Hruntime.shift) := by
    apply checkPositivityStep.forall₂_map_right Hindices
    intro source target Hsource
    simpa using Hsource.weakFV' R.checking.tr.wf.ordered Hruntime.lift
      Hruntime.context.wf
  have hbound : indices.toList = Hbound.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList Hbound.expressions
  have Hunique : ∀ source ∈ indices.toList,
      TrExprS.IsUnique source := by
    intro source hsource
    rw [hbound] at hsource
    rcases List.mem_map.mp hsource with ⟨fv, _hfv, rfl⟩
    trivial
  have Heq := Lean4Lean.VerifyInductive.TrExprS.forall₂_unique
    (Lean4Lean.VerifyInductive.VLCtx.IsDefEq.toIsUniqueCtx_ofOnlyLams
      Hruntime.context R.onlyLams)
    Hunique Hweak Hframe.familyIndicesTr
  simpa [hcanonical] using Heq

/-- Instantiate the abstract parallel motive telescope from the independently
checked header, weaken it through the exact runtime embedding, and identify
its family head with the executable frame by strict translation uniqueness. -/
theorem CheckedRecursorHeaderAt.completedRecursorCanonicalMotiveFrame
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    {indices : Array Expr}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (henv : R.venv = Hc.venv)
    (hindices : indices.size = nindices)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    ∃ Hcanonical : RecursorMotiveCanonicalFrameWF R stats familyIdx
        indices elimLevel Hframe,
      Hcanonical.familyType =
        ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
          nindices 0).lift' Hruntime.shift ∧
      Hcanonical.motiveType =
        ((VExpr.wrapForalls Hsynthesis.indices
          (.forallE
            (VExpr.mkApps
              ((VExpr.mkApps
                (.const H.target.name (H.recursorAbstractLevels Helim))
                (recursorCanonicalVars Hsynthesis.params.length)).liftN
                  Hsynthesis.indices.length 0)
              (recursorCanonicalVars Hsynthesis.indices.length))
            (.sort Hframe.resultLevel))).liftN nindices 0).lift'
              Hruntime.shift := by
  let familyBase := VExpr.mkApps
    (.const H.target.name (H.recursorAbstractLevels Helim))
    (recursorCanonicalVars Hsynthesis.params.length)
  let Hbase := RecursorMotiveTelescope.wrapForalls Hsynthesis.indices
    familyBase narrowTarget Hframe.resultLevel
  let Hscope := Hbase.liftN nindices 0
  let Hfull := Hscope.lift' Hruntime.shift
  have hparameterCount : Hsynthesis.params.length = decl.nparams := by
    rw [Hsynthesis.parameterCount, H.parameterCount]
  have hfamilyScope : familyBase.liftN nindices 0 =
      VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (decl.paramVars nindices) := by
    simp [familyBase, recursorCanonicalVars, VInductDecl.paramVars,
      VExpr.liftN_mkApps, VExpr.liftN, hparameterCount,
      ← List.map_reverse, Function.comp_def, Nat.add_comm]
  have hfamily := H.completedRecursorFamilyPrefixEq Helim R Hsynthesis
    Hstats Hruntime henv Hframe
  have hfamilyFull :
      (familyBase.liftN nindices 0).lift' Hruntime.shift =
        Hframe.familyTarget := by
    rw [hfamilyScope]
    exact hfamily
  have Htelescope : RecursorMotiveTelescope Hframe.resultLevel indices.size
      Hframe.familyTarget
      (((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
        nindices 0).lift' Hruntime.shift)
      (((VExpr.wrapForalls Hsynthesis.indices
        (.forallE
          (VExpr.mkApps (familyBase.liftN Hsynthesis.indices.length 0)
            (recursorCanonicalVars Hsynthesis.indices.length))
          (.sort Hframe.resultLevel))).liftN nindices 0).lift'
            Hruntime.shift) := by
    have harity : Hsynthesis.indices.length = indices.size :=
      Hsynthesis.indexCount.trans hindices.symm
    have Hfull' := Hfull
    rw [hfamilyFull] at Hfull'
    simpa only [harity] using Hfull'
  refine ⟨{
    familyType :=
      ((VExpr.wrapForalls Hsynthesis.indices narrowTarget).liftN
        nindices 0).lift' Hruntime.shift
    motiveType :=
      ((VExpr.wrapForalls Hsynthesis.indices
        (.forallE
          (VExpr.mkApps (familyBase.liftN Hsynthesis.indices.length 0)
            (recursorCanonicalVars Hsynthesis.indices.length))
          (.sort Hframe.resultLevel))).liftN nindices 0).lift'
            Hruntime.shift
    familyTyping := H.completedRecursorFamilyPrefixTyping Helim R Hsynthesis
      Hstats Hruntime henv Hframe
    telescope := Htelescope }, rfl, ?_⟩
  rfl

/-- The motive telescope generated by production is definitionally equal to
the independently reconstructed canonical telescope.  The proof closes the
leading index declarations on both sides of the narrow/runtime context
conversion, compares the canonical family application with the consumed
major domain, and then reopens the closed telescope in the executable
context. -/
theorem CheckedRecursorHeaderAt.completedRecursorMotiveTypeDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    {indices : Array Expr} {indexTargets : List VExpr}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (Hindices : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      indices.toList indexTargets)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (Hbound : BoundFVarArray current indices)
    (henv : R.venv = Hc.venv)
    (hindices : indices.size = nindices)
    (hfront : Hruntime.frontSourceDomains = Hsynthesis.indices)
    (Hframe : RecursorMotiveFrameWF R stats familyIdx indices elimLevel) :
    ∃ Hcanonical : RecursorMotiveCanonicalFrameWF R stats familyIdx
        indices elimLevel Hframe,
      R.venv.IsDefEqU
          (AddInductive.getRecLevelParams elimLevel c.lparams).length
          R.mlctx.vlctx.toCtx
          ((VExpr.wrapForalls Hframe.indexDomains
            (.forallE Hframe.majorTarget
              (.sort Hframe.resultLevel))).liftN indices.size 0)
          Hcanonical.motiveType ∧
        R.venv.IsDefEqU
          (AddInductive.getRecLevelParams elimLevel c.lparams).length
          (R.mlctx.vlctx.toCtx.drop indices.size)
          (VExpr.wrapForalls Hframe.indexDomains
            (.forallE Hframe.majorTarget
              (.sort Hframe.resultLevel)))
          (VExpr.wrapForalls Hruntime.frontExpandedDomains
            (.forallE Hframe.majorSourceTarget
              (.sort Hframe.resultLevel))) ∧
        Hcanonical.motiveType =
          (VExpr.wrapForalls Hruntime.frontExpandedDomains
            (.forallE Hframe.majorSourceTarget
              (.sort Hframe.resultLevel))).liftN indices.size 0 ∧
        (let familyBase := VExpr.mkApps
            (.const H.target.name (H.recursorAbstractLevels Helim))
            (recursorCanonicalVars Hsynthesis.params.length)
         let canonicalMajor := VExpr.mkApps
            (familyBase.liftN Hsynthesis.indices.length 0)
            (recursorCanonicalVars Hsynthesis.indices.length)
         let canonicalBody :=
            VExpr.forallE canonicalMajor (.sort Hframe.resultLevel)
         canonicalBody.lift' Hruntime.shift =
            .forallE Hframe.majorSourceTarget
              (.sort Hframe.resultLevel)) := by
  rcases H.completedRecursorCanonicalMotiveFrame Helim R Hsynthesis Hstats
      Hruntime henv hindices Hframe with
    ⟨Hcanonical, _hfamilyType, hmotiveType⟩
  let familyBase := VExpr.mkApps
    (.const H.target.name (H.recursorAbstractLevels Helim))
    (recursorCanonicalVars Hsynthesis.params.length)
  let canonicalMajor := VExpr.mkApps
    (familyBase.liftN Hsynthesis.indices.length 0)
    (recursorCanonicalVars Hsynthesis.indices.length)
  let canonicalBody :=
    VExpr.forallE canonicalMajor (.sort Hframe.resultLevel)
  have hparameterCount : Hsynthesis.params.length = decl.nparams := by
    rw [Hsynthesis.parameterCount, H.parameterCount]
  have hfamilyScope : familyBase.liftN nindices 0 =
      VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (decl.paramVars nindices) := by
    simp [familyBase, recursorCanonicalVars, VInductDecl.paramVars,
      VExpr.liftN_mkApps, VExpr.liftN, hparameterCount,
      ← List.map_reverse, Function.comp_def, Nat.add_comm]
  have hfamily := H.completedRecursorFamilyPrefixEq Helim R Hsynthesis
    Hstats Hruntime henv Hframe
  have hfamilyFull :
      (familyBase.liftN nindices 0).lift' Hruntime.shift =
        Hframe.familyTarget := by
    rw [hfamilyScope]
    exact hfamily
  have hindexTargets := H.completedRecursorIndexTargetsEq Helim R Hsynthesis
    Hruntime Hindices hcanonical Hbound Hframe
  have hcanonicalMajor : canonicalMajor.lift' Hruntime.shift =
      Hframe.majorSourceTarget := by
    dsimp only [canonicalMajor]
    rw [VExpr.lift'_mkApps]
    have hfamilyFull' :
        (familyBase.liftN Hsynthesis.indices.length 0).lift'
            Hruntime.shift = Hframe.familyTarget := by
      simpa [Hsynthesis.indexCount] using hfamilyFull
    rw [hfamilyFull']
    have hindexTargets' :
        (recursorCanonicalVars Hsynthesis.indices.length).map
            (fun target => target.lift' Hruntime.shift) =
          Hframe.familyIndexTargets := by
      simpa [recursorCanonicalVars, canonicalIndexVars,
        List.map_reverse, Function.comp_def, Hsynthesis.indexCount] using
        hindexTargets
    rw [hindexTargets']
    exact Hframe.majorSourceEq.symm
  have hcanonicalBody : canonicalBody.lift' Hruntime.shift =
      .forallE Hframe.majorSourceTarget (.sort Hframe.resultLevel) := by
    simp [canonicalBody, hcanonicalMajor]
  rcases Hframe.majorType with ⟨majorLevel, hmajorType⟩
  have hmajorRuntime := Hframe.majorSourceDefEq.of_r R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx hmajorType
  have hbodyRuntime : R.venv.IsDefEq
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      R.mlctx.vlctx.toCtx
      (.forallE Hframe.majorSourceTarget (.sort Hframe.resultLevel))
      (.forallE Hframe.majorTarget (.sort Hframe.resultLevel))
      (.sort (.imax majorLevel (.succ Hframe.resultLevel))) :=
    .forallEDF hmajorRuntime (VEnv.HasType.sort Hframe.resultLevelWF)
  have hbodyExpanded := hbodyRuntime.defeqDFC R.checking.tr.wf.ordered
    (Hruntime.context.defeqCtx.symm R.checking.tr.wf.ordered)
  have hfrontLength : Hruntime.frontExpandedDomains.length = indices.size := by
    rw [← Hruntime.front.length_eq, hfront, Hsynthesis.indexCount,
      ← hindices]
  have hcloseLE : indices.size ≤ Hruntime.expanded.toCtx.length := by
    rw [← hfrontLength]
    exact Hruntime.front.expandedLengthLE
  rcases Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.closeHeads
      Hruntime.context.defeqCtx indices.size hcloseLE hbodyExpanded with
    ⟨closedLevel, hclosed⟩
  have hexpandedPrefix :
      (Hruntime.expanded.toCtx.take indices.size).reverse =
        Hruntime.frontExpandedDomains := by
    rw [← hfrontLength]
    exact Hruntime.front.expandedPrefix
  have hruntimePrefix :
      (R.mlctx.vlctx.toCtx.take indices.size).reverse =
        Hframe.indexDomains := Hframe.indexDomains_eq.symm
  rw [hexpandedPrefix, hruntimePrefix] at hclosed
  have hclosedRuntime := hclosed.defeqDFC R.checking.tr.wf.ordered
    (Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.dropHeads
      Hruntime.context.defeqCtx indices.size)
  have hreopened := hclosedRuntime.weakN R.checking.tr.wf.ordered
    (Ctx.LiftN.zero (R.mlctx.vlctx.toCtx.take indices.size))
  have hruntimeLE : indices.size ≤ R.mlctx.vlctx.toCtx.length := by
    have hlength := Hframe.indexDomains_length
    rw [Hframe.indexDomains_eq, List.length_reverse,
      List.length_take] at hlength
    omega
  have hreopened' : R.venv.IsDefEq
      (AddInductive.getRecLevelParams elimLevel c.lparams).length
      R.mlctx.vlctx.toCtx
      ((VExpr.wrapForalls Hruntime.frontExpandedDomains
        (.forallE Hframe.majorSourceTarget
          (.sort Hframe.resultLevel))).liftN indices.size 0)
      ((VExpr.wrapForalls Hframe.indexDomains
        (.forallE Hframe.majorTarget
          (.sort Hframe.resultLevel))).liftN indices.size 0)
      ((VExpr.sort closedLevel).liftN indices.size 0) := by
    simpa [List.take_append_drop, Nat.min_eq_left hruntimeLE] using hreopened
  have hnatural := Hruntime.front.closeReopen canonicalBody
  have hnatural' :
      ((VExpr.wrapForalls Hsynthesis.indices canonicalBody).liftN
          indices.size 0).lift' Hruntime.shift =
        (VExpr.wrapForalls Hruntime.frontExpandedDomains
          (.forallE Hframe.majorSourceTarget
            (.sort Hframe.resultLevel))).liftN indices.size 0 := by
    simpa [hfront, Hsynthesis.indexCount, hindices, hfrontLength,
      hcanonicalBody] using hnatural
  have hmotiveType' : Hcanonical.motiveType =
      ((VExpr.wrapForalls Hsynthesis.indices canonicalBody).liftN
        indices.size 0).lift' Hruntime.shift := by
    simpa [familyBase, canonicalMajor, canonicalBody, hindices] using
      hmotiveType
  have hresult := hreopened'.symm
  rw [← hnatural', ← hmotiveType'] at hresult
  exact ⟨Hcanonical, ⟨_, hresult⟩, ⟨_, hclosedRuntime.symm⟩,
    hmotiveType'.trans hnatural', hcanonicalBody⟩

theorem CheckedRecursorHeaderAt.recursorCanonicalFamilyApplication
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {narrowTarget : VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget
        stats.params.size nindices)
    (henv : R.venv = Hc.venv)
    (hnindices : nindices = H.target.numIndices) :
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (canonicalIndexVars (decl.nparams + H.target.numIndices)))
      narrowTarget := by
  have hhead := H.recursorConstHasType Helim R henv
  have hheadTelescope : R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length []
      (.const H.target.name (H.recursorAbstractLevels Helim))
      (VExpr.wrapForalls (Hsynthesis.params ++ Hsynthesis.indices)
        narrowTarget) := by
    apply hhead.defeqU_r R.checking.tr.wf (by trivial)
    exact ⟨Hsynthesis.exprType, Hsynthesis.header⟩
  have happ := VEnv.HasType.mkApps_wrapForalls_canonical
    R.checking.tr.wf.ordered hheadTelescope
  have hparamCount : Hsynthesis.params.length = decl.nparams := by
    rw [Hsynthesis.parameterCount, H.parameterCount]
  have hindexCount : Hsynthesis.indices.length = H.target.numIndices := by
    rw [Hsynthesis.indexCount, hnindices]
  simpa [List.reverse_append, Hsynthesis.scopeCtx, hparamCount,
    hindexCount, canonicalIndexVars, VExpr.liftN, ← List.map_reverse] using happ

/-- Recursor-universe form of the completed family application theorem. -/
theorem CheckedRecursorHeaderAt.completedRecursorNarrowFamilyApplication
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {type : VExpr}
    {indices : Array Expr} {indexTargets : List VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope type
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hindices : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true)
    (henv : R.venv = Hc.venv) :
    TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope
      (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params) indices)
      (VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (canonicalIndexVars (decl.nparams + H.target.numIndices))) ∧
    R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (canonicalIndexVars (decl.nparams + H.target.numIndices))) type ∧
    R.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (canonicalIndexVars (decl.nparams + H.target.numIndices))) := by
  have htranslated : indices.size = indexTargets.length := by
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hindices
  have hguard : indices.size = stats.nindices[familyIdx]! := by
    simpa using harity
  have hfamily : stats.nindices[familyIdx]! = H.target.numIndices := by
    simp [Array.getElem!_eq_getD, H.indexCount]
  have hnindices : nindices = H.target.numIndices := by omega
  have hargs := H.completedRecursorNarrowArguments Helim R Hstats Hindices
    hreplay hcanonical harity
  have hhead := H.recursorIndConstTranslation Helim R Hstats henv
  have happ := H.recursorCanonicalFamilyApplication Helim R Hsynthesis henv
    hnindices
  have huvars : H.target.uvars = decl.uvars := by
    rw [H.sourceTranslation.uvars, H.materialized.uvars]
  have htargetWF : H.target.toVConstant.WF Hc.venv :=
    H.sourceTranslation.wf
  have hshape : decl.TypeShape Hc.venv
      H.materialized.headers.params H.target :=
    H.shape
  rcases typeShape_forallAritySort huvars Hc.checking.tr.wf htargetWF
      hshape with
    ⟨functionType, typeLevel, hfunctionType, hfunctionShape⟩
  have hlevelsWF := H.recursorAbstractLevels_wf Helim
  have hlevelsLength := H.recursorAbstractLevels_length Helim
  have hfunctionTypeInst := hfunctionType.instL hlevelsWF
  have hlookup : R.venv.constants H.target.name =
      some H.target.toVConstant := by
    simpa [henv] using H.targetLookup
  have hconstBase := VEnv.HasType.const (env := R.venv)
    (U := (AddInductive.getRecLevelParams elimLevel c.lparams).length)
    (Γ := scope.toCtx) hlookup hlevelsWF hlevelsLength
  have hconstType : R.venv.HasType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (.const H.target.name (H.recursorAbstractLevels Helim))
      (functionType.instL (H.recursorAbstractLevels Helim)) := by
    have hfunctionTypeInst' : R.venv.IsDefEq
        (AddInductive.getRecLevelParams elimLevel c.lparams).length []
        (H.target.type.instL (H.recursorAbstractLevels Helim))
        (functionType.instL (H.recursorAbstractLevels Helim))
        (.sort (typeLevel.inst (H.recursorAbstractLevels Helim))) := by
      simpa [henv, VExpr.instL] using hfunctionTypeInst
    exact (hfunctionTypeInst'.weak0 R.checking.tr.wf.ordered).defeq hconstBase
  have happType : R.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c.lparams).length scope.toCtx
      (VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (canonicalIndexVars (decl.nparams + H.target.numIndices))) := by
    apply VEnv.HasType.mkApps_isType R.checking.tr.wf
      Hsynthesis.scopeWF.toCtx hconstType
    · simpa [canonicalIndexVars] using
        hfunctionShape.instL (H.recursorAbstractLevels Helim)
    · exact ⟨type, happ⟩
  have htr : TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope
      (Expr.mkAppList stats.indConsts[familyIdx]!
        (stats.params.toList ++ indices.toList))
      (VExpr.mkApps
        (.const H.target.name (H.recursorAbstractLevels Helim))
        (canonicalIndexVars (decl.nparams + H.target.numIndices))) :=
    checkPositivityStep.TrExprS.mkAppList R.checking.tr.wf.ordered
      Hsynthesis.scopeWF.toCtx hhead hargs ⟨_, happ⟩
  refine ⟨?_, happ, happType⟩
  simpa [Expr.mkAppN_eq_mkAppList, Expr.mkAppList_append] using htr

/-- The completed executable family application has a checked consumed
domain directly in the current recursor context. -/
theorem CheckedRecursorHeaderAt.completedRecursorMajorDomain
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel)
    {current : AddInductive.Context}
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel c.lparams))
    {scope : VLCtx} {type : VExpr}
    {indices : Array Expr} {indexTargets : List VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel c.lparams)
        (H.recursorTargetSkeleton Helim) scope type
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      scope R.mlctx.vlctx)
    (Hindices : List.Forall₂ (TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel c.lparams) scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true)
    (henv : R.venv = Hc.venv)
    (hconsume : RecursorConsumeTypeAnnotationsCompat) :
    ∃ sourceTarget consumedTarget,
      R.ConsumedDomain
        (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params) indices)
        sourceTarget consumedTarget := by
  rcases H.completedRecursorNarrowFamilyApplication Helim R Hsynthesis Hstats
      Hindices hreplay hcanonical harity henv with
    ⟨hnarrow, _happ, hnarrowType⟩
  rcases Hruntime.transportType R.checking.tr.wf hnarrow hnarrowType with
    ⟨sourceTarget, hsource, hsourceType⟩
  rcases hconsume current _ R hsource hsourceType with
    ⟨consumedTarget, Hconsumed⟩
  exact ⟨sourceTarget, consumedTarget, Hconsumed⟩

/-- The successful arity branch independently types both declarations added
by one `loopInd1` frame: the family major and the exact nested `mkForall`
motive used by production. -/
theorem CheckedRecursorHeaderAt.completedInitialRecursorFrame
    {c : AddInductive.Context} {Hc : ContextWF c}
    {c' : AddInductive.Context} {Hc' : ContextWF c'}
    {scope : VLCtx} {type : VExpr}
    {indices : Array Expr} {indexTargets : List VExpr}
    {nindices : Nat}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc'.venv c'.lparams H.target.toSkeleton scope type
        stats.params.size nindices)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc'.venv c'.lparams scope Hc'.mlctx.vlctx)
    (Hindices : List.Forall₂ (TrExprS Hc'.venv c'.lparams scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true)
    (henv : Hc'.venv = Hc.venv)
    (hlparams : c'.lparams = c.lparams)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hrecent : RecentBoundFVarArray Hc Hc' indices)
    (Helim : AddInductive.AdmissibleElimLevel c'.lparams elimLevel) :
    Nonempty (RecursorMotiveFrameWF
      (Hc'.toAdmissibleRecursorContextWF Helim)
      stats familyIdx indices elimLevel) := by
  let majorTy :=
    (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
      indices).consumeTypeAnnotations
  let Rindices := Hc'.toAdmissibleRecursorContextWF Helim
  rcases H.completedMajorDomain Hsynthesis Hstats Hruntime Hindices hreplay
      hcanonical harity henv hlparams hconsume with
    ⟨sourceTarget, consumedTarget, Hdom⟩
  rcases Hdom.toRecursorContext Helim with
    ⟨sourceTarget', majorTarget, Hdom'⟩
  have hsourceList : TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel c'.lparams)
      Rindices.mlctx.vlctx
      (Expr.mkAppList
        (mkAppN stats.indConsts[familyIdx]! stats.params) indices.toList)
      sourceTarget' := by
    simpa only [← Expr.mkAppN_eq_mkAppList] using Hdom'.source
  rcases checkPositivityStep.TrExprS.mkAppList_inv hsourceList with
    ⟨familyTarget, familyIndexTargets, hfamily, hfamilyIndices,
      hsourceTarget'⟩
  let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
    Hdom'.consumed Hdom'.isType
  let cMajor : AddInductive.Context := { c' with
    ngen := c'.ngen.next
    lctx := c'.lctx.mkLocalDecl ⟨c'.ngen.curr⟩ `t majorTy .default }
  let major := Expr.fvar ⟨c'.ngen.curr⟩
  let majorBody := cMajor.lctx.mkForall #[major] (.sort elimLevel)
  let motiveTy := cMajor.lctx.mkForall indices majorBody
  rcases Helim.sortType (env := Rmajor.venv) (Δ := Rmajor.mlctx.vlctx) with
    ⟨sortLevel, hsort, hsortType⟩
  have hone : 1 ≤ Rmajor.mlctx.length := by
    dsimp only [Rmajor, RecursorContextWF.withLocalDecl]
    simp
  have hmajorRecent : #[major].toList.reverse =
      (Rmajor.mlctx.fvarRevList 1 hone).map Expr.fvar := by
    dsimp only [major, Rmajor, RecursorContextWF.withLocalDecl]
    simp
  have hmajorClosed := Rmajor.mkForallRecent hsort hsortType 1 hone #[major]
    hmajorRecent
  have hmajorClosed' :
      TrExprS Rindices.venv
          (AddInductive.getRecLevelParams elimLevel c'.lparams)
          Rindices.mlctx.vlctx majorBody
          (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel)) ∧
        Rindices.venv.IsType
          (AddInductive.getRecLevelParams elimLevel c'.lparams).length
          Rindices.mlctx.vlctx.toCtx
          (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel)) := by
    simpa only [majorBody, Rmajor, RecursorContextWF.withLocalDecl,
      TypeChecker.MLCtx.dropN] using hmajorClosed
  let hindicesSize := Hrecent.recursorSizeLE Helim
  have hindicesRecent : indices.toList.reverse =
      (Rindices.mlctx.fvarRevList indices.size hindicesSize).map Expr.fvar :=
    Hrecent.recursorReverseEq Helim
  have hmotiveClosed := Rindices.mkForallRecent hmajorClosed'.1
    hmajorClosed'.2 indices.size hindicesSize indices hindicesRecent
  let hmajorLE := BindingContextLE.withLocalDecl c'
    Hc'.toBindingContextWF `t majorTy .default
  have hmotiveConcrete : motiveTy = c'.lctx.mkForall indices majorBody := by
    dsimp [motiveTy]
    exact Hrecent.toFreshBoundFVarArray.toBoundFVarArray.mkForall_mono
      hmajorLE majorBody
  rw [← hmotiveConcrete] at hmotiveClosed
  let Windices := Rindices.onlyLams.dropN_fvlift indices.size hindicesSize
  have hmotiveAtIndices := hmotiveClosed.1.weakFV
    Rindices.checking.tr.wf.ordered Windices Rindices.mlctx_wf.tr.wf
  have hmotiveTypeAtIndices := hmotiveClosed.2.weakN
    Rindices.checking.tr.wf.ordered Windices.toCtx
  let Wmajor : VLCtx.FVLift Rindices.mlctx.vlctx Rmajor.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have hmotiveAtMajor := hmotiveAtIndices.weakFV
    Rmajor.checking.tr.wf.ordered Wmajor Rmajor.mlctx_wf.tr.wf
  have hmotiveTypeAtMajor := hmotiveTypeAtIndices.weakN
    Rmajor.checking.tr.wf.ordered Wmajor.toCtx
  have hmajorConcrete : majorBody =
      Rmajor.mlctx.mkForall 1 hone (Expr.sort elimLevel) := by
    dsimp only [majorBody]
    rw [← Rmajor.lctx_eq]
    exact Rmajor.mlctx_wf.mkForall_eq 1 hone hmajorRecent
  have hsortConsume : (Expr.sort elimLevel).consumeTypeAnnotations =
      Expr.sort elimLevel := by
    apply Expr.consumeTypeAnnotations_eq_self <;> rfl
  have hconsumeMajor : majorBody.consumeTypeAnnotations = majorBody := by
    rw [hmajorConcrete]
    exact Rmajor.onlyLams.mkForall_consumeTypeAnnotations_eq_self
      1 hone hsortConsume
  have hmotiveMkForall : motiveTy =
      Rindices.mlctx.mkForall indices.size hindicesSize majorBody := by
    rw [hmotiveConcrete, ← Rindices.lctx_eq]
    exact Rindices.mlctx_wf.mkForall_eq indices.size hindicesSize
      hindicesRecent
  have hconsumeMotive : motiveTy.consumeTypeAnnotations = motiveTy := by
    rw [hmotiveMkForall]
    exact Rindices.onlyLams.mkForall_consumeTypeAnnotations_eq_self
      indices.size hindicesSize hconsumeMajor
  refine ⟨{
    familyTarget := familyTarget
    familyTr := hfamily
    familyIndexTargets := familyIndexTargets
    familyIndicesTr := hfamilyIndices
    majorSourceTarget := sourceTarget'
    majorSourceEq := hsourceTarget'
    majorSourceDefEq := by
      rcases Hdom'.source_defeq with ⟨level, heq⟩
      exact ⟨.sort level, heq⟩
    majorTarget := majorTarget
    majorTr := ?_
    majorType := ?_
    indexDomains := MLCtxForallDomains Rindices.mlctx indices.size
      hindicesSize
    indexDomains_length :=
      Rindices.onlyLams.forallDomains_length indices.size hindicesSize
    indexDomains_eq :=
      Rindices.onlyLams.forallDomains_eq_take_reverse indices.size
        hindicesSize
    resultLevel := sortLevel
    resultLevelWF := by
      cases hsort with
      | sort hlevel => exact .of_ofLevel hlevel
    motiveTarget :=
      ((Rindices.mlctx.mkForall' indices.size hindicesSize
        (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel))).liftN
          indices.size 0).liftN 1 0
    motiveTarget_eq := by
      rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls,
        TypeChecker.MLCtx.mkForall'_eq_wrapForalls]
      have hmajorDomains : MLCtxForallDomains Rmajor.mlctx 1 hone =
          [majorTarget] := by
        dsimp only [Rmajor, RecursorContextWF.withLocalDecl]
        simp only [MLCtxForallDomains, List.nil_append]
      rw [hmajorDomains]
      rfl
    motiveClosed := ?_
    motiveTr := ?_
    motiveType := ?_
    motiveSourceEq := ?_ }⟩
  · change TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel c'.lparams)
      Rindices.mlctx.vlctx majorTy majorTarget
    exact Hdom'.consumed
  · change Rindices.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c'.lparams).length
      Rindices.mlctx.vlctx.toCtx majorTarget
    exact Hdom'.isType
  · refine ⟨hindicesSize,
      Rindices.mlctx.mkForall' indices.size hindicesSize
        (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel)), ?_, ?_, ?_⟩
    · rw [hconsumeMotive]
      exact hmotiveClosed.1
    · exact hmotiveClosed.2
    · rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls,
        TypeChecker.MLCtx.mkForall'_eq_wrapForalls]
      have hmajorDomains : MLCtxForallDomains Rmajor.mlctx 1 hone =
          [majorTarget] := by
        dsimp only [Rmajor, RecursorContextWF.withLocalDecl]
        simp only [MLCtxForallDomains, List.nil_append]
      rw [hmajorDomains]
      rfl
  · change TrExprS Rmajor.venv
      (AddInductive.getRecLevelParams elimLevel c'.lparams)
      Rmajor.mlctx.vlctx motiveTy.consumeTypeAnnotations _
    rw [hconsumeMotive]
    exact hmotiveAtMajor
  · change Rmajor.venv.IsType
      (AddInductive.getRecLevelParams elimLevel c'.lparams).length
      Rmajor.mlctx.vlctx.toCtx _
    exact hmotiveTypeAtMajor
  · exact hconsumeMotive

/-- Construct the major/motive frame from a completed header replay in any
existing recursor context.  This is the mutual-recursion form of
`completedInitialRecursorFrame`: earlier family frames remain in the ambient
prefix, while only this family's recent index suffix is closed into the
motive telescope. -/
theorem CheckedRecursorHeaderAt.completedRecursorFrame
    {base root current : AddInductive.Context} {Hbase : ContextWF base}
    (H : CheckedRecursorHeaderAt Hbase stats decl depth source familyIdx)
    {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (Rroot : RecursorContextWF root
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (Rindices : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    {scope : VLCtx} {type : VExpr}
    {indices : Array Expr} {indexTargets : List VExpr} {nindices : Nat}
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Rindices.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        (H.recursorTargetSkeleton Helim) scope type
        stats.params.size nindices)
    (Hstats : RecursorValidAppStatsWF Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope stats decl nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      scope Rindices.mlctx.vlctx)
    (Hindices : List.Forall₂ (TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) scope)
      indices.toList indexTargets)
    (hreplay : indexTargets.length = nindices)
    (hcanonical : indexTargets = canonicalIndexVars nindices)
    (harity : (indices.size == stats.nindices[familyIdx]!) = true)
    (henv : Rindices.venv = Hbase.venv)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (Hrecent : RecursorRecentBoundFVarArray Rroot Rindices indices) :
    Nonempty (RecursorMotiveFrameWF Rindices stats familyIdx indices
      elimLevel) := by
  let majorTy :=
    (mkAppN (mkAppN stats.indConsts[familyIdx]! stats.params)
      indices).consumeTypeAnnotations
  rcases H.completedRecursorMajorDomain Helim Rindices Hsynthesis Hstats
      Hruntime Hindices hreplay hcanonical harity henv hconsume with
    ⟨sourceTarget, majorTarget, Hdom⟩
  have hsourceList : TrExprS Rindices.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      Rindices.mlctx.vlctx
      (Expr.mkAppList
        (mkAppN stats.indConsts[familyIdx]! stats.params) indices.toList)
      sourceTarget := by
    simpa only [← Expr.mkAppN_eq_mkAppList] using Hdom.source
  rcases checkPositivityStep.TrExprS.mkAppList_inv hsourceList with
    ⟨familyTarget, familyIndexTargets, hfamily, hfamilyIndices,
      hsourceTarget⟩
  let Rmajor := Rindices.withLocalDecl (name := `t) (bi := .default)
    Hdom.consumed Hdom.isType
  let cMajor : AddInductive.Context := { current with
    ngen := current.ngen.next
    lctx := current.lctx.mkLocalDecl ⟨current.ngen.curr⟩ `t majorTy .default }
  let major := Expr.fvar ⟨current.ngen.curr⟩
  let majorBody := cMajor.lctx.mkForall #[major] (.sort elimLevel)
  let motiveTy := cMajor.lctx.mkForall indices majorBody
  rcases Helim.sortType (env := Rmajor.venv) (Δ := Rmajor.mlctx.vlctx) with
    ⟨sortLevel, hsort, hsortType⟩
  have hone : 1 ≤ Rmajor.mlctx.length := by
    dsimp only [Rmajor, RecursorContextWF.withLocalDecl]
    simp
  have hmajorRecent : #[major].toList.reverse =
      (Rmajor.mlctx.fvarRevList 1 hone).map Expr.fvar := by
    dsimp only [major, Rmajor, RecursorContextWF.withLocalDecl]
    simp
  have hmajorClosed := Rmajor.mkForallRecent hsort hsortType 1 hone #[major]
    hmajorRecent
  have hmajorClosed' :
      TrExprS Rindices.venv
          (AddInductive.getRecLevelParams elimLevel base.lparams)
          Rindices.mlctx.vlctx majorBody
          (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel)) ∧
        Rindices.venv.IsType
          (AddInductive.getRecLevelParams elimLevel base.lparams).length
          Rindices.mlctx.vlctx.toCtx
          (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel)) := by
    simpa only [majorBody, Rmajor, RecursorContextWF.withLocalDecl,
      TypeChecker.MLCtx.dropN] using hmajorClosed
  let hindicesSize := Hrecent.size_le
  have hindicesRecent : indices.toList.reverse =
      (Rindices.mlctx.fvarRevList indices.size hindicesSize).map Expr.fvar :=
    Hrecent.reverse_eq
  have hmotiveClosed := Rindices.mkForallRecent hmajorClosed'.1
    hmajorClosed'.2 indices.size hindicesSize indices hindicesRecent
  let hmajorLE := BindingContextLE.withLocalDecl current
    Rindices.toBindingContextWF `t majorTy .default
  have hmotiveConcrete : motiveTy =
      current.lctx.mkForall indices majorBody := by
    dsimp [motiveTy]
    exact Hrecent.toFreshBoundFVarArray.toBoundFVarArray.mkForall_mono
      hmajorLE majorBody
  rw [← hmotiveConcrete] at hmotiveClosed
  let Windices := Rindices.onlyLams.dropN_fvlift indices.size hindicesSize
  have hmotiveAtIndices := hmotiveClosed.1.weakFV
    Rindices.checking.tr.wf.ordered Windices Rindices.mlctx_wf.tr.wf
  have hmotiveTypeAtIndices := hmotiveClosed.2.weakN
    Rindices.checking.tr.wf.ordered Windices.toCtx
  let Wmajor : VLCtx.FVLift Rindices.mlctx.vlctx Rmajor.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have hmotiveAtMajor := hmotiveAtIndices.weakFV
    Rmajor.checking.tr.wf.ordered Wmajor Rmajor.mlctx_wf.tr.wf
  have hmotiveTypeAtMajor := hmotiveTypeAtIndices.weakN
    Rmajor.checking.tr.wf.ordered Wmajor.toCtx
  have hmajorConcrete : majorBody =
      Rmajor.mlctx.mkForall 1 hone (Expr.sort elimLevel) := by
    dsimp only [majorBody]
    rw [← Rmajor.lctx_eq]
    exact Rmajor.mlctx_wf.mkForall_eq 1 hone hmajorRecent
  have hsortConsume : (Expr.sort elimLevel).consumeTypeAnnotations =
      Expr.sort elimLevel := by
    apply Expr.consumeTypeAnnotations_eq_self <;> rfl
  have hconsumeMajor : majorBody.consumeTypeAnnotations = majorBody := by
    rw [hmajorConcrete]
    exact Rmajor.onlyLams.mkForall_consumeTypeAnnotations_eq_self
      1 hone hsortConsume
  have hmotiveMkForall : motiveTy =
      Rindices.mlctx.mkForall indices.size hindicesSize majorBody := by
    rw [hmotiveConcrete, ← Rindices.lctx_eq]
    exact Rindices.mlctx_wf.mkForall_eq indices.size hindicesSize
      hindicesRecent
  have hconsumeMotive : motiveTy.consumeTypeAnnotations = motiveTy := by
    rw [hmotiveMkForall]
    exact Rindices.onlyLams.mkForall_consumeTypeAnnotations_eq_self
      indices.size hindicesSize hconsumeMajor
  refine ⟨{
    familyTarget := familyTarget
    familyTr := hfamily
    familyIndexTargets := familyIndexTargets
    familyIndicesTr := hfamilyIndices
    majorSourceTarget := sourceTarget
    majorSourceEq := hsourceTarget
    majorSourceDefEq := by
      rcases Hdom.source_defeq with ⟨level, heq⟩
      exact ⟨.sort level, heq⟩
    majorTarget := majorTarget
    majorTr := Hdom.consumed
    majorType := Hdom.isType
    indexDomains := MLCtxForallDomains Rindices.mlctx indices.size
      hindicesSize
    indexDomains_length :=
      Rindices.onlyLams.forallDomains_length indices.size hindicesSize
    indexDomains_eq :=
      Rindices.onlyLams.forallDomains_eq_take_reverse indices.size
        hindicesSize
    resultLevel := sortLevel
    resultLevelWF := by
      cases hsort with
      | sort hlevel => exact .of_ofLevel hlevel
    motiveTarget :=
      ((Rindices.mlctx.mkForall' indices.size hindicesSize
        (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel))).liftN
          indices.size 0).liftN 1 0
    motiveTarget_eq := by
      rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls,
        TypeChecker.MLCtx.mkForall'_eq_wrapForalls]
      have hmajorDomains : MLCtxForallDomains Rmajor.mlctx 1 hone =
          [majorTarget] := by
        dsimp only [Rmajor, RecursorContextWF.withLocalDecl]
        simp only [MLCtxForallDomains, List.nil_append]
      rw [hmajorDomains]
      rfl
    motiveClosed := ?_
    motiveTr := ?_
    motiveType := ?_
    motiveSourceEq := ?_ }⟩
  · refine ⟨hindicesSize,
      Rindices.mlctx.mkForall' indices.size hindicesSize
        (Rmajor.mlctx.mkForall' 1 hone (.sort sortLevel)), ?_, ?_, ?_⟩
    · rw [hconsumeMotive]
      exact hmotiveClosed.1
    · exact hmotiveClosed.2
    · rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls,
        TypeChecker.MLCtx.mkForall'_eq_wrapForalls]
      have hmajorDomains : MLCtxForallDomains Rmajor.mlctx 1 hone =
          [majorTarget] := by
        dsimp only [Rmajor, RecursorContextWF.withLocalDecl]
        simp only [MLCtxForallDomains, List.nil_append]
      rw [hmajorDomains]
      rfl
  · change TrExprS Rmajor.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams)
      Rmajor.mlctx.vlctx motiveTy.consumeTypeAnnotations _
    rw [hconsumeMotive]
    exact hmotiveAtMajor
  · change Rmajor.venv.IsType
      (AddInductive.getRecLevelParams elimLevel base.lparams).length
      Rmajor.mlctx.vlctx.toCtx _
    exact hmotiveTypeAtMajor
  · exact hconsumeMotive

/-- One semantically justified cached-parameter step.  The syntax translation
of the cached free variable is not enough on its own: preservation of
typehood uses the definitional equality between the exposed header domain and
the cached parameter type that was established by `checkInductiveTypes`. -/
theorem parameterStep
    (Hc : ContextWF c)
    {stats : AddInductive.InductiveStats} {i : Nat}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {current paramTarget paramType : VExpr}
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.forallE name dom body bi) current)
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      stats.params[i]! paramTarget)
    (hparamType : Hc.venv.HasType c.lparams.length
      Hc.mlctx.vlctx.toCtx paramTarget paramType)
    (hmatch : ∀ {domainTarget},
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom domainTarget →
      Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        domainTarget paramType) :
    ∃ bodyTarget,
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        (body.instantiate1 stats.params[i]!) bodyTarget ∧
      Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx bodyTarget := by
  rcases TrExpr.forallE_source htype with
    ⟨domainTarget, sourceBody, hdom, hbody, _hdomType, hbodyType,
      _hcurrent⟩
  have heq := hmatch hdom
  have hparamType' := hparamType.defeqU_r Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx heq.symm
  refine ⟨sourceBody.inst paramTarget,
    Hc.instantiateDefEq hbody hparam hparamType heq, ?_⟩
  exact hbodyType.instN Hc.checking.tr.wf.ordered .zero hparamType'

/-- Discharge `parameterStep`'s domain match from the independently checked
family shape and the retained parameter-cache certificates.  The narrow
equality is lifted into the executable reader context only after it has been
proved against the source specification. -/
theorem parameterStepOfCheckedHeader
    (Hc : ContextWF c)
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {decl : VInductDecl} {params : List VExpr}
    {target : VInductiveType}
    {current currentDomain currentBody : VExpr}
    (Hscope : checkInductiveTypes.loopType.LaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams target.toSkeleton Hscope.older
        (.forallE currentDomain currentBody) i 0)
    (hi : i < stats.params.size)
    (hparams : stats.params.size = decl.nparams)
    (huvars : c.lparams.length = decl.uvars)
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (hshape : decl.TypeShape Hc.venv params target)
    (htypeNarrow : TrExprS Hc.venv c.lparams Hscope.older
      (.forallE name dom body bi) (.forallE currentDomain currentBody))
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.forallE name dom body bi) current) :
    ∃ bodyTarget,
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        (body.instantiate1 stats.params[i]!) bodyTarget ∧
      Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx bodyTarget := by
  rcases Hscope.typing with
    ⟨_paramTy, paramTy', param', _hget, _hparamTy, hparamTyEq,
      hparam, hparamType⟩
  have hnarrowMatch := Hscope.currentDomainDefEq Hsynthesis hi hparams
    huvars hctx hshape
  cases htypeNarrow with
  | forallE _hdomType _hbodyType hdomNarrow _hbodyNarrow =>
    apply parameterStep Hc htype hparam hparamType
    intro domainTarget hdomFull
    have hdomWeak := hdomNarrow.weakFV Hc.checking.tr.wf.ordered
      Hscope.olderLift Hc.mlctx_wf.tr.wf
    have hdomainToNarrow := hdomFull.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hdomWeak
    have hmatchFull :=
      (VEnv.IsDefEqU.weakN_iff Hc.checking.tr.wf
        Hc.mlctx_wf.tr.wf.toCtx Hscope.olderLift.toCtx).2 hnarrowMatch
    have hresult := hdomainToNarrow.trans Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx hmatchFull
    rw [hparamTyEq]
    simpa [Nat.succ_eq_add_one, VExpr.liftN_liftN, Nat.add_comm]
      using hresult

/-- One cached-parameter substitution interpreted directly under the
recursor universe list. -/
theorem recursorParameterStep
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {stats : AddInductive.InductiveStats} {i : Nat}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {current paramTarget paramType : VExpr}
    (htype : TrExpr R.venv recLparams R.mlctx.vlctx
      (.forallE name dom body bi) current)
    (hparam : TrExprS R.venv recLparams R.mlctx.vlctx
      stats.params[i]! paramTarget)
    (hparamType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      paramTarget paramType)
    (hmatch : ∀ {domainTarget},
      TrExprS R.venv recLparams R.mlctx.vlctx dom domainTarget →
      R.venv.IsDefEqU recLparams.length R.mlctx.vlctx.toCtx
        domainTarget paramType) :
    ∃ bodyTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx
        (body.instantiate1 stats.params[i]!) bodyTarget ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx bodyTarget := by
  rcases TrExpr.forallE_source htype with
    ⟨domainTarget, sourceBody, hdom, hbody, _hdomType, hbodyType,
      _hcurrent⟩
  have heq := hmatch hdom
  have hparamType' := hparamType.defeqU_r R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx heq.symm
  refine ⟨sourceBody.inst paramTarget,
    R.instantiateDefEq hbody hparam hparamType heq, ?_⟩
  exact hbodyType.instN R.checking.tr.wf.ordered .zero hparamType'

/-- Discharge a recursor-universe cached-parameter step from the independent
rebased family header and the exact retained suffix. -/
theorem parameterStepOfCheckedRecursorHeader
    {base current : AddInductive.Context} {Hbase : ContextWF base}
    (H : CheckedRecursorHeaderAt Hbase stats decl depth source familyIdx)
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    {Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth}
    {i : Nat} {name : Name} {dom body : Expr} {bi : BinderInfo}
    {currentTarget currentDomain currentBody : VExpr}
    (Hscope : RecursorLaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
        (H.recursorTargetSkeleton Helim) Hscope.older
        (.forallE currentDomain currentBody) i 0)
    (hi : i < stats.params.size)
    (henv : R.venv = Hbase.venv)
    (hctx : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx)
    (htypeNarrow : TrExprS R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) Hscope.older
      (.forallE name dom body bi) (.forallE currentDomain currentBody))
    (htype : TrExpr R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) R.mlctx.vlctx
      (.forallE name dom body bi) currentTarget) :
    ∃ bodyTarget,
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams) R.mlctx.vlctx
        (body.instantiate1 stats.params[i]!) bodyTarget ∧
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx bodyTarget := by
  rcases Hscope.typing with
    ⟨_paramTy, paramTy', param', _hget, _hparamTy, hparamTyEq,
      hparam, hparamType⟩
  have hnarrowMatch := H.recursorCurrentDomainDefEq Helim Hscope
    Hsynthesis hi henv hctx
  cases htypeNarrow with
  | forallE _hdomType _hbodyType hdomNarrow _hbodyNarrow =>
    apply recursorParameterStep R htype hparam hparamType
    intro domainTarget hdomFull
    have hdomWeak := hdomNarrow.weakFV R.checking.tr.wf.ordered
      Hscope.olderLift R.mlctx_wf.tr.wf
    have hdomainToNarrow := hdomFull.uniq R.checking.tr.wf
      (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) hdomWeak
    have hmatchFull :=
      (VEnv.IsDefEqU.weakN_iff R.checking.tr.wf
        R.mlctx_wf.tr.wf.toCtx Hscope.olderLift.toCtx).2 hnarrowMatch
    have hresult := hdomainToNarrow.trans R.checking.tr.wf
      R.mlctx_wf.tr.wf.toCtx hmatchFull
    rw [hparamTyEq]
    simpa [Nat.succ_eq_add_one, VExpr.liftN_liftN, Nat.add_comm]
      using hresult

/-- Operational strengthening of `continueWith`: every non-parameter binder
opened while replaying an inductive header is retained in the local context
and appended to the certified index array. -/
theorem continueWithBindings {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M alpha)
    {Q : alpha → Prop}
    (Hk : ∀ indices originTypes c, BindingContextWF c →
      FreshBoundFVarArray root c indices →
      BoundFVarTypeOrigins c indices originTypes →
      BindingContextLE root c → (k indices c).WF Q) :
    ∀ type i indices originTypes fuel c,
      BindingContextWF c → FreshBoundFVarArray root c indices →
      BoundFVarTypeOrigins c indices originTypes →
      BindingContextLE root c →
      (AddInductive.mkRecInfos.loopArgs1 stats type i indices fuel k c).WF Q
  | _, _, _, _, 0, _, _, _, _, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | type, i, indices, originTypes, fuel + 1, c, Hc, Hindices, Horigins,
      Hroot => by
      cases type with
      | forallE name dom body bi =>
        rw [AddInductive.mkRecInfos.loopArgs1]
        by_cases hparam : i < stats.params.size
        · rw [if_pos hparam]
          have hwhnf :
              ((monadLift (TypeChecker.whnf
                (body.instantiate1 stats.params[i]!)) :
                AddInductive.M Expr) c).WF (fun _ => True) := by
            intro _ _
            trivial
          exact hwhnf.bind fun next _ =>
            continueWithBindings stats k Hk next (i + 1) indices originTypes
              fuel c Hc Hindices Horigins Hroot
        · rw [if_neg hparam]
          unfold Lean4Lean.withLocalDecl
            MonadLocalNameGenerator.withFreshId
            AddInductive.instMonadLocalNameGeneratorM
            AddInductive.instMonadWithReaderOfLocalContextM
          let c' : AddInductive.Context := { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }
          change ((monadLift (TypeChecker.whnf
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
              AddInductive.M Expr) c' >>= fun next =>
              AddInductive.mkRecInfos.loopArgs1 stats next i
                (indices.push (.fvar ⟨c.ngen.curr⟩)) fuel k c').WF Q
          have hwhnf :
              ((monadLift (TypeChecker.whnf
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
                AddInductive.M Expr) c').WF (fun _ => True) := by
            intro _ _
            trivial
          exact hwhnf.bind fun next _ =>
            continueWithBindings stats k Hk next i
              (indices.push (.fvar ⟨c.ngen.curr⟩))
              (originTypes.push dom.consumeTypeAnnotations) fuel c'
              (Hc.withLocalDecl name dom.consumeTypeAnnotations bi)
              (Hindices.pushCurrent Hc Hroot name
                dom.consumeTypeAnnotations bi)
              (Horigins.pushCurrent Hc name dom.consumeTypeAnnotations bi)
              (Hroot.trans <| BindingContextLE.withLocalDecl c Hc name
                dom.consumeTypeAnnotations bi)
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
          by_cases hi : i < stats.params.size
          · simp only [AddInductive.mkRecInfos.loopArgs1, hi, if_pos]
            exact Except.WF.throw
          · simpa [AddInductive.mkRecInfos.loopArgs1, hi] using
            Hk indices originTypes c Hc Hindices Horigins Hroot

/-- Semantic strengthening for the genuine-index suffix of `loopArgs1`.
Every introduced index variable remains translated in the final reader
context, and every exact consumed declaration type is retained with a typed
translation.  Common parameters are deliberately excluded here; the caller
enters this theorem once `i` has reached `stats.params.size`. -/
theorem continueIndexSemantics {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M alpha)
    {Q : alpha → Prop}
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hk : ∀ {c : AddInductive.Context} (Hc : ContextWF c)
      {type : Expr} {typeTarget : VExpr} {indices originTypes : Array Expr}
      {indexTargets : List VExpr},
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type typeTarget →
      Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx typeTarget →
      List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx)
        indices.toList indexTargets →
      TranslatedOriginTypes Hc originTypes →
      (k indices c).WF Q) :
    ∀ type typeTarget i indices originTypes indexTargets fuel c,
      stats.params.size ≤ i →
      (Hc : ContextWF c) →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type typeTarget →
      Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx typeTarget →
      List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx)
        indices.toList indexTargets →
      TranslatedOriginTypes Hc originTypes →
      (AddInductive.mkRecInfos.loopArgs1 stats type i indices fuel k c).WF Q
  | _, _, _, _, _, _, 0, _, _, _, _, _, _, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | type, typeTarget, i, indices, originTypes, indexTargets, fuel + 1, c,
      hdone, Hc, htype, htypeType, Hindices, Horigins => by
      cases type with
      | forallE name dom body bi =>
        rw [AddInductive.mkRecInfos.loopArgs1]
        have hparam : ¬ i < stats.params.size := by omega
        rw [if_neg hparam]
        rcases TrExpr.forallE_source htype with
          ⟨sourceDom, sourceBody, hdom, hbody, hdomType, hbodyType,
            _hcurrent⟩
        rcases hconsume c Hc hdom hdomType with
          ⟨consumedDom, Hdom⟩
        rcases Hdom.body Hc hbody with
          ⟨consumedBody, hbodyConsumed, hbodyEq⟩
        refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
          Hc Hdom.consumed Hdom.isType ?_
        let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
        let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
          .skip_fvar _ _ .refl
        have HindicesWeak : List.Forall₂
            (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
            indices.toList (indexTargets.map fun target => target.liftN 1 0) := by
          apply checkPositivityStep.forall₂_map_right Hindices
          intro source target Hsource
          exact Hsource.weakFV Hc.checking.tr.wf.ordered W
            Hc'.mlctx_wf.tr.wf
        have Hindex : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
            (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
          exact TrExprS.fvar (A := consumedDom.lift) (by
            change VLCtx.find? ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotations.fvarsList), .vlam consumedDom) ::
                Hc.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
            simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
              VLocalDecl.value, VLocalDecl.type])
        have Hindices' : List.Forall₂
            (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
            (indices.push (.fvar ⟨c.ngen.curr⟩)).toList
            ((indexTargets.map fun target => target.liftN 1 0) ++ [.bvar 0]) := by
          simpa using checkPositivityStep.forall₂_append HindicesWeak
            (.cons Hindex .nil)
        have hopened := Hc.instantiateFresh (name := name) (bi := bi)
          Hdom.consumed Hdom.isType hbodyConsumed
        rcases Hdom.source_defeq with ⟨_sort, hsourceDefEq⟩
        have hctx : VLCtx.IsDefEq Hc.venv c.lparams.length
            ((none, .vlam sourceDom) :: Hc.mlctx.vlctx)
            ((none, .vlam consumedDom) :: Hc.mlctx.vlctx) :=
          VLCtx.IsDefEq.cons
            (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) nofun
            (.vlam hsourceDefEq)
        have hsourceBodyType : Hc'.venv.IsType c.lparams.length
            Hc'.mlctx.vlctx.toCtx sourceBody := by
          simpa only [Hc', ContextWF.withLocalDecl_venv,
            ContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using
            hbodyType.defeqDFC Hc.checking.tr.wf.ordered hctx.defeqCtx
        have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
        have hconsumedBodyType : Hc'.venv.IsType c.lparams.length
            Hc'.mlctx.vlctx.toCtx consumedBody := by
          apply hsourceBodyType.defeqU_l Hc'.checking.tr.wf
            Hc'.mlctx_wf.tr.wf.toCtx
          simpa only [Hc', ContextWF.withLocalDecl_venv,
            ContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using hbodyEq'
        have hwhnf := whnfInContext.WF Hc' hopened
        exact hwhnf.bind fun next hnext =>
          continueIndexSemantics stats k hconsume Hk next consumedBody i
            (indices.push (.fvar ⟨c.ngen.curr⟩))
            (originTypes.push dom.consumeTypeAnnotations)
            ((indexTargets.map fun target => target.liftN 1 0) ++ [.bvar 0])
            fuel _ hdone Hc' hnext hconsumedBodyType Hindices'
            (Horigins.push Hdom name bi)
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
          have hi : ¬ i < stats.params.size := by omega
          simpa [AddInductive.mkRecInfos.loopArgs1, hi] using
            Hk Hc htype htypeType Hindices Horigins

/-- Semantic index replay retaining the independently synthesized header.
Unlike `continueIndexSemantics`, the terminal continuation receives the
completed narrow telescope and its embedding into the executable context;
this is the evidence needed to construct the family application used as the
major-premise type. -/
theorem continueIndexSynthesisSemantics {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M alpha)
    {Q : alpha → Prop}
    {target : VInductiveTypeSkeleton} {decl : VInductDecl} {depth : Nat}
    {root : AddInductive.Context}
    (HrootCtx : ContextWF root)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hk : ∀ {c : AddInductive.Context} (Hc : ContextWF c)
      {type : Expr} {fullTarget narrowTarget : VExpr} {scope : VLCtx}
      {nindices : Nat} {indices originTypes : Array Expr}
      {indexTargets : List VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc.venv c.lparams target scope narrowTarget
          stats.params.size nindices) →
      checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams scope stats decl
        nindices →
      checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams Hc.mlctx.vlctx stats decl
        (depth + nindices) →
      checkInductiveTypes.loopType.NarrowRuntimeScope Hc.venv c.lparams
        scope Hc.mlctx.vlctx →
      TrExprS Hc.venv c.lparams scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullTarget →
      Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx)
        indices.toList indexTargets →
      List.Forall₂ (TrExprS Hc.venv c.lparams scope)
        indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = canonicalIndexVars nindices →
      TranslatedOriginTypes Hc originTypes →
      RecentBoundFVarArray HrootCtx Hc indices →
      (k indices c).WF Q) :
    ∀ type fullTarget narrowTarget scope i nindices indices originTypes
        indexTargets fuel c,
      stats.params.size ≤ i →
      (Hc : ContextWF c) →
      (Hsynthesis :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc.venv c.lparams target scope narrowTarget
          stats.params.size nindices) →
      checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams scope stats decl
        nindices →
      checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams Hc.mlctx.vlctx stats decl
        (depth + nindices) →
      checkInductiveTypes.loopType.NarrowRuntimeScope Hc.venv c.lparams
        scope Hc.mlctx.vlctx →
      TrExprS Hc.venv c.lparams scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullTarget →
      Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx)
        indices.toList indexTargets →
      List.Forall₂ (TrExprS Hc.venv c.lparams scope)
        indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = canonicalIndexVars nindices →
      TranslatedOriginTypes Hc originTypes →
      RecentBoundFVarArray HrootCtx Hc indices →
      (AddInductive.mkRecInfos.loopArgs1 stats type i indices fuel k c).WF Q
  | _, _, _, _, _, _, _, _, _, 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | type, fullTarget, narrowTarget, scope, i, nindices, indices,
      originTypes, indexTargets, fuel + 1, c, hdone, Hc, Hsynthesis,
      HnarrowStats, Hstats, Hruntime, htypeNarrow, htypeFVars, htypeFull,
      htypeFullType, Hindices, HnarrowIndices, hindexCount, hcanonical,
      Horigins, Hrecent => by
      cases type with
      | forallE name dom body bi =>
        rw [AddInductive.mkRecInfos.loopArgs1]
        have hparam : ¬ i < stats.params.size := by omega
        rw [if_neg hparam]
        cases htypeNarrow with
        | @forallE indexType narrowBody _ _ _ _ _
            hdomType _hbodyType hdomNarrow hbodyNarrow =>
          rcases TrExpr.forallE_source htypeFull with
            ⟨sourceDom, fullBody, hdomFull, hbodyFull, hdomFullType,
              hbodyFullType, _hfullCurrent⟩
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          rcases Hdom.body Hc hbodyFull with
            ⟨consumedBody, hbodyConsumed, _hbodyEq⟩
          refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
            Hc Hdom.consumed Hdom.isType ?_
          let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType
          let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
            .skip_fvar _ _ .refl
          have HindicesWeak : List.Forall₂
              (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
              indices.toList
              (indexTargets.map fun result => result.liftN 1 0) := by
            apply checkPositivityStep.forall₂_map_right Hindices
            intro source result Hsource
            exact Hsource.weakFV Hc.checking.tr.wf.ordered W
              Hc'.mlctx_wf.tr.wf
          have Hindex : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
              (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
            exact TrExprS.fvar (A := consumedDom.lift) (by
              change VLCtx.find? ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList), .vlam consumedDom) ::
                  Hc.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
              simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
                VLocalDecl.value, VLocalDecl.type])
          have Hindices' : List.Forall₂
              (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
              (indices.push (.fvar ⟨c.ngen.curr⟩)).toList
              ((indexTargets.map fun result => result.liftN 1 0) ++
                [.bvar 0]) := by
            simpa using checkPositivityStep.forall₂_append HindicesWeak
              (.cons Hindex .nil)
          have hopened := Hc.instantiateFresh (name := name) (bi := bi)
            Hdom.consumed Hdom.isType hbodyConsumed
          have hctx : VLCtx.IsDefEq Hc.venv c.lparams.length
              ((none, .vlam sourceDom) :: Hc.mlctx.vlctx)
              ((none, .vlam consumedDom) :: Hc.mlctx.vlctx) :=
            VLCtx.IsDefEq.cons
              (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) nofun
              (.vlam Hdom.source_defeq.choose_spec)
          have hsourceBodyType : Hc'.venv.IsType c.lparams.length
              Hc'.mlctx.vlctx.toCtx fullBody := by
            simpa only [Hc', ContextWF.withLocalDecl_venv,
              ContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using
              hbodyFullType.defeqDFC Hc.checking.tr.wf.ordered hctx.defeqCtx
          have hbodyEq' := Hdom.bodyDefEqConsumed Hc _hbodyEq
          have hconsumedBodyType : Hc'.venv.IsType c.lparams.length
              Hc'.mlctx.vlctx.toCtx consumedBody := by
            apply hsourceBodyType.defeqU_l Hc'.checking.tr.wf
              Hc'.mlctx_wf.tr.wf.toCtx
            simpa only [Hc', ContextWF.withLocalDecl_venv,
              ContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using hbodyEq'
          have hdeps : dom.consumeTypeAnnotations.fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotations_fvarsIn htypeFVars.1)).1
          rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
            ⟨_domainLevel, hdomain⟩
          let Hruntime' :
              checkInductiveTypes.loopType.NarrowRuntimeScope
                Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam indexType) :: scope)
                Hc'.mlctx.vlctx :=
            Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
          have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
          let Wnarrow : VLCtx.FVLift scope
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope) 0 1 0 :=
            .skip_fvar _ _ .refl
          have HnarrowIndicesWeak : List.Forall₂
              (TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam indexType) :: scope))
              indices.toList
              (indexTargets.map fun result => result.liftN 1 0) := by
            apply checkPositivityStep.forall₂_map_right HnarrowIndices
            intro source result Hsource
            exact Hsource.weakFV Hc.checking.tr.wf.ordered Wnarrow hscopeWF
          have HnarrowIndex : TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope)
              (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
            exact TrExprS.fvar (A := indexType.lift) (by
              simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
                VLocalDecl.value, VLocalDecl.type])
          have HnarrowIndices' : List.Forall₂
              (TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam indexType) :: scope))
              (indices.push (.fvar ⟨c.ngen.curr⟩)).toList
              ((indexTargets.map fun result => result.liftN 1 0) ++
                [.bvar 0]) := by
            rw [Array.toList_push]
            exact checkPositivityStep.forall₂_append
              HnarrowIndicesWeak (.cons HnarrowIndex .nil)
          have hopenedNarrow : TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope)
              (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
            rw [Expr.instantiate1_eq]
            exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
          have hopenedFVars : FVarsIn
              (· ∈ VLCtx.fvars ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope))
              (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) := by
            rw [Expr.instantiate1_eq]
            apply (htypeFVars.2.mono fun fv hfv => by
              rw [VLCtx.fvars_cons_some]
              exact List.mem_cons_of_mem _ hfv).instantiate1
            rw [VLCtx.fvars_cons_some]
            exact List.mem_cons_self
          have hwhnf := whnfInContext.scopeWF Hc' hopened
          exact hwhnf.bind fun next hnext => by
            have hnormalizedFVars :=
              hnext.1 _ Hruntime'.upset hopenedFVars
            rcases hnext.2 with
              ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
            have hnormalizedClosed : Closed next 0 := by
              have := hnormalizedFull.closed
              simpa [Hc'.mlctx.noBV] using this
            rcases Hruntime'.restrictEq Hc'.checking.tr.wf
                hnormalizedFull hnormalizedClosed hnormalizedFVars with
              ⟨normalizedNarrow, hnormalizedNarrow, hnormalizedEq⟩
            have hopenedWeak : TrExprS Hc'.venv c.lparams
                Hruntime'.expanded
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
                (narrowBody.lift' Hruntime'.shift) := by
              simpa using hopenedNarrow.weakFV' Hc'.checking.tr.wf.ordered
                Hruntime'.lift Hruntime'.context.wf
            have hopenedEq := hopenedWeak.uniq Hc'.checking.tr.wf
              Hruntime'.context hopened
            have hopenedEq' := hopenedEq.defeqDFC
              Hc'.checking.tr.wf.ordered Hruntime'.context.defeqCtx
            have hnormalizeU : Hc'.venv.IsDefEqU c.lparams.length
                Hc'.mlctx.vlctx.toCtx consumedBody normalizedFull :=
              hnormalizeEq.symm
            have hsourceNormalized := hopenedEq'.trans Hc'.checking.tr.wf
              Hc'.mlctx_wf.tr.wf.toCtx hnormalizeU
            have hfull : Hc'.venv.IsDefEqU c.lparams.length
                Hc'.mlctx.vlctx.toCtx
                (narrowBody.lift' Hruntime'.shift)
                (normalizedNarrow.lift' Hruntime'.shift) :=
              hsourceNormalized.trans Hc'.checking.tr.wf
                Hc'.mlctx_wf.tr.wf.toCtx hnormalizedEq
            have hexpanded := hfull.defeqDFC Hc'.checking.tr.wf.ordered
              (Hruntime'.context.defeqCtx.symm Hc'.checking.tr.wf.ordered)
            have hnarrow : Hc'.venv.IsDefEqU c.lparams.length
                (indexType :: scope.toCtx) narrowBody normalizedNarrow :=
              (VEnv.IsDefEqU.weak'_iff Hc'.checking.tr.wf
                Hruntime'.context.wf.toCtx Hruntime'.lift.toCtx).1 hexpanded
            have hdomainNarrow : ∃ sourceDom',
                TrExprS Hc'.venv c.lparams scope dom sourceDom' ∧
                Hc'.venv.IsDefEqU c.lparams.length scope.toCtx
                  sourceDom' indexType :=
              ⟨_, hdomNarrow, ⟨.sort (Classical.choose hdomType),
                Classical.choose_spec hdomType⟩⟩
            have htransition : ∃ sourceBody' normalized',
                TrExprS Hc'.venv c.lparams
                  ((none, .vlam indexType) :: scope) body sourceBody' ∧
                TrExprS Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    dom.consumeTypeAnnotations.fvarsList),
                    .vlam indexType) :: scope) next normalized' ∧
                Hc'.venv.IsDefEqU c.lparams.length
                  (indexType :: scope.toCtx) sourceBody' normalized' :=
              ⟨narrowBody, normalizedNarrow, hbodyNarrow,
                hnormalizedNarrow, hnarrow⟩
            rcases Hsynthesis.consumeIndex (name := name) (bi := bi)
                Hc'.checking.tr.wf
                (.forallE hdomType _hbodyType hdomNarrow hbodyNarrow)
                hscopeWF hdomainNarrow htransition with
              ⟨nextNarrow, hnextNarrow, Hsynthesis',
                ⟨_hparams, _hindices⟩⟩
            exact continueIndexSynthesisSemantics stats k HrootCtx hconsume Hk
              next consumedBody nextNarrow
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope)
              i (nindices + 1)
              (indices.push (.fvar ⟨c.ngen.curr⟩))
              (originTypes.push dom.consumeTypeAnnotations)
              ((indexTargets.map fun result => result.liftN 1 0) ++
                [.bvar 0]) fuel _ hdone Hc' Hsynthesis'
              (HnarrowStats.withFVar Hc'.checking.tr.wf hscopeWF)
              (by simpa [Nat.add_assoc] using
                Hstats.withLocalDecl Hc Hdom.consumed Hdom.isType)
              Hruntime'
              hnextNarrow hnormalizedFVars
              ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
              hconsumedBodyType Hindices' HnarrowIndices'
              (by simp [hindexCount])
              (by simpa [hcanonical] using canonicalIndexVars_succ nindices)
              (Horigins.push Hdom name bi)
              (Hrecent.pushCurrent name dom.consumeTypeAnnotations consumedDom
                bi Hdom.consumed Hdom.isType)
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
          have hi : ¬ i < stats.params.size := by omega
          simpa [AddInductive.mkRecInfos.loopArgs1, hi] using
            Hk Hc Hsynthesis HnarrowStats Hstats Hruntime htypeNarrow
              htypeFVars htypeFull htypeFullType Hindices HnarrowIndices
              hindexCount hcanonical Horigins Hrecent

/-- Replay the common-parameter prefix from the independent family shape,
advancing both the retained concrete suffix and the narrow semantic header.
At parameter completion the exact cached-parameter scope is re-embedded in
the executable context and passed to `continueIndexSynthesisSemantics`, which
owns the genuine-index suffix.  A defensive executable exit before that
boundary is rejected before the continuation is invoked. -/
theorem continueCheckedSemantics {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M alpha)
    {Q : alpha → Prop}
    {target : VInductiveType} {decl : VInductDecl} {depth : Nat}
    (hconsume : ConsumeTypeAnnotationsCompat)
    {c : AddInductive.Context} (Hc : ContextWF c)
    (Hk : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      {type : Expr} {fullTarget narrowTarget : VExpr} {scope : VLCtx}
      {nindices : Nat} {indices originTypes : Array Expr}
      {indexTargets : List VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc'.venv c'.lparams target.toSkeleton scope narrowTarget
          stats.params.size nindices) →
      checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams scope stats decl
        nindices →
      checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl
        (depth + nindices) →
      checkInductiveTypes.loopType.NarrowRuntimeScope Hc'.venv c'.lparams
        scope Hc'.mlctx.vlctx →
      TrExprS Hc'.venv c'.lparams scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr Hc'.venv c'.lparams Hc'.mlctx.vlctx type fullTarget →
      Hc'.venv.IsType c'.lparams.length Hc'.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
        indices.toList indexTargets →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams scope)
        indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = canonicalIndexVars nindices →
      TranslatedOriginTypes Hc' originTypes →
      RecentBoundFVarArray Hc Hc' indices →
      (k indices c').WF Q)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    {params : List VExpr}
    (hparams : stats.params.size = decl.nparams)
    (huvars : c.lparams.length = decl.uvars)
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (hshape : decl.TypeShape Hc.venv params target)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth) :
    ∀ type fullTarget narrowTarget scope i indices originTypes
        indexTargets fuel,
      i ≤ stats.params.size →
      (Hscope : ∀ hi : i < stats.params.size,
        checkInductiveTypes.loopType.LaterParameterScope
          Hsuffix i type) →
      (∀ hi : i < stats.params.size, scope = (Hscope hi).older) →
      (i = stats.params.size → scope = Hsuffix.parameterDecls) →
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams target.toSkeleton scope narrowTarget i 0 →
      TrExprS Hc.venv c.lparams scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullTarget →
      Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx)
        indices.toList indexTargets →
      indexTargets.length = 0 →
      indexTargets = canonicalIndexVars 0 →
      TranslatedOriginTypes Hc originTypes →
      (AddInductive.mkRecInfos.loopArgs1 stats type i indices fuel k c).WF Q
  | _, _, _, _, _, _, _, _, 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | type, fullTarget, narrowTarget, scope, i, indices, originTypes,
      indexTargets, fuel + 1, hbound, Hscope, hscopeEq, hcompleteScope,
      Hsynthesis, htypeNarrow, htypeFVars, htypeFull, htypeFullType,
      Hindices, hindexCount, hcanonical, Horigins => by
      by_cases hdone : stats.params.size ≤ i
      · have hieq : i = stats.params.size := by omega
        subst i
        have hscope : scope = Hsuffix.parameterDecls :=
          hcompleteScope rfl
        subst scope
        let Hruntime :=
          checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
            Hc Hsuffix
        have hindexTargets : indexTargets = [] :=
          List.eq_nil_of_length_eq_zero hindexCount
        have hindicesList : indices.toList = [] := by
          apply List.eq_nil_of_length_eq_zero
          have hlength :=
            Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hindices
          rw [hindexTargets] at hlength
          exact hlength
        have hindicesEmpty : indices = #[] := by
          apply Array.eq_empty_of_size_eq_zero
          simpa using congrArg List.length hindicesList
        have Hrecent : RecentBoundFVarArray Hc Hc indices := by
          rw [hindicesEmpty]
          exact RecentBoundFVarArray.empty Hc
        have HnarrowIndices : List.Forall₂
            (TrExprS Hc.venv c.lparams Hsuffix.parameterDecls)
            indices.toList indexTargets := by
          rw [hindicesList, hindexTargets]
          exact .nil
        exact continueIndexSynthesisSemantics stats k Hc hconsume Hk type
          fullTarget narrowTarget Hsuffix.parameterDecls stats.params.size 0
          indices originTypes indexTargets (fuel + 1) c (by omega) Hc
          Hsynthesis (Hsuffix.narrowStats Hstats hparams) Hstats Hruntime
          htypeNarrow htypeFVars htypeFull htypeFullType Hindices
          HnarrowIndices
          hindexCount hcanonical Horigins Hrecent
      · have hi : i < stats.params.size := by omega
        cases type with
        | forallE name dom body bi =>
          rw [AddInductive.mkRecInfos.loopArgs1, if_pos hi]
          have htypeNarrow' := htypeNarrow
          cases htypeNarrow with
          | @forallE currentDomain currentBody _ _ _ _ _
              _hdomType _hbodyType hdomNarrow _hbodyNarrow =>
            let Hcurrent := Hscope hi
            have hscope : scope = Hcurrent.older := hscopeEq hi
            subst scope
            rcases parameterStepOfCheckedHeader Hc Hcurrent Hsynthesis hi
                hparams huvars hctx hshape
                htypeNarrow' htypeFull with
              ⟨bodyTarget, hopened, hopenedType⟩
            have hwhnf := whnfInContext.scopeWF Hc hopened
            exact hwhnf.bind fun next hnext => by
              have hnarrowMatch := Hcurrent.currentDomainDefEq Hsynthesis
                hi hparams huvars hctx hshape
              have hindices : Hsynthesis.indices = [] :=
                List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
              have hcurrentWF := Hcurrent.lift.wf Hc.checking.tr.wf
                Hc.mlctx_wf.tr.wf
              let Hbody :
                  checkInductiveTypes.loopType.LaterParameterScope
                    Hsuffix i body :=
                { Hcurrent with fvars := Hcurrent.fvars.2 }
              rcases Hbody.normalizedBody hopened hnext.1 hnext.2 with
                ⟨sourceBody, normalizedTarget, hsourceBody,
                  hnormalizedNarrow, hbodyEq⟩
              rcases Hsynthesis.consumeParameter Hc.checking.tr.wf
                  hindices htypeNarrow'
                  hcurrentWF
                  ⟨currentDomain, hdomNarrow, hnarrowMatch⟩
                  ⟨sourceBody, normalizedTarget, hsourceBody,
                    hnormalizedNarrow, hbodyEq⟩ with
                ⟨nextNarrow, hnormalizedNarrow', ⟨Hsynthesis'⟩⟩
              exact continueCheckedSemantics stats k hconsume Hc Hk
                Hsuffix hparams huvars hctx hshape Hstats next bodyTarget nextNarrow
                ((some (Hcurrent.fv, Hcurrent.deps),
                  .vlam Hcurrent.paramType) :: Hcurrent.older)
                (i + 1) indices originTypes indexTargets fuel
                (by omega)
                (fun hlt => Hbody.next hlt hnext.1)
                (fun hlt => Hbody.nextOlder
                  (Hbody.next hlt hnext.1) hlt)
                (fun heq => by
                  have hfinished : i + 1 = stats.params.size := heq
                  exact Hcurrent.completedScope hfinished)
                Hsynthesis' hnormalizedNarrow'
                (Hbody.consumedFVars hnext.1) hnext.2 hopenedType
                Hindices hindexCount hcanonical Horigins
        | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
          | proj =>
            simp only [AddInductive.mkRecInfos.loopArgs1, hi, if_pos]
            exact Except.WF.throw
termination_by
  type fullTarget narrowTarget scope i indices originTypes indexTargets fuel => fuel

/-- Replay the genuine-index suffix wholly under the recursor universe list.
The exact cached-parameter telescope remains a suffix of every generated
context, while the narrow synthesized header and the executable context grow
in lockstep by one semantically checked index declaration. -/
theorem continueRecursorIndexSynthesisSemantics {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M alpha)
    {Q : alpha → Prop}
    {base root : AddInductive.Context} {Hbase : ContextWF base}
    {decl : VInductDecl} {depth familyIdx : Nat} {source : InductiveType}
    (H : CheckedRecursorHeaderAt Hbase stats decl depth source familyIdx)
    {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (Rroot : RecursorContextWF root
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    {rootParameterDecls : VLCtx}
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (Hk : ∀ {current : AddInductive.Context} {runtimeDepth : Nat}
      (R : RecursorContextWF current
        (AddInductive.getRecLevelParams elimLevel base.lparams))
      (henv : R.venv = Hbase.venv)
      (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
      (hparameterDecls :
        Hsuffix.parameterDecls = rootParameterDecls)
      {type : Expr} {fullTarget narrowTarget : VExpr} {scope : VLCtx}
      {nindices : Nat} {indices originTypes : Array Expr}
      {indexTargets : List VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
          (H.recursorTargetSkeleton Helim) scope narrowTarget
          stats.params.size nindices) →
      Hsynthesis.params.reverse = rootParameterDecls.toCtx →
      scope.drop nindices = rootParameterDecls →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope stats decl nindices →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx stats decl runtimeDepth →
      (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope R.mlctx.vlctx) →
      Hruntime.frontSourceDomains = Hsynthesis.indices →
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx type fullTarget →
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx) indices.toList indexTargets →
      List.Forall₂ (TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope) indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = canonicalIndexVars nindices →
      BoundFVarTypeOrigins current indices originTypes →
      RecursorTranslatedOriginTypes R originTypes →
      RecursorRecentBoundFVarArray Rroot R indices →
      (k indices current).WF Q) :
    ∀ {current : AddInductive.Context} {runtimeDepth : Nat}
      (R : RecursorContextWF current
        (AddInductive.getRecLevelParams elimLevel base.lparams))
      (henv : R.venv = Hbase.venv)
      (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
      (hparameterDecls : Hsuffix.parameterDecls = rootParameterDecls)
      type fullTarget narrowTarget scope nindices indices originTypes
        indexTargets fuel,
      (Hsynthesis :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
          (H.recursorTargetSkeleton Helim) scope narrowTarget
          stats.params.size nindices) →
      Hsynthesis.params.reverse = rootParameterDecls.toCtx →
      scope.drop nindices = rootParameterDecls →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope stats decl nindices →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx stats decl runtimeDepth →
      (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope R.mlctx.vlctx) →
      Hruntime.frontSourceDomains = Hsynthesis.indices →
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx type fullTarget →
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx) indices.toList indexTargets →
      List.Forall₂ (TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope) indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = canonicalIndexVars nindices →
      BoundFVarTypeOrigins current indices originTypes →
      RecursorTranslatedOriginTypes R originTypes →
      RecursorRecentBoundFVarArray Rroot R indices →
      (AddInductive.mkRecInfos.loopArgs1 stats type stats.params.size
        indices fuel k current).WF Q
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | current, runtimeDepth, R, henv, Hsuffix, hparameterDecls, type,
      fullTarget, narrowTarget,
      scope, nindices, indices, originTypes, indexTargets, fuel + 1, Hsynthesis,
      hcanonicalParams, hscopeBase, HnarrowStats, Hstats, Hruntime, hfront, htypeNarrow,
      htypeFVars, htypeFull,
      htypeFullType, Hindices, HnarrowIndices, hindexCount, hcanonical,
      Horigins, HoriginTypes, Hrecent => by
      cases type with
      | forallE name dom body bi =>
        rw [AddInductive.mkRecInfos.loopArgs1]
        have hparam : ¬ stats.params.size < stats.params.size := by omega
        rw [if_neg hparam]
        cases htypeNarrow with
        | @forallE indexType narrowBody _ _ _ _ _
            hdomType _hbodyType hdomNarrow hbodyNarrow =>
          rcases TrExpr.forallE_source htypeFull with
            ⟨sourceDom, fullBody, hdomFull, hbodyFull, hdomFullType,
              hbodyFullType, _hfullCurrent⟩
          rcases hconsume current _ R hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          rcases Hdom.body R hbodyFull with
            ⟨consumedBody, hbodyConsumed, hbodyEq⟩
          refine withLocalDecl.recursorWF (name := name) (bi := bi) (Q := Q)
            R Hdom.consumed Hdom.isType ?_
          let R' := R.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType
          let Hsuffix' := Hsuffix.withAmbient (name := name) (bi := bi)
            Hdom.consumed Hdom.isType
          let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
            .skip_fvar _ _ .refl
          have HindicesWeak : List.Forall₂
              (TrExprS R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                R'.mlctx.vlctx)
              indices.toList
              (indexTargets.map fun result => result.liftN 1 0) := by
            apply checkPositivityStep.forall₂_map_right Hindices
            intro source result Hsource
            exact Hsource.weakFV R.checking.tr.wf.ordered W
              R'.mlctx_wf.tr.wf
          have Hindex : TrExprS R'.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams)
              R'.mlctx.vlctx (.fvar ⟨current.ngen.curr⟩) (.bvar 0) := by
            exact TrExprS.fvar (A := consumedDom.lift) (by
              change VLCtx.find? ((some (⟨current.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList), .vlam consumedDom) ::
                  R.mlctx.vlctx) (Sum.inr ⟨current.ngen.curr⟩) = _
              simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
                VLocalDecl.value, VLocalDecl.type])
          have Hindices' : List.Forall₂
              (TrExprS R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                R'.mlctx.vlctx)
              (indices.push (.fvar ⟨current.ngen.curr⟩)).toList
              ((indexTargets.map fun result => result.liftN 1 0) ++
                [.bvar 0]) := by
            simpa using checkPositivityStep.forall₂_append HindicesWeak
              (.cons Hindex .nil)
          have hopened := R.instantiateFresh (name := name) (bi := bi)
            Hdom.consumed Hdom.isType hbodyConsumed
          have hctx : VLCtx.IsDefEq R.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams).length
              ((none, .vlam sourceDom) :: R.mlctx.vlctx)
              ((none, .vlam consumedDom) :: R.mlctx.vlctx) :=
            VLCtx.IsDefEq.cons
              (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) nofun
              (.vlam Hdom.source_defeq.choose_spec)
          have hsourceBodyType : R'.venv.IsType
              (AddInductive.getRecLevelParams elimLevel base.lparams).length
              R'.mlctx.vlctx.toCtx fullBody := by
            simpa only [R', RecursorContextWF.withLocalDecl_venv,
              RecursorContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using
              hbodyFullType.defeqDFC R.checking.tr.wf.ordered hctx.defeqCtx
          have hbodyEq' := Hdom.bodyDefEqConsumed R hbodyEq
          have hconsumedBodyType : R'.venv.IsType
              (AddInductive.getRecLevelParams elimLevel base.lparams).length
              R'.mlctx.vlctx.toCtx consumedBody := by
            apply hsourceBodyType.defeqU_l R'.checking.tr.wf
              R'.mlctx_wf.tr.wf.toCtx
            simpa only [R', RecursorContextWF.withLocalDecl_venv,
              RecursorContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using
              hbodyEq'
          have hdeps : dom.consumeTypeAnnotations.fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotations_fvarsIn htypeFVars.1)).1
          rcases Hruntime.recursorConsumedDomain R Hdom hdomNarrow with
            ⟨_domainLevel, hdomain⟩
          let Hruntime' :
              checkInductiveTypes.loopType.NarrowRuntimeScope
                R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                ((some (⟨current.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam indexType) :: scope)
                R'.mlctx.vlctx :=
            Hruntime.withIndex R'.mlctx_wf.tr.wf hdeps hdomain
          have hscopeWF := Hruntime'.scopeWF R'.checking.tr.wf
          let Wnarrow : VLCtx.FVLift scope
              ((some (⟨current.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope) 0 1 0 :=
            .skip_fvar _ _ .refl
          have HnarrowIndicesWeak : List.Forall₂
              (TrExprS R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                ((some (⟨current.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam indexType) :: scope))
              indices.toList
              (indexTargets.map fun result => result.liftN 1 0) := by
            apply checkPositivityStep.forall₂_map_right HnarrowIndices
            intro source result Hsource
            exact Hsource.weakFV R.checking.tr.wf.ordered Wnarrow hscopeWF
          have HnarrowIndex : TrExprS R'.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams)
              ((some (⟨current.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope)
              (.fvar ⟨current.ngen.curr⟩) (.bvar 0) := by
            exact TrExprS.fvar (A := indexType.lift) (by
              simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
                VLocalDecl.value, VLocalDecl.type])
          have HnarrowIndices' : List.Forall₂
              (TrExprS R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                ((some (⟨current.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam indexType) :: scope))
              (indices.push (.fvar ⟨current.ngen.curr⟩)).toList
              ((indexTargets.map fun result => result.liftN 1 0) ++
                [.bvar 0]) := by
            rw [Array.toList_push]
            exact checkPositivityStep.forall₂_append
              HnarrowIndicesWeak (.cons HnarrowIndex .nil)
          have hopenedNarrow : TrExprS R'.venv
              (AddInductive.getRecLevelParams elimLevel base.lparams)
              ((some (⟨current.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope)
              (body.instantiate1 (.fvar ⟨current.ngen.curr⟩)) narrowBody := by
            rw [Expr.instantiate1_eq]
            exact hbodyNarrow.inst_fvar R.checking.tr.wf.ordered hscopeWF
          have hopenedFVars : FVarsIn
              (· ∈ VLCtx.fvars ((some (⟨current.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope))
              (body.instantiate1 (.fvar ⟨current.ngen.curr⟩)) := by
            rw [Expr.instantiate1_eq]
            apply (htypeFVars.2.mono fun fv hfv => by
              rw [VLCtx.fvars_cons_some]
              exact List.mem_cons_of_mem _ hfv).instantiate1
            rw [VLCtx.fvars_cons_some]
            exact List.mem_cons_self
          have hnormalize := whnfInRecursorContext.scopeWF hwhnf R' hopened
          exact hnormalize.bind fun next hnext => by
            have hnormalizedFVars := hnext.1 _ Hruntime'.upset hopenedFVars
            rcases hnext.2 with
              ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
            have hnormalizedClosed : Closed next 0 := by
              have := hnormalizedFull.closed
              simpa [R'.mlctx.noBV] using this
            rcases Hruntime'.restrictEq R'.checking.tr.wf
                hnormalizedFull hnormalizedClosed hnormalizedFVars with
              ⟨normalizedNarrow, hnormalizedNarrow, hnormalizedEq⟩
            have hopenedWeak : TrExprS R'.venv
                (AddInductive.getRecLevelParams elimLevel base.lparams)
                Hruntime'.expanded
                (body.instantiate1 (.fvar ⟨current.ngen.curr⟩))
                (narrowBody.lift' Hruntime'.shift) := by
              simpa using hopenedNarrow.weakFV' R'.checking.tr.wf.ordered
                Hruntime'.lift Hruntime'.context.wf
            have hopenedEq := hopenedWeak.uniq R'.checking.tr.wf
              Hruntime'.context hopened
            have hopenedEq' := hopenedEq.defeqDFC
              R'.checking.tr.wf.ordered Hruntime'.context.defeqCtx
            have hnormalizeU : R'.venv.IsDefEqU
                (AddInductive.getRecLevelParams elimLevel base.lparams).length
                R'.mlctx.vlctx.toCtx consumedBody normalizedFull :=
              hnormalizeEq.symm
            have hsourceNormalized := hopenedEq'.trans R'.checking.tr.wf
              R'.mlctx_wf.tr.wf.toCtx hnormalizeU
            have hfull : R'.venv.IsDefEqU
                (AddInductive.getRecLevelParams elimLevel base.lparams).length
                R'.mlctx.vlctx.toCtx
                (narrowBody.lift' Hruntime'.shift)
                (normalizedNarrow.lift' Hruntime'.shift) :=
              hsourceNormalized.trans R'.checking.tr.wf
                R'.mlctx_wf.tr.wf.toCtx hnormalizedEq
            have hexpanded := hfull.defeqDFC R'.checking.tr.wf.ordered
              (Hruntime'.context.defeqCtx.symm R'.checking.tr.wf.ordered)
            have hnarrow : R'.venv.IsDefEqU
                (AddInductive.getRecLevelParams elimLevel base.lparams).length
                (indexType :: scope.toCtx) narrowBody normalizedNarrow :=
              (VEnv.IsDefEqU.weak'_iff R'.checking.tr.wf
                Hruntime'.context.wf.toCtx Hruntime'.lift.toCtx).1 hexpanded
            have hdomainNarrow : ∃ sourceDom',
                TrExprS R'.venv
                  (AddInductive.getRecLevelParams elimLevel base.lparams)
                  scope dom sourceDom' ∧
                R'.venv.IsDefEqU
                  (AddInductive.getRecLevelParams elimLevel base.lparams).length
                  scope.toCtx sourceDom' indexType :=
              ⟨_, hdomNarrow, ⟨.sort (Classical.choose hdomType),
                Classical.choose_spec hdomType⟩⟩
            have htransition : ∃ sourceBody' normalized',
                TrExprS R'.venv
                  (AddInductive.getRecLevelParams elimLevel base.lparams)
                  ((none, .vlam indexType) :: scope) body sourceBody' ∧
                TrExprS R'.venv
                  (AddInductive.getRecLevelParams elimLevel base.lparams)
                  ((some (⟨current.ngen.curr⟩,
                    dom.consumeTypeAnnotations.fvarsList),
                    .vlam indexType) :: scope) next normalized' ∧
                R'.venv.IsDefEqU
                  (AddInductive.getRecLevelParams elimLevel base.lparams).length
                  (indexType :: scope.toCtx) sourceBody' normalized' :=
              ⟨narrowBody, normalizedNarrow, hbodyNarrow,
                hnormalizedNarrow, hnarrow⟩
            rcases Hsynthesis.consumeIndex (name := name) (bi := bi)
                R'.checking.tr.wf
                (.forallE hdomType _hbodyType hdomNarrow hbodyNarrow)
                hscopeWF hdomainNarrow htransition with
              ⟨nextNarrow, hnextNarrow, Hsynthesis',
                ⟨hparams, hfrontIndices⟩⟩
            exact continueRecursorIndexSynthesisSemantics stats k H Helim
              Rroot hwhnf hconsume Hk R' (by simpa [R'] using henv)
              Hsuffix' (by
                change Hsuffix.parameterDecls = rootParameterDecls
                exact hparameterDecls)
              next consumedBody nextNarrow
              ((some (⟨current.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope)
              (nindices + 1)
              (indices.push (.fvar ⟨current.ngen.curr⟩))
              (originTypes.push dom.consumeTypeAnnotations)
              ((indexTargets.map fun result => result.liftN 1 0) ++
                [.bvar 0]) fuel Hsynthesis' (by
                  rw [hparams]
                  exact hcanonicalParams)
              (by
                change scope.drop nindices = rootParameterDecls
                exact hscopeBase)
              (HnarrowStats.withFVar R'.checking.tr.wf hscopeWF)
              (Hstats.withFVar R'.checking.tr.wf R'.mlctx_wf.tr.wf)
              Hruntime' (by
                change Hruntime.frontSourceDomains ++ [indexType] =
                  Hsynthesis'.indices
                rw [hfront, hfrontIndices])
              hnextNarrow hnormalizedFVars
              ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
              hconsumedBodyType Hindices' HnarrowIndices'
              (by simp [hindexCount])
              (by simpa [hcanonical] using
                canonicalIndexVars_succ nindices)
              (Horigins.pushCurrent R.toBindingContextWF name
                dom.consumeTypeAnnotations bi)
              (HoriginTypes.push (name := name) (bi := bi)
                Hdom.consumed Hdom.isType)
              (Hrecent.pushCurrent name dom.consumeTypeAnnotations consumedDom
                bi Hdom.consumed Hdom.isType)
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
          simpa [AddInductive.mkRecInfos.loopArgs1] using
            Hk R henv Hsuffix hparameterDecls Hsynthesis hcanonicalParams
              hscopeBase HnarrowStats Hstats Hruntime
              hfront htypeNarrow htypeFVars htypeFull htypeFullType Hindices
              HnarrowIndices hindexCount hcanonical Horigins HoriginTypes Hrecent
termination_by
  current runtimeDepth R henv Hsuffix hparameterDecls type fullTarget narrowTarget scope
    nindices indices originTypes indexTargets fuel => fuel

/-- Replay the cached common-parameter prefix directly in a universe-rebased
recursor context.  The terminal continuation begins at the genuine-index
boundary with the exact completed narrow suffix; no generated index, major,
or motive declaration is admitted into the parameter telescope. -/
theorem continueRecursorParameterSemantics {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M alpha)
    {Q : alpha → Prop}
    {base current : AddInductive.Context} {Hbase : ContextWF base}
    {decl : VInductDecl} {depth runtimeDepth familyIdx : Nat}
    {source : InductiveType}
    (H : CheckedRecursorHeaderAt Hbase stats decl depth source familyIdx)
    {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (hwhnf : WhnfLParamsCompat)
    (henv : R.venv = Hbase.venv)
    (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
    (hctx : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) R.mlctx.vlctx
      stats decl runtimeDepth)
    (Hk : ∀ {type : Expr} {fullTarget narrowTarget : VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
          (H.recursorTargetSkeleton Helim) Hsuffix.parameterDecls
          narrowTarget stats.params.size 0) →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls stats decl 0 →
      (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls R.mlctx.vlctx) →
      Hruntime.frontSourceDomains = Hsynthesis.indices →
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls type narrowTarget →
      FVarsIn (· ∈ Hsuffix.parameterDecls.fvars) type →
      TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx type fullTarget →
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx fullTarget →
      ∀ indices fuel,
        indices = #[] →
        (AddInductive.mkRecInfos.loopArgs1 stats type stats.params.size
          indices fuel k current).WF Q) :
    ∀ type fullTarget narrowTarget scope i indices fuel,
      i ≤ stats.params.size →
      (Hscope : ∀ hi : i < stats.params.size,
        RecursorLaterParameterScope Hsuffix i type) →
      (∀ hi : i < stats.params.size, scope = (Hscope hi).older) →
      (i = stats.params.size → scope = Hsuffix.parameterDecls) →
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
        (H.recursorTargetSkeleton Helim) scope narrowTarget i 0 →
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx type fullTarget →
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx fullTarget →
      indices = #[] →
      (AddInductive.mkRecInfos.loopArgs1 stats type i indices fuel
        k current).WF Q
  | _, _, _, _, _, _, 0, _, _, _, _, _, _, _, _, _, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | type, fullTarget, narrowTarget, scope, i, indices, fuel + 1,
      hbound, Hscope, hscopeEq, hcompleteScope, Hsynthesis,
      htypeNarrow, htypeFVars, htypeFull, htypeFullType, hindicesEmpty => by
      by_cases hdone : stats.params.size ≤ i
      · have hieq : i = stats.params.size := by omega
        subst i
        have hscope : scope = Hsuffix.parameterDecls :=
          hcompleteScope rfl
        subst scope
        exact Hk Hsynthesis (Hsuffix.narrowStats Hstats)
          Hsuffix.runtimeScope (by
            change [] = Hsynthesis.indices
            exact (List.eq_nil_of_length_eq_zero
              Hsynthesis.indexCount).symm)
          htypeNarrow htypeFVars htypeFull
          htypeFullType indices (fuel + 1) hindicesEmpty
      · have hi : i < stats.params.size := by omega
        cases type with
        | forallE name dom body bi =>
          rw [AddInductive.mkRecInfos.loopArgs1, if_pos hi]
          have htypeNarrow' := htypeNarrow
          cases htypeNarrow with
          | @forallE currentDomain currentBody _ _ _ _ _ _hdomType
              _hbodyType hdomNarrow _hbodyNarrow =>
            let Hcurrent := Hscope hi
            have hscope : scope = Hcurrent.older := hscopeEq hi
            subst scope
            rcases parameterStepOfCheckedRecursorHeader H Helim R Hcurrent
                Hsynthesis hi henv hctx htypeNarrow' htypeFull with
              ⟨bodyTarget, hopened, hopenedType⟩
            have hnormalize :=
              whnfInRecursorContext.scopeWF hwhnf R hopened
            exact hnormalize.bind fun next hnext => by
              have hnarrowMatch := H.recursorCurrentDomainDefEq Helim
                Hcurrent Hsynthesis hi henv hctx
              have hindices : Hsynthesis.indices = [] :=
                List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
              have hcurrentWF := Hcurrent.lift.wf R.checking.tr.wf
                R.mlctx_wf.tr.wf
              let Hbody : RecursorLaterParameterScope Hsuffix i body :=
                { Hcurrent with fvars := Hcurrent.fvars.2 }
              rcases Hbody.normalizedBody hopened hnext.1 hnext.2 with
                ⟨sourceBody, normalizedTarget, hsourceBody,
                  hnormalizedNarrow, hbodyEq⟩
              rcases Hsynthesis.consumeParameter R.checking.tr.wf
                  hindices htypeNarrow' hcurrentWF
                  ⟨currentDomain, hdomNarrow, hnarrowMatch⟩
                  ⟨sourceBody, normalizedTarget, hsourceBody,
                    hnormalizedNarrow, hbodyEq⟩ with
                ⟨nextNarrow, hnextNarrow, ⟨Hsynthesis'⟩⟩
              exact continueRecursorParameterSemantics stats k H Helim R
                hwhnf henv Hsuffix hctx Hstats Hk next bodyTarget
                nextNarrow
                ((some (Hcurrent.fv, Hcurrent.deps),
                  .vlam Hcurrent.paramType) :: Hcurrent.older)
                (i + 1) indices fuel (by omega)
                (fun hlt => Hbody.next hlt hnext.1)
                (fun hlt => Hbody.nextOlder
                  (Hbody.next hlt hnext.1) hlt)
                (fun heq => Hcurrent.completedScope heq)
                Hsynthesis' hnextNarrow
                (Hbody.consumedFVars hnext.1) hnext.2 hopenedType
                hindicesEmpty
        | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
          | proj =>
            simp only [AddInductive.mkRecInfos.loopArgs1, hi, if_pos]
            exact Except.WF.throw
termination_by
  type fullTarget narrowTarget scope i indices fuel => fuel

/-- Start checked argument replay at the exact `whnf` boundary used by
`loopInd1`.  Closed source headers initialize an empty narrow scope; the
materialized parameter suffix supplies every subsequent cached parameter. -/
theorem startCheckedSemantics {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M alpha)
    {Q : alpha → Prop}
    {decl : VInductDecl} {params : List VExpr} {depth : Nat}
    {source : InductiveType} {target : VInductiveType}
    (hconsume : ConsumeTypeAnnotationsCompat)
    {c : AddInductive.Context} (Hc : ContextWF c)
    (Hk : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      {type : Expr} {fullTarget narrowTarget : VExpr} {scope : VLCtx}
      {nindices : Nat} {indices originTypes : Array Expr}
      {indexTargets : List VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc'.venv c'.lparams target.toSkeleton scope narrowTarget
          stats.params.size nindices) →
      checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams scope stats decl
        nindices →
      checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl
        (depth + nindices) →
      checkInductiveTypes.loopType.NarrowRuntimeScope Hc'.venv c'.lparams
        scope Hc'.mlctx.vlctx →
      TrExprS Hc'.venv c'.lparams scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr Hc'.venv c'.lparams Hc'.mlctx.vlctx type fullTarget →
      Hc'.venv.IsType c'.lparams.length Hc'.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
        indices.toList indexTargets →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams scope)
        indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = canonicalIndexVars nindices →
      TranslatedOriginTypes Hc' originTypes →
      RecentBoundFVarArray Hc Hc' indices →
      (k indices c').WF Q)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Htarget : TrSourceConst Hc.venv c.lparams source.name source.type
      target.toVConstVal)
    (hparams : stats.params.size = decl.nparams)
    (huvars : c.lparams.length = decl.uvars)
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (hshape : decl.TypeShape Hc.venv params target)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth)
    (fuel : Nat) :
    ((monadLift (TypeChecker.whnf source.type) : AddInductive.M Expr) c >>=
      fun normalized => AddInductive.mkRecInfos.loopArgs1 stats normalized 0
        #[] fuel k c).WF Q := by
  let W : VLCtx.FVLift [] Hc.mlctx.vlctx 0
      Hc.mlctx.vlctx.toCtx.length 0 :=
    VLCtx.FVLift.from_nil Hc.mlctx.noBV
  have htargetType : Hc.venv.IsType c.lparams.length [] target.type := by
    have htargetType := Htarget.wf
    change Hc.venv.IsType target.uvars [] target.type at htargetType
    rwa [Htarget.uvars] at htargetType
  have hsource : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      source.type (target.type.liftN Hc.mlctx.vlctx.toCtx.length 0) := by
    simpa using Htarget.type.weakFV Hc.checking.tr.wf.ordered W
      Hc.mlctx_wf.tr.wf
  have hsourceTarget :
      target.type.liftN Hc.mlctx.vlctx.toCtx.length 0 = target.type := by
    have hclosed := (Classical.choose_spec htargetType).closedN
      Hc.checking.tr.wf.ordered (by trivial)
    exact hclosed.liftN_eq (Nat.zero_le _)
  rw [hsourceTarget] at hsource
  have hsourceType : Hc.venv.IsType c.lparams.length
      Hc.mlctx.vlctx.toCtx target.type := by
    have hweak := htargetType.weakN Hc.checking.tr.wf.ordered W.toCtx
    simpa [hsourceTarget] using hweak
  have hwhnf := whnfInContext.scopeWF Hc hsource
  exact hwhnf.bind fun normalized hnormalized => by
    have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
      Htarget.type.fvarsIn.mono fun fv hfv => by
        simpa [VLCtx.fvars] using hfv
    have hfalseUpSet : IsFVarUpSet (fun _ => False) Hc.mlctx.vlctx := by
      have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
        Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
      simpa [VLCtx.fvars] using hsuffix
    have hnormalizedNoFVars : FVarsIn (fun _ => False) normalized :=
      hnormalized.1 _ hfalseUpSet hsourceNoFVars
    have HtargetSkeleton : TrSourceConst Hc.venv c.lparams
        source.name source.type target.toSkeleton.toVConstVal := by
      simpa [VInductiveType.toSkeleton] using Htarget
    rcases checkInductiveTypes.loopInd.initialLaterHeaderSynthesisStateOfTranslation Hc
        HtargetSkeleton hsource hnormalized.2 hnormalizedNoFVars with
      ⟨narrowTarget, hnormalizedNarrow, ⟨Hsynthesis⟩⟩
    let Hscope : ∀ hi : 0 < stats.params.size,
        checkInductiveTypes.loopType.LaterParameterScope
          Hsuffix 0 normalized := fun hi =>
      checkInductiveTypes.loopInd.initialLaterParameterScope Hc Hsuffix hi
        HtargetSkeleton hnormalized.1
    have hscopeEq : ∀ hi : 0 < stats.params.size,
        [] = (Hscope hi).older := by
      intro hi
      exact (Hscope hi).older_eq_nil hi |>.symm
    have hcompleteScope : 0 = stats.params.size →
        ([] : VLCtx) = Hsuffix.parameterDecls := by
      intro hzero
      exact (List.eq_nil_of_length_eq_zero (by
        rw [Hsuffix.parameterDecls_length, ← hzero])).symm
    exact continueCheckedSemantics stats k hconsume Hc Hk Hsuffix
      hparams huvars hctx hshape Hstats normalized target.type narrowTarget [] 0
      #[] #[] [] fuel (by omega) Hscope hscopeEq hcompleteScope Hsynthesis
      hnormalizedNarrow (by simpa [VLCtx.fvars] using hnormalizedNoFVars)
      hnormalized.2 hsourceType .nil rfl rfl
      (TranslatedOriginTypes.empty Hc)

/-- Start universe-rebased cached-parameter replay from the exact production
`whnf` boundary.  This wrapper is valid after arbitrary earlier mutual
recursor frames have accumulated in the executable reader context. -/
theorem CheckedRecursorHeaderAt.startRecursorParameterSemantics
    {alpha : Type} {Q : alpha → Prop}
    {base current : AddInductive.Context} {Hbase : ContextWF base}
    (H : CheckedRecursorHeaderAt Hbase stats decl depth source familyIdx)
    {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (hwhnf : WhnfLParamsCompat)
    (henv : R.venv = Hbase.venv)
    (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
    (hctx : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) R.mlctx.vlctx
      stats decl runtimeDepth)
    (k : Array Expr → AddInductive.M alpha)
    (Hk : ∀ {type : Expr} {fullTarget narrowTarget : VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          R.venv (AddInductive.getRecLevelParams elimLevel base.lparams)
          (H.recursorTargetSkeleton Helim) Hsuffix.parameterDecls
          narrowTarget stats.params.size 0) →
      RecursorValidAppStatsWF R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls stats decl 0 →
      (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls R.mlctx.vlctx) →
      Hruntime.frontSourceDomains = Hsynthesis.indices →
      TrExprS R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Hsuffix.parameterDecls type narrowTarget →
      FVarsIn (· ∈ Hsuffix.parameterDecls.fvars) type →
      TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx type fullTarget →
      R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx fullTarget →
      ∀ indices fuel,
        indices = #[] →
        (AddInductive.mkRecInfos.loopArgs1 stats type stats.params.size
          indices fuel k current).WF Q)
    (fuel : Nat) :
    ((monadLift (TypeChecker.whnf source.type) : AddInductive.M Expr)
      current >>= fun normalized =>
        AddInductive.mkRecInfos.loopArgs1 stats normalized 0 #[] fuel k
          current).WF Q := by
  have hstart := H.startRecursorHeaderSemantics Helim R henv hwhnf
  exact hstart.bind fun normalized hnormalized => by
    rcases hnormalized.2 with
      ⟨narrowTarget, hnormalizedNarrow, ⟨Hsynthesis⟩⟩
    have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
      (H.recursorSourceTranslation Helim).fvarsIn.mono fun fv hfv => by
        simpa [VLCtx.fvars] using hfv
    have hfalseUpSet : IsFVarUpSet (fun _ => False) R.mlctx.vlctx := by
      have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
        R.mlctx.vlctx (by simpa using R.mlctx_wf.tr.wf)
      simpa [VLCtx.fvars] using hsuffix
    have hnormalizedNoFVars : FVarsIn (fun _ => False) normalized :=
      hnormalized.1 _ hfalseUpSet hsourceNoFVars
    let W : VLCtx.FVLift [] R.mlctx.vlctx 0
        R.mlctx.vlctx.toCtx.length 0 :=
      VLCtx.FVLift.from_nil R.mlctx.noBV
    have hnormalizedFullS := hnormalizedNarrow.weakFV
      R.checking.tr.wf.ordered W R.mlctx_wf.tr.wf
    have hnormalizedFull : TrExpr R.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        R.mlctx.vlctx normalized
        (narrowTarget.liftN R.mlctx.vlctx.toCtx.length 0) :=
      hnormalizedFullS.trExpr R.checking.tr.wf R.mlctx_wf.tr.wf
    have hnormalizedFullType : R.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        R.mlctx.vlctx.toCtx
        (narrowTarget.liftN R.mlctx.vlctx.toCtx.length 0) :=
      Hsynthesis.currentType.weakN R.checking.tr.wf.ordered W.toCtx
    let Hscope : ∀ hi : 0 < stats.params.size,
        RecursorLaterParameterScope Hsuffix 0 normalized := fun hi =>
      RecursorLaterParameterScope.ofNoFVars hi hnormalizedNoFVars
    have hscopeEq : ∀ hi : 0 < stats.params.size,
        [] = (Hscope hi).older := by
      intro hi
      exact (Hscope hi).older_eq_nil hi |>.symm
    have hcompleteScope : 0 = stats.params.size →
        ([] : VLCtx) = Hsuffix.parameterDecls := by
      intro hzero
      exact (List.eq_nil_of_length_eq_zero (by
        rw [Hsuffix.parameterDecls_length, ← hzero])).symm
    exact continueRecursorParameterSemantics stats k H Helim R hwhnf henv
      Hsuffix hctx Hstats Hk normalized
      (narrowTarget.liftN R.mlctx.vlctx.toCtx.length 0) narrowTarget [] 0
      #[] fuel (by omega) Hscope hscopeEq hcompleteScope Hsynthesis
      hnormalizedNarrow
      (by simpa [VLCtx.fvars] using hnormalizedNoFVars)
      hnormalizedFull hnormalizedFullType rfl

/-- Complete parameter and genuine-index replay under one recursor-universe
context.  The continuation is reached with the exact retained parameter
suffix, canonical index variables, and a recent-index certificate rooted at
the context in which this family began. -/
theorem CheckedRecursorHeaderAt.startRecursorSemantics
    {alpha : Type} {Q : alpha → Prop}
    {base current : AddInductive.Context} {Hbase : ContextWF base}
    (H : CheckedRecursorHeaderAt Hbase stats decl depth source familyIdx)
    {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel base.lparams elimLevel)
    (R : RecursorContextWF current
      (AddInductive.getRecLevelParams elimLevel base.lparams))
    (hwhnf : WhnfLParamsCompat)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (henv : R.venv = Hbase.venv)
    (Hsuffix : RecursorParameterContextSuffix R stats runtimeDepth)
    (hctx : VEnv.IsDefEqCtx R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams).length []
      (H.recursorParams Helim).reverse Hsuffix.parameterDecls.toCtx)
    (Hstats : RecursorValidAppStatsWF R.venv
      (AddInductive.getRecLevelParams elimLevel base.lparams) R.mlctx.vlctx
      stats decl runtimeDepth)
    (k : Array Expr → AddInductive.M alpha)
    (Hk : ∀ {next : AddInductive.Context} {nextDepth : Nat}
      (Rnext : RecursorContextWF next
        (AddInductive.getRecLevelParams elimLevel base.lparams))
      (henvNext : Rnext.venv = Hbase.venv)
      (HsuffixNext : RecursorParameterContextSuffix Rnext stats nextDepth)
      (hparameterDecls :
        HsuffixNext.parameterDecls = Hsuffix.parameterDecls)
      {type : Expr} {fullTarget narrowTarget : VExpr} {scope : VLCtx}
      {nindices : Nat} {indices originTypes : Array Expr}
      {indexTargets : List VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Rnext.venv
          (AddInductive.getRecLevelParams elimLevel base.lparams)
          (H.recursorTargetSkeleton Helim) scope narrowTarget
          stats.params.size nindices) →
      Hsynthesis.params.reverse = Hsuffix.parameterDecls.toCtx →
      scope.drop nindices = Hsuffix.parameterDecls →
      RecursorValidAppStatsWF Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope stats decl nindices →
      RecursorValidAppStatsWF Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Rnext.mlctx.vlctx stats decl nextDepth →
      (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope Rnext.mlctx.vlctx) →
      Hruntime.frontSourceDomains = Hsynthesis.indices →
      TrExprS Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Rnext.mlctx.vlctx type fullTarget →
      Rnext.venv.IsType
        (AddInductive.getRecLevelParams elimLevel base.lparams).length
        Rnext.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        Rnext.mlctx.vlctx) indices.toList indexTargets →
      List.Forall₂ (TrExprS Rnext.venv
        (AddInductive.getRecLevelParams elimLevel base.lparams)
        scope) indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = canonicalIndexVars nindices →
      BoundFVarTypeOrigins next indices originTypes →
      RecursorTranslatedOriginTypes Rnext originTypes →
      RecursorRecentBoundFVarArray R Rnext indices →
      (k indices next).WF Q)
    (fuel : Nat) :
    ((monadLift (TypeChecker.whnf source.type) : AddInductive.M Expr)
      current >>= fun normalized =>
        AddInductive.mkRecInfos.loopArgs1 stats normalized 0 #[] fuel k
          current).WF Q := by
  refine H.startRecursorParameterSemantics Helim R hwhnf henv Hsuffix hctx
    Hstats k ?_ fuel
  intro type fullTarget narrowTarget Hsynthesis HnarrowStats Hruntime hfront
    htypeNarrow htypeFVars htypeFull htypeFullType indices remaining
    hindicesEmpty
  subst indices
  have hcanonicalParams : Hsynthesis.params.reverse =
      Hsuffix.parameterDecls.toCtx := by
    have hindices : Hsynthesis.indices = [] :=
      List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
    simpa [hindices] using Hsynthesis.scopeCtx.symm
  exact continueRecursorIndexSynthesisSemantics stats k H Helim R hwhnf
    hconsume Hk R henv Hsuffix rfl type fullTarget narrowTarget
    Hsuffix.parameterDecls 0 #[] #[] [] remaining Hsynthesis
    hcanonicalParams rfl HnarrowStats
    Hstats Hruntime hfront htypeNarrow htypeFVars htypeFull htypeFullType .nil .nil
    rfl rfl (BoundFVarTypeOrigins.empty current)
    (RecursorTranslatedOriginTypes.empty R)
    (RecursorRecentBoundFVarArray.empty R)

/-- Package-facing entry to checked recursor replay.  All family selection,
parameter-cache, universe, and source-translation premises are projected from
one indexed header certificate; only the completed-index continuation remains
for `loopInd1` to discharge. -/
theorem CheckedRecursorHeaderAt.startSemantics {alpha : Type}
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : CheckedRecursorHeaderAt Hc stats decl depth source familyIdx)
    (k : Array Expr → AddInductive.M alpha) {Q : alpha → Prop}
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hk : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      {type : Expr} {fullTarget narrowTarget : VExpr} {scope : VLCtx}
      {nindices : Nat} {indices originTypes : Array Expr}
      {indexTargets : List VExpr},
      (Hsynthesis :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc'.venv c'.lparams H.target.toSkeleton scope narrowTarget
          stats.params.size nindices) →
      checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams scope stats decl
        nindices →
      checkPositivityStep.ValidAppStatsWF Hc'.venv c'.lparams Hc'.mlctx.vlctx stats decl
        (depth + nindices) →
      checkInductiveTypes.loopType.NarrowRuntimeScope Hc'.venv c'.lparams
        scope Hc'.mlctx.vlctx →
      TrExprS Hc'.venv c'.lparams scope type narrowTarget →
      FVarsIn (· ∈ scope.fvars) type →
      TrExpr Hc'.venv c'.lparams Hc'.mlctx.vlctx type fullTarget →
      Hc'.venv.IsType c'.lparams.length Hc'.mlctx.vlctx.toCtx fullTarget →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
        indices.toList indexTargets →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams scope)
        indices.toList indexTargets →
      indexTargets.length = nindices →
      indexTargets = canonicalIndexVars nindices →
      TranslatedOriginTypes Hc' originTypes →
      RecentBoundFVarArray Hc Hc' indices →
      (k indices c').WF Q)
    (fuel : Nat) :
    ((monadLift (TypeChecker.whnf source.type) : AddInductive.M Expr) c >>=
      fun normalized => AddInductive.mkRecInfos.loopArgs1 stats normalized 0
        #[] fuel k c).WF Q := by
  exact startCheckedSemantics stats k hconsume Hc Hk H.parameterSuffix
    H.sourceTranslation H.parameterCount H.materialized.uvars H.paramsContext
    H.shape (checkPositivityStep.ValidAppStatsWF.ofMaterializedHeader
      H.materialized) fuel

end mkRecInfos.loopArgs1


end VerifyInductive
end Lean4Lean
