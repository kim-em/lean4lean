import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterAlignment
import Lean4Lean.Verify.Inductive.Nested.FinalEnvironmentEvidence

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- The left member of a shared concrete forall prefix exposes that exact
number of binders, independently of either residual. -/
theorem Expr.SameForallPrefix.leftTelescope
    (H : Expr.SameForallPrefix n left right) :
    ∃ residual, Expr.ForallTelescope left n residual := by
  induction H with
  | @nil left right => exact ⟨left, .nil left⟩
  | cons _ ih =>
    rcases ih with ⟨residual, Htail⟩
    exact ⟨residual, .cons Htail⟩

/-- Assemble the restored parameter-domain payload from one actual checked
constructor prefix.

The family half is deliberately stated as an exact decomposition plus its
alignment with the executable cached scope.  The constructor half is fully
derived: its domains are selected from the restored source translation, and
`SameForallPrefix` transfers the checked lowered trace without translating
the changed lowered residual. -/
theorem RestoredConstructorParameterDomains.ofCheckedSameForallPrefix
    (henv : env.WF)
    (hscope : VLCtx.WF env levelParams.length scope)
    (Hchecked : CheckedConstructorParameterPrefix env levelParams stats
      loweredSource numParams loweredTail scope checkedDomains)
    (Hsame : Expr.SameForallPrefix numParams sourceConstructor loweredSource)
    (Hconstructor : TrExprS env levelParams [] sourceConstructor
      constructorTarget.type)
    (familyDomains : List VExpr) (familyTail : VExpr)
    (HfamilyTarget : env.IsDefEqU levelParams.length [] familyTarget.type
      (VExpr.wrapForalls familyDomains familyTail))
    (hfamilyLength : familyDomains.length = numParams)
    (hfamilyScope : env.IsDefEqCtx levelParams.length []
      familyDomains.reverse scope.toCtx) :
    Nonempty (RestoredConstructorParameterDomains env levelParams numParams
      familyTarget constructorTarget) := by
  rcases Hsame.leftTelescope with ⟨sourceResidual, HsourceTelescope⟩
  rcases TrExprS.forallTelescope_shape HsourceTelescope Hconstructor with
    ⟨constructorDomains, constructorTail, hconstructorLength,
      hconstructorTarget⟩
  have HconstructorFull : TrExpr env levelParams [] sourceConstructor
      (VExpr.wrapForalls constructorDomains constructorTail) := by
    rw [← hconstructorTarget]
    exact Hconstructor.trExpr henv.ordered (by trivial)
  have hconstructorScope : env.IsDefEqCtx levelParams.length []
      constructorDomains.reverse scope.toCtx :=
    Hchecked.contextDefEqOfSameForallPrefixTranslation henv hscope Hsame
      HconstructorFull hconstructorLength
  exact ⟨{
    familyDomains := familyDomains
    constructorDomains := constructorDomains
    familyTail := familyTail
    constructorTail := constructorTail
    familyTarget_defeq := HfamilyTarget
    constructorTarget_eq := hconstructorTarget
    familyLength := hfamilyLength
    constructorLength := hconstructorLength
    parameterDomains := VEnv.IsDefEqCtx.transEmpty henv hfamilyScope
      (hconstructorScope.symm henv.ordered) }⟩

/-- The exact restored-family half of constructor parameter coherence.  This
is family-indexed (rather than constructor-indexed): every constructor of one
family is compared with the same executable cached parameter scope. -/
structure RestoredFamilyParameterScope
    (env : VEnv) (levelParams : List Name) (numParams : Nat)
    (scope : VLCtx) (familyTarget : VConstant) where
  domains : List VExpr
  tail : VExpr
  target_defeq : env.IsDefEqU levelParams.length [] familyTarget.type
    (VExpr.wrapForalls domains tail)
  length : domains.length = numParams
  context : env.IsDefEqCtx levelParams.length [] domains.reverse scope.toCtx

/-- Build restored constructor-parameter coherence from the independent raw
constructor-formation judgment, rather than transporting the particular
definitional-equality proofs chosen by the executable parameter replay.

Both the restored family and the restored constructor are compared with the
same canonical parameter list.  The executable cached scope is used only as
the already-verified bridge for the family's normalized header; no
derivation-locality or environment-restriction premise enters this theorem.
-/
theorem RestoredFamilyParameterScope.constructorDomains
    {decl : VInductDecl} {params : List VExpr} {constructor : VConstVal}
    (Hfamily : RestoredFamilyParameterScope env levelParams numParams scope
      familyTarget)
    (henv : env.WF)
    (Hctor : decl.CtorParameterShape env params constructor)
    (huvars : decl.uvars = levelParams.length)
    (hnparams : decl.nparams = numParams)
    (hparamsScope : env.IsDefEqCtx levelParams.length []
      params.reverse scope.toCtx) :
    Nonempty (RestoredConstructorParameterDomains env levelParams numParams
      familyTarget constructor.toVConstant) := by
  rcases Hctor with ⟨constructorDomains, constructorTail,
    hconstructorTake, hconstructorParams⟩
  rcases VExpr.takeForalls_rebuild hconstructorTake with
    ⟨hconstructorTarget, hconstructorLength⟩
  have hconstructorToParams : env.IsDefEqCtx levelParams.length []
      constructorDomains.reverse params.reverse := by
    have hparams : env.IsDefEqCtx levelParams.length []
        params.reverse constructorDomains.reverse := by
      simpa [VInductDecl.ParamsDefEq, huvars] using hconstructorParams
    exact hparams.symm henv.ordered
  have hconstructorScope : env.IsDefEqCtx levelParams.length []
      constructorDomains.reverse scope.toCtx :=
    VEnv.IsDefEqCtx.transEmpty henv hconstructorToParams hparamsScope
  exact ⟨{
    familyDomains := Hfamily.domains
    constructorDomains := constructorDomains
    familyTail := Hfamily.tail
    constructorTail := constructorTail
    familyTarget_defeq := Hfamily.target_defeq
    constructorTarget_eq := hconstructorTarget
    familyLength := Hfamily.length
    constructorLength := hconstructorLength.trans hnparams
    parameterDomains := VEnv.IsDefEqCtx.transEmpty henv Hfamily.context
      (hconstructorScope.symm henv.ordered) }⟩

/-- A completed constructor run exposes its actual checked parameter-prefix
trace in the original post-header environment where the executable
comparison occurred. -/
theorem ConstructorPhasesResult.checkedConstructorParameterPrefixAt
    {c : AddInductive.Context}
    {stats : AddInductive.InductiveStats} {decl : VInductDecl}
    {nparams depth : Nat} {isUnsafe : Bool} {sourceEnv : VEnv}
    {indTypes : Array InductiveType} {headerEnv outEnv : Environment}
    {H : DeclaredHeadersResult c stats decl nparams isUnsafe depth sourceEnv
      indTypes headerEnv}
    (R : ConstructorPhasesResult H outEnv)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctorIdx : Nat) (hctor : ctorIdx < indTypes[familyIdx].ctors.length) :
    ∃ tail sourceDomains,
      CheckedConstructorParameterPrefix H.context.venv c.lparams stats
        indTypes[familyIdx].ctors[ctorIdx].type stats.params.size tail
        H.materialized.parameterScope sourceDomains := by
  rcases R.checkedRecursorConstructorTailAt familyIdx hfamily ctorIdx hctor with
    ⟨_ctorVal, tail, _tailTarget, sourceDomains, _hctorMem,
      _Hctor, _Hprefix, Hchecked, _Htail, _Hcertificate, _Hsynthesis⟩
  exact ⟨tail, sourceDomains, Hchecked⟩

/-- The checked comparisons contain enough typing information to rebuild the
cached scope in any environment where the exact trace lives.  Free-variable
freshness and dependency closure are syntax-only and are supplied by the
original executable scope. -/
theorem CheckedConstructorParameterPrefix.scopeWFOfFVWF
    (henv : env.WF)
    (H : CheckedConstructorParameterPrefix env Us stats original
      i current scope sourceDomains)
    (hfv : scope.FVWF) : scope.WF env Us.length := by
  induction H with
  | zero => trivial
  | step H hparam hparamFVar hdomain hdomainType hcompare ih =>
    rename_i i name dom body bi oldScope oldDomains param fv sourceDomain
      paramType deps
    rcases hfv with ⟨hfv, hfresh⟩
    have hparamType : env.IsType Us.length oldScope.toCtx paramType := by
      exact hdomainType.defeqU_l henv (ih hfv).toCtx hcompare
    exact ⟨ih hfv, hfresh, hparamType⟩

/-- Family-indexed parameter scopes connecting the production checker trace
to restored constructors.  This chooses no constructor and contains no
constructor semantics. -/
def NestedRestoredFamilyParameterScopes
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes sourceEnv
      decl lparams nparams isUnsafe safety outEnv) : Prop :=
  ∀ familyIdx (hfamily : familyIdx < decl.types.length),
    Nonempty (RestoredFamilyParameterScope E.assembly.canonical.venvCtors
      lparams nparams E.production.headers.materialized.parameterScope
      decl.types[familyIdx].toVConstVal.toVConstant)

/-- The independently restored source family has the same semantic parameter
telescope as the lowered header that the executable checker materialized.
The telescope need not be syntactically visible in the restored constant:
header checking normalizes before exposing `TypeShape`. -/
theorem NestedExactFinalRunResult.restoredFamilyParameterScopes
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes sourceEnv
      decl lparams nparams isUnsafe safety outEnv)
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed E.productionContext.env fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[]) :
    NestedRestoredFamilyParameterScopes E := by
  let Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl E.assembly.canonical.venvTypes
        E.assembly.canonical.venvCtors :=
    E.assembly.sourceSemantics.core E.assembly.typesSource E.assembly.uvars
      E.assembly.numParams E.assembly.unsafeEq E.assembly.typesAdded
      E.assembly.constructorsAdded
  have hsourceWF : sourceEnv.WF := by
    have hwf := E.production.headers.sourceContext.checking.tr.wf
    rw [E.production.headers.sourceContextVEnv] at hwf
    simpa only [E.production_initialEnv] using hwf
  have hcanonicalWF : E.assembly.canonical.venvCtors.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF Hsource hsourceWF
  have hsourceLE : sourceEnv ≤ E.assembly.canonical.venvCtors :=
    (VEnv.addConstVals_le E.assembly.typesAdded).trans
      (VEnv.addConstVals_le E.assembly.constructorsAdded)
  have hlparams : E.production.c.lparams = lparams := by
    rw [E.production_c, E.productionContext_lparams]
  intro familyIdx hfamily
  have hsourceFamily : familyIdx < sourceTypes.length := by
    rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  have hresultFamily : familyIdx < result.types.length :=
    Nat.lt_of_lt_of_le hsourceFamily Hlower.toResult.sourceTypes_length_le
  have hloweredFamily : familyIdx < E.production.loweredDecl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
      E.production.constructors.core]
    simpa only [E.production_indTypes] using hresultFamily
  let sourceTarget := decl.types[familyIdx]
  let loweredTarget := E.production.loweredDecl.types[familyIdx]
  have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource
    familyIdx hsourceFamily hfamily
  have HproductionCore : TrInductDeclCore E.production.initialEnv lparams
      nparams result.types E.production.isUnsafe E.production.loweredDecl
      E.production.headers.context.venv
      E.production.constructors.declared.venvCtors := by
    simpa [hlparams, E.production_nparams, E.production_indTypes]
      using E.production.constructors.core
  rcases Hlower.sourceHeaderTranslationAtFresh hempty
      HproductionCore familyIdx hsourceFamily with
    ⟨_hdecl, HloweredHeader⟩
  have HtargetEq : sourceEnv.IsDefEqU lparams.length []
      sourceTarget.type loweredTarget.type := by
    exact HsourceType.header.type.uniq hsourceWF
      (.refl hsourceWF (by trivial)) (by
        simpa only [E.production_initialEnv, hlparams,
          sourceTarget, loweredTarget]
        using HloweredHeader.type)
  have HloweredShape : E.production.loweredDecl.TypeShape sourceEnv
      E.production.headers.sourceMaterialized.headers.params loweredTarget := by
    have Hshape :=
      E.production.headers.sourceMaterialized.headers.typeShapes loweredTarget
        (List.getElem_mem hloweredFamily)
    simpa only [E.production.headers.sourceContextVEnv,
      E.production_initialEnv] using Hshape
  rcases HloweredShape with
    ⟨normalized, ownParams, afterParams, _indices, _familyResult, exprType,
      Hnormalized, HparamsTake, _HindicesTake, Hparams, _Hresult⟩
  rcases VExpr.takeForalls_rebuild HparamsTake with
    ⟨HnormalizedEq, hownParams⟩
  have HsourceNormalized : sourceEnv.IsDefEq lparams.length []
      sourceTarget.type normalized exprType := by
    have HtargetEq' : sourceEnv.IsDefEqU E.production.loweredDecl.uvars []
        sourceTarget.type loweredTarget.type := by
      simpa [E.production.constructors.core.uvars, hlparams] using HtargetEq
    have Hnormalized' := VEnv.IsDefEq.transU_r hsourceWF (by trivial)
      HtargetEq' Hnormalized
    simpa [E.production.constructors.core.uvars, hlparams] using Hnormalized'
  have HtargetDefEq : E.assembly.canonical.venvCtors.IsDefEqU
      lparams.length [] sourceTarget.type
      (VExpr.wrapForalls ownParams afterParams) := by
    rw [← HnormalizedEq]
    exact ⟨exprType, HsourceNormalized.mono hsourceLE⟩
  have HownCommon : E.assembly.canonical.venvCtors.IsDefEqCtx
      lparams.length [] ownParams.reverse
      E.production.headers.sourceMaterialized.headers.params.reverse := by
    have Hparams' : sourceEnv.IsDefEqCtx lparams.length []
        E.production.headers.sourceMaterialized.headers.params.reverse
        ownParams.reverse := by
      simpa [VInductDecl.ParamsDefEq,
        E.production.constructors.core.uvars, hlparams] using Hparams
    exact (Hparams'.symm hsourceWF.ordered).mono hsourceLE
  have HcommonCached : E.assembly.canonical.venvCtors.IsDefEqCtx
      lparams.length []
      E.production.headers.sourceMaterialized.headers.params.reverse
      E.production.headers.sourceMaterialized.parameterScope.toCtx := by
    have Hcached₀ := E.production.headers.sourceMaterialized.paramsContext
    have Hcached : sourceEnv.IsDefEqCtx lparams.length []
        E.production.headers.sourceMaterialized.headers.params.reverse
        E.production.headers.sourceMaterialized.parameterScope.toCtx := by
      simpa only [E.production.headers.sourceContextVEnv,
        E.production_initialEnv, hlparams] using Hcached₀
    exact Hcached.mono hsourceLE
  have HownCached := VEnv.IsDefEqCtx.transEmpty hcanonicalWF HownCommon
    HcommonCached
  exact ⟨{
    domains := ownParams
    tail := afterParams
    target_defeq := by simpa [sourceTarget] using HtargetDefEq
    length := by
      calc
        ownParams.length = E.production.loweredDecl.nparams := hownParams
        _ = E.production.nparams := E.production.constructors.core.nparams
        _ = nparams := E.production_nparams
    context := by
      rw [E.production.headers.parameterScopeEq]
      exact HownCached }⟩

/-- Build restored constructor-parameter coherence directly from the source
parameter-formation certificate retained by nested assembly.  The source
certificate fixes one canonical parameter list for every family and
constructor.  For each restored family, equal-length forall inversion aligns
that list with the executable cached parameter scope.  Consequently no
derivation-locality or environment-restriction premise is required. -/
theorem NestedExactFinalRunResult.restoredConstructorParameterDomainsNative
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes sourceEnv
      decl lparams nparams isUnsafe safety outEnv)
    (Hfamilies : NestedRestoredFamilyParameterScopes E) :
    NestedRestoredConstructorParameterDomains E.assembly := by
  rcases E.assembly.formationAssembly.sourceParameters with
    ⟨params, parameterEnv, hparameterEnv, Htypes, Hconstructors⟩
  have hcanonicalTypes : parameterEnv =
      E.assembly.canonical.venvTypes := by
    exact Option.some.inj (hparameterEnv.symm.trans
      E.assembly.typesAdded)
  subst parameterEnv
  have hsourceTypes : sourceEnv ≤ E.assembly.canonical.venvTypes :=
    VEnv.addConstVals_le E.assembly.typesAdded
  have htypesCtors : E.assembly.canonical.venvTypes ≤
      E.assembly.canonical.venvCtors :=
    VEnv.addConstVals_le E.assembly.canonical.ctorsAdded.abstract
  have hsourceCtors : sourceEnv ≤ E.assembly.canonical.venvCtors :=
    hsourceTypes.trans htypesCtors
  have hcanonicalWF : E.assembly.canonical.venvCtors.WF := by
    let Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
        isUnsafe decl E.assembly.canonical.venvTypes
          E.assembly.canonical.venvCtors :=
      E.assembly.sourceSemantics.core E.assembly.typesSource E.assembly.uvars
        E.assembly.numParams E.assembly.unsafeEq
        E.assembly.typesAdded E.assembly.constructorsAdded
    have hsourceWF : sourceEnv.WF := by
      have hwf := E.production.headers.sourceContext.checking.tr.wf
      rw [E.production.headers.sourceContextVEnv] at hwf
      simpa only [E.production_initialEnv] using hwf
    exact TrInductDeclCore.envCtorsWF Hsource hsourceWF
  intro familyIdx hfamily ctorIdx hctor
  let family := decl.types[familyIdx]
  let constructor := family.ctors[ctorIdx]
  have hfamilyMem : family ∈ decl.types :=
    List.getElem_mem hfamily
  have hctorMem : constructor ∈ family.ctors :=
    List.getElem_mem hctor
  have Hshape := Htypes family hfamilyMem
  have Hconstructor : decl.CtorParameterShape
      E.assembly.canonical.venvCtors params constructor :=
    (Hconstructors family hfamilyMem constructor hctorMem).mono htypesCtors
  rcases Hfamilies familyIdx hfamily with ⟨Hfamily⟩
  rcases Hshape with
    ⟨normalized, ownParams, afterParams, indices, resultType, exprType,
      Hnormalized, HparamsTake, _HindicesTake, Hparams, _Hresult⟩
  rcases VExpr.takeForalls_rebuild HparamsTake with
    ⟨HnormalizedTarget, hownLength⟩
  have HsourcePresentation :
      E.assembly.canonical.venvCtors.IsDefEqU lparams.length []
        family.type (VExpr.wrapForalls ownParams afterParams) := by
    rw [← HnormalizedTarget]
    exact ⟨exprType, by
      simpa [E.assembly.uvars] using Hnormalized.mono hsourceCtors⟩
  have Hpresentations :
      E.assembly.canonical.venvCtors.IsDefEqU lparams.length []
        (VExpr.wrapForalls ownParams afterParams)
        (VExpr.wrapForalls Hfamily.domains Hfamily.tail) := by
    exact HsourcePresentation.symm.trans hcanonicalWF (by trivial)
      (by simpa [family] using Hfamily.target_defeq)
  have HownFamily := VEnv.IsDefEqU.wrapForalls_context hcanonicalWF
    (VEnv.IsDefEqCtx.refl (by trivial))
    (hownLength.trans (E.assembly.numParams.trans Hfamily.length.symm))
    Hpresentations
  have HparamsOwn : E.assembly.canonical.venvCtors.IsDefEqCtx
      lparams.length [] params.reverse ownParams.reverse := by
    simpa [VInductDecl.ParamsDefEq, E.assembly.uvars] using
      Hparams.mono hsourceCtors
  have HparamsFamily : E.assembly.canonical.venvCtors.IsDefEqCtx
      lparams.length [] params.reverse Hfamily.domains.reverse :=
    VEnv.IsDefEqCtx.transEmpty hcanonicalWF HparamsOwn (by
      simpa using HownFamily)
  have HparamsScope : E.assembly.canonical.venvCtors.IsDefEqCtx
      lparams.length [] params.reverse
        E.production.headers.materialized.parameterScope.toCtx :=
    VEnv.IsDefEqCtx.transEmpty hcanonicalWF HparamsFamily Hfamily.context
  simpa [family, constructor] using
    Hfamily.constructorDomains hcanonicalWF Hconstructor
      E.assembly.uvars E.assembly.numParams HparamsScope

/-- Convert the exact producer-side restriction contract into the complete
pointwise restored constructor-domain payload.  Constructor domains,
lowering alignment, environment rebasing, and source translations are all
derived here; the only separate input is the single family parameter scope
shared by all constructors of that family. -/
theorem NestedExactFinalRunResult.restoredConstructorParameterDomains
    (E : NestedExactFinalRunResult result sourceProdEnv sourceTypes sourceEnv
      decl lparams nparams isUnsafe safety outEnv)
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hlower : NestedLoweringResultClosed E.productionContext.env fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (Hlocality : ConstructorParameterReplayLocality)
    (Hfamilies : NestedRestoredFamilyParameterScopes E) :
    NestedRestoredConstructorParameterDomains E.assembly := by
  let Hsource : TrInductDeclCore sourceEnv lparams nparams sourceTypes
      isUnsafe decl E.assembly.canonical.venvTypes
        E.assembly.canonical.venvCtors :=
    E.assembly.sourceSemantics.core E.assembly.typesSource E.assembly.uvars
      E.assembly.numParams E.assembly.unsafeEq E.assembly.typesAdded
      E.assembly.constructorsAdded
  have hsourceWF : sourceEnv.WF := by
    have hwf := E.production.headers.sourceContext.checking.tr.wf
    rw [E.production.headers.sourceContextVEnv] at hwf
    simpa only [E.production_initialEnv] using hwf
  have hcanonicalWF : E.assembly.canonical.venvCtors.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF Hsource hsourceWF
  have HsourceFromProduction : TrInductDeclCore E.production.initialEnv
      lparams nparams sourceTypes isUnsafe decl
      E.assembly.canonical.venvTypes E.assembly.canonical.venvCtors := by
    simpa only [E.production_initialEnv] using Hsource
  have Henvironments : VEnv.LEExcept
      (fun name => name ∈ E.production.loweredDecl.sourceNames)
      E.production.headers.context.venv
      E.assembly.canonical.venvCtors :=
    TrInductDeclCore.typeEnvToCtorEnvLEExcept
      E.production.constructors.core HsourceFromProduction
  intro familyIdx hfamily ctorIdx hctor
  have hsourceFamily : familyIdx < sourceTypes.length := by
    rw [Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  have Htype := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt Hsource
    familyIdx hsourceFamily hfamily
  have hsourceCtor : ctorIdx < sourceTypes[familyIdx].ctors.length := by
    rw [Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htype]
    exact hctor
  have HsourceCtor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt Htype
    ctorIdx hsourceCtor hctor
  have hresultFamily : familyIdx < result.types.length :=
    Nat.lt_of_lt_of_le hsourceFamily Hlower.toResult.sourceTypes_length_le
  have hproductionFamily : familyIdx < E.production.indTypes.size := by
    rw [E.production_indTypes]
    simpa using hresultFamily
  rcases Hlower.sourceFinalMappingAtFreshAligned hempty hsourceFamily with
    ⟨_fvars, _stepState, loweredFamily, _loweredState, _hparams, _hnodup,
      _hsize, Hmapping, hloweredFamily⟩
  obtain ⟨_hresultFamily', hloweredFamilyEq⟩ :=
    _root_.getElem?_eq_some_iff.mp hloweredFamily
  have hproductionFamilyEq :
      E.production.indTypes[familyIdx] = loweredFamily := by
    calc
      E.production.indTypes[familyIdx] =
          E.production.indTypes.toList[familyIdx] :=
        Array.getElem_toList hproductionFamily
      _ = result.types[familyIdx] := by
        simp [E.production_indTypes]
      _ = loweredFamily := hloweredFamilyEq
  rcases Hmapping.constructors.mappingAt ctorIdx hsourceCtor with
    ⟨sourceCtor, loweredCtor, _before, _after, hsourceCtorEq,
      hloweredCtorEq, HctorMapping⟩
  obtain ⟨_hsourceCtor', hsourceCtorValue⟩ :=
    _root_.getElem?_eq_some_iff.mp hsourceCtorEq
  obtain ⟨hloweredCtor, hloweredCtorValue⟩ :=
    _root_.getElem?_eq_some_iff.mp hloweredCtorEq
  have hsourceCtorValue' : sourceCtor = sourceTypes[familyIdx].ctors[ctorIdx] :=
    hsourceCtorValue.symm
  subst sourceCtor
  have hproductionCtor :
      ctorIdx < E.production.indTypes[familyIdx].ctors.length := by
    rw [hproductionFamilyEq]
    exact hloweredCtor
  rcases E.production.constructors.checkedConstructorParameterPrefixAt
      familyIdx hproductionFamily ctorIdx hproductionCtor with
    ⟨tail, checkedDomains, HcheckedHeader⟩
  have HcheckedUses := Hlocality E.production.constructors familyIdx
    hproductionFamily ctorIdx hproductionCtor HcheckedHeader
  have HcheckedRestored := HcheckedHeader.rebaseExcept Henvironments
    HcheckedUses
  have Hsame : Expr.SameForallPrefix nparams
      sourceTypes[familyIdx].ctors[ctorIdx].type
      E.production.indTypes[familyIdx].ctors[ctorIdx].type := by
    have Hsame' := HctorMapping.sourceTargetSameForallPrefix
      ((HsourceCtor.type.fvarsIn).mono fun fv hfv => by
        simpa [VLCtx.fvars] using hfv)
    simpa only [hproductionFamilyEq, hloweredCtorValue] using Hsame'
  have Hconstructor : TrExprS E.assembly.canonical.venvCtors lparams []
      sourceTypes[familyIdx].ctors[ctorIdx].type
      decl.types[familyIdx].ctors[ctorIdx].toVConstant.type :=
    HsourceCtor.type.mono (VEnv.addConstVals_le E.assembly.constructorsAdded)
  rcases Hfamilies familyIdx hfamily with ⟨Hfamily⟩
  have hscopeFVWF :
      E.production.headers.materialized.parameterScope.FVWF :=
    (E.production.headers.materialized.runtimeScope.scopeWF
      E.production.headers.context.checking.tr.wf).fvwf
  have hscopeWF := HcheckedRestored.scopeWFOfFVWF hcanonicalWF hscopeFVWF
  have hstatsParams : E.production.stats.params.size = nparams := by
    have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      E.production.headers.materialized.params
    calc
      E.production.stats.params.size = E.production.loweredDecl.nparams := by
        simpa [VInductDecl.paramVars] using hlength
      _ = E.production.nparams := E.production.constructors.core.nparams
      _ = nparams := E.production_nparams
  exact RestoredConstructorParameterDomains.ofCheckedSameForallPrefix
    hcanonicalWF (by
      simpa only [E.production_c, E.productionContext_lparams] using hscopeWF)
    (by
      simpa only [E.production_c, E.productionContext_lparams,
        hstatsParams]
        using HcheckedRestored)
    Hsame Hconstructor Hfamily.domains Hfamily.tail Hfamily.target_defeq
    Hfamily.length Hfamily.context

end VerifyInductive
end Lean4Lean
