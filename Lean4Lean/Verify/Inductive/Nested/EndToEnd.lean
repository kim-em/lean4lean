import Lean4Lean.Verify.Inductive.Nested.LoweringInstallation
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidationRun
import Lean4Lean.Verify.Inductive.Nested.Restoration
import Lean4Lean.Verify.Inductive.Nested.OriginalHeaderSeedRebase
import Lean4Lean.Verify.Inductive.Recursor.Binders.MotivesAndIndices
import Lean4Lean.Verify.Inductive.Formation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

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

theorem NestedLoweringResultClosed.toResult
    (H : NestedLoweringResultClosed env fuel nparams types initialState result) :
    NestedLoweringResult env fuel nparams types initialState result := by
  rcases H with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  exact ⟨finalState, Hrun⟩

/-- A generated-family provenance witness selects exactly the independently
validated auxiliary translation associated with its surviving cache entry. -/
theorem GeneratedFamilyWitness.closedAuxiliaryTranslation
    (H : GeneratedFamilyWitness sourceEnv params finalState.nestedAux family)
    (Hmap : NestedAuxMapModels result finalState)
    {selection : LocalForallSelection result.lctx result.params}
    (Htranslations : ClosedNestedAuxiliaryTranslations venv lparams result
      selection) :
    Nonempty (ClosedNestedAuxiliaryTranslation venv lparams result selection
      H.data.nested) :=
  Htranslations H.auxName H.data.nested (Hmap _ _ H.cached)

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

/-- Rebase a validated auxiliary residual along a semantic conversion from
the caller's parameter telescope to the domains recovered by validation.
This is the syntax-independent core needed by nested restoration: once the
two dependent parameter contexts have been related, neither a dummy residual
nor the concrete free variables used by either opening remain relevant. -/
theorem ClosedNestedAuxiliaryTranslation.residualAtDefEqParameterDomains
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e)
    (henv : venv.WF) (parameterDomains : List VExpr)
    (Hcontexts : VEnv.IsDefEqCtx venv lparams.length []
      parameterDomains.reverse H.domains.reverse) :
    ∃ target targetType,
      TrExprS venv lparams (abstractForallContext parameterDomains [])
        (e.abstractList selection.fvars) target ∧
      venv.HasType lparams.length
        (abstractForallContext parameterDomains []).toCtx target
        targetType := by
  have Hvlctx := abstractForallContext.isDefEq Hcontexts
  rcases H.residual.defeqDFC henv (Hvlctx.symm henv.ordered) with
    ⟨target, Hresidual⟩
  refine ⟨target, H.residualType, Hresidual, ?_⟩
  have HctxSymm := Hvlctx.symm henv.ordered
  have Htyping := H.residualTyping.defeqDFC henv.ordered
    HctxSymm.defeqCtx
  have HtargetEq := H.residual.uniq henv HctxSymm Hresidual
  have HtargetEq' := HtargetEq.defeqDFC henv.ordered HctxSymm.defeqCtx
  exact (HtargetEq'.of_l henv Hvlctx.wf.toCtx Htyping).hasType.2

theorem NestedLoweringResultClosed.resultParamsSize
    (H : NestedLoweringResultClosed env fuel nparams types initialState result) :
    result.params.size = result.nparams := by
  rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
  exact Hrun.resultParamsSize.trans Hrun.resultNParams.symm

/-- The final lowering parameter selection closes the same raw source-header
prefix with any residual body.  This is the exact syntactic leg used before
the independent abstract header normalization takes over; it deliberately
does not compare lowering's raw domains with the checker's consumed domains. -/
theorem NestedLoweringResultClosed.sourceParameterPrefix
    (H : NestedLoweringResultClosed env fuel nparams types initialState result)
    (Hclosed : ∀ source ∈ types,
      source.type.FVarsIn fun _ => False)
    (HbClosed : ∀ source ∈ types, Closed source.type)
    (body : Expr) :
    ∃ first rest residual,
      types = first :: rest ∧
      Expr.ForallTelescope first.type nparams residual ∧
      Expr.SameForallPrefix nparams
        (result.lctx.mkForall result.params body) first.type := by
  rcases H with ⟨finalState, Hrun, Hcache, Hparams⟩
  have Hwhole : NestedLoweringResultClosed env fuel nparams types
      initialState result := ⟨finalState, Hrun, Hcache, Hparams⟩
  rcases Hrun.source with
    ⟨first, rest, tail, paramsState, lctx, params, htypes, Hopening,
      _hnewTypes, _hnestedAux, _hnextIdx, _hprefix, Hctx, Hselection, Hqueue⟩
  rcases Hselection with ⟨Hselection⟩
  rcases Hopening.forallTelescope with ⟨residual, Htelescope⟩
  have hsourceClosed : first.type.FVarsIn fun _ => False :=
    Hclosed first (by rw [htypes]; simp)
  have hclosed := Hopening.toRestoreParamOpening.root_mkForall_tail Hctx.wf
    Htelescope (FVarsIn_to_FVarIdsIn hsourceClosed)
    (HbClosed first (by rw [htypes]; simp))
  have HselectionResult : LocalForallSelection result.lctx result.params := by
    rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
    rw [hlctx, hparams]
    exact Hselection
  have Hsame := HselectionResult.sameForallPrefix
    (Hwhole.selectionNodup HselectionResult) body tail
  have hclosedResult : result.lctx.mkForall result.params tail =
      first.type := by
    rcases Hqueue.resultContext with ⟨hlctx, hparams⟩
    rw [hlctx, hparams]
    exact hclosed
  rw [Hrun.resultParamsSize, hclosedResult] at Hsame
  exact ⟨first, rest, residual, htypes, Htelescope, Hsame⟩

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
production cache. -/
theorem NestedLoweringResult.sourceFinalMappingAtOfEmpty
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (hempty : initialState.nestedAux = #[])
    (hj : j < sourceTypes.length) :
    ∃ params stepState target loweredState,
      params.size = nparams ∧
      LoweredInductiveMapping env params nparams result sourceTypes[j]
        stepState (target, loweredState) ∧
      result.types[j]? = some target := by
  rcases H.sourceFinalMappingAt hj with ⟨finalState, Hrun, Hmapped⟩
  apply Hmapped
  apply Hrun.resultNamesNodupOfEmpty
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
  H.sourceFinalMappingAtOfEmpty hempty hj

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
  apply Hrun.resultNamesNodupOfEmpty
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

/-- Constructor freshness required by source-expression restoration is not a
family-wise semantic input.  When lowering and ordinary installation start
from the same production environment, it follows from generated-family
freshness, the complete staged installation trace, and the persistent kernel
metadata invariant for pre-existing constructors. -/
theorem NestedLoweringResultClosed.restoreAuxConstructorsFreshAtBase
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv := by
  rcases H with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  simpa [RestoreAuxConstructorsFresh] using
    Hrun.restoreAuxConstructorsFreshOfInstallation
      ((((Hheaders.installed.append R.declared.installed).addEliminators
        (es := R.declared.eliminators)).addProjections
          (projections := decl.projectionEntries)).append Hprod.staged.recursorsAdded)
      Hc.checking.tr.map_wf Howners hempty

/-- Lift generated-constructor freshness through the source-header prefix
reconstructed directly from lowering, without source constructors or a
completed source declaration. -/
theorem NestedLoweringResultClosed.restoreAuxConstructorsFreshAtHeaderPrefix
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv) :
    RestoreAuxConstructorsFresh result loweredEnv sourceTypesVEnv := by
  intro name nested auxFamily hrecognized
  have Hbase := H.restoreAuxConstructorsFreshAtBase Hc Hprod Howners hempty
  have hbase : sourceVEnv.constants name = none :=
    Hbase name nested auxFamily hrecognized
  rcases H with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  have hnames : ∀ ci ∈
      (loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal, ci.name ≠ name := by
    intro ci hci
    rcases List.mem_map.mp hci with ⟨targetType, htargetType, rfl⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r HsourceHeaders targetType
        htargetType with ⟨sourceType, hsourceType, Htype⟩
    rcases Hrun.preservesInitialTypeName
        ⟨sourceType, by simpa using hsourceType, rfl⟩ with
      ⟨loweredType, hloweredType, hloweredName⟩
    rcases Hprod.findSourceHeader Hc (by simpa using hloweredType) with
      ⟨info, hheader, _hctors, _hall⟩
    intro htargetName
    have hsourceName : sourceType.name = name :=
      Htype.name.symm.trans (by simpa using htargetName)
    have hloweredName' : loweredType.name = name :=
      hloweredName.trans hsourceName
    rw [hloweredName'] at hheader
    rcases getNestedIfAuxCtor_refines result loweredEnv name nested auxFamily
        hrecognized with ⟨⟨ctorInfo, hconstructor, _hfamily, _hmap⟩⟩
    rw [hheader] at hconstructor
    cases hconstructor
  rw [VEnv.addConstVals_constants_of_forall_ne HsourceAdded hnames]
  exact hbase

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
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
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
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.find?
      (Lean.mkRecName sourceTypes[familyIdx].name) = none := by
  rcases H with ⟨finalState, Hrun, Hcache, Hparams⟩
  rcases Hrun.source with
    ⟨main, rest, tail, paramsState, lctx, params, hsource, Hopening,
      hinitial, hinitialAux, hinitialNext, _hprefix, Hctx, Hselection, Hqueue⟩
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
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
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
    RestoredSourceConstructorTrace result loweredEnv c.lparams c.safety canonicalEnv
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
      (H.resultParamsSize.trans H.toResult.resultNParams)
  simpa [hctorNames] using Hsemantic

/-- Native source-constructor semantics for one restored family.  The
constructor list comes from the successful header-only executable validation;
the lowering/restoration mapping supplies the exact installed translations. -/
theorem NestedLoweringResultClosed.sourceConstructorSemanticsAtFreshOfValidation
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv sourceTypesVEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Howners : ConstructorOwnersPresent c.env)
    (HsourceHeaders : List.Forall₂
      (fun source target => TrSourceConst sourceVEnv c.lparams source.name
        source.type target.toVConstVal)
      sourceTypes (loweredDecl.types.take sourceTypes.length))
    (HsourceAdded : sourceVEnv.addConstVals
      ((loweredDecl.types.take sourceTypes.length).map
        VInductiveType.toVConstVal) = some sourceTypesVEnv)
    (HvalidationValid : CheckingEnv.Valid c.safety validationEnv
      sourceTypesVEnv)
    (HparameterRun :
      Lean4Lean.validateRestoredConstructorParameters.run validationEnv
        c.lparams c.safety validationFuel sourceTypes result = .ok ())
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv) :
    ∃ constructors : List VConstVal,
      RestoredSourceConstructorTrace result loweredEnv c.lparams c.safety
        sourceTypesVEnv Hstep.oldInfo.ctors Hstep.restored.headerEnv
          Hstep.restored.constructorEnv sourceTypes[familyIdx].ctors
            constructors := by
  rcases validateRestoredConstructorParameters.sourceConsts_of_run
      HvalidationValid Hsources HparameterRun (List.getElem_mem hfamily) with
    ⟨constructors, Htranslations⟩
  have Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases H with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh hempty
  have Hconstructors : RestoreAuxConstructorsFresh result loweredEnv
      sourceTypesVEnv :=
    H.restoreAuxConstructorsFreshAtHeaderPrefix Hc Hprod Howners hempty
      HsourceHeaders HsourceAdded
  exact ⟨constructors, H.sourceConstructorSemanticsAtFresh Hc Hprod
    Hsources hfamily Htranslations Hfamilies Hconstructors hempty Hstep⟩

/-- Realize one restored primary recursor from the one irreducibly semantic
fact about it: translation of its restored concrete type in the canonical
source environment. Source translation, shared metadata materialization,
lowering, and the generated recursor certificate determine every remaining
name, universe, and telescope-cardinality premise. -/
theorem NestedLoweringResultClosed.sourcePrimaryRecursorRealizationAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors recEnv : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
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
    (Htype : TrExprS recEnv Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type targetType) :
    ∃ recursor, Nonempty (SourcePrimaryRecursorRealization sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor recEnv
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
    recursor recEnv rfl huvars rfl H.toResult.resultNParams
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
    {sourceVEnv envTypes envCtors recEnv : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
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
    (Htype : Expr.ForallTelescopeTypeTranslation recEnv
      Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type
      (result.nparams + (Hprod.recInfos.map (·.motive)).size +
        (Hprod.recInfos.flatMap (·.minors)).size +
        Hprod.recInfos[familyIdx]!.indices.size + 1)
      targetType) :
    ∃ recursor, Nonempty (SourcePrimaryRecursorRealization sourceDecl
      (sourceDecl.types[familyIdx]'hdecl) Hstep.restored.recursor recEnv
      recursor) :=
  H.sourcePrimaryRecursorRealizationAtFresh Hprod Hsource Hmetadata hempty
    familyIdx hfamily hdecl hentry Hstep targetType Htype.translation

/-- Package one original family into the payload consumed by whole-mutual
semantic-trace assembly.  Header and constructor semantics come from the
independent source translation. The source-recursion payload is explicitly
indexed by the original declaration, while the installed expanded declaration
is used only to recover production safety metadata and name preservation. -/
theorem NestedLoweringResultClosed.sourceInductiveSemanticsAtFreshExactOwner
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
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
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
    Nonempty { S : RestoredSourceInductiveSemantics sourceDecl c.lparams
        c.safety sourceVEnv envTypes envCtors Hstep //
      S.owner = sourceDecl.types[familyIdx]'hdecl } := by
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
  exact ⟨⟨{
    owner := sourceDecl.types[familyIdx]'hdecl
    header := Hsource.header
    constructors := HctorSemantics
    recursor := HrecSemantics }, rfl⟩⟩

/-- Fold exact-owner family producers over the operational restoration trace
while consuming the source declaration's `Forall₂` alignment in lockstep.
The aggregate owner list is therefore the source declaration's literal type
list, rather than an existential list later identified by a callback. -/
theorem StateForMTrace.sourceInductiveSemanticTraceExactOwners
    {decl : VInductDecl} {lparams : List Name}
    {safety : DefinitionSafety} {sourceVEnv envTypes envCtors : VEnv}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name}
    {allIndNames : List Name}
    {sourceTypes : List InductiveType}
    {sourceProdEnv targetProdEnv : Environment}
    {owners : List VInductiveType}
    (Htrace : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      sourceTypes sourceProdEnv targetProdEnv)
    (Htypes : List.Forall₂
      (TrInductiveType sourceVEnv envTypes lparams) sourceTypes owners)
    (Hsemantics : ∀ i
      (hsource : i < sourceTypes.length) (howner : i < owners.length)
      stepSource stepTarget
      (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
        sourceTypes[i] stepSource stepTarget)
      (Htype : TrInductiveType sourceVEnv envTypes lparams
        sourceTypes[i] owners[i]),
      Nonempty { S : RestoredSourceInductiveSemantics decl lparams safety
          sourceVEnv envTypes envCtors Hstep // S.owner = owners[i] }) :
    ∃ recursors,
      RestoredSourceInductiveSemanticTrace decl lparams safety sourceVEnv
        envTypes envCtors Htrace owners recursors := by
  induction Htrace generalizing owners with
  | nil =>
    cases Htypes
    exact ⟨[], .nil _⟩
  | @cons head source middle tail target Hstep Htail ih =>
    cases Htypes with
    | @cons _ owner _ tailOwners HheadTypes HtailTypes =>
      rcases Hsemantics 0 (by simp) (by simp) source middle (by
          simpa using Hstep) (by simpa using HheadTypes) with
        ⟨⟨Hhead, hheadOwner⟩⟩
      have hheadOwner' : Hhead.owner = owner := by
        simpa using hheadOwner
      rcases ih HtailTypes (fun i hsource howner stepSource stepTarget
          HtailStep HtailType => by
        have hsource' : i + 1 < (head :: tail).length := by
          simpa using hsource
        have howner' : i + 1 < (owner :: tailOwners).length := by
          simpa using howner
        rcases Hsemantics (i + 1) hsource' howner' stepSource stepTarget
            (by simpa using HtailStep) (by simpa using HtailType) with
          ⟨⟨S, hS⟩⟩
        exact ⟨⟨S, by simpa using hS⟩⟩) with
        ⟨tailRecursors, Hrest⟩
      cases hheadOwner'
      exact ⟨Hhead.recursor.recursor :: tailRecursors,
        .cons Hstep Htail Hhead.header Hhead.constructors Hhead.recursor
          Hrest⟩

/-- Preferred whole-mutual boundary for canonical restored recursor typing.
The remaining family-wise obligation is decomposed at every forall binder and
already includes typehood of every domain and the final result.  The fold is
indexed by the literal source declaration types, so downstream assembly never
chooses an existential owner list or asks for a post-hoc owner equality. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceAtFreshOfTelescopeTranslations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors recEnv : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed loweredSourceEnv fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
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
      ∃ targetType, Expr.ForallTelescopeTypeTranslation recEnv
        Hstep.restored.recursor.oldInfo.levelParams []
        Hstep.restored.recursor.restored.newInfo.type
        (result.nparams + (Hprod.recInfos.map (·.motive)).size +
          (Hprod.recInfos.flatMap (·.minors)).size +
          Hprod.recInfos[familyIdx]!.indices.size + 1)
        targetType) :
    ∃ recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes recEnv Hrestored.inductives sourceDecl.types
          recursors := by
  apply Hrestored.inductives.sourceInductiveSemanticTraceExactOwners
    Hsource.types
  intro familyIdx hfamily hdecl stepSource stepTarget Hstep Htype
  rcases H.toResult.sourceFinalMappingAtFresh hempty hfamily with
    ⟨_mappingParams, _mappingState, _mappingTarget, _mappingLowered,
      _mappingSize, _mapping, htarget⟩
  have hresult : familyIdx < result.types.length :=
    (_root_.getElem?_eq_some_iff.mp htarget).1
  have hentry : familyIdx < Hprod.entries.length := by
    rw [Hprod.generated.length, Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simpa using hresult
  rcases HtelescopeTypes familyIdx hfamily hdecl hentry stepSource stepTarget
      Hstep with ⟨targetType, Htelescope⟩
  rcases H.sourcePrimaryRecursorRealizationAtFreshOfTelescope Hprod Hsource
      Hmetadata hempty familyIdx hfamily hdecl hentry Hstep targetType
        Htelescope with
    ⟨recursor, ⟨Hrealization⟩⟩
  have Hrefinement := Hrealization.refinement
  rw [← Hrealization.recursor_eq] at Hrefinement
  exact H.sourceInductiveSemanticsAtFreshExactOwner Hc Hprod Hsources hempty
    familyIdx hfamily hdecl hentry Htype Hfamilies Hconstructors Hstep
      Hrealization.source Hrefinement

theorem NestedLoweringResult.sourceTypeName
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResult env fuel nparams types
      { initialState with newTypes := types.toArray } result)
    (hsource : source ∈ types) :
    ∃ lowered ∈ result.types, lowered.name = source.name := by
  rcases H with ⟨finalState, Hrun⟩
  apply Hrun.preservesInitialTypeName
  exact ⟨source, by simpa using hsource, rfl⟩

/-- Lift automatically derived auxiliary-constructor freshness through the
source mutual-header environment used to translate original constructors.
An auxiliary constructor cannot share a name with a source header: lowering
preserves every source header in the installed block, where the two names
would otherwise resolve to incompatible kernel metadata. -/
theorem NestedLoweringResultClosed.restoreAuxConstructorsFreshAtTypes
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : CompletedRecursorPhasesResult R.completed loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxConstructorsFresh result loweredEnv envTypes := by
  intro name nested auxFamily hrecognized
  have Hbase := H.restoreAuxConstructorsFreshAtBase Hc Hprod Howners hempty
  have hbase : sourceVEnv.constants name = none :=
    Hbase name nested auxFamily hrecognized
  have hnames : ∀ ci ∈ sourceDecl.typeConstants, ci.name ≠ name := by
    intro ci hci
    simp only [VInductDecl.typeConstants] at hci
    rcases List.mem_map.mp hci with ⟨targetType, htargetType, rfl⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r Hsource.types targetType
        htargetType with ⟨sourceType, hsourceType, Htype⟩
    rcases H.toResult.sourceTypeName hsourceType with
      ⟨loweredType, hloweredType, hloweredName⟩
    rcases Hprod.findSourceHeader Hc (by simpa using hloweredType) with
      ⟨info, hheader, _hctors, _hall⟩
    intro htargetName
    have hsourceName : sourceType.name = name :=
      Htype.header.name.symm.trans (by simpa using htargetName)
    have hloweredName' : loweredType.name = name :=
      hloweredName.trans hsourceName
    rw [hloweredName'] at hheader
    rcases getNestedIfAuxCtor_refines result loweredEnv name nested auxFamily
        hrecognized with ⟨⟨ctorInfo, hconstructor, _hfamily, _hmap⟩⟩
    rw [hheader] at hconstructor
    cases hconstructor
  rw [VEnv.addConstVals_constants_of_forall_ne Hsource.typesAdded hnames]
  exact hbase

/-- Specialize `restorationSources` from the installed lowered family list
back to each original source family, using the lowering trace for name
preservation and target constructor telescopes. -/
theorem CompletedRecursorPhasesResult.restorationSourcesOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : CompletedRecursorPhasesResult R.completed outEnv)
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
theorem CompletedRecursorPhasesResult.auxRestorationSourcesOfLowering
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {res : Lean4Lean.ElimNestedInductive.Result}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv res.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (Hc : ContextWF c) (H : CompletedRecursorPhasesResult R.completed outEnv)
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
      hinitial, _hinitialAux, _hinitialNext, _hprefix, _Hctx, _Hselection, Hqueue⟩
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
    (Hc : ContextWF c) (H : CompletedRecursorPhasesResult R.completed loweredEnv)
    (Hlower : NestedLoweringResult sourceProdEnv loweringFuel nparams
      sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res)
    (hsourceWF : sourceProdEnv.constants.WF)
    (lparams : List Name) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (Validated : Environment → Prop)
    (Hvalidate : ∀ restoredEnv validationEnv auxiliaryHeaderEnv,
      Nonempty (RestoredNestedDeclarationsResult res loweredEnv sourceProdEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        (sourceTypes.map (·.name)) sourceTypes
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
        ((), restoredEnv)) →
      Nonempty (RestoredConstructorValidationEnvironment res loweredEnv
        sourceProdEnv (sourceTypes.map (·.name)) allowPrimitive sourceTypes
        validationEnv) →
      Nonempty (RestoredHeaderValidationEnvironment loweredEnv sourceProdEnv
        (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv) →
      Lean4Lean.validateRestoredConstructorParameters.run auxiliaryHeaderEnv
        lparams safety fuel sourceTypes res = .ok () →
      Lean4Lean.validateRestoredRecursorTypes.run validationEnv loweredEnv
        lparams safety fuel res
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok () →
      Lean4Lean.validateRestoredRecursorRules.run
        (Lean4Lean.stripRecursorRules restoredEnv
          (Lean4Lean.restoredRecursorNames
            (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 sourceTypes
            (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1))
        loweredEnv lparams safety fuel res
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1 = .ok () →
      (Lean4Lean.validateNestedAuxiliaries auxiliaryHeaderEnv lparams safety
        fuel res).WF fun _ => Validated restoredEnv) :
    (Environment.restoreNestedAfterInstall sourceProdEnv loweredEnv lparams
      sourceTypes safety allowPrimitive fuel res).WF fun outEnv =>
        RestoredAfterInstallResult res sourceProdEnv loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          lparams safety allowPrimitive fuel
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
  · exact hsourceWF
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
    (Hc : ContextWF c) (H : CompletedRecursorPhasesResult R.completed loweredEnv)
    (Hlower : NestedLoweringResultClosed sourceProdEnv loweringFuel nparams
      sourceTypes
      { initialState with newTypes := sourceTypes.toArray } res)
    (hsourceWF : sourceProdEnv.constants.WF)
    (lparams : List Name) (safety : DefinitionSafety)
    (allowPrimitive : Bool) (fuel : FuelConfig)
    (venv : VEnv)
    (hvalid : ∀ auxiliaryHeaderEnv,
      Nonempty (RestoredHeaderValidationEnvironment loweredEnv sourceProdEnv
        (sourceTypes.map (·.name)) sourceTypes auxiliaryHeaderEnv) →
      CheckingEnv.Valid safety auxiliaryHeaderEnv venv)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv) :
    (Environment.restoreNestedAfterInstall sourceProdEnv loweredEnv lparams
      sourceTypes safety allowPrimitive fuel res).WF fun outEnv =>
        RestoredAfterInstallResult res sourceProdEnv loweredEnv
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) sourceTypes
          lparams safety allowPrimitive fuel
          (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).1
          (fun _ =>
            ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res ∧
            ∃ selection : LocalForallSelection res.lctx res.params,
              ClosedNestedAuxiliaryTranslations venv lparams res selection)
          outEnv := by
  apply Environment.restoreNestedAfterInstall.ofLoweringWF Hc H
    Hlower.toResult hsourceWF lparams safety allowPrimitive fuel
    (fun _ =>
      ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res ∧
      ∃ selection : LocalForallSelection res.lctx res.params,
        ClosedNestedAuxiliaryTranslations venv lparams res selection)
  intro _restoredEnv _validationEnv auxiliaryHeaderEnv _Hrestoration
    _Hvalidation HheaderValidation _Hparameters _HrecursorTypes
    _HrecursorRules
  have Hvalid := hvalid auxiliaryHeaderEnv HheaderValidation
  refine (Hlower.validateNestedAuxiliariesWF Hvalid mlctx hmlctx hlctx
    hfresh).mono fun _ Hvalidated => ⟨Hvalidated, ?_⟩
  rcases Hlower with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  exact Hrun.validatedAuxiliaryResidualTranslations Hvalid.tr.wf
    mlctx hmlctx hlctx Hvalidated

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

/-- Outer composition that discharges dynamic auxiliary-family closedness and
the final cache scoping invariant from the source checks and the verified
production environment. -/
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


end VerifyInductive
end Lean4Lean
