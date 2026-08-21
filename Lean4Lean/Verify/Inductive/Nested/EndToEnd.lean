import Lean4Lean.Verify.Inductive.Nested.LoweringTrace

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
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv := by
  rcases H with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  exact Hrun.restoreAuxConstructorsFreshOfInstallation
    Hprod.staged.combined Hc.checking.tr.map_wf Howners hempty

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
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
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

/-- Preferred whole-mutual nested source-semantics boundary after executable
installation.  Both generated-family namespace reservation and auxiliary
constructor freshness are consequences of lowering and the staged lowered
block; callers provide only the persistent source-environment owner invariant
and the still-semantic restored recursor telescope translations. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceOfInstalledTelescopes
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
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsources : SourceSyntaxChecks sourceTypes)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Howners : ConstructorOwnersPresent c.env)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result loweredEnv c.env
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
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
  have Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true := by
    rcases H with ⟨finalState, Hrun, _Hcache, _Hparams⟩
    exact Hrun.resultFamilyNamesReservedFresh hempty
  have Hconstructors :
      RestoreAuxConstructorsFresh result loweredEnv envTypes :=
    H.restoreAuxConstructorsFreshAtTypes Hc Hprod Hsource Howners hempty
  exact H.sourceSemanticTraceAtFreshOfTelescopeTranslations Hc Hprod Hsources
    Hsource Hmetadata Hfamilies Hconstructors hempty Hrestored HtelescopeTypes

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


end VerifyInductive
end Lean4Lean
