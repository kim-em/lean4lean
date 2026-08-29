import Lean4Lean.Verify.Inductive.Nested.LoweringInstallation
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterValidationRun
import Lean4Lean.Verify.Inductive.Nested.FamilyRealization
import Lean4Lean.Verify.Inductive.Nested.OriginalHeaderSeedRebase
import Lean4Lean.Verify.Inductive.Recursor.FirstPass
import Lean4Lean.Verify.Inductive.Specification.Formation

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

/-- Provenance for an arbitrary member of the expanded lowering result.  The
existential final state is retained so generated-family cache evidence can be
fed directly to the final restoration map. -/
theorem NestedLoweringResult.finalFamilyOriginAt
    (H : NestedLoweringResult env fuel nparams types initialState result)
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitial : initialState.newTypes = types.toArray)
    (hj : j < result.types.length) :
    ∃ finalState,
      NestedLoweringRun env fuel nparams types initialState
        (result, finalState) ∧
      Nonempty (FinalLoweredFamilyOrigin env result.params nparams
        initialState.newTypes finalState result.types[j]) := by
  rcases H with ⟨finalState, Hrun⟩
  exact ⟨finalState, Hrun,
    Hrun.finalFamilyOriginAt Henv hclosures Hsources hinitial hj⟩

theorem NestedLoweringResultClosed.finalFamilyOriginAt
    (H : NestedLoweringResultClosed env fuel nparams types initialState result)
    (Henv : EnvironmentTypesClosed env)
    (hclosures : MutualInductivesClosed env)
    (Hsources : SourceSyntaxChecks types)
    (hinitial : initialState.newTypes = types.toArray)
    (hj : j < result.types.length) :
    ∃ finalState,
      NestedLoweringRun env fuel nparams types initialState
        (result, finalState) ∧
      Nonempty (FinalLoweredFamilyOrigin env result.params nparams
        initialState.newTypes finalState result.types[j]) :=
  H.toResult.finalFamilyOriginAt Henv hclosures Hsources hinitial hj

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

/-- Reinterpret a validated auxiliary witness in the universe context used
by generated recursors.  Small elimination leaves the certificate unchanged;
large elimination prepends the fresh universe parameter and structurally
re-inverts the same closed concrete telescope after shifting its abstract
target.  Re-inversion is deliberate: it avoids assuming that a particular
choice of validation domains is preserved definitionally by universe
substitution. -/
theorem ClosedNestedAuxiliaryTranslation.toRecursorContext
    {c : AddInductive.Context}
    (H : ClosedNestedAuxiliaryTranslation venv c.lparams res selection e)
    (henv : venv.WF)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    Nonempty (ClosedNestedAuxiliaryTranslation venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      res selection e) := by
  cases elimLevel with
  | zero => exact ⟨by simpa [AddInductive.getRecLevelParams] using H⟩
  | param fresh =>
    let shift := VLevel.prependShift c.lparams.length
    have hshift : ∀ level ∈ shift,
        level.WF (fresh :: c.lparams).length := by
      simpa [shift] using
        VLevel.prependShift_wf (n := c.lparams.length)
    have Hclosed : TrExprS venv (fresh :: c.lparams) []
        (res.lctx.mkForall res.params e) (H.closedTarget.instL shift) := by
      simpa [VLCtx.instL, shift] using H.closed.prependLevelParam
        henv (by trivial) Helim
    have HclosedType : venv.IsType (fresh :: c.lparams).length []
        (H.closedTarget.instL shift) := H.closedType.instL hshift
    have Htel := selection.forallTelescope e
    rcases TrExprS.forallTelescope_typed_shape_with_context henv Htel Hclosed
        HclosedType with
      ⟨domains, residualTarget, harity, htarget, Hresidual,
        HresidualType⟩
    exact ⟨⟨H.closedTarget.instL shift, domains, residualTarget, harity,
      Hclosed, HclosedType, htarget, Hresidual, HresidualType⟩⟩
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

/-- Pointwise universe rebasing of all validated nested auxiliaries. -/
theorem ClosedNestedAuxiliaryTranslations.toRecursorContext
    {c : AddInductive.Context}
    (H : ClosedNestedAuxiliaryTranslations venv c.lparams res selection)
    (henv : venv.WF)
    (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    ClosedNestedAuxiliaryTranslations venv
      (AddInductive.getRecLevelParams elimLevel c.lparams)
      res selection := by
  intro name e hfind
  rcases H name e hfind with ⟨Haux⟩
  exact Haux.toRecursorContext henv Helim

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
    Expr.AbstractTypeTranslation venv lparams
      (abstractForallContext parameterDomains [])
      (e.abstractList selection.fvars) := by
  have Hvlctx := abstractForallContext.isDefEq Hcontexts
  rcases H.residual.defeqDFC henv (Hvlctx.symm henv.ordered) with
    ⟨target, Hresidual⟩
  refine ⟨target, Hresidual, ?_⟩
  have HctxSymm := Hvlctx.symm henv.ordered
  have HresidualType := H.residualType.defeqDFC henv.ordered
    HctxSymm.defeqCtx
  have HtargetEq := H.residual.uniq henv HctxSymm Hresidual
  have HtargetEq' := HtargetEq.defeqDFC henv.ordered HctxSymm.defeqCtx
  exact VEnv.IsType.defeqU_l henv Hvlctx.wf.toCtx HtargetEq'
    HresidualType

/-- A successfully validated auxiliary witness is already a restored family
with no remaining indices: its cached source-family prefix itself has a sort
as type.  The separate end-to-end header-alignment theorem is responsible for
showing that production assigned the corresponding generated family zero
indices; this constructor packages the resulting source-facing semantics. -/
theorem ClosedNestedAuxiliaryTranslation.toRestoredFamilySemanticsZero
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e)
    (henv : venv.WF) (parameterDomains : List VExpr)
    (Hcontexts : VEnv.IsDefEqCtx venv lparams.length []
      parameterDomains.reverse H.domains.reverse) :
    Nonempty (RestoredFamilySemantics venv lparams parameterDomains 0) := by
  rcases H.residualType with ⟨resultLevel, Htyping⟩
  have HtypingBase : venv.HasType lparams.length H.domains.reverse
      H.residualTarget (.sort resultLevel) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Htyping
  have Htyping' := HtypingBase.defeqDFC henv.ordered
    (Hcontexts.symm henv.ordered)
  refine ⟨{
    family := H.residualTarget
    indexDomains := []
    familyResult := .sort resultLevel
    indexCount := rfl
    familyTyping := by simpa [VExpr.wrapForalls] using Htyping'
    familyApplicationType := by
      exact ⟨resultLevel, by simpa [VExpr.mkApps] using Htyping'⟩
  }⟩

/-- Rebase a validated auxiliary residual onto any independently translated
copy of the same concrete parameter telescope.  Validation obtains its
`domains` by inverting a closed witness, while restored recursors obtain their
parameter domains from the source-header telescope.  Those lists need not be
syntactically equal: translation may choose definitionally equal dependent
domains.  The common concrete `mkForall` prefix induces the context conversion
consumed by `residualAtDefEqParameterDomains`. -/
theorem ClosedNestedAuxiliaryTranslation.residualAtParameterDomains
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e)
    (henv : venv.WF) (hselectionNodup : selection.fvars.Nodup)
    (dummy : Expr) (parameterDomains : List VExpr) (dummyTarget : VExpr)
    (hparameterDomains : parameterDomains.length = res.params.size)
    (Hdummy : TrExprS venv lparams []
      (res.lctx.mkForall res.params dummy)
      (VExpr.wrapForalls parameterDomains dummyTarget)) :
    Expr.AbstractTypeTranslation venv lparams
      (abstractForallContext parameterDomains [])
      (e.abstractList selection.fvars) := by
  have Hsame := selection.sameForallPrefix hselectionNodup dummy e
  have Hclosed : TrExprS venv lparams []
      (res.lctx.mkForall res.params e)
      (VExpr.wrapForalls H.domains H.residualTarget) := by
    rw [← H.target]
    exact H.closed
  have Hcontexts : VEnv.IsDefEqCtx venv lparams.length []
      parameterDomains.reverse H.domains.reverse := by
    have Hconverted := Hsame.translatedContextsExact henv
      (.refl henv (by trivial)) Hdummy Hclosed
      hparameterDomains H.arity
    simpa [VLCtx.toCtx] using Hconverted
  exact H.residualAtDefEqParameterDomains henv parameterDomains Hcontexts

/-- Weakening of `residualAtDefEqParameterDomains` below an already
translated recursor suffix. -/
theorem
    ClosedNestedAuxiliaryTranslation.residualAtDefEqParameterDomainsUnder
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e)
    (henv : venv.WF) (hselectionNodup : selection.fvars.Nodup)
    (parameterDomains suffixDomains : List VExpr)
    (Hcontexts : VEnv.IsDefEqCtx venv lparams.length []
      parameterDomains.reverse H.domains.reverse) :
    Expr.AbstractTypeTranslation venv lparams
      (abstractForallContext (parameterDomains ++ suffixDomains) [])
      (e.abstractList selection.fvars suffixDomains.length) := by
  rcases H.residualAtDefEqParameterDomains henv parameterDomains Hcontexts
      with ⟨target, Hresidual, HresidualType⟩
  have Hweak := Hresidual.weakBV henv.ordered
    (abstractForallContext.bvLift suffixDomains
      (abstractForallContext parameterDomains []))
  rw [← Expr.abstractList_add_eq_liftLooseBVars H.sourceClosed
    hselectionNodup] at Hweak
  have HweakType := HresidualType.weakN henv.ordered
    (abstractForallContext.bvLift suffixDomains
      (abstractForallContext parameterDomains [])).toCtx
  refine ⟨target.liftN suffixDomains.length 0, ?_, ?_⟩
  · simpa only [abstractForallContext_append, Nat.zero_add] using Hweak
  · simpa only [abstractForallContext_append] using HweakType

/-- Depth-general canonical-parameter form of
`residualAtParameterDomains`.  This is the form consumed by restored
recursor domains: `suffixDomains` are precisely the motive/minor/index/major
binders already opened after the common source parameters. -/
theorem ClosedNestedAuxiliaryTranslation.residualAtParameterDomainsUnder
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e)
    (henv : venv.WF) (hselectionNodup : selection.fvars.Nodup)
    (dummy : Expr) (parameterDomains suffixDomains : List VExpr)
    (dummyTarget : VExpr)
    (hparameterDomains : parameterDomains.length = res.params.size)
    (Hdummy : TrExprS venv lparams []
      (res.lctx.mkForall res.params dummy)
      (VExpr.wrapForalls parameterDomains dummyTarget)) :
    Expr.AbstractTypeTranslation venv lparams
      (abstractForallContext (parameterDomains ++ suffixDomains) [])
      (e.abstractList selection.fvars suffixDomains.length) := by
  rcases H.residualAtParameterDomains henv hselectionNodup dummy
      parameterDomains dummyTarget hparameterDomains Hdummy with
    ⟨target, Hresidual, HresidualType⟩
  have Hweak := Hresidual.weakBV henv.ordered
    (abstractForallContext.bvLift suffixDomains
      (abstractForallContext parameterDomains []))
  rw [← Expr.abstractList_add_eq_liftLooseBVars H.sourceClosed
    hselectionNodup] at Hweak
  have HweakType := HresidualType.weakN henv.ordered
    (abstractForallContext.bvLift suffixDomains
      (abstractForallContext parameterDomains [])).toCtx
  refine ⟨target.liftN suffixDomains.length 0, ?_, ?_⟩
  · simpa only [abstractForallContext_append, Nat.zero_add] using Hweak
  · simpa only [abstractForallContext_append] using HweakType

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

/-- Semantic-context form of the exact-family interpreter.  The caller may
identify the canonical source parameter context with validation's dependent
domains by definitional equality, without manufacturing a second concrete
dummy telescope solely to compare their translations. -/
theorem
    NestedRestorationOpening.exactFamilyHitAbstractTypeTranslationAtDefEqPrefix
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation venv lparams result selection e)
    (henv : venv.WF)
    (parameterDomains : List VExpr)
    (Hcontexts : VEnv.IsDefEqCtx venv lparams.length []
      parameterDomains.reverse Haux.domains.reverse)
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
      (abstractForallContext (parameterDomains ++ suffixDomains) [])
      (restored.abstractList Hopen.selection.fvars suffixDomains.length) := by
  have Hexact := restoreNestedNode_family_exactParams result prodEnv
    Hopen.params auxRec t e family levels hhead hrec hfind hargs
  have hrestored : restored =
      (e.abstract result.params).instantiateRev Hopen.params :=
    Option.some.inj (Hhit.symm.trans Hexact)
  subst restored
  rw [Hopen.auxiliaryAlphaAt Hlower selection Haux family hfind
    suffixDomains.length]
  exact Haux.residualAtDefEqParameterDomainsUnder henv
    (Hlower.selectionNodup selection) parameterDomains suffixDomains Hcontexts

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

/-- Canonical-parameter specialization of the lookup-driven family-hit
interpreter.  Unlike `exactFamilyHitOfTranslationsAtPrefix`, this theorem
does not expose the validation-derived parameter domains existentially: it
rebases the selected auxiliary witness onto the independently translated
source parameter telescope used by the restored recursor fold. -/
theorem
    NestedRestorationOpening.exactFamilyHitOfTranslationsAtCanonicalPrefix
    (Hopen : NestedRestorationOpening result prodEnv auxRec input output)
    (Hlower : NestedLoweringResultClosed env fuel nparams types initialState
      result)
    (selection : LocalForallSelection result.lctx result.params)
    (Htranslations : ClosedNestedAuxiliaryTranslations venv lparams result
      selection)
    (henv : venv.WF)
    (dummy : Expr) (parameterDomains : List VExpr) (dummyTarget : VExpr)
    (hparameterDomains : parameterDomains.length = result.params.size)
    (Hdummy : TrExprS venv lparams []
      (result.lctx.mkForall result.params dummy)
      (VExpr.wrapForalls parameterDomains dummyTarget))
    (family : Name) (levels : List Level) (e : Expr)
    (hfind : result.aux2nested.find? family = some e)
    (hrec : auxRec.find? family = none)
    (t restored : Expr)
    (hhead : t.getAppFn = .const family levels)
    (hargs : t.getAppArgs.size = result.nparams)
    (Hhit : result.restoreNestedNode prodEnv Hopen.params auxRec t =
      some restored)
    (suffixDomains : List VExpr) :
    Expr.AbstractTypeTranslation venv lparams
      (abstractForallContext (parameterDomains ++ suffixDomains) [])
      (restored.abstractList Hopen.selection.fvars suffixDomains.length) := by
  rcases Htranslations family e hfind with ⟨Haux⟩
  have Hexact := restoreNestedNode_family_exactParams result prodEnv
    Hopen.params auxRec t e family levels hhead hrec hfind hargs
  have hrestored : restored =
      (e.abstract result.params).instantiateRev Hopen.params :=
    Option.some.inj (Hhit.symm.trans Hexact)
  subst restored
  rw [Hopen.auxiliaryAlphaAt Hlower selection Haux family hfind
    suffixDomains.length]
  exact Haux.residualAtParameterDomainsUnder henv
    (Hlower.selectionNodup selection) dummy parameterDomains suffixDomains
    dummyTarget hparameterDomains Hdummy

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

/-- Semantic family telescope for an original (non-generated) member of a
lowered mutual block.  The family constant is rebuilt in the independently
checked source-constructor environment, rather than transported from the
lowered constructor environment: the latter also contains generated nested
constructors and therefore need not be comparable by environment inclusion.

The common parameter context comes from the materialized source-header
cache.  The family-local parameter and index domains come from the lowered
header's `TypeShape`; uniqueness of translation of the unchanged original
header transfers that shape to the independently materialized source family.
-/
theorem NestedLoweringResultClosed.originalFamilyRestoredRealizationAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    let Us := AddInductive.getRecLevelParams Hprod.elimLevel c.lparams
    let parameterDomains :=
      (Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
        Hprod.elimLevelAdmissible).parameterDecls.toCtx.reverse
    let sourceFamily := Expr.mkAppList
      (.const sourceTypes[familyIdx].name stats.levels)
      (sourceCanonicalVars parameterDomains.length)
    ∃ sourceIndexType, Nonempty (RestoredIndexedFamilyRealization envCtors
      Us parameterDomains Hprod.recInfos[familyIdx]!.indices.size
      sourceFamily sourceIndexType) := by
  dsimp only
  have hresult : familyIdx < result.types.length :=
    Nat.lt_of_lt_of_le hfamily H.toResult.sourceTypes_length_le
  have hloweredDecl : familyIdx < loweredDecl.types.length := by
    rw [<- Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    exact hresult
  have hsourceDecl : familyIdx < sourceDecl.types.length := by
    rw [<- Lean4Lean.VerifyInductive.TrInductDeclCore.types_length Hsource]
    exact hfamily
  have hrecInfo : familyIdx < Hprod.recInfos.size := by
    rw [Hprod.cardinality.records]
    exact hloweredDecl
  let sourceTarget := sourceDecl.types[familyIdx]
  let loweredTarget := loweredDecl.types[familyIdx]
  have HsourceType := Lean4Lean.VerifyInductive.TrInductDeclCore.typeAt
    Hsource familyIdx hfamily hsourceDecl
  rcases H.sourceHeaderTranslationAtFresh hempty R.core familyIdx hfamily with
    ⟨_hdecl, HloweredHeader⟩
  have hsourceWF : sourceVEnv.WF := by
    rw [<- Hheaders.sourceContextVEnv]
    exact Hheaders.sourceContext.checking.tr.wf
  have hsourceLE : sourceVEnv ≤ envCtors :=
    (VEnv.addConstVals_le Hsource.typesAdded).trans
      (VEnv.addConstVals_le Hsource.ctorsAdded)
  have henvCtors : envCtors.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF Hsource hsourceWF
  have HtargetEq : sourceVEnv.IsDefEqU c.lparams.length []
      sourceTarget.type loweredTarget.type := by
    exact HsourceType.header.type.uniq hsourceWF
      (.refl hsourceWF (by trivial)) (by
        simpa [sourceTarget, loweredTarget] using HloweredHeader.type)
  rcases Hheaders.sourceMaterialized.normalizedShapes familyIdx hloweredDecl with
    ⟨sourceTelescope, familyResult, exprType, Hnormalized, Hresult⟩
  let ownParams := sourceTelescope.ownParams
  let indices := sourceTelescope.indices
  have HnormalizedBase : sourceVEnv.IsDefEq c.lparams.length []
      loweredTarget.type
        (VExpr.wrapForalls (ownParams ++ indices) familyResult) exprType := by
    simpa only [Hheaders.sourceContextVEnv, loweredTarget, ownParams, indices]
      using Hnormalized
  have HresultBase : sourceVEnv.IsDefEq c.lparams.length
      (indices.reverse ++ ownParams.reverse) familyResult
      (.sort loweredTarget.resultLevel)
      (.sort (.succ loweredTarget.resultLevel)) := by
    simpa only [Hheaders.sourceContextVEnv, loweredTarget, ownParams, indices]
      using Hresult
  have Hparams : VEnv.IsDefEqCtx sourceVEnv c.lparams.length []
      Hheaders.sourceMaterialized.headers.params.reverse ownParams.reverse := by
    simpa only [Hheaders.sourceContextVEnv, ownParams] using
      sourceTelescope.parameters
  have HsourceNormalized : sourceVEnv.IsDefEq c.lparams.length []
      sourceTarget.type
        (VExpr.wrapForalls (ownParams ++ indices) familyResult) exprType := by
    have Hnormalized' := VEnv.IsDefEq.transU_r hsourceWF (by trivial)
      HtargetEq HnormalizedBase
    exact Hnormalized'
  have hsourceTargetUvars : sourceTarget.uvars = c.lparams.length := by
    simpa [sourceTarget] using HsourceType.header.uvars
  have hindexCount : indices.length =
      Hprod.recInfos[familyIdx]!.indices.size := by
    have hsourceIndices : sourceTarget.numIndices =
        loweredTarget.numIndices := by
      exact Hmetadata.numIndices
        (by
          calc
            sourceDecl.types.length = sourceTypes.length :=
              (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
                Hsource).symm
            _ ≤ result.types.length := H.toResult.sourceTypes_length_le
            _ = loweredDecl.types.length :=
              Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core)
        familyIdx hsourceDecl hloweredDecl
    calc
      indices.length = loweredTarget.numIndices := by
        simpa only [indices] using sourceTelescope.indexCount
      _ = sourceTarget.numIndices := hsourceIndices.symm
      _ = Hprod.recInfos[familyIdx]!.indices.size := by
        rw [hsourceIndices]
        exact (Hprod.cardinality.indices familyIdx hrecInfo).symm
  have HloweredCoreAtSourceContext : TrInductDeclCore
      Hheaders.sourceContext.venv c.lparams nparams result.types.toArray.toList
      isUnsafe loweredDecl Hheaders.context.venv R.declared.venvCtors := by
    simpa only [Hheaders.sourceContextVEnv] using R.core
  have hsourceContextLE : Hheaders.sourceContext.venv ≤ envCtors := by
    simpa only [Hheaders.sourceContextVEnv] using hsourceLE
  rcases sourceTelescope.closedIndexSuffixRebasedCanonical
      HloweredCoreAtSourceContext Hheaders.sourceContext.checking.tr.wf
      hsourceContextLE (VEnv.LEExcept.rfl envCtors
        (fun name => name ∈ loweredDecl.sourceNames)) with
    ⟨_headerSource, _headerTarget, replayParameterDomains, indexSource,
      _indexTarget, replayIndexDomains, _oldResidual, _hreplayParameters,
      _HparameterSource, _hheaderTarget, _HindexSource,
      hreplayIndexCount, _hindexTarget, HindexReplay, HsourceReplay⟩
  have hreplayArity : loweredDecl.types[familyIdx].numIndices =
      Hprod.recInfos[familyIdx]!.indices.size := by
    calc
      loweredDecl.types[familyIdx].numIndices = indices.length := by
        simpa [indices] using sourceTelescope.indexCount.symm
      _ = Hprod.recInfos[familyIdx]!.indices.size := hindexCount
  rw [hreplayArity] at HindexReplay hreplayIndexCount
  have hsourceTargetMem : sourceTarget.toVConstVal ∈
      sourceDecl.typeConstants := by
    exact List.mem_map_of_mem (List.getElem_mem hsourceDecl)
  have hlookupTypes : envTypes.constants sourceTarget.name =
      some sourceTarget.toVConstant := by
    exact VEnv.addConstVals_get Hsource.typesAdded hsourceTargetMem
  have hlookupCtors : envCtors.constants sourceTarget.name =
      some sourceTarget.toVConstant :=
    (VEnv.addConstVals_le Hsource.ctorsAdded).constants hlookupTypes
  have build : ∀ (elimLevel : Level)
      (Helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel),
      ∃ sourceIndexType, Nonempty (RestoredIndexedFamilyRealization envCtors
        (AddInductive.getRecLevelParams elimLevel c.lparams)
        (Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
          Helim).parameterDecls.toCtx.reverse
        Hprod.recInfos[familyIdx]!.indices.size
        (Expr.mkAppList
          (.const sourceTypes[familyIdx].name stats.levels)
          (sourceCanonicalVars
            (Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
              Helim).parameterDecls.toCtx.reverse.length)) sourceIndexType) := by
    intro elimLevel Helim
    cases elimLevel with
    | zero =>
      change ∃ sourceIndexType, Nonempty (RestoredIndexedFamilyRealization
        envCtors c.lparams
        Hheaders.sourceMaterialized.parameterScope.toCtx.reverse
        Hprod.recInfos[familyIdx]!.indices.size
        (Expr.mkAppList
          (.const sourceTypes[familyIdx].name stats.levels)
          (sourceCanonicalVars
            Hheaders.sourceMaterialized.parameterScope.toCtx.reverse.length))
        sourceIndexType)
      let parameterDomains :=
        Hheaders.sourceMaterialized.parameterScope.toCtx.reverse
      let levels := VLevel.params c.lparams.length
      have hlevelsWF : ∀ level ∈ levels,
          level.WF c.lparams.length := by
        simpa [levels] using VLevel.params_wf
      have hlevelsLength : levels.length = sourceTarget.uvars := by
        simp [levels, hsourceTargetUvars]
      have htargetInst : sourceTarget.type.instL levels = sourceTarget.type := by
        change sourceTarget.type.instL (VLevel.params c.lparams.length) = _
        rw [<- hsourceTargetUvars]
        have htyped := Classical.choose_spec HsourceType.header.wf
        exact (htyped.levelWF (by trivial)).1.instL_id
      have HconstBase := VEnv.HasType.const (env := envCtors)
        (U := c.lparams.length) (Γ := []) hlookupCtors hlevelsWF hlevelsLength
      have Hconst : envCtors.HasType c.lparams.length []
          (.const sourceTarget.name levels)
          (VExpr.wrapForalls (ownParams ++ indices) familyResult) := by
        have HsourceNormalized' := HsourceNormalized.mono hsourceLE
        have HconstBase' : envCtors.HasType c.lparams.length []
            (.const sourceTarget.name levels) sourceTarget.type := by
          simpa [htargetInst] using HconstBase
        exact HconstBase'.defeqU_r henvCtors (by trivial)
          ⟨exprType, HsourceNormalized'⟩
      have Hfamily := VEnv.HasType.mkApps_wrapForalls_prefix_canonical
        henvCtors.ordered Hconst
      have HownCommon : VEnv.IsDefEqCtx envCtors c.lparams.length []
          ownParams.reverse
          Hheaders.sourceMaterialized.headers.params.reverse := by
        have Hparams' : VEnv.IsDefEqCtx sourceVEnv c.lparams.length []
            Hheaders.sourceMaterialized.headers.params.reverse
            ownParams.reverse := by
          simpa [VInductDecl.ParamsDefEq, R.core.uvars] using Hparams
        exact (Hparams'.symm hsourceWF.ordered).mono hsourceLE
      have HcommonCached : VEnv.IsDefEqCtx envCtors c.lparams.length []
          Hheaders.sourceMaterialized.headers.params.reverse
          Hheaders.sourceMaterialized.parameterScope.toCtx := by
        have Hcached₀ := Hheaders.sourceMaterialized.paramsContext
        have Hcached : VEnv.IsDefEqCtx sourceVEnv c.lparams.length []
            Hheaders.sourceMaterialized.headers.params.reverse
            Hheaders.sourceMaterialized.parameterScope.toCtx := by
          simpa only [Hheaders.sourceContextVEnv] using Hcached₀
        exact Hcached.mono hsourceLE
      have HownCached := VEnv.IsDefEqCtx.transEmpty henvCtors HownCommon
        HcommonCached
      have Hfamily₀ : envCtors.HasType c.lparams.length ownParams.reverse
          (VExpr.mkApps
            ((VExpr.const sourceTarget.name levels).liftN ownParams.length 0)
            (recursorCanonicalVars ownParams.length))
          (VExpr.wrapForalls indices familyResult) := by
        simpa [recursorCanonicalVars] using Hfamily
      have Hfamily' := Hfamily₀.defeqDFC henvCtors.ordered HownCached
      have Happlication₀ := VEnv.HasType.mkApps_wrapForalls_canonical
        henvCtors.ordered Hfamily₀
      have Hresult₀ : envCtors.IsDefEq c.lparams.length
          (indices.reverse ++ ownParams.reverse) familyResult
          (.sort loweredTarget.resultLevel)
          (.sort (.succ loweredTarget.resultLevel)) := by
        simpa [R.core.uvars] using HresultBase.mono hsourceLE
      have HfamilyType := Hfamily₀.isType henvCtors.ordered
        HownCached.isType
      have HfullCtx :=
        (VEnv.IsType.wrapForalls_inv henvCtors.ordered HownCached.isType
          HfamilyType).1
      have HapplicationType₀ : envCtors.IsType c.lparams.length
          (indices.reverse ++ ownParams.reverse)
          (VExpr.mkApps
            ((VExpr.mkApps
              ((VExpr.const sourceTarget.name levels).liftN ownParams.length 0)
              (recursorCanonicalVars ownParams.length)).liftN
                indices.length 0)
            (recursorCanonicalVars indices.length)) :=
        ⟨loweredTarget.resultLevel,
          Happlication₀.defeqU_r henvCtors HfullCtx
            ⟨.sort (.succ loweredTarget.resultLevel), Hresult₀⟩⟩
      have HapplicationType := HapplicationType₀.imp fun _ Htype =>
        Htype.defeqDFC' henvCtors.ordered HownCached
      have hparameterLength : parameterDomains.length = ownParams.length := by
        simpa [parameterDomains] using HownCached.length_eq.symm
      have HsourceLevels :
          stats.levels.mapM
              (VLevel.ofLevel c.lparams) = some levels := by
        have Hlevels := Hheaders.sourceMaterialized.recursorLevelTranslation
          Hprod.lparamsNodup Helim
        simpa [Hheaders.sourceMaterialized.levelParams,
          AddInductive.getRecLevelParams, recursorDeclarationAbstractLevels,
          levels] using Hlevels
      have HsourceHead : TrExprS envCtors c.lparams
          (abstractForallContext parameterDomains [])
          (.const sourceTypes[familyIdx].name stats.levels)
          (.const sourceTarget.name levels) := by
        have hname : sourceTypes[familyIdx].name = sourceTarget.name := by
          simpa [sourceTarget] using HsourceType.header.name.symm
        rw [hname]
        exact TrExprS.const hlookupCtors HsourceLevels (by
          simpa [sourceTarget, Hheaders.sourceMaterialized.levelParams] using
            hsourceTargetUvars.symm)
      have HsourceArgs : List.Forall₂
          (TrExprS envCtors c.lparams
          (abstractForallContext parameterDomains []))
          (sourceCanonicalVars parameterDomains.length)
          (recursorCanonicalVars ownParams.length) := by
        rw [← hparameterLength]
        rw [recursorCanonicalVars_eq_ofFn]
        exact TrExprS.canonicalBvars_of_abstractForallContext
          parameterDomains [] parameterDomains.length (by omega)
      have HsourceApplication := checkPositivityStep.TrExprS.mkAppList
        henvCtors.ordered
        (by
          simpa [parameterDomains, abstractForallContext_toCtx, VLCtx.toCtx]
            using (HownCached.symm henvCtors.ordered).isType)
        HsourceHead HsourceArgs (by
          refine ⟨VExpr.wrapForalls indices familyResult, ?_⟩
          change envCtors.HasType _ _ _ _
          simpa [hparameterLength, parameterDomains, VExpr.liftN,
            abstractForallContext_toCtx, VLCtx.toCtx] using Hfamily')
      let F : RestoredFamilyRealization envCtors c.lparams parameterDomains
          Hprod.recInfos[familyIdx]!.indices.size
          (Expr.mkAppList
            (.const sourceTypes[familyIdx].name stats.levels)
            (sourceCanonicalVars parameterDomains.length)) := {
        semantics := {
          family := VExpr.mkApps
            ((VExpr.const sourceTarget.name levels).liftN ownParams.length 0)
            (recursorCanonicalVars ownParams.length)
          indexDomains := indices
          familyResult := familyResult
          indexCount := hindexCount
          familyTyping := by simpa [parameterDomains] using Hfamily'
          familyApplicationType := by
            rcases HapplicationType with
              ⟨applicationLevel, HapplicationType⟩
            refine ⟨applicationLevel, ?_⟩
            change envCtors.IsDefEq _ _ _ _ _
            simpa [parameterDomains] using HapplicationType }
        sourceTranslation := by
          simpa [parameterDomains, VExpr.liftN] using HsourceApplication
      }
      have hparameterDomains : OnCtx parameterDomains.reverse
          (envCtors.IsType c.lparams.length) := by
        simpa [parameterDomains] using
          (HownCached.symm henvCtors.ordered).isType
      refine ⟨indexSource, ?_⟩
      apply F.toIndexedOfCanonicalReplay henvCtors hparameterDomains
        HindexReplay hreplayIndexCount
      · simpa [F, ownParams, indices] using HsourceReplay
      · simpa [F, parameterDomains, ownParams] using HownCached
    | param fresh =>
      let shift := VLevel.prependShift c.lparams.length
      change ∃ sourceIndexType, Nonempty (RestoredIndexedFamilyRealization
        envCtors (fresh :: c.lparams)
        (Hheaders.sourceMaterialized.parameterScope.instL shift).toCtx.reverse
        Hprod.recInfos[familyIdx]!.indices.size
        (Expr.mkAppList
          (.const sourceTypes[familyIdx].name stats.levels)
          (sourceCanonicalVars
            (Hheaders.sourceMaterialized.parameterScope.instL shift).toCtx.reverse.length))
        sourceIndexType)
      let parameterDomains :=
        (Hheaders.sourceMaterialized.parameterScope.instL shift).toCtx.reverse
      let ownParams' := ownParams.map (VExpr.instL shift)
      let indices' := indices.map (VExpr.instL shift)
      let familyResult' := familyResult.instL shift
      have hshift : ∀ level ∈ shift,
          level.WF (fresh :: c.lparams).length := by
        simpa [shift] using
          VLevel.prependShift_wf (n := c.lparams.length)
      have hshiftLength : shift.length = sourceTarget.uvars := by
        simp [shift, hsourceTargetUvars]
      have HconstBase := VEnv.HasType.const (env := envCtors)
        (U := (fresh :: c.lparams).length) (Γ := []) hlookupCtors hshift
        hshiftLength
      have HsourceNormalized' := HsourceNormalized.instL hshift |>.mono hsourceLE
      have Hconst : envCtors.HasType (fresh :: c.lparams).length []
          (.const sourceTarget.name shift)
          (VExpr.wrapForalls (ownParams' ++ indices') familyResult') := by
        have HsourceNormalizedU : envCtors.IsDefEqU
            (fresh :: c.lparams).length [] (sourceTarget.type.instL shift)
            (VExpr.wrapForalls (ownParams' ++ indices') familyResult') := by
          refine ⟨exprType.instL shift, ?_⟩
          simpa [ownParams', indices', familyResult',
            VExpr.instL_wrapForalls] using HsourceNormalized'
        exact HconstBase.defeqU_r henvCtors (by trivial)
          HsourceNormalizedU
      have Hfamily := VEnv.HasType.mkApps_wrapForalls_prefix_canonical
        henvCtors.ordered Hconst
      have Hparams' :=
        Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.instL hshift Hparams
      have HownCommon : VEnv.IsDefEqCtx envCtors
          (fresh :: c.lparams).length [] ownParams'.reverse
          (Hheaders.sourceMaterialized.headers.params.map
            (VExpr.instL shift)).reverse := by
        have Hparams'' := Hparams'.symm hsourceWF.ordered |>.mono hsourceLE
        simpa only [VInductDecl.ParamsDefEq, R.core.uvars, ownParams',
          List.map_reverse, List.map_nil] using Hparams''
      have Hcached₀ := Hheaders.sourceMaterialized.paramsContext
      have Hcached : VEnv.IsDefEqCtx sourceVEnv c.lparams.length []
          Hheaders.sourceMaterialized.headers.params.reverse
          Hheaders.sourceMaterialized.parameterScope.toCtx := by
        simpa only [Hheaders.sourceContextVEnv] using Hcached₀
      have Hcached' :=
        Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.instL hshift Hcached
      have HcommonCached : VEnv.IsDefEqCtx envCtors
          (fresh :: c.lparams).length []
          (Hheaders.sourceMaterialized.headers.params.map
            (VExpr.instL shift)).reverse
          (Hheaders.sourceMaterialized.parameterScope.instL shift).toCtx := by
        have Hcached'' := Hcached'.mono hsourceLE
        simpa only [VLCtx.instL_toCtx, List.map_reverse, List.map_nil,
          shift] using Hcached''
      have HownCached := VEnv.IsDefEqCtx.transEmpty henvCtors HownCommon
        HcommonCached
      have Hfamily₀ : envCtors.HasType (fresh :: c.lparams).length
          ownParams'.reverse
          (VExpr.mkApps
            ((VExpr.const sourceTarget.name shift).liftN ownParams'.length 0)
            (recursorCanonicalVars ownParams'.length))
          (VExpr.wrapForalls indices' familyResult') := by
        simpa [recursorCanonicalVars] using Hfamily
      have Hfamily' := Hfamily₀.defeqDFC henvCtors.ordered HownCached
      have Happlication₀ := VEnv.HasType.mkApps_wrapForalls_canonical
        henvCtors.ordered Hfamily₀
      have Hresult₀ : envCtors.IsDefEq (fresh :: c.lparams).length
          (indices'.reverse ++ ownParams'.reverse) familyResult'
          (.sort (loweredTarget.resultLevel.inst shift))
          (.sort (.succ (loweredTarget.resultLevel.inst shift))) := by
        have Hresult' := HresultBase.instL hshift |>.mono hsourceLE
        simpa [R.core.uvars, ownParams', indices', familyResult',
          VExpr.instL, VLevel.inst] using
          Hresult'
      have HfamilyType := Hfamily₀.isType henvCtors.ordered
        HownCached.isType
      have HfullCtx :=
        (VEnv.IsType.wrapForalls_inv henvCtors.ordered HownCached.isType
          HfamilyType).1
      have HapplicationType₀ : envCtors.IsType
          (fresh :: c.lparams).length
          (indices'.reverse ++ ownParams'.reverse)
          (VExpr.mkApps
            ((VExpr.mkApps
              ((VExpr.const sourceTarget.name shift).liftN
                ownParams'.length 0)
              (recursorCanonicalVars ownParams'.length)).liftN
                indices'.length 0)
            (recursorCanonicalVars indices'.length)) :=
        ⟨loweredTarget.resultLevel.inst shift,
          Happlication₀.defeqU_r henvCtors HfullCtx
            ⟨.sort (.succ (loweredTarget.resultLevel.inst shift)), Hresult₀⟩⟩
      have HapplicationType := HapplicationType₀.imp fun _ Htype =>
        Htype.defeqDFC' henvCtors.ordered HownCached
      have hparameterLength : parameterDomains.length = ownParams'.length := by
        simpa [parameterDomains] using HownCached.length_eq.symm
      have HsourceLevels :
          stats.levels.mapM
              (VLevel.ofLevel (fresh :: c.lparams)) = some shift := by
        have Hlevels := Hheaders.sourceMaterialized.recursorLevelTranslation
          Hprod.lparamsNodup Helim
        have Hlevels' :
            stats.levels.mapM
                (VLevel.ofLevel (fresh :: c.lparams)) =
              some ((VLevel.params c.lparams.length).map
                (VLevel.inst shift)) := by
          simpa [Hheaders.sourceMaterialized.levelParams,
            AddInductive.getRecLevelParams,
            recursorDeclarationAbstractLevels, shift] using Hlevels
        rw [VLevel.inst_map_id (by simp [shift])] at Hlevels'
        simpa [
          AddInductive.getRecLevelParams, recursorDeclarationAbstractLevels,
          shift, VLevel.prependShift] using Hlevels'
      have HsourceHead : TrExprS envCtors (fresh :: c.lparams)
          (abstractForallContext parameterDomains [])
          (.const sourceTypes[familyIdx].name stats.levels)
          (.const sourceTarget.name shift) := by
        have hname : sourceTypes[familyIdx].name = sourceTarget.name := by
          simpa [sourceTarget] using HsourceType.header.name.symm
        rw [hname]
        exact TrExprS.const hlookupCtors HsourceLevels (by
          simpa [sourceTarget, Hheaders.sourceMaterialized.levelParams] using
            hsourceTargetUvars.symm)
      have HsourceArgs : List.Forall₂
          (TrExprS envCtors (fresh :: c.lparams)
          (abstractForallContext parameterDomains []))
          (sourceCanonicalVars parameterDomains.length)
          (recursorCanonicalVars ownParams'.length) := by
        rw [← hparameterLength]
        rw [recursorCanonicalVars_eq_ofFn]
        exact TrExprS.canonicalBvars_of_abstractForallContext
          parameterDomains [] parameterDomains.length (by omega)
      have HsourceApplication := checkPositivityStep.TrExprS.mkAppList
        henvCtors.ordered
        (by
          simpa [parameterDomains, abstractForallContext_toCtx, VLCtx.toCtx]
            using (HownCached.symm henvCtors.ordered).isType)
        HsourceHead HsourceArgs (by
          refine ⟨VExpr.wrapForalls indices' familyResult', ?_⟩
          change envCtors.HasType _ _ _ _
          simpa [hparameterLength, parameterDomains, VExpr.liftN,
            abstractForallContext_toCtx, VLCtx.toCtx] using Hfamily')
      let F : RestoredFamilyRealization envCtors (fresh :: c.lparams)
          parameterDomains Hprod.recInfos[familyIdx]!.indices.size
          (Expr.mkAppList
            (.const sourceTypes[familyIdx].name stats.levels)
            (sourceCanonicalVars parameterDomains.length)) := {
        semantics := {
          family := VExpr.mkApps
            ((VExpr.const sourceTarget.name shift).liftN ownParams'.length 0)
            (recursorCanonicalVars ownParams'.length)
          indexDomains := indices'
          familyResult := familyResult'
          indexCount := by simpa [indices'] using hindexCount
          familyTyping := by simpa [parameterDomains] using Hfamily'
          familyApplicationType := by
            rcases HapplicationType with
              ⟨applicationLevel, HapplicationType⟩
            refine ⟨applicationLevel, ?_⟩
            change envCtors.IsDefEq _ _ _ _ _
            simpa [parameterDomains] using HapplicationType }
        sourceTranslation := by
          simpa [parameterDomains, VExpr.liftN] using HsourceApplication
      }
      have hfresh : fresh ∉ c.lparams := by
        simpa [AddInductive.AdmissibleElimLevel, Level.isParam] using Helim
      have HreplayParameters : VEnv.IsDefEqCtx envCtors c.lparams.length []
          ownParams.reverse replayParameterDomains.reverse := by
        apply VEnv.IsDefEqCtx.dropPrefixes HsourceReplay
        simpa only [List.length_reverse] using
          sourceTelescope.indexCount.trans
            (hreplayArity.trans hreplayIndexCount.symm)
      have HreplayScopeWF :
          (abstractForallContext replayParameterDomains []).WF envCtors
            c.lparams.length :=
        abstractForallContext_wf_of_onCtx
          (HreplayParameters.symm henvCtors.ordered).isType
      have HindexReplayFresh := HindexReplay.prependLevelParam
        henvCtors HreplayScopeWF hfresh
      have HsourceReplayFresh :=
        Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.instL hshift HsourceReplay
      let replayParameterDomains' :=
        replayParameterDomains.map (VExpr.instL shift)
      let replayIndexDomains' := replayIndexDomains.map (VExpr.instL shift)
      have HindexReplayFresh' : Expr.ForallTelescopeTypeTranslation envCtors
          (fresh :: c.lparams)
          (abstractForallContext replayParameterDomains' []) indexSource
          Hprod.recInfos[familyIdx]!.indices.size
          (VExpr.wrapForalls replayIndexDomains'
            (.sort (.zero : VLevel))) := by
        simpa [shift, replayParameterDomains', replayIndexDomains',
          VLCtx.instL, VExpr.instL_wrapForalls, VExpr.instL, VLevel.inst] using
          HindexReplayFresh
      have HsourceReplayFresh' : VEnv.IsDefEqCtx envCtors
          (fresh :: c.lparams).length []
          (indices'.reverse ++ ownParams'.reverse)
          (replayIndexDomains'.reverse ++
            replayParameterDomains'.reverse) := by
        simpa [indices', ownParams', replayIndexDomains',
          replayParameterDomains', List.map_reverse] using HsourceReplayFresh
      have hreplayIndexCount' : replayIndexDomains'.length =
          Hprod.recInfos[familyIdx]!.indices.size := by
        simpa [replayIndexDomains'] using hreplayIndexCount
      have hparameterDomains : OnCtx parameterDomains.reverse
          (envCtors.IsType (fresh :: c.lparams).length) := by
        simpa [parameterDomains] using
          (HownCached.symm henvCtors.ordered).isType
      refine ⟨indexSource, ?_⟩
      apply F.toIndexedOfCanonicalReplay henvCtors hparameterDomains
        HindexReplayFresh' hreplayIndexCount'
      · simpa [F, indices', ownParams'] using HsourceReplayFresh'
      · simpa [F, parameterDomains, ownParams'] using HownCached
    | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
      simp [AddInductive.AdmissibleElimLevel] at Helim
  exact build Hprod.elimLevel Hprod.elimLevelAdmissible

/-- Environment-only projection retained for consumers that do not need the
concrete source family application.  The stronger theorem above is the native
replay input used by restored recursor suffix assembly. -/
theorem NestedLoweringResultClosed.originalFamilyRestoredSemanticsAtFresh
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length) :
    let Us := AddInductive.getRecLevelParams Hprod.elimLevel c.lparams
    let parameterDomains :=
      (Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
        Hprod.elimLevelAdmissible).parameterDecls.toCtx.reverse
    Nonempty (RestoredFamilySemantics envCtors Us parameterDomains
      Hprod.recInfos[familyIdx]!.indices.size) := by
  rcases H.originalFamilyRestoredRealizationAtFresh Hprod Hsource Hmetadata
      hempty familyIdx hfamily with ⟨_sourceIndexType, ⟨F⟩⟩
  exact ⟨F.family.semantics⟩

/-- The canonical production parameter suffix and every validated auxiliary
parameter telescope describe the same dependent context.  The proof crosses
the executable passes only through the unchanged raw source header: lowering
supplies exact syntax on one side, while `MaterializedHeaderResult` supplies
the independent semantic normalization on the other. -/
theorem NestedLoweringResultClosed.auxiliaryCanonicalParameterContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    (H : NestedLoweringResultClosed c.env fuel nparams sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (hempty : initialState.nestedAux = #[])
    (selection : LocalForallSelection result.lctx result.params)
    (Haux : ClosedNestedAuxiliaryTranslation envCtors
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams)
      result selection e) :
    let parameterDomains :=
      (Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
        Hprod.elimLevelAdmissible).parameterDecls.toCtx.reverse
    VEnv.IsDefEqCtx envCtors
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams).length []
      parameterDomains.reverse Haux.domains.reverse := by
  dsimp only
  have HsourceClosed : ∀ source ∈ sourceTypes,
      source.type.FVarsIn fun _ => False := by
    intro source hsource
    rcases Lean4Lean.List.Forall₂.forall_exists_l Hsource.types source
        hsource with ⟨target, _htarget, Htarget⟩
    exact Htarget.header.type.fvarsIn.mono fun fv hfv => by
      simpa [VLCtx.fvars] using hfv
  rcases H.sourceParameterPrefix HsourceClosed e with
    ⟨first, rest, residual, hsourceTypes, Htelescope, Hsame⟩
  subst sourceTypes
  have hfamily : 0 < (first :: rest).length := by simp
  rcases H.sourceHeaderTranslationAtFresh hempty R.core 0 hfamily with
    ⟨hdecl, Hheader⟩
  have Hheader' : TrSourceConst Hheaders.sourceContext.venv c.lparams
      first.name first.type (loweredDecl.types[0]'hdecl).toVConstVal := by
    rw [Hheaders.sourceContextVEnv]
    simpa using Hheader
  have Htelescope' : Expr.ForallTelescope first.type loweredDecl.nparams
      residual := by
    rw [R.core.nparams]
    exact Htelescope
  rcases Hheaders.sourceMaterialized.sourceParameterDomainsAt first
      loweredDecl.types[0] Hheader' (List.getElem_mem hdecl)
      Hprod.elimLevelAdmissible Htelescope' with
    ⟨sourceDomains, sourceResidual, hsourceDomains,
      HsourceTranslation, HsourceContext⟩
  rw [Hheaders.sourceContextVEnv] at HsourceTranslation HsourceContext
  have hsourceLE : sourceVEnv ≤ envCtors :=
    (VEnv.addConstVals_le Hsource.typesAdded).trans
      (VEnv.addConstVals_le Hsource.ctorsAdded)
  have hsourceWF : sourceVEnv.WF := by
    have hwf := Hheaders.sourceContext.checking.tr.wf
    rw [Hheaders.sourceContextVEnv] at hwf
    exact hwf
  have henv : envCtors.WF :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.envCtorsWF Hsource hsourceWF
  have HsourceTranslation' : TrExprS envCtors
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams) []
      first.type (VExpr.wrapForalls sourceDomains sourceResidual) :=
    HsourceTranslation.mono hsourceLE
  have HauxClosed : TrExprS envCtors
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams) []
      (result.lctx.mkForall result.params e)
      (VExpr.wrapForalls Haux.domains Haux.residualTarget) := by
    rw [← Haux.target]
    exact Haux.closed
  have HauxSource : VEnv.IsDefEqCtx envCtors
      (AddInductive.getRecLevelParams Hprod.elimLevel c.lparams).length []
      Haux.domains.reverse sourceDomains.reverse := by
    have hauxDomains : Haux.domains.length = nparams :=
      Haux.arity.trans (H.resultParamsSize.trans H.toResult.resultNParams)
    have Hcontexts := Hsame.translatedContextsExact henv
      (.refl henv (by trivial)) HauxClosed HsourceTranslation'
      hauxDomains (by simpa [R.core.nparams] using hsourceDomains)
    simpa [VLCtx.toCtx] using Hcontexts
  have HsourceContext' := HsourceContext.mono hsourceLE
  have HparameterSource := HsourceContext'.symm henv.ordered
  have HsourceAux := HauxSource.symm henv.ordered
  have HparameterAux := VEnv.IsDefEqCtx.transEmpty henv
    HparameterSource HsourceAux
  simpa using HparameterAux

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

/-- Lift generated-constructor freshness through the source-header prefix
reconstructed directly from lowering.  Unlike the legacy source-core route,
this needs neither source constructors nor a completed source declaration. -/
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
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
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

/-- Every key selected by the production auxiliary-recursor map is one of
the recursors generated for the complete dynamically lowered family list.
This connects `mkAuxRecNameMap`'s metadata suffix to the independently
verified recursor batch without assuming a naming convention for that suffix. -/
theorem NestedLoweringResultClosed.auxRecKeyGeneratedAtFresh
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
    (hmap : (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.find? old =
      some new) :
    old ∈ (Hprod.entries.map Prod.snd).map (·.name) := by
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
  have hkey := mkAuxRecNameMap_recMap_find_mem main rest loweredEnv mainInfo
    hmainFind' hmap
  rcases mkAuxRecNameMap_recNames_mem main rest loweredEnv mainInfo hmainFind'
      hkey with ⟨familyName, hfamilyInfo, holdName⟩
  rw [hall] at hfamilyInfo
  rcases List.mem_map.mp hfamilyInfo with
    ⟨family, hfamily, hfamilyName⟩
  rcases List.mem_iff_getElem.mp hfamily with
    ⟨familyIdx, hfamilyIdx, hfamilyEq⟩
  have hrecords : Hprod.recInfos.size = result.types.toArray.size := by
    rw [Hprod.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core]
    simp
  have hgenerated := Hprod.generated.recursorName_mem hrecords familyIdx
    (by simpa using hfamilyIdx)
  have hget : result.types.toArray[familyIdx]! =
      result.types.toArray.toList[familyIdx] := by
    rw [Array.getElem!_eq_getD,
      ← Array.getElem_eq_getD (h := by simpa using hfamilyIdx) default]
    exact (Array.getElem_toList hfamilyIdx).symm
  have hname : old = Lean.mkRecName result.types.toArray[familyIdx]!.name := by
    rw [holdName, ← hfamilyName, ← hfamilyEq, ← hget]
  rwa [hname]

/-- Consequently every auxiliary-recursion key is fresh in the abstract
constructor environment in which generated recursor domains were built. -/
theorem NestedLoweringResultClosed.auxRecKeyFreshAtCtors
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
    (hmap : (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2.find? old =
      some new) :
    R.declared.venvCtors.constants old = none := by
  apply Hprod.recursorNamesFresh [] (by simp) old
  change old ∈ (Hprod.entries.map Prod.snd).map (·.name)
  exact H.auxRecKeyGeneratedAtFresh Hc Hprod hempty hmap

/-- Every retained generated-recursors declaration type avoids the entire
fresh recursor-name set.  The proof uses its semantic translation in the
pre-recursors constructor environment, so it applies uniformly to motive,
minor, index, and major declarations. -/
theorem RecursorPhasesResult.declarationTypeAvoidsGeneratedRecursors
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
    (D : BoundFVarDeclarationAt H.localContext xs i) :
    D.type.AvoidsConsts ((H.entries.map Prod.snd).map (·.name)) := by
  rcases H.recursorWF.translatedDeclarationType D with ⟨target, Htype⟩
  apply checkPositivityStep.TrExprS.sourceAvoidsFresh _ Htype
  intro name hname
  rw [H.recursorEnv, R.declared.contextVEnv]
  apply H.recursorNamesFresh [] (by simp) name
  change name ∈ (H.entries.map Prod.snd).map (·.name)
  exact hname

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
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R loweredEnv)
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

/-- Compatibility projection of the exact-owner source-family producer. -/
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
  rcases H.sourceInductiveSemanticsAtFreshExactOwner Hc Hprod Hsources hempty
      familyIdx hfamily hdecl hentry Hsource Hfamilies Hconstructors Hstep
        HsourceRec Hrefine with ⟨⟨S, _howner⟩⟩
  exact ⟨S⟩

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

/-- Assemble source semantics with the aggregate owner list fixed to the
literal independently specified declaration.  The indexed fold consumes the
source core's `Forall₂` proof and the exact owner retained by each producer;
no post-hoc owner-list equality is required. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceAtFreshExactOwners
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
    ∃ recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes envCtors Hrestored.inductives sourceDecl.types
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
  rcases HsourceRecursors familyIdx hfamily hdecl hentry with
    ⟨HsourceRec⟩
  rcases H.sourceInductiveSemanticsAtFreshExactOwner Hc Hprod Hsources hempty
      familyIdx hfamily hdecl hentry Htype Hfamilies Hconstructors Hstep
      HsourceRec
      (HrecursorRefinements familyIdx hfamily hdecl hentry stepSource
        stepTarget Hstep HsourceRec) with ⟨⟨S, howner⟩⟩
  exact ⟨⟨S, by simpa using howner⟩⟩

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
already includes typehood of every domain and the final result.  The fold is
indexed by the literal source declaration types, so downstream assembly never
chooses an existential owner list or asks for a post-hoc owner equality. -/
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
    ∃ recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes envCtors Hrestored.inductives sourceDecl.types
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

/-- Reclose any aligned generated recursor after independently transporting
its restored suffix into the source constructor environment.  This
owner-generic core is shared by primary and auxiliary restoration: ordinary
header production supplies the unchanged parameter telescope, and the suffix
invariant supplies every later binder and the residual. -/
theorem RecursorPhasesResult.restoredTelescopeOfSuffix
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv envTypes envCtors : VEnv}
    {headerEnv ctorEnv loweredEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe depth
      sourceVEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      sourceIsUnsafe sourceDecl envTypes envCtors)
    (ownerIdx : Nat) (hentry : ownerIdx < Hprod.entries.length)
    (A : GeneratedRecursorRestorationTelescopeAlignment result loweredEnv
      auxRec newInfo (Hprod.generated.entry ownerIdx hentry))
    (hresultNparams : result.nparams = nparams)
    (Hsemantics : GeneratedRecursorRestoredSuffixTranslationsInvariant A
      Hprod.origins envCtors []
      ((Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
        Hprod.elimLevelAdmissible).parameterDecls.toCtx.reverse)) :
    ∃ targetType, Expr.ForallTelescopeTypeTranslation envCtors
      (Hprod.generated.entry ownerIdx hentry).info.levelParams [] newInfo.type
      (result.nparams + (Hprod.recInfos.map (fun info => info.motive)).size +
        (Hprod.recInfos.flatMap (fun info => info.minors)).size +
        Hprod.recInfos[ownerIdx]!.indices.size + 1)
      targetType := by
  let E := Hprod.generated.entry ownerIdx hentry
  let Us := AddInductive.getRecLevelParams Hprod.elimLevel c.lparams
  let sourceSuffix :=
    Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
      Hprod.elimLevelAdmissible
  let parameterDomains := sourceSuffix.parameterDecls.toCtx.reverse
  let template :=
    (c.lctx.mkForall stats.params
      (.sort (.zero : Level))).inferImplicit 1000 false
  have hsourceLE : sourceVEnv <= envCtors :=
    (VEnv.addConstVals_le Hsource.typesAdded).trans
      (VEnv.addConstVals_le Hsource.ctorsAdded)
  have HtemplateData :
      Expr.ForallTelescope template stats.params.size
          (.sort (.zero : Level)) ∧
        Lean.Expr.SameForallDomains stats.params.size template E.info.type ∧
        TrExprS envCtors Us [] template
            (VExpr.wrapForalls parameterDomains
              (.sort (.zero : VLevel))) ∧
        envCtors.IsType Us.length []
          (VExpr.wrapForalls parameterDomains
            (.sort (.zero : VLevel))) := by
    simpa [E, Us, sourceSuffix, parameterDomains, template] using
      Hprod.sourceRecursorParameterTemplateAt ownerIdx hentry hsourceLE
  rcases HtemplateData with
    ⟨HtemplateTelescope, HtemplatePrefix, Htemplate, HtemplateType⟩
  have hparams : result.nparams = stats.params.size :=
    hresultNparams.trans <|
      R.core.nparams.symm.trans Hprod.cardinality.params.symm
  have hparameterDomains : parameterDomains.length = result.nparams := by
    calc
      parameterDomains.length = sourceSuffix.parameterDecls.toCtx.length := by
        simp [parameterDomains]
      _ = sourceSuffix.parameterDecls.length :=
        checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
          sourceSuffix.cached
      _ = stats.params.size := sourceSuffix.parameterDecls_length
      _ = result.nparams := hparams.symm
  have HtemplateTelescope' : Expr.ForallTelescope template result.nparams
      (.sort (.zero : Level)) := by
    simpa [template, hparams] using HtemplateTelescope
  have HtemplatePrefix' : Lean.Expr.SameForallDomains result.nparams template
      E.info.type := by
    simpa [template, E, hparams] using HtemplatePrefix
  have hlevels : E.info.levelParams = Us := by
    rw [E.levels, Hprod.localExtends.lparams_eq]
  have Htemplate' : TrExprS envCtors E.info.levelParams [] template
      (VExpr.wrapForalls parameterDomains (.sort (.zero : VLevel))) := by
    rw [hlevels]
    simpa [template, parameterDomains, sourceSuffix] using Htemplate
  have HtemplateType' : envCtors.IsType E.info.levelParams.length []
      (VExpr.wrapForalls parameterDomains (.sort (.zero : VLevel))) := by
    rw [hlevels]
    simpa [parameterDomains, sourceSuffix] using HtemplateType
  have hsourceOrdered : sourceVEnv.Ordered := by
    rw [← Hheaders.sourceContextVEnv]
    exact Hheaders.sourceContext.checking.tr.wf.ordered
  have htypesOrdered : envTypes.Ordered := by
    apply hsourceOrdered.addConstVals _ Hsource.typesAdded
    intro ci hci
    simp only [VInductDecl.typeConstants] at hci
    rcases List.mem_map.mp hci with ⟨target, htarget, rfl⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r Hsource.types target htarget
      with ⟨source, _hsource, Htarget⟩
    exact Htarget.header.wf
  have hctorsOrdered : envCtors.Ordered := by
    apply htypesOrdered.addConstVals _ Hsource.ctorsAdded
    intro ci hci
    simp only [VInductDecl.constructorConstants] at hci
    rcases List.mem_flatMap.mp hci with ⟨target, htarget, hctor⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r Hsource.types target htarget
      with ⟨source, _hsource, Htarget⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget.ctors ci hctor with
      ⟨sourceCtor, _hsourceCtor, Hctor⟩
    exact Hctor.wf
  have HparameterContext : OnCtx
      (abstractForallContext parameterDomains []).toCtx
      (envCtors.IsType E.info.levelParams.length) := by
    have Hopened := VEnv.IsType.wrapForalls_inv hctorsOrdered (by trivial)
      HtemplateType'
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Hopened.1
  have hrecInfo : ownerIdx < Hprod.recInfos.size := by
    simpa [Hprod.generated.length] using hentry
  have HsuffixSemantics :
      GeneratedRecursorRestoredSuffixTranslationsInvariant A Hprod.origins
        envCtors [] parameterDomains := by
    simpa [parameterDomains, sourceSuffix] using Hsemantics
  rcases A.transportSuffixOfInvariantSemantics envCtors [] parameterDomains
      HparameterContext Hprod.localWF Hprod.bindings Hprod.origins hrecInfo
      HsuffixSemantics with ⟨suffixTarget, Hsuffix⟩
  refine ⟨VExpr.wrapForalls parameterDomains suffixTarget, ?_⟩
  have Hclosed := A.closeTransportedSuffix hctorsOrdered HtemplatePrefix'
    HtemplateTelescope' Htemplate' hparameterDomains Hsuffix
  simpa [E, Nat.add_assoc] using Hclosed

/-- Assemble the complete canonical type of one restored primary recursor
from independently translated source parameters and a stateful source-facing
semantic invariant for its restored motive/minor/index/major suffix. -/
theorem NestedLoweringResultClosed.restoredPrimaryTelescopeAtFreshOfSuffix
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
    (Hprod : RecursorPhasesResult R loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams sourceTypes
      isUnsafe sourceDecl envTypes envCtors)
    (familyIdx : Nat) (hfamily : familyIdx < sourceTypes.length)
    (hentry : familyIdx < Hprod.entries.length)
    (Hstep : RestoredInductiveStep result loweredEnv
      (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
      sourceTypes[familyIdx] stepSource stepTarget)
    (hempty : initialState.nestedAux = #[])
    (Hsemantics : forall A :
      GeneratedRecursorRestorationTelescopeAlignment result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        Hstep.restored.recursor.restored.newInfo
        (Hprod.generated.entry familyIdx hentry),
      GeneratedRecursorRestoredSuffixTranslationsInvariant A Hprod.origins
        envCtors []
        ((Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
          Hprod.elimLevelAdmissible).parameterDecls.toCtx.reverse)) :
    exists targetType, Expr.ForallTelescopeTypeTranslation envCtors
      Hstep.restored.recursor.oldInfo.levelParams []
      Hstep.restored.recursor.restored.newInfo.type
      (result.nparams + (Hprod.recInfos.map (fun info => info.motive)).size +
        (Hprod.recInfos.flatMap (fun info => info.minors)).size +
        Hprod.recInfos[familyIdx]!.indices.size + 1)
      targetType := by
  have hresultNparams : result.nparams = nparams := H.toResult.resultNParams
  have hresultParams : result.params.size = result.nparams :=
    H.resultParamsSize
  have holdRecName : Lean.mkRecName sourceTypes[familyIdx].name =
      Lean.mkRecName result.types.toArray[familyIdx]!.name := by
    rcases H.sourceFinalMappingAtFreshAligned (initialState := initialState)
        hempty hfamily with
      ⟨_fvars, _stepState, target, _loweredState, _hparams, _hnodup,
        _hsize, Hmapping, htarget⟩
    obtain ⟨hresult, htargetEq⟩ := _root_.getElem?_eq_some_iff.mp htarget
    have harray : result.types.toArray[familyIdx]! = target := by
      simp [Array.getElem!_eq_getD, Array.getD, hresult, htargetEq]
    rw [harray, Hmapping.name]
  have holdRecName' : Lean.mkRecName sourceTypes[familyIdx].name =
      Lean.mkRecName result.types.toArray[familyIdx]!.name := holdRecName
  rcases Hprod.restoredPrimaryTelescopeAlignment familyIdx hentry
      Hstep.restored.recursor holdRecName' hresultNparams hresultParams with
    ⟨A⟩
  let E := Hprod.generated.entry familyIdx hentry
  let Us := AddInductive.getRecLevelParams Hprod.elimLevel c.lparams
  let sourceSuffix :=
    Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
      Hprod.elimLevelAdmissible
  let parameterDomains := sourceSuffix.parameterDecls.toCtx.reverse
  let template :=
    (c.lctx.mkForall stats.params
      (.sort (.zero : Level))).inferImplicit 1000 false
  have hsourceLE : sourceVEnv <= envCtors :=
    (VEnv.addConstVals_le Hsource.typesAdded).trans
      (VEnv.addConstVals_le Hsource.ctorsAdded)
  have HtemplateData :
      Expr.ForallTelescope template stats.params.size
          (.sort (.zero : Level)) ∧
        Lean.Expr.SameForallDomains stats.params.size template E.info.type ∧
        TrExprS envCtors Us [] template
            (VExpr.wrapForalls parameterDomains
              (.sort (.zero : VLevel))) ∧
        envCtors.IsType Us.length []
          (VExpr.wrapForalls parameterDomains
            (.sort (.zero : VLevel))) := by
    simpa [E, Us, sourceSuffix, parameterDomains, template] using
      Hprod.sourceRecursorParameterTemplateAt familyIdx hentry hsourceLE
  rcases HtemplateData with
    ⟨HtemplateTelescope, HtemplatePrefix, Htemplate, HtemplateType⟩
  have hparams : result.nparams = stats.params.size :=
    hresultNparams.trans <|
      R.core.nparams.symm.trans Hprod.cardinality.params.symm
  have hparameterDomains : parameterDomains.length = result.nparams := by
    calc
      parameterDomains.length = sourceSuffix.parameterDecls.toCtx.length := by
        simp [parameterDomains]
      _ = sourceSuffix.parameterDecls.length :=
        checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
          sourceSuffix.cached
      _ = stats.params.size := sourceSuffix.parameterDecls_length
      _ = result.nparams := hparams.symm
  have HtemplateTelescope' : Expr.ForallTelescope template result.nparams
      (.sort (.zero : Level)) := by
    simpa [template, hparams] using HtemplateTelescope
  have HtemplatePrefix' : Lean.Expr.SameForallDomains result.nparams template
      E.info.type := by
    simpa [template, E, hparams] using HtemplatePrefix
  have hlevels : E.info.levelParams = Us := by
    rw [E.levels, Hprod.localExtends.lparams_eq]
  have Htemplate' : TrExprS envCtors E.info.levelParams [] template
      (VExpr.wrapForalls parameterDomains (.sort (.zero : VLevel))) := by
    rw [hlevels]
    simpa [template, parameterDomains, sourceSuffix] using Htemplate
  have HtemplateType' : envCtors.IsType E.info.levelParams.length []
      (VExpr.wrapForalls parameterDomains (.sort (.zero : VLevel))) := by
    rw [hlevels]
    simpa [parameterDomains, sourceSuffix] using HtemplateType
  have hsourceOrdered : sourceVEnv.Ordered := by
    rw [← Hheaders.sourceContextVEnv]
    exact Hheaders.sourceContext.checking.tr.wf.ordered
  have htypesOrdered : envTypes.Ordered := by
    apply hsourceOrdered.addConstVals _ Hsource.typesAdded
    intro ci hci
    simp only [VInductDecl.typeConstants] at hci
    rcases List.mem_map.mp hci with ⟨target, htarget, rfl⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r Hsource.types target htarget
      with ⟨source, _hsource, Htarget⟩
    exact Htarget.header.wf
  have hctorsOrdered : envCtors.Ordered := by
    apply htypesOrdered.addConstVals _ Hsource.ctorsAdded
    intro ci hci
    simp only [VInductDecl.constructorConstants] at hci
    rcases List.mem_flatMap.mp hci with ⟨target, htarget, hctor⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r Hsource.types target htarget
      with ⟨source, _hsource, Htarget⟩
    rcases Lean4Lean.List.Forall₂.forall_exists_r Htarget.ctors ci hctor with
      ⟨sourceCtor, _hsourceCtor, Hctor⟩
    exact Hctor.wf
  have HparameterContext : OnCtx
      (abstractForallContext parameterDomains []).toCtx
      (envCtors.IsType E.info.levelParams.length) := by
    have Hopened := VEnv.IsType.wrapForalls_inv hctorsOrdered (by trivial)
      HtemplateType'
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Hopened.1
  have hrecInfo : familyIdx < Hprod.recInfos.size := by
    simpa [Hprod.generated.length] using hentry
  have HsuffixSemantics :
      GeneratedRecursorRestoredSuffixTranslationsInvariant A Hprod.origins
        envCtors [] parameterDomains := by
    simpa [parameterDomains, sourceSuffix] using Hsemantics A
  rcases A.transportSuffixOfInvariantSemantics envCtors [] parameterDomains
      HparameterContext Hprod.localWF Hprod.bindings Hprod.origins hrecInfo
      HsuffixSemantics with ⟨suffixTarget, Hsuffix⟩
  refine ⟨VExpr.wrapForalls parameterDomains suffixTarget, ?_⟩
  have Hclosed := A.closeTransportedSuffix hctorsOrdered HtemplatePrefix'
    HtemplateTelescope' Htemplate' hparameterDomains Hsuffix
  have holdLevels := Hprod.restoredPrimaryRecursorLevelParams familyIdx hentry
    Hstep.restored.recursor holdRecName'
  rw [holdLevels]
  simpa [E, Nat.add_assoc] using Hclosed

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
    ∃ recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes envCtors Hrestored.inductives sourceDecl.types
          recursors := by
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

/-- Whole-mutual nested source semantics with the opaque restored-telescope
premise eliminated.  The remaining premise is a stateful source-facing
interpretation of the exact restored suffix prefix; parameter translation,
operational alignment, dependent transport, and reclosing are derived here. -/
theorem NestedLoweringResultClosed.sourceSemanticTraceOfInstalledSuffixes
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
    (Hsuffixes : forall familyIdx
      (hfamily : familyIdx < sourceTypes.length)
      (hdecl : familyIdx < sourceDecl.types.length)
      (hentry : familyIdx < Hprod.entries.length)
      (stepSource stepTarget : Environment)
      (Hstep : RestoredInductiveStep result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2 allIndNames
        sourceTypes[familyIdx] stepSource stepTarget)
      (A : GeneratedRecursorRestorationTelescopeAlignment result loweredEnv
        (Lean4Lean.mkAuxRecNameMap loweredEnv sourceTypes).2
        Hstep.restored.recursor.restored.newInfo
        (Hprod.generated.entry familyIdx hentry)),
      GeneratedRecursorRestoredSuffixTranslationsInvariant A Hprod.origins
        envCtors []
        ((Hheaders.sourceMaterialized.parameterSuffix.toRecursorContext
          Hprod.elimLevelAdmissible).parameterDecls.toCtx.reverse)) :
    exists recursors,
      RestoredSourceInductiveSemanticTrace sourceDecl c.lparams c.safety
        sourceVEnv envTypes envCtors Hrestored.inductives sourceDecl.types
          recursors := by
  apply H.sourceSemanticTraceOfInstalledTelescopes Hc Hprod Hsources Hsource
    Hmetadata Howners hempty Hrestored
  intro familyIdx hfamily hdecl hentry stepSource stepTarget Hstep
  exact H.restoredPrimaryTelescopeAtFreshOfSuffix Hprod Hsource familyIdx
    hfamily hentry Hstep hempty fun A =>
      Hsuffixes familyIdx hfamily hdecl hentry stepSource stepTarget Hstep A

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
    (Hc : ContextWF c) (H : RecursorPhasesResult R loweredEnv)
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
      Lean4Lean.validateRestoredRecursorRules.run restoredEnv loweredEnv
        lparams safety fuel res
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
    (Hc : ContextWF c) (H : RecursorPhasesResult R loweredEnv)
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
