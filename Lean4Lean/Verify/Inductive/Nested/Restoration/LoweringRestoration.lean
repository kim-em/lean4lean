import Lean4Lean.Verify.Inductive.Nested.Lowering.Output
import Lean4Lean.Verify.Inductive.Nested.Restoration.Steps

/-! # The restoration side of the lowering verification

Ported from the source branch's `Nested/Lowering/Basic.lean` (its first section: the typing of
the validated nested occurrences, `NestedOccurrencesTyped`, `ClosedNestedOccurrencesTyped`,
`ClosedNestedOccurrenceTyping`) and `Nested/Lowering/Queue.lean` (the theorems that read the
restoration steps: `ConstructorLowering.Resolved.constructorRestoration_inverse`,
`restoredType_translation`, `LoweredRestoredConstructors`, `NestedLowering.closeNestedOccurrencesTyped`,
`validatedAuxiliaryResidualTranslations`, `restoreAuxConstructorsFreshOfInstallation`). The
lowering owner ported the rest of these files under `Nested/Lowering/`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Postcondition of the executable nested-auxiliary validation pass:
every nested application stored in `aux2nested` has a translated typing derivation in the
restored parameter context.  Such an application is a nested occurrence `I Ds` applied
to its parameters only, so for an indexed family `I` it is a type family, not
a type; like the C++ kernel, validation only type-checks it. -/
def NestedOccurrencesTyped (venv : VEnv) (lparams : List Name)
    (vlctx : VLCtx) (res : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∀ name e, res.aux2nested.find? name = some e →
    ∃ ty e' ty', TrTyping venv lparams vlctx e ty e' ty'

/-- Context-independent form of nested-auxiliary validation.  Each open
nested application `e : T` is closed with lambdas over the exact parameter telescope
retained by lowering, and its inferred type `T` with foralls over the same
telescope, so that the closed application `fun params => e` has type
`∀ params, T`; both closures share one list of translated parameter domains.
Later restoration may choose fresh binder names without changing the
statement that must be translated.  Closing the application with lambdas, rather
than with foralls, is what admits nested occurrences of indexed families:
there `T` is `∀ indices, Sort u`, not a sort, and `∀ params, e` would be
ill-typed. -/
def ClosedNestedOccurrencesTyped (venv : VEnv) (lparams : List Name)
    (res : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∀ name e, res.aux2nested.find? name = some e →
    Closed e ∧ ∃ type domains body bodyType, Closed type ∧
      domains.length = res.params.size ∧
      TrExprS venv lparams [] (res.lctx.mkLambda res.params e)
        (VExpr.wrapLams domains body) ∧
      TrExprS venv lparams [] (res.lctx.mkForall res.params type)
        (VExpr.wrapForalls domains bodyType) ∧
      venv.HasType lparams.length [] (VExpr.wrapLams domains body)
        (VExpr.wrapForalls domains bodyType)

/-- De-Bruijn form of one closed nested application.  It records the closed
translation of the application's parameter-closed type, whose forall telescope
fixes the translated parameter domains, and the residual translation and
typing of the application itself in those domains, so no kernel free-variable
identifier occurs in the semantic context.  The residual is typed, not
required to be a type: for a nested indexed family it is a type family. -/
structure ClosedNestedOccurrenceTyping
    (venv : VEnv) (lparams : List Name)
    (res : Lean4Lean.ElimNestedInductive.Result)
    (selection : CDeclArray res.lctx res.params)
    (e : Expr) where
  /-- The type inferred for the open application by validation. -/
  type : Expr
  typeClosed : Closed type
  domains : List VExpr
  residualTarget : VExpr
  residualType : VExpr
  arity : domains.length = res.params.size
  closed : TrExprS venv lparams []
    (res.lctx.mkForall res.params type)
    (VExpr.wrapForalls domains residualType)
  residual : TrExprS venv lparams (abstractForallContext domains [])
    (e.abstractList selection.fvars) residualTarget
  residualTyping : venv.HasType lparams.length
    (abstractForallContext domains []).toCtx residualTarget residualType

/-- Over a telescope of local assumptions, `mkLambda'` and `mkForall'` wrap
one common list of translated domains, one per opened variable. -/
theorem nestedMLCtxSharedBinderDomains {c : TypeChecker.MLCtx}
    (wf : c.WF env Us) (n : Nat) (hn : n ≤ c.length)
    (hcdecl : ∀ fv ∈ c.fvarRevList n hn, ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    ∃ domains : List VExpr, domains.length = n ∧
      (∀ e, c.mkLambda' n hn e = VExpr.wrapLams domains e) ∧
      (∀ e, c.mkForall' n hn e = VExpr.wrapForalls domains e) := by
  induction n generalizing c with
  | zero => exact ⟨[], rfl, fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    match c, wf, hn, hcdecl with
    | .nil, _, hn, _ => simp at hn
    | .vlam id name ty ty' bi c, wf, hn, hcdecl =>
      have hrest : ∀ fv ∈ c.fvarRevList n (Nat.le_of_succ_le_succ hn),
          ∃ index name type bi kind,
            c.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
        intro fv hfv
        have hne : fv ≠ id := by
          rintro rfl
          exact wf.1.tr.find?_eq_none.1 wf.2.1
            (c.fvarRevList_prefix.subset hfv)
        rcases hcdecl fv (by simp [hfv]) with
          ⟨index, name', type, bi', kind, hfind⟩
        refine ⟨index, name', type, bi', kind, ?_⟩
        rw [wf.find?_eq] at hfind
        rw [wf.1.find?_eq]
        have hbeq : (fv == id) = false := by simpa using hne
        simpa [TypeChecker.MLCtx.decls, LocalDecl.fvarId, hbeq] using hfind
      rcases ih wf.1 (Nat.le_of_succ_le_succ hn) hrest with
        ⟨domains, hlength, hlam, hforall⟩
      exact ⟨domains ++ [ty'], by simp [hlength],
        fun e => by simp [hlam, VExpr.wrapLams],
        fun e => by simp [hforall, VExpr.wrapForalls]⟩
    | .vlet id name ty v ty' v' c, wf, hn, hcdecl =>
      exfalso
      rcases hcdecl id (by simp) with ⟨index, name', type, bi', kind, hfind⟩
      rw [wf.find?_eq] at hfind
      simp [TypeChecker.MLCtx.decls, LocalDecl.fvarId] at hfind

/-- The open nested application contains no pre-existing loose bound
variables.  This is derived from the residual translation's scoping theorem,
not imposed as an additional executable validation condition. -/
theorem ClosedNestedOccurrenceTyping.sourceClosed
    (H : ClosedNestedOccurrenceTyping venv lparams res selection e) :
    Closed e 0 := by
  have HresidualClosed := H.residual.closed
  have hmap : ∀ domains : List VExpr,
      VLCtx.bvars (domains.map fun type =>
        ((none, VLocalDecl.vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = domains.length := by
    intro domains
    induction domains with
    | nil => rfl
    | cons domain domains ih => simp [VLCtx.bvars, ih]
  have hbvars : (abstractForallContext H.domains []).bvars =
      H.domains.length := by
    simp only [abstractForallContext,
      VLCtx.bvars_append, VLCtx.bvars, Nat.add_zero]
    rw [hmap]
    simp
  apply Expr.closed_of_abstractList
  rw [hbvars] at HresidualClosed
  simpa [H.arity, selection.size] using HresidualClosed

def ClosedNestedOccurrenceTypings
    (venv : VEnv) (lparams : List Name)
    (res : Lean4Lean.ElimNestedInductive.Result)
    (selection : CDeclArray res.lctx res.params) : Prop :=
  ∀ name e, res.aux2nested.find? name = some e →
    Nonempty (ClosedNestedOccurrenceTyping venv lparams res selection e)

/-- Telescope inversion turns every context-independent validated nested application
into the bound-variable representation used beneath restored
recursor parameter binders. -/
theorem ClosedNestedOccurrencesTyped.residualTranslations
    (H : ClosedNestedOccurrencesTyped venv lparams res)
    (henv : venv.WF)
    (selection : CDeclArray res.lctx res.params)
    (hnodup : selection.fvars.Nodup) :
    ClosedNestedOccurrenceTypings venv lparams res selection := by
  intro name e hfind
  rcases H name e hfind with
    ⟨hclosedE, type, domains, body, bodyType, htypeClosed, harity, Hlambda,
      Hforall, Htyping⟩
  have Htel : Expr.LambdaTelescope (res.lctx.mkLambda res.params e)
      domains.length (e.abstractList selection.fvars) := by
    have Htel := LocalContext.mkLambda_fvars_lambdaTelescopeList
      (lctx := res.lctx) selection.declarations hnodup hclosedE
    have hlambda : res.lctx.mkLambda res.params e =
        res.lctx.mkLambda (selection.fvars.map Expr.fvar).toArray e :=
      congrArg (res.lctx.mkLambda · e) selection.expressions
    rw [hlambda, harity, selection.size]
    exact Htel
  have Hresidual := TrExprS.lambdaTelescope_exact_residual Htel rfl Hlambda
  have Hbody := (VEnv.HasType.wrapLams_inv henv (by trivial) Htyping).2
  exact ⟨⟨type, htypeClosed, domains, body, bodyType, harity, Hforall,
    Hresidual, by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Hbody⟩⟩

private theorem checkNestedAuxiliaryList.WF
    {c : TypeChecker.VContext} {s : TypeChecker.State}

/-- Metadata-facing form of the constructor inverse.  Installation exposes a
`ConstructorVal`, while lowering is indexed by the corresponding
`Constructor`; the explicit type equality is the only alignment fact needed
to connect the two verified relations. -/
theorem ConstructorLowering.Resolved.constructorRestoration_inverse
    (H : ConstructorLowering.Resolved env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (hsourceBVar : Closed source.type)
    (hparamsSize : params.size = nparams)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type) :
    Nonempty (ConstructorRestorationInverse result restoreEnv nparams source
      out.1 newInfo.type) := by
  apply H.nestedRestoration_inverse hresultParams paramFvars hparams hnodup
    HsourceClosed hsourceBVar hparamsSize restoreEnv HsourceDisjoint hresultNParams
  simpa [htype] using Hrestored.type

/-- Transport source translation across constructor restoration using
source disjointness (`RestoreSourceDisjoint`), without imposing a namespace convention on
auxiliary constructor names. -/
theorem ConstructorLowering.Resolved.restoredType_translation
    (H : ConstructorLowering.Resolved env params nparams result source state out)
    (hresultParams : result.params = params)
    (paramFvars : List FVarId)
    (hparams : params = (paramFvars.map Expr.fvar).toArray)
    (hnodup : paramFvars.Nodup)
    (HsourceClosed : source.type.FVarsIn fun _ => False)
    (hsourceBVar : Closed source.type)
    (hparamsSize : params.size = nparams)
    (restoreEnv : Environment)
    (HsourceDisjoint : RestoreSourceDisjoint result restoreEnv source.type)
    (hresultNParams : result.nparams = nparams)
    (Hrestored : ConstructorRestoration result restoreEnv oldInfo newInfo)
    (htype : oldInfo.type = out.1.type)
    (Hsource : TrExprS venv oldInfo.levelParams [] source.type targetType) :
    TrExprS venv oldInfo.levelParams [] newInfo.type targetType := by
  rcases H.constructorRestoration_inverse hresultParams paramFvars hparams
      hnodup HsourceClosed hsourceBVar hparamsSize restoreEnv HsourceDisjoint
      hresultNParams Hrestored
      htype with
    ⟨Hinverse⟩
  apply Hsource.eqv
  simpa [beq_comm] using Hinverse.restoredType_eqv_source

        Hmapping⟩

/-- Lockstep alignment of the state-threaded constructor lowering relation
with the executable restoration fold.  The kernel lookup theorem
has already identified the `oldInfo.type` read at every step with that step's
positionally corresponding lowered constructor type. -/
inductive LoweredRestoredConstructors
    (result : Lean4Lean.ElimNestedInductive.Result)
    (mappingEnv loweredEnv : Environment) (params : Array Expr)
    (nparams : Nat) (safety : DefinitionSafety) (lparams : List Name) :
    List Constructor → Lean4Lean.ElimNestedInductive.State →
      List Constructor → Lean4Lean.ElimNestedInductive.State →
      Environment → Environment → Prop
  | nil (state : Lean4Lean.ElimNestedInductive.State)
      (sourceProdEnv : Environment) :
      LoweredRestoredConstructors result mappingEnv loweredEnv params
        nparams safety lparams [] state [] state sourceProdEnv sourceProdEnv
  | cons
      (Hmapping : ConstructorLowering.Resolved mappingEnv params nparams result
        source state (target, nextState))
      (Hstep : RestoredConstructorStep result loweredEnv target.name
        sourceProdEnv middleProdEnv)
      (hsafety : safety ≤ (ConstantInfo.ctorInfo Hstep.oldInfo).safety)
      (hlevels : Hstep.oldInfo.levelParams = lparams)
      (hname : Hstep.oldInfo.name = target.name)
      (htype : Hstep.oldInfo.type = target.type)
      (Hrest : LoweredRestoredConstructors result mappingEnv loweredEnv params
        nparams safety lparams sources nextState targets finalState
          middleProdEnv targetProdEnv) :
      LoweredRestoredConstructors result mappingEnv loweredEnv params nparams
        safety lparams (source :: sources) state (target :: targets) finalState
          sourceProdEnv targetProdEnv


/-- Interpret the lockstep lowering/restoration relation against the
independently translated source constructors.  This connects the executable and the
specification for the constructor list: every executable restoration step is
shown to translate the same abstract constructor that appears in the source
inductive specification. -/
theorem LoweredRestoredConstructors.sourceTyping
    (H : LoweredRestoredConstructors result mappingEnv loweredEnv params
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
    (hresultNParams : result.nparams = nparams)
    (hparamsSize : params.size = nparams) :
    RestoredConstructorTranslations result loweredEnv lparams safety canonicalEnv
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
            hnodup HsourceSyntax.closed
            (by simpa [VLCtx.bvars] using HsourceType.closed) hparamsSize loweredEnv
            (Hdisjoint source (by simp)) hresultNParams
            Hstep.restored.restoration htype HsourceType
        have Htranslated : TrConstVal safety canonicalEnv
            (.ctorInfo Hstep.restored.newInfo) vctor :=
          Hstep.restored.restoration.translatedOfMetadata hsafety (by
            rw [hlevels]
            exact Hsource.uvars.symm) (by
            exact (hname.trans Hmapping.name).trans Hsource.name.symm)
            HrestoredType
        apply RestoredConstructorTranslations.cons Hstep
          { constructor := vctor
            sourceTranslation := Hsource
            restoredTranslation := Htranslated }
        apply ih Hsources Hsyntax
        intro tail htail
        exact Hdisjoint tail (by simp [htail])

/-- The executable auxiliary checks can be closed over lowering's retained
parameter telescope: each nested application with lambdas, its inferred type with
foralls.  This removes the concrete free-variable names from the typing
facts before restoration reopens the same telescope with its own fresh
names.  Every variable of the telescope is a local assumption of lowering's
context, so both closures wrap the same translated parameter domains. -/
theorem NestedLowering.closeNestedOccurrencesTyped
    (H : NestedLowering sourceEnv fuel nparams types initialState
      (res, finalState))
    (henv : venv.WF)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (Hvalidated : NestedOccurrencesTyped venv lparams mlctx.vlctx res) :
    ClosedNestedOccurrencesTyped venv lparams res := by
  have hfull : mlctx.fvarRevList mlctx.length (Nat.le_refl _) =
      mlctx.vlctx.fvars := mlctx.fvarRevList_all
  have hparams : res.params.toList.reverse =
      (mlctx.fvarRevList mlctx.length (Nat.le_refl _)).map Expr.fvar := by
    rw [hfull, ← hmlctx.tr.fvars_eq, hlctx]
    exact H.resultParams_reverse_fvars
  rcases H.resultContextSelection with ⟨selection⟩
  have hcdecl : ∀ fv ∈ mlctx.fvarRevList mlctx.length (Nat.le_refl _),
      ∃ index name type bi kind,
        mlctx.lctx.find? fv = some (.cdecl index fv name type bi kind) := by
    intro fv hfv
    have hmem : Expr.fvar fv ∈ res.params.toList := by
      rw [← List.mem_reverse, hparams]
      exact List.mem_map_of_mem hfv
    have hsel : fv ∈ selection.fvars := by
      rw [selection.expressions] at hmem
      simpa using hmem
    rw [hlctx]
    exact selection.declarations fv hsel
  rcases nestedMLCtxSharedBinderDomains hmlctx mlctx.length (Nat.le_refl _)
      hcdecl with ⟨domains, hlength, hlam, hforall⟩
  have hsize : res.params.size = mlctx.length := by
    have := congrArg List.length hparams
    simpa using this
  intro name e hfind
  rcases Hvalidated name e hfind with
    ⟨ty, e', ty', ⟨_hfvars, Hexpr, Htype, Htyping⟩⟩
  have hclosedE : Closed e := by
    simpa [TypeChecker.MLCtx.noBV] using Hexpr.closed
  have hclosedTy : Closed ty := by
    simpa [TypeChecker.MLCtx.noBV] using Htype.closed
  have HtyType : venv.IsType lparams.length mlctx.vlctx.toCtx ty' :=
    Htyping.isType henv.ordered hmlctx.tr.wf.toCtx
  have Hlambda := hmlctx.mkLambda_trS henv Hexpr Htyping
    mlctx.length (Nat.le_refl _)
  have Hforall := hmlctx.mkForall_trS henv Htype HtyType
    mlctx.length (Nat.le_refl _)
  rw [mlctx.dropN_all] at Hlambda Hforall
  have hlambdaEq : res.lctx.mkLambda res.params e =
      mlctx.mkLambda mlctx.length (Nat.le_refl _) e := by
    rw [← hlctx]
    exact hmlctx.mkLambda_eq mlctx.length (Nat.le_refl _) hparams hclosedE
  have hforallEq : res.lctx.mkForall res.params ty =
      mlctx.mkForall mlctx.length (Nat.le_refl _) ty := by
    rw [← hlctx]
    exact hmlctx.mkForall_eq mlctx.length (Nat.le_refl _) hparams hclosedTy
  refine ⟨hclosedE, ty, domains, e', ty', hclosedTy,
    hlength.trans hsize.symm, ?_, ?_, ?_⟩
  · rw [hlambdaEq, ← hlam]
    exact Hlambda.1
  · rw [hforallEq, ← hforall]
    exact Hforall.1
  · rw [← hlam, ← hforall]
    exact Hlambda.2

/-- Name-independent typing of the validated nested applications:
the free variables selected by lowering are abstracted into the
de-Bruijn parameter context before restoration is inspected. -/
theorem NestedLowering.validatedAuxiliaryResidualTranslations
    (H : NestedLowering sourceEnv fuel nparams types initialState
      (res, finalState))
    (henv : venv.WF)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (Hvalidated : NestedOccurrencesTyped venv lparams mlctx.vlctx res) :
    ∃ selection : CDeclArray res.lctx res.params,
      ClosedNestedOccurrenceTypings venv lparams res selection := by
  rcases H.resultContextSelection with ⟨selection⟩
  have hparams : res.params.toList.reverse =
      (mlctx.fvarRevList mlctx.length (Nat.le_refl _)).map Expr.fvar := by
    rw [mlctx.fvarRevList_all, ← hmlctx.tr.fvars_eq, hlctx]
    exact H.resultParams_reverse_fvars
  have hnodup : selection.fvars.Nodup := by
    have h1 : res.params.toList = selection.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList selection.expressions
    have h2 : selection.fvars.reverse = mlctx.fvarRevList mlctx.length (Nat.le_refl _) := by
      apply (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp
      rw [List.map_reverse, ← h1]
      exact hparams
    have := hmlctx.fvarRevList_nodup mlctx.length (Nat.le_refl _)
    rw [← h2] at this
    simpa using this
  exact ⟨selection,
    (H.closeNestedOccurrencesTyped henv mlctx hmlctx hlctx Hvalidated
      ).residualTranslations henv selection hnodup⟩


/-- Build the lockstep constructor relation `LoweredRestoredConstructors` from the
verified lowered installation.  The only list premise is that all mapped targets belong
to the installed owner; in the family specialization this is immediate because `targets`
is that owner's constructor list. -/
theorem LoweredRestoredConstructors.ofInstalled
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv : Environment}
    {Hheaders : HeaderEnvironment c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : OrdinaryConstructorCheck Hheaders ctorEnv}
    (Hprod : RecursorCheck R.toConstructorCheck loweredEnv)
    (howner : owner ∈ indTypes.toList)
    (Hmapping : ConstructorLowerings.Resolved mappingEnv params nparams result
      sources state (targets, finalState))
    (Htrace : FoldSteps (RestoredConstructorStep result loweredEnv)
      (targets.map (fun ctor => ctor.name)) sourceProdEnv targetProdEnv)
    (Htargets : ∀ target ∈ targets, target ∈ owner.ctors) :
    LoweredRestoredConstructors result mappingEnv loweredEnv params nparams
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
      apply LoweredRestoredConstructors.cons Hhead Hstep
      · exact Hmetadata.1
      · exact Hmetadata.2.1
      · exact Hmetadata.2.2.1
      · exact Hstep.oldType_eq_ofInstalled Hprod howner
          (Htargets _ (by simp)) rfl
      · apply LoweredRestoredConstructors.ofInstalled Hprod howner
          Htail Hsteps
        intro target htarget
        exact Htargets target (by simp [htarget])

/-- Freshness of auxiliary constructors for restoration: lowering proves auxiliary
families fresh in the source kernel environment, and lockstep installation turns that
into abstract freshness for every constructor recognized through those
families. -/
theorem NestedLowering.restoreAuxConstructorsFreshOfInstallation
    (H : NestedLowering sourceProdEnv fuel nparams types initialState
      (result, finalState))
    (Hinstall : AddConstants safety sourceProdEnv sourceVEnv entries
      loweredEnv loweredVEnv)
    (hwf : sourceProdEnv.constants.WF)
    (Howners : ConstructorOwnersPresent sourceProdEnv)
    (hempty : initialState.nestedAux = #[]) :
    RestoreAuxConstructorsFresh result loweredEnv sourceVEnv :=
  Hinstall.restoreAuxConstructorsFresh hwf Howners
    (H.resultFamilyNamesFreshOfEmpty hwf hempty)


end VerifyInductive
end Lean4Lean
