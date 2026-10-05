import Lean4Lean.Verify.Inductive.Recursor.CanonicalParameterReplay

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- Recover the actual consumed motive telescope in its original narrow
parameter scope. Its domain syntax is selected from the retained translation,
while the earlier semantic telescope supplies only typed equality. -/
theorem RecursorMotiveTelescopeSeed.consumedTranslation
    {Rroot : RecursorContextWF root recLparams}
    (S : RecursorMotiveTelescopeSeed Rroot stats decl owner info elimLevel) :
    ∃ target,
      TrExprS Rroot.venv recLparams S.motiveSourceScope
        (root.lctx.mkForall info.indices
          (root.lctx.mkForall #[info.major] (.sort elimLevel))) target ∧
      Rroot.venv.IsType recLparams.length S.motiveSourceScope.toCtx target ∧
      Rroot.venv.IsDefEqU recLparams.length S.motiveSourceScope.toCtx
        target S.canonical.motiveType := by
  have henv := Rroot.checking.tr.wf
  have W := S.motiveSourceLift
  have Hcontext := S.motiveSourceContext
  have hbvars : VLCtx.bvars S.motiveClosedScope = 0 := by
    calc
      VLCtx.bvars S.motiveClosedScope =
          VLCtx.bvars S.motiveSourceExpanded := Hcontext.bvars.symm
      _ = VLCtx.bvars S.motiveSourceScope := W.bvars_eq
      _ = 0 := S.motiveSourceNoBV
  have hclosed := S.motiveClosedTr.closed
  rw [hbvars] at hclosed
  rcases S.motiveClosedTr.weakFV'_inv henv W
      (Hcontext.symm henv.ordered) hclosed S.motiveSourceFVars with
    ⟨target, Hnarrow⟩
  have Hweak := Hnarrow.weakFV' henv.ordered W Hcontext.wf
  have Htarget := Hweak.uniq henv Hcontext S.motiveClosedTr
  have Htype := S.motiveClosedType.defeqDFC henv.ordered
    (Hcontext.defeqCtx.symm henv.ordered)
  have HweakType := Htype.defeqU_l henv Hcontext.wf.toCtx Htarget.symm
  obtain ⟨level, HweakType⟩ := HweakType
  have HnarrowType : Rroot.venv.IsType recLparams.length S.motiveSourceScope.toCtx target := by
    refine ⟨level, ?_⟩
    exact (VEnv.HasType.weak'_iff henv Hcontext.wf.toCtx W.toCtx).1 HweakType
  have HcanonicalExpanded := S.motiveClosedCanonicalDefEq.defeqDFC
    henv.ordered (Hcontext.defeqCtx.symm henv.ordered)
  have HweakCanonical := Htarget.trans henv Hcontext.wf.toCtx HcanonicalExpanded
  rw [← S.motiveClosedCanonicalEq] at HweakCanonical
  have Hcanonical :=
    (VEnv.IsDefEqU.weak'_iff henv Hcontext.wf.toCtx W.toCtx).1 HweakCanonical
  exact ⟨target, Hnarrow, HnarrowType, Hcanonical⟩

/-- Translate a completed motive over the block's one cached parameter
choice, before any recursor declaration is installed. -/
theorem CompletedRecursorConstruction.consumedMotiveAtParameters
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size) :
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner H.recInfos[owner]! H.elimLevel,
      ∃ target,
        TrExprS H.recursorWF.venv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
          ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
            H.params.fvars) target ∧
        H.recursorWF.venv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          H.parameterSuffix.parameterDecls.toCtx target ∧
        H.recursorWF.venv.IsDefEqU
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          H.parameterSuffix.parameterDecls.toCtx target S.canonical.motiveType := by
  have henv := H.recursorWF.checking.tr.wf
  obtain ⟨S, hparams⟩ := H.motiveTelescopes.seed owner howner
  rw [← H.parameterDecls] at hparams
  obtain ⟨narrowTarget, Hnarrow, HnarrowType, Hcanonical⟩ := S.consumedTranslation
  let source := H.localContext.lctx.mkForall H.recInfos[owner]!.indices
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))
  have HnarrowParameters : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      S.motiveParameterScope source narrowTarget := by
    simpa [source, S.motiveSourceParameterScope] using Hnarrow
  rcases cachedParameterDecls_fvars S.motiveParameterDecls with
    ⟨parameterFVars, hparameterExprs, hparameterScopeFVars⟩
  have hstatsParams : stats.params.toList.reverse =
      H.params.fvars.reverse.map Expr.fvar := by
    have h := congrArg Array.toList H.params.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  have hparameterFVars : parameterFVars = H.params.fvars.reverse := by
    apply (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp
    exact hparameterExprs.symm.trans hstatsParams
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type, entry = (some (fv, deps), .vlam type))
      H.params.fvars.reverse S.motiveParameterScope := by
    have Hcached := S.motiveParameterDecls
    rw [hparameterExprs, List.forall₂_map_left_iff] at Hcached
    have Hdecls' : List.Forall₂
        (fun fv entry => ∃ deps type, entry = (some (fv, deps), .vlam type))
        parameterFVars S.motiveParameterScope :=
      Lean4Lean.List.Forall₂.imp (fun fv entry hentry => by
        rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
        cases Expr.fvar.inj hparam
        exact ⟨deps, type, hentry⟩) Hcached
    simpa [hparameterFVars] using Hdecls'
  have hscopeWF := S.motiveSourceLift.wf henv S.motiveSourceContext.wf
  have hparamsNodup : H.params.fvars.reverse.Nodup := by
    have h := hscopeWF.fvars_nodup
    rwa [S.motiveSourceParameterScope, hparameterScopeFVars, hparameterFVars] at h
  have Habstract := Lean4Lean.VerifyInductive.TrExprS.abstractFVarLambdaSuffix
    (domains := []) Hdecls hparamsNodup (by
      simpa [abstractForallContext] using HnarrowParameters)
  simp only [List.reverse_reverse] at Habstract
  have Habstract' : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext S.motiveParameterScope.toCtx.reverse [])
      (source.abstractList H.params.fvars) narrowTarget := by
    simpa using Habstract
  have hsourceToParams := VEnv.IsDefEqCtx.transEmpty henv
    (S.motiveParameterAlignment.symm henv.ordered) hparams
  have Hctx : VLCtx.IsDefEq H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext S.motiveParameterScope.toCtx.reverse [])
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) := by
    exact abstractForallContext.isDefEq (by simpa using hsourceToParams)
  obtain ⟨target, Htarget⟩ := Habstract'.defeqDFC henv Hctx
  have Htargets := Habstract'.uniq henv Hctx Htarget
  have Htype : H.recursorWF.venv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext S.motiveParameterScope.toCtx.reverse []).toCtx narrowTarget := by
    simpa [abstractForallContext, ← S.motiveSourceParameterScope] using HnarrowType
  have Htype' := (Htype.defeqU_l henv Hctx.wf.toCtx Htargets).defeqDFC henv.ordered Hctx.defeqCtx
  have Hcanonical' : H.recursorWF.venv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext S.motiveParameterScope.toCtx.reverse []).toCtx
      narrowTarget S.canonical.motiveType := by
    simpa [abstractForallContext, ← S.motiveSourceParameterScope] using Hcanonical
  have Hcanonical'' := (Htargets.symm.trans henv Hctx.wf.toCtx Hcanonical').defeqDFC
    henv.ordered Hctx.defeqCtx
  exact ⟨S, target, Htarget, by simpa [abstractForallContext] using Htype',
    by simpa [abstractForallContext] using Hcanonical''⟩

private theorem abstractList_sort (u : Level) (fvars : List FVarId) (k : Nat := 0) :
    (Expr.sort u).abstractList fvars k = .sort u :=
  Expr.abstractList_eq_self_of_abstract1 (.sort u)
    (by intro fv k; simp [Expr.abstract1]) fvars k

/-- The actual consumed index domains and the major binder are exposed from
one pre-install translation. In particular, the terminal sort is the exact
universe selected by the executable elimination check. -/
theorem CompletedRecursorConstruction.consumedMotiveDomains
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (owner : Nat) (howner : owner < H.recInfos.size) :
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner H.recInfos[owner]! H.elimLevel,
      ∃ indices major level,
        indices.length = H.recInfos[owner]!.indices.size ∧
        VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams) H.elimLevel = some level ∧
        TrExprS H.recursorWF.venv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
          ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
            H.params.fvars) (VExpr.wrapForalls indices (.forallE major (.sort level))) ∧
        H.recursorWF.venv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          H.parameterSuffix.parameterDecls.toCtx
          (VExpr.wrapForalls indices (.forallE major (.sort level))) ∧
        H.recursorWF.venv.IsDefEqU
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          H.parameterSuffix.parameterDecls.toCtx
          (VExpr.wrapForalls indices (.forallE major (.sort level))) S.canonical.motiveType := by
  obtain ⟨S, target, Htr, Htype, Heq⟩ := H.consumedMotiveAtParameters owner howner
  have hlctx : LocalContext.LctxClosed H.localContext.lctx := H.recursorWF.lctxClosed
  have hparts := (H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner).parts
  have hmajorNodup : S.majorBound.fvars.Nodup := by
    rw [S.majorBound.fvars_eq (H.bindings.major owner howner) (by simp)]; exact hparts.major
  have hindicesNodup : S.indicesBound.fvars.Nodup := by
    rw [S.indicesBound.fvars_eq (H.bindings.indices owner howner) (by simp)]; exact hparts.indices
  have hmajorClosed : Closed (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.sort H.elimLevel)) :=
    S.majorBound.mkForall_closed H.localWF hmajorNodup hlctx trivial
  have hinnerClosed : Closed (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))) :=
    S.indicesBound.mkForall_closed H.localWF hindicesNodup hlctx hmajorClosed
  have Hmajor := S.majorBound.mkForall_forallTelescopeList H.localWF (.sort H.elimLevel)
    hmajorNodup trivial
  have Hindices := S.indicesBound.mkForall_forallTelescopeList H.localWF
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))
    hindicesNodup hmajorClosed
  have Htel := (Hindices.trans (Hmajor.abstractList S.indicesBound.fvars)).abstractList H.params.fvars
  simp only [Array.size_singleton, abstractList_sort, Nat.zero_add] at Htel
  obtain ⟨domains, result, hlength, htarget, Hresult⟩ :=
    TrExprS.forallTelescope_shape_with_context Htel Htr
  cases Hresult with
  | sort hlevel =>
    rename_i level
    have hnonempty : domains ≠ [] := by intro heq; simp [heq] at hlength
    let indices := domains.dropLast
    let major := domains.getLast hnonempty
    have hdomains : indices ++ [major] = domains := List.dropLast_concat_getLast hnonempty
    have hindices : indices.length = H.recInfos[owner]!.indices.size := by
      rw [← hdomains, List.length_append, List.length_singleton] at hlength
      omega
    have htarget' : target = VExpr.wrapForalls indices (.forallE major (.sort level)) := by
      rw [htarget, ← hdomains, VExpr.wrapForalls_append]
      rfl
    rw [htarget'] at Htr Htype Heq
    exact ⟨S, indices, major, _, hindices, hlevel, Htr, Htype, Heq⟩

theorem CompletedConstructorPhases.family_not_annotation
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    family.name ≠ ``optParam ∧ family.name ≠ ``autoParam ∧
    family.name ≠ ``outParam ∧ family.name ≠ ``semiOutParam := by
  have hfresh := (VEnv.addConstVals_names_fresh R.core.typesAdded).2
    family.toVConstVal (List.mem_map.mpr ⟨family, hf, rfl⟩)
  have habsent (name : Name) (hexists : ∃ info, c.env.find? name = some info ∧ info.safety = .safe) :
      family.name ≠ name := by
    intro heq
    obtain ⟨info, hlookup, hsafety⟩ := hexists
    obtain ⟨value, hvalue, _⟩ := R.sourceContext.checking.tr.find? hlookup
      (hsafety ▸ DefinitionSafety.le_safe)
    rw [R.sourceContextVEnv, ← heq] at hvalue
    rw [hfresh] at hvalue
    cases hvalue
  have hw := R.sourceContext.checking.typeAnnotationWrappers
  refine ⟨habsent _ ?_, habsent _ ?_, habsent _ ?_, habsent _ ?_⟩
  · obtain ⟨info, _, hlookup, hsafety, _⟩ := hw.optParam.operational
    exact ⟨info, hlookup, hsafety⟩
  · obtain ⟨info, _, hlookup, hsafety, _⟩ := hw.autoParam.operational
    exact ⟨info, hlookup, hsafety⟩
  · obtain ⟨info, _, hlookup, hsafety, _⟩ := hw.outParam.operational
    exact ⟨info, hlookup, hsafety⟩
  · obtain ⟨info, _, hlookup, hsafety, _⟩ := hw.semiOutParam.operational
    exact ⟨info, hlookup, hsafety⟩

theorem Expr.consumeTypeAnnotationsVerified_eq_of_head {e : Expr}
    (hhead : e.getAppFn = .const name levels)
    (hnames : name ≠ ``optParam ∧ name ≠ ``autoParam ∧
      name ≠ ``outParam ∧ name ≠ ``semiOutParam) : e.consumeTypeAnnotationsVerified = e := by
  fun_induction Expr.consumeTypeAnnotationsVerified e
  case case1 n ls first second hannotation ih =>
    have hname : n = name := by simpa [Expr.getAppFn, Expr.constName!] using congrArg Expr.constName! hhead
    subst n
    simp [hnames.1, hnames.2.1] at hannotation
  case case3 n ls arg hannotation ih =>
    have hname : n = name := by simpa [Expr.getAppFn, Expr.constName!] using congrArg Expr.constName! hhead
    subst n
    simp [hnames.2.2.1, hnames.2.2.2] at hannotation
  all_goals rfl


/-- The major premise really is the source family applied to its parameters
and indices; reserved wrapper names cannot occur among the fresh families. -/
theorem CompletedRecursorConstruction.majorSourceType
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (D : BoundFVarDeclarationAt H.localContext #[H.recInfos[owner]!.major] 0) :
    D.type = mkAppN (mkAppN
      (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name
        stats.levels) stats.params) H.recInfos[owner]!.indices := by
  have hfamily : owner < decl.types.length := by simpa [H.cardinality.records] using howner
  let Dall : BoundFVarDeclarationAt H.localContext (H.recInfos.map (·.major)) owner := {
    D with
    inBounds := by simpa using howner
    expression := by
      simpa [Array.getElem!_eq_getD, Array.getD, howner] using D.expression }
  have htype := (H.origins.majors.type_eq Dall).trans (H.majorShapes.shape owner howner)
  have hconst : stats.indConsts[owner]! = .const decl.types[owner].name stats.levels := by
    rw [R.materialized.consts]
    simp [hfamily]
  rw [hconst] at htype
  change D.type = _ at htype
  rw [htype]
  apply Expr.consumeTypeAnnotationsVerified_eq_of_head
    (name := decl.types[owner].name) (levels := stats.levels)
  · simp [Expr.getAppFn_mkAppN, Expr.getAppFn]
  · exact R.family_not_annotation _ (List.getElem_mem hfamily)

/-- Recover one concrete binder's strict domain translation at its exact
anonymous prefix. This inversion does not assert uniqueness for projections. -/
theorem Expr.ForallBinderAt.translation
    (Hb : Expr.ForallBinderAt source i domain)
    (Htr : TrExprS env Us Δ source (VExpr.wrapForalls domains result))
    (hi : i < domains.length) :
    TrExprS env Us (abstractForallContext (domains.take i) Δ) domain domains[i] := by
  induction Hb generalizing Δ domains result with
  | here =>
    cases domains with
    | nil => simp at hi
    | cons dom domains =>
      cases Htr with
      | forallE _ _ Hdom _ => simpa [abstractForallContext] using Hdom
  | @there body i domain name outerDomain bi Hb ih =>
    cases domains with
    | nil => simp at hi
    | cons dom domains =>
      cases Htr with
      | forallE _ _ _ Hbody =>
        have ht := ih Hbody (by simpa using hi)
        simpa [abstractForallContext, List.map_append, List.append_assoc] using ht


theorem Expr.abstractList_fullApp
    (fvars : List FVarId) (hnd : fvars.Nodup) (name : Name) (levels : List Level) :
    (mkAppN (.const name levels) (fvars.map Expr.fvar).toArray).abstractList fvars =
      Expr.mkAppList (.const name levels)
        (List.ofFn fun i : Fin fvars.length => Expr.bvar (fvars.length - 1 - i)) := by
  rw [Expr.abstractList_mkAppN, Expr.abstractList_const,
    Expr.abstractList_fvarArray fvars 0 hnd, Expr.mkAppN_eq_mkAppList]
  simp

theorem CompletedRecursorConstruction.majorBinderSource
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    Expr.ForallBinderAt
      ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
          H.params.fvars)
      H.recInfos[owner]!.indices.size
      (Expr.mkAppList
        (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name stats.levels)
        (List.ofFn fun i : Fin (stats.params.size + H.recInfos[owner]!.indices.size) =>
          Expr.bvar (stats.params.size + H.recInfos[owner]!.indices.size - 1 - i))) := by
  have hfamily : owner < decl.types.length := by simpa [H.cardinality.records] using howner
  let I := H.bindings.indices owner howner
  let M := H.bindings.major owner howner
  have hparts := (H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner).parts
  have hparams : H.params.fvars.Nodup := hparts.params
  have hindices : I.fvars.Nodup := hparts.indices
  have hmajor : M.fvars.Nodup := hparts.major
  have hcombined : (H.params.fvars ++ I.fvars).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hparams, hindices, ?_⟩
    intro a ha b hb
    exact hparts.params_later a ha b (by simp [RecInfoBindings.toRecursorLocalSelections,
      BoundFVarArray.toLocalForallSelection, I, hb])
  have hsizeI : I.fvars.length = H.recInfos[owner]!.indices.size := by
    simpa using congrArg Array.size I.expressions.symm
  have hsizeP : H.params.fvars.length = stats.params.size := by
    simpa using congrArg Array.size H.params.expressions.symm
  obtain ⟨D⟩ := M.declarationAt H.localWF 0 (by simp)
  have hlctx : LocalContext.LctxClosed H.localContext.lctx := H.recursorWF.lctxClosed
  have hDtype : Closed D.type := hlctx.cdecl D.declaration
  have Hb := (M.toLocalForallSelection H.localWF).forallBinderAtList hmajor D hDtype
    (body := .sort H.elimLevel)
  simp only [List.take_zero, Expr.abstractList] at Hb
  have hmajorClosed : Closed (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.sort H.elimLevel)) :=
    M.mkForall_closed H.localWF hmajor hlctx trivial
  have HI := I.mkForall_forallTelescopeList H.localWF
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))
    hindices hmajorClosed
  have Hclosed := (HI.prependBinderAt (Hb.abstractList I.fvars)).abstractList H.params.fvars
  simp only [Nat.add_zero, Nat.zero_add] at Hclosed
  have hdomain := Expr.abstractList_after_inner (e := D.type)
    (outer := H.params.fvars) (inner := I.fvars) (k := 0) hcombined
  simp only [Nat.zero_add, hsizeI] at hdomain
  rw [hdomain] at Hclosed
  rw [H.majorSourceType owner howner D] at Hclosed
  have hsource : mkAppN
      (mkAppN (.const decl.types[owner].name stats.levels) stats.params)
        H.recInfos[owner]!.indices =
      mkAppN (.const decl.types[owner].name stats.levels)
        ((H.params.fvars ++ I.fvars).map Expr.fvar).toArray := by
    conv => lhs; rw [H.params.expressions, I.expressions]
    simp [Expr.mkAppN_eq_mkAppList, List.map_append, Expr.mkAppList_append]
  rw [hsource, Expr.abstractList_fullApp _ hcombined] at Hclosed
  have hvars :
      (List.ofFn fun i : Fin (H.params.fvars ++ I.fvars).length =>
        Expr.bvar ((H.params.fvars ++ I.fvars).length - 1 - i)) =
      (List.ofFn fun i : Fin (stats.params.size + H.recInfos[owner]!.indices.size) =>
        Expr.bvar (stats.params.size + H.recInfos[owner]!.indices.size - 1 - i)) := by
    apply List.ext_getElem
    · simp [hsizeP, hsizeI]
    · intro i hi hj
      simp [hsizeP, hsizeI]
  rwa [hvars] at Hclosed


theorem TrExprS.const_canonicalBvars_eq
    (Hlevels : levels.mapM (VLevel.ofLevel Us) = some vlevels)
    (Htr : TrExprS env Us (abstractForallContext domains Δ)
      (Expr.mkAppList (.const name levels)
        (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i))) target)
    (hn : n ≤ domains.length) :
    target = VExpr.mkApps (.const name vlevels) (recursorCanonicalVars n) := by
  let args := List.ofFn fun i : Fin n => n - 1 - i
  have hargs : ∀ i ∈ args, i < domains.length := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    have := j.isLt
    omega
  have hsource : Expr.mkAppList (.const name levels)
      (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i)) =
      args.foldl (fun fn i => .app fn (.bvar i)) (.const name levels) := by
    rw [show (List.ofFn fun i : Fin n => Expr.bvar (n - 1 - i)) =
      args.map Expr.bvar by simp [args, List.map_ofFn, Function.comp_def]]
    simp [Expr.mkAppList_eq_foldl, List.foldl_map]
  rw [hsource] at Htr
  have heq := TrExprS.foldl_bvars_eq domains Δ args hargs (.const name levels)
    (.const name vlevels) (fun out Hconst => by
      cases Hconst with
      | const _ hlevels _ =>
        rw [Hlevels] at hlevels
        cases Option.some.inj hlevels
        rfl) Htr
  have htargets : recursorCanonicalVars n = args.map VExpr.bvar := by
    simp [recursorCanonicalVars_eq_ofFn, args, List.map_ofFn, Function.comp_def]
  simpa [VExpr.mkApps, htargets, List.foldl_map] using heq

/-- Any strict motive translation has the same major family application,
although its index domains may legitimately vary by typed equality. -/
theorem CompletedRecursorConstruction.consumedMotiveMajor
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (hindices : indices.length = H.recInfos[owner]!.indices.size)
    (hlevels : stats.levels.mapM (VLevel.ofLevel
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)) = some levels)
    (Htr : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
      ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
          H.params.fvars)
      (VExpr.wrapForalls indices (.forallE major result))) :
    major = VExpr.mkApps
      (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name levels)
      (recursorCanonicalVars (stats.params.size + H.recInfos[owner]!.indices.size)) := by
  have Hclosed := H.majorBinderSource owner howner
  have Htr' : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
      ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
          H.params.fvars)
      (VExpr.wrapForalls (indices ++ [major]) result) := by
    simpa [VExpr.wrapForalls_append, VExpr.wrapForalls] using Htr
  have Hdomain := Hclosed.translation Htr' (by simp [hindices])
  have htake : (indices ++ [major]).take H.recInfos[owner]!.indices.size = indices := by
    rw [← hindices]
    simp
  have hget : (indices ++ [major])[H.recInfos[owner]!.indices.size]'(by simp [hindices]) = major := by
    simp [← hindices]
  rw [htake, hget] at Hdomain
  have Hdomain' : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (H.parameterSuffix.parameterDecls.toCtx.reverse ++ indices) [])
      (Expr.mkAppList (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name
        stats.levels)
        (List.ofFn fun i : Fin (stats.params.size + H.recInfos[owner]!.indices.size) =>
          Expr.bvar (stats.params.size + H.recInfos[owner]!.indices.size - 1 - i))) major := by
    simpa [abstractForallContext, List.map_append, List.append_assoc] using Hdomain
  apply TrExprS.const_canonicalBvars_eq hlevels Hdomain'
  have hlength := Lean4Lean.List.Forall₂.length_eq H.parameterSuffix.cached
  have hctxLength := checkInductiveTypes.loopType.CachedParameterDecl.forall₂_toCtx_length
    H.parameterSuffix.cached
  simp only [List.length_append, List.length_reverse, hctxLength, hindices]
  simpa using Nat.le_of_eq (congrArg (· + H.recInfos[owner]!.indices.size)
    (by simpa using hlength))



/-- The complete consumed motive is reconstructed from its actual index
translations. The major application is derived, not chosen independently. -/
theorem CompletedRecursorConstruction.consumedMotive
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner H.recInfos[owner]! H.elimLevel,
      ∃ indices level,
        indices.length = H.recInfos[owner]!.indices.size ∧
        VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams) H.elimLevel = some level ∧
        let motive := VExpr.wrapForalls indices (.forallE
          (VExpr.mkApps (.const (decl.types[owner]'(by simpa [H.cardinality.records] using howner)).name
            S.canonical.levels)
            (recursorCanonicalVars (stats.params.size + H.recInfos[owner]!.indices.size)))
          (.sort level))
        TrExprS H.recursorWF.venv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse [])
          ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major] (.sort H.elimLevel))).abstractList
            H.params.fvars) motive ∧
        H.recursorWF.venv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          H.parameterSuffix.parameterDecls.toCtx motive ∧
        H.recursorWF.venv.IsDefEqU
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          H.parameterSuffix.parameterDecls.toCtx motive S.canonical.motiveType := by
  obtain ⟨S, indices, major, level, hindices, hlevel, Htr, Htype, Heq⟩ :=
    H.consumedMotiveDomains owner howner
  have hmajor := H.consumedMotiveMajor owner howner hindices
    S.canonical.levels_translation Htr
  rw [hmajor] at Htr Htype Heq
  exact ⟨S, indices, level, hindices, hlevel, Htr, Htype, Heq⟩

end Lean4Lean.VerifyInductive
