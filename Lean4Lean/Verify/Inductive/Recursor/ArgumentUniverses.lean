import Lean4Lean.Verify.Inductive.Recursor.ConsumedGenerationAssembly
import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldUniverses

/-! Universe support of the higher-order argument telescope of an induction
hypothesis.

The executable `loopUArgs` infers the type of a recursive field, normalizes it
and then repeatedly opens a forall binder and normalizes the instantiated body.
Each of these type-checker calls preserves the universe-parameter support of
its input (`VContext.LevelsBelow`), relative to any universe scope of the
local context.  Starting from a universe scope containing the field, every
argument declaration opened by the traversal, and the exposed family
application, therefore mention only the universe parameters of that scope. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-! ### Type-checker runs in a recursor context -/

/-- `whnf` in a recursor context preserves the universe support of its input. -/
theorem whnfInRecursorContext.levelsWF
    (Hc : RecursorContextWF c recLparams)
    (he : TrExprS Hc.venv recLparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      Hc.typeChecker.LevelsBelow e e₁ := by
  change (TypeChecker.M.run c.env c.safety c.lctx
    (c.typeCheckerLParams.getD c.lparams) c.fuel
    (TypeChecker.whnf e)).WF _
  rw [Hc.typeCheckerLParams_eq]
  rw [← Hc.lctx_eq]
  have Hx : TypeChecker.M.WF Hc.typeChecker {}
      (TypeChecker.whnf e) (fun e₁ _ => Hc.typeChecker.LevelsBelow e e₁) :=
    (TypeChecker.Inner.whnf.WF_levels he).run
  exact TypeChecker.M.WF.runCheckingValidMLC
    (lparams := recLparams) (fuel := c.fuel)
    Hc.kernelFresh Hx

/-- Type inference of a free variable in a recursor context preserves the
universe support of its input. -/
theorem inferTypeFVarInRecursorContext.levelsWF
    (Hc : RecursorContextWF c recLparams)
    (he : TrExprS Hc.venv recLparams Hc.mlctx.vlctx (.fvar fv) e') :
    ((monadLift (TypeChecker.inferType (.fvar fv)) :
        AddInductive.M Expr) c).WF fun ty =>
      Hc.typeChecker.LevelsBelow (.fvar fv) ty := by
  change (TypeChecker.M.run c.env c.safety c.lctx
    (c.typeCheckerLParams.getD c.lparams) c.fuel
    (TypeChecker.inferType (.fvar fv))).WF _
  rw [inferTypeFVar_lparams_compat c.env c.safety c.lctx
    (c.typeCheckerLParams.getD c.lparams) recLparams c.fuel fv]
  rw [← Hc.lctx_eq]
  have Hx : TypeChecker.M.WF Hc.typeChecker {}
      (TypeChecker.inferType (.fvar fv)) (fun ty _ =>
        Hc.typeChecker.LevelsBelow (.fvar fv) ty) :=
    (TypeChecker.Inner.inferType.WF_levels he).run
  exact TypeChecker.M.WF.runCheckingValidMLC
    (lparams := recLparams) (fuel := c.fuel)
    Hc.kernelFresh Hx

/-! ### The `loopUArgs` traversal -/

/-- Universe support along an exact `loopUArgs.loop` trace.  If the
normalized input type lies in a universe scope `P` of a recursor context and
mentions only `Us`, then at the terminal context of the trace there is a
universe scope containing every opened argument, and the exposed type mentions
only `Us` and lies in that scope. -/
theorem RecursorLoopUArgsPrefix.universeSupport
    (hconsume : RecursorConsumeTypeAnnotationsCompat) {Us : List Name}
    {root : AddInductive.Context} {source : Expr}
    {current : AddInductive.Context} {exposed : Expr} {args : Array Expr}
    (trace : RecursorLoopUArgsPrefix root source current exposed args)
    {recLparams : List Name} (Rroot : RecursorContextWF root recLparams)
    {P : FVarId → Prop} (hscope : Rroot.typeChecker.UniverseScope Us P)
    {sourceTarget : VExpr}
    (hsource : TrExpr Rroot.venv recLparams Rroot.mlctx.vlctx source sourceTarget)
    (hsourceType : Rroot.venv.IsType recLparams.length Rroot.mlctx.vlctx.toCtx
      sourceTarget)
    (hsourceU : source.levelParamsIn Us = true) (hsourceP : source.FVarsIn P) :
    ∃ (Rcurrent : RecursorContextWF current recLparams) (P' : FVarId → Prop)
      (T : VExpr),
      TrExpr Rcurrent.venv recLparams Rcurrent.mlctx.vlctx exposed T ∧
      Rcurrent.venv.IsType recLparams.length Rcurrent.mlctx.vlctx.toCtx T ∧
      Rcurrent.typeChecker.UniverseScope Us P' ∧
      exposed.levelParamsIn Us = true ∧ exposed.FVarsIn P' ∧
      ∀ a ∈ args.toList, ∃ fv, a = .fvar fv ∧ P' fv := by
  induction trace with
  | root => exact ⟨Rroot, P, _, hsource, hsourceType, hscope, hsourceU, hsourceP, by simp⟩
  | @push current next args name domain body normalized bi _previous next_eq
      normalization ih =>
    obtain ⟨R, P', T, htype, htypeType, hsc, hU, hP, hargs⟩ := ih
    subst next_eq
    rcases TrExpr.forallE_source htype with
      ⟨sourceDom, sourceBody, hdom, hbody, hdomType, hbodyType, hforallEq⟩
    rcases hconsume current recLparams R hdom hdomType with ⟨consumedDom, Hdom⟩
    rcases Hdom.body R hbody with ⟨consumedBody, hbodyConsumed, hbodyEq⟩
    let x : FVarId := ⟨current.ngen.curr⟩
    let R' := R.withLocalDecl (name := name) (bi := bi) Hdom.consumed Hdom.isType
    have hopened := R.instantiateFresh (name := name) (bi := bi)
      Hdom.consumed Hdom.isType hbodyConsumed
    simp only [Expr.levelParamsIn, Bool.and_eq_true] at hU
    have hdomP : domain.FVarsIn P' := hP.1
    have hbodyP : body.FVarsIn P' := hP.2
    let P'' : FVarId → Prop := fun fv => fv = x ∨ P' fv
    have hsc' : R'.typeChecker.UniverseScope Us P'' := by
      refine TypeChecker.VContext.UniverseScope.cons (x := x)
        (deps := domain.consumeTypeAnnotationsVerified.fvarsList)
        (d := .vlam consumedDom) rfl ?_ R.current_not_mem hsc ?_ ?_
      · intro fv hne
        change (TypeChecker.MLCtx.vlam x name domain.consumeTypeAnnotationsVerified
          consumedDom bi R.mlctx).lctx.find? fv = R.mlctx.lctx.find? fv
        have hwf : (TypeChecker.MLCtx.vlam x name domain.consumeTypeAnnotationsVerified
            consumedDom bi R.mlctx).WF R.venv recLparams := R'.mlctx_wf
        rw [hwf.find?_eq, R.mlctx_wf.find?_eq]
        have hbeq : (fv == x) = false := by simpa using hne
        simp [TypeChecker.MLCtx.decls, LocalDecl.fvarId, hbeq]
      · intro dep hdep
        exact (fvarsIn_iff.mp
          (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomP)).1 dep hdep
      · intro decl hdecl
        have hself := R'.mlctx_wf.find?_vlam_self
        change (TypeChecker.MLCtx.vlam x name domain.consumeTypeAnnotationsVerified
          consumedDom bi R.mlctx).lctx.find? x = some decl at hdecl
        rw [hself] at hdecl
        cases hdecl
        exact ⟨Expr.levelParamsIn_consumeTypeAnnotationsVerified hU.1,
          fun v hv => by simp [LocalDecl.value?] at hv⟩
    have hinstU : (body.instantiate1 (.fvar x)).levelParamsIn Us = true := by
      rw [Expr.instantiate1_eq]
      exact Expr.levelParamsIn_instantiate1 hU.2 rfl
    have hinstP : (body.instantiate1 (.fvar x)).FVarsIn P'' := by
      rw [Expr.instantiate1_eq]
      exact (hbodyP.mono fun _ h => Or.inr h).instantiate1 (by
        simp [FVarsIn])
    have hscopeRun := (whnfInRecursorContext.scopeWF R' hopened) normalized normalization
    have hlevelRun := (whnfInRecursorContext.levelsWF R' hopened) normalized normalization
    have hbodyEq' := Hdom.bodyDefEqConsumed R hbodyEq
    have hsourceBodyType : R'.venv.IsType recLparams.length
        R'.mlctx.vlctx.toCtx sourceBody := by
      let hctxEq : VLCtx.IsDefEq R.venv recLparams.length
          ((none, .vlam sourceDom) :: R.mlctx.vlctx)
          ((none, .vlam consumedDom) :: R.mlctx.vlctx) :=
        VLCtx.IsDefEq.cons
          (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) nofun
          (.vlam Hdom.source_defeq.choose_spec)
      simpa only [R', RecursorContextWF.withLocalDecl_venv,
        RecursorContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using
        hbodyType.defeqDFC R.checking.tr.wf.ordered hctxEq.defeqCtx
    have hconsumedBodyType : R'.venv.IsType recLparams.length
        R'.mlctx.vlctx.toCtx consumedBody := by
      apply hsourceBodyType.defeqU_l R'.checking.tr.wf
        R'.mlctx_wf.tr.wf.toCtx
      simpa only [R', RecursorContextWF.withLocalDecl_venv,
        RecursorContextWF.withLocalDecl_toCtx, VLCtx.toCtx] using hbodyEq'
    refine ⟨R', P'', consumedBody, hscopeRun.2, hconsumedBodyType, hsc',
      hlevelRun Us P'' hsc' hinstU hinstP, hscopeRun.1 P'' hsc'.1 hinstP, ?_⟩
    intro a ha
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · obtain ⟨fv, rfl, hfv⟩ := hargs a ha
      exact ⟨fv, rfl, Or.inr hfv⟩
    · exact ⟨x, rfl, Or.inl rfl⟩

/-! ### Closed telescopes -/

theorem Expr.forallDomainList_levelParamsIn {Us : List Name} :
    ∀ (n : Nat) {e : Expr}, e.levelParamsIn Us = true →
      ∀ d ∈ Expr.forallDomainList n e, d.levelParamsIn Us = true
  | 0, _, _ => by simp [Expr.forallDomainList]
  | n + 1, e, h => by
    cases e with
    | forallE name dom body bi =>
      simp only [Expr.levelParamsIn, Bool.and_eq_true] at h
      intro d hd
      simp only [Expr.forallDomainList, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact h.1
      · exact Expr.forallDomainList_levelParamsIn n h.2 d hd
    | _ => simp [Expr.forallDomainList]

theorem LocalContext.levelParamsIn_mkForall_foldN
    {lctx : LocalContext} {fvars : List FVarId} {Us : List Name}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind) ∧
        type.levelParamsIn Us = true)
    {body : Expr} (hbody : body.levelParamsIn Us = true) :
    (fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
      (result.abstractN [fv])) body).levelParamsIn Us = true := by
  induction fvars with
  | nil => exact hbody
  | cons fv fvars ih =>
    obtain ⟨index, name, type, bi, kind, hfind, htype⟩ := hdecl fv (by simp)
    have ih' := ih (fun other hother => hdecl other (by simp [hother]))
    simp only [List.foldr_cons, LocalContext.mkBindingList1N, hfind,
      Bool.false_eq_true, ↓reduceIte, Expr.levelParamsIn, Bool.and_eq_true,
      Expr.levelParamsIn_abstractN]
    exact ⟨htype, ih'⟩

/-- A telescope closed over bound ordinary declarations whose types mention
only `Us` mentions only `Us` when its body does. -/
theorem BoundFVarArray.mkForall_levelParamsIn
    (H : BoundFVarArray c xs) (Hc : BindingContextWF c)
    (hnodup : H.fvars.Nodup) {Us : List Name}
    (htypes : ∀ fv ∈ H.fvars, ∀ decl, c.lctx.find? fv = some decl →
      decl.type.levelParamsIn Us = true)
    {body : Expr} (hbody : body.levelParamsIn Us = true) :
    (c.lctx.mkForall xs body).levelParamsIn Us = true := by
  have hdecl : ∀ fv ∈ H.fvars, ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) ∧
        type.levelParamsIn Us = true := by
    intro fv hfv
    obtain ⟨index, name, type, bi, kind, h⟩ := Hc.findCDecl fv (H.members fv hfv)
    exact ⟨index, name, type, bi, kind, h, htypes fv hfv _ h⟩
  have hfind : ∀ fv ∈ H.fvars, ∃ decl, c.lctx.find? fv = some decl := by
    intro fv hfv
    obtain ⟨index, name, type, bi, kind, h, _⟩ := hdecl fv hfv
    exact ⟨_, h⟩
  rw [H.expressions, LocalContext.mkForall, LocalContext.mkBinding_eqN,
    LocalContext.mkBindingListN_eq_fold hfind hnodup]
  exact LocalContext.levelParamsIn_mkForall_foldN hdecl hbody

/-! ### Induction-hypothesis origins -/

/-- The argument domains and exposed indices of a first-pass induction
hypothesis origin mention only `Us`, provided its root context is a recursor
context with a universe scope `P` for `Us` containing the recursive field. -/
theorem RecInfoMinorHypothesisTypeOrigin.universeSupport
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    {stats : AddInductive.InductiveStats} {recInfos : Array AddInductive.RecInfo}
    {root : AddInductive.Context} {field type : Expr}
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type)
    {recLparams : List Name} (Rroot : RecursorContextWF root recLparams)
    {Us : List Name} {P : FVarId → Prop} (hscope : Rroot.typeChecker.UniverseScope Us P)
    {fv : FVarId} (hfv : field = .fvar fv) (hfvP : P fv) {fieldTarget : VExpr}
    (hfield : TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx (.fvar fv) fieldTarget) :
    (∀ d ∈ O.argDomains, d.levelParamsIn Us = true) ∧
      (∀ e ∈ (O.exposedType.getAppArgs[stats.params.size:] : Array Expr).toList,
        e.levelParamsIn Us = true) := by
  have hinference := O.loopInput.inference
  have hnormalization := O.loopInput.normalization
  subst hfv
  obtain ⟨inferredTarget, hbelow, _, hinferredTr, hfieldTyping⟩ :=
    inferTypeFVarInRecursorContext.WF Rroot hfield _ hinference
  have hfieldP : (Expr.fvar fv).FVarsIn P := by simpa [FVarsIn] using hfvP
  have hinferredU : O.loopInput.inferredType.levelParamsIn Us = true :=
    inferTypeFVarInRecursorContext.levelsWF Rroot hfield _ hinference Us P hscope rfl hfieldP
  have hinferredP : O.loopInput.inferredType.FVarsIn P := hbelow P hscope.1 hfieldP
  have hinferredType : Rroot.venv.IsType recLparams.length
      Rroot.mlctx.vlctx.toCtx inferredTarget :=
    hfieldTyping.isType Rroot.checking.tr.wf Rroot.mlctx_wf.tr.wf.toCtx
  obtain ⟨hnormalizedBelow, hnormalizedTr⟩ :=
    whnfInRecursorContext.scopeWF Rroot hinferredTr _ hnormalization
  have hnormalizedU : O.loopInput.normalizedType.levelParamsIn Us = true :=
    whnfInRecursorContext.levelsWF Rroot hinferredTr _ hnormalization Us P hscope
      hinferredU hinferredP
  have hnormalizedP : O.loopInput.normalizedType.FVarsIn P :=
    hnormalizedBelow P hscope.1 hinferredP
  obtain ⟨Rcurrent, P', _, _, _, hsc', hexposedU, _, hargs⟩ :=
    O.loopTrace.universeSupport hconsume Rroot hscope hnormalizedTr hinferredType
      hnormalizedU hnormalizedP
  have hindices : ∀ e ∈ (O.exposedType.getAppArgs[stats.params.size:] : Array Expr).toList,
      e.levelParamsIn Us = true := by
    intro e he
    rw [Expr.getAppArgs_slice_toList] at he
    exact Expr.levelParamsIn_of_mem_getAppArgsList hexposedU (List.mem_of_mem_drop he)
  refine ⟨?_, hindices⟩
  -- Every opened argument is declared with a type in `Us`.
  have hargTypes : ∀ x ∈ O.arguments_bound.fvars, ∀ decl,
      O.current.lctx.find? x = some decl → decl.type.levelParamsIn Us = true := by
    intro x hx decl hdecl
    have hxArg : Expr.fvar x ∈ O.args.toList := by
      rw [O.arguments_bound.expressions]
      simpa using hx
    obtain ⟨y, hy, hyP⟩ := hargs _ hxArg
    cases hy
    have hdecl' : Rcurrent.typeChecker.lctx'.find? x = some decl := by
      change Rcurrent.mlctx.lctx.find? x = some decl
      rw [Rcurrent.lctx_eq]
      exact hdecl
    exact (hsc'.2 x decl hyP hdecl').1
  -- The motive application mentions only `Us`.
  have hmotiveApp : (Expr.app
      (mkAppN recInfos[O.ownerIdx]!.motive O.exposedType.getAppArgs[stats.params.size:])
      (mkAppN (.fvar fv) O.args)).levelParamsIn Us = true := by
    obtain ⟨m, hm, _⟩ := O.motive_is_fvar
    simp only [Expr.levelParamsIn, Bool.and_eq_true, Expr.mkAppN_eq_mkAppList]
    refine ⟨Expr.levelParamsIn_mkAppList (by rw [hm]; rfl) hindices,
      Expr.levelParamsIn_mkAppList rfl ?_⟩
    intro a ha
    obtain ⟨y, rfl, _⟩ := hargs a ha
    rfl
  have htypeU : type.levelParamsIn Us = true := by
    rw [O.type_eq]
    exact O.arguments_bound.toBoundFVarArray.mkForall_levelParamsIn O.current_wf
      O.arguments_bound.nodup hargTypes hmotiveApp
  exact Expr.forallDomainList_levelParamsIn _ htypeU

/-! ### The completed construction -/

section
variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}

/-- The root-context evidence consumed by `argumentUniverses_of_rootScopes`:
the root of every quantified hypothesis origin is a recursor context with a
universe scope for the declaration's universe parameters that contains the
recursive field.  `ArgumentUniverses` quantifies over arbitrary roots, so this
evidence is only available for the origins retained by the producer, where it
is the parameters together with the fields before the recursive one
(`RecursorFieldPrefixScope`). -/
def CompletedRecursorConstruction.ArgumentRootScopes (H : CompletedRecursorConstruction R) :
    Prop :=
  ∀ owner (howner : owner < H.recInfos.size) localIndex
    (hlocal : localIndex < H.origins.minorTypes[owner]!.size)
    (origins : RecInfoMinorHypothesisTypeOrigins
      (H.origins.minorShapes owner howner localIndex hlocal).sourceFullContext
      (H.origins.minorShapes owner howner localIndex hlocal).recursiveFields
      (H.origins.minorShapes owner howner localIndex hlocal).hypotheses),
    (H.origins.minorShapes owner howner localIndex hlocal).hypothesis_type_origins = some origins →
    ∀ (j : Nat) (root : AddInductive.Context) (sourceType : Expr)
      (_O : RecInfoMinorHypothesisTypeOrigin origins.stats origins.recInfos root
        ((H.origins.minorShapes owner howner localIndex hlocal).recursiveFields[j]!) sourceType),
      ∃ (recLparams : List Name) (Rroot : RecursorContextWF root recLparams)
        (P : FVarId → Prop) (fv : FVarId) (fieldTarget : VExpr),
        Rroot.typeChecker.UniverseScope c.lparams P ∧
        (H.origins.minorShapes owner howner localIndex hlocal).recursiveFields[j]! = .fvar fv ∧
        P fv ∧
        TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx (.fvar fv) fieldTarget

theorem CompletedRecursorConstruction.argumentUniverses_of_rootScopes
    (H : CompletedRecursorConstruction R)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (HS : H.ArgumentRootScopes) : H.ArgumentUniverses := by
  intro owner howner localIndex hlocal origins horig j root sourceType O
  obtain ⟨_, Rroot, P, fv, _, hscope, hfv, hfvP, hfield⟩ :=
    HS owner howner localIndex hlocal origins horig j root sourceType O
  exact O.universeSupport hconsume Rroot hscope hfv hfvP hfield

end

end Lean4Lean.VerifyInductive
