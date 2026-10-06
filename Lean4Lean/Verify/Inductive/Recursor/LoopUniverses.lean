import Lean4Lean.Verify.Inductive.Recursor.UniverseScope
import Lean4Lean.Verify.Inductive.Recursor.ReplayCompat
import Lean4Lean.Verify.Inductive.Recursor.FieldTypeScope

/-! Universe support of the `loopUArgs` traversal.

The executable `loopUArgs` infers the type of a recursive field, normalizes it
and then repeatedly opens a forall binder and normalizes the instantiated body.
Each of these type-checker calls preserves the universe-parameter support of
its input (`VContext.LevelsBelow`), relative to any universe scope of the
local context.  Starting from a universe scope in which the inferred field
type lives, every argument declaration opened by the traversal, and the
exposed family application, therefore mention only the universe parameters
of that scope.  These lemmas only need the recursor context and the
`loopUArgs` trace, so they sit below the second pass, which retains their
conclusion in each generated recursive-call row. -/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive


def FieldUniverseSupport (params : List Name) (c : AddInductive.Context) (fields : Array Expr) : Prop :=
  ∀ e ∈ fields, ∃ fv index name type bi kind,
    e = .fvar fv ∧ c.lctx.find? fv = some (.cdecl index fv name type bi kind) ∧
      type.levelParamsIn params = true

private theorem fieldUniverseSupport_push
    (Hc : BindingContextWF c) (H : FieldUniverseSupport params c fields)
    (hdom : dom.levelParamsIn params = true) :
    FieldUniverseSupport params { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name dom bi }
      (fields.push (.fvar ⟨c.ngen.curr⟩)) := by
  intro e he
  simp only [Array.mem_push] at he
  have hnew : (c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name dom bi).find? ⟨c.ngen.curr⟩ =
      some (.cdecl c.lctx.decls.size ⟨c.ngen.curr⟩ name dom bi .default) := by
    simp [LocalContext.mkLocalDecl, LocalContext.find?, Hc.wf.map_wf.find?_insert]
  rcases he with he | rfl
  · obtain ⟨fv, index, oldName, type, oldBi, kind, rfl, hfind, htype⟩ := H e he
    by_cases hfv : fv = ⟨c.ngen.curr⟩
    · subst fv
      exact ⟨_, _, _, _, _, _, rfl, hnew, hdom⟩
    · refine ⟨fv, index, oldName, type, oldBi, kind, rfl, ?_, htype⟩
      simpa [LocalContext.mkLocalDecl, LocalContext.find?, Hc.wf.map_wf.find?_insert,
        Ne.symm hfv] using hfind
  · exact ⟨_, _, _, _, _, _, rfl, hnew, hdom⟩

theorem RecursorFieldDecisions.levelParamsIn
    (H : RecursorFieldDecisions stats root source current terminal fields selected positions)
    (Hroot : BindingContextWF root) (hsource : source.levelParamsIn params = true) :
    terminal.levelParamsIn params = true ∧ FieldUniverseSupport params current fields := by
  induction H with
  | nil => exact ⟨hsource, by intro e he; simp at he⟩
  | @nonrecursive c name dom body bi fields selected positions H _ ih
  | @recursive c name dom body bi fields selected positions target H _ ih =>
    have Hc := (H.freshBindings Hroot).choose
    have hx : dom.levelParamsIn params = true ∧ body.levelParamsIn params = true := by
      simpa [Expr.levelParamsIn] using ih.1
    have hdom := hx.1
    have hbody := hx.2
    refine ⟨?_, fieldUniverseSupport_push Hc ih.2
      (Expr.levelParamsIn_consumeTypeAnnotationsVerified hdom)⟩
    simpa using hbody

theorem FieldUniverseSupport.mono
    (H : FieldUniverseSupport params c fields) (Hfields : BoundFVarArray c fields)
    (hle : BindingContextLE c c') : FieldUniverseSupport params c' fields := by
  intro e he
  obtain ⟨fv, index, name, type, bi, kind, rfl, hfind, htype⟩ := H e he
  have hfv : fv ∈ c.lctx.fvars := by
    rw [Hfields.expressions] at he
    simp only [List.mem_toArray, List.mem_map, Expr.fvar.injEq] at he
    obtain ⟨fv', hfv', rfl⟩ := he
    exact Hfields.members _ hfv'
  exact ⟨fv, index, name, type, bi, kind, rfl, (hle.declarations fv hfv).trans hfind, htype⟩

theorem FieldUniverseSupport.mkForall
    (H : FieldUniverseSupport params c fields) (Hfields : BoundFVarArray c fields)
    (hbody : body.levelParamsIn params = true) :
    (c.lctx.mkForall fields body).levelParamsIn params = true := by
  have hdecl : ∀ fv ∈ Hfields.fvars, ∃ index name type bi kind,
      c.lctx.find? fv = some (.cdecl index fv name type bi kind) ∧ type.levelParamsIn params = true := by
    intro fv hfv
    have he : Expr.fvar fv ∈ fields := by
      rw [Hfields.expressions]
      simpa using hfv
    obtain ⟨fv', index, name, type, bi, kind, heq, hfind, htype⟩ := H _ he
    cases Expr.fvar.inj heq
    exact ⟨index, name, type, bi, kind, hfind, htype⟩
  have hgo : ∀ fvars : List FVarId, (∀ fv ∈ fvars, fv ∈ Hfields.fvars) →
      ∀ body : Expr, body.levelParamsIn params = true →
      (LocalContext.mkBindingListN.go false c.lctx fvars body).levelParamsIn params = true := by
    intro fvars hmem body hbody
    induction fvars generalizing body with
    | nil => exact hbody
    | cons fv fvars ih =>
      obtain ⟨index, name, type, bi, kind, hfind, htype⟩ := hdecl fv (hmem _ (by simp))
      apply ih (fun other hother => hmem other (by simp [hother]))
      simpa [LocalContext.mkBindingList1N, hfind, Expr.levelParamsIn, htype] using hbody
  rw [Hfields.expressions, LocalContext.mkForall, LocalContext.mkBinding_eqN]
  apply hgo Hfields.fvars.reverse (by simp) _
  simpa using hbody

theorem Expr.getAppArgs_slice_toList (e : Expr) (n : Nat) :
    ((e.getAppArgs[n:] : Array Expr)).toList = e.getAppArgsList.drop n := by
  rw [← Expr.getAppArgs_toList]
  let suffix := e.getAppArgs.toSubarray n
  calc
    (Std.Slice.toArray suffix).toList = suffix.toList := by
      exact (congrArg Array.toList
        (Subarray.toArray_eq_sliceToArray (s := suffix)).symm).trans
          Subarray.toList_toArray
    _ = e.getAppArgs.toList.drop n := by
      rw [List.drop_eq_drop_min]
      simp only [suffix, Subarray.toList_eq, Array.array_toSubarray,
        Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
        Array.toList_extract, List.extract_eq_take_drop,
        Array.length_toList]
      apply List.take_of_length_le
      simp

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

/-- Checked constructor tails are translated at the declaration's universe
parameters. -/
theorem CheckedRecursorConstructorTails.levelParamsIn
    (H : CheckedRecursorConstructorTails env Us scope stats decl indTypes)
    (familyIdx : Nat) (hfamily : familyIdx < indTypes.size)
    (ctor : Constructor) (hctor : ctor ∈ indTypes[familyIdx].ctors)
    (tail : Expr) (Hprefix : RecursorParamPrefix stats 0 ctor.type tail) :
    tail.levelParamsIn Us = true := by
  rcases List.mem_iff_getElem.mp hctor with ⟨ctorIdx, hctorIdx, rfl⟩
  obtain ⟨_, tail', _, _, _, _, Hprefix', _, Htail', _⟩ :=
    H.replay familyIdx hfamily ctorIdx hctorIdx
  rw [Hprefix.tail_eq Hprefix']
  exact Htail'.levelParamsIn

/-! ### Retained recursive calls -/

/-- Universe support of the payload of one `loopUArgs` traversal: the
argument telescope closed over the opened arguments and the exposed family
arguments mention only `Us`, provided the inferred field type does and lies
in a universe scope `P` of the root context. -/
theorem RecursorLoopUArgsInput.callUniverses
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    {root : AddInductive.Context} {fv : FVarId}
    (Hinput : RecursorLoopUArgsInput root (.fvar fv))
    {current : AddInductive.Context} {exposed : Expr} {args : Array Expr}
    (trace : RecursorLoopUArgsPrefix root Hinput.normalizedType current exposed args)
    {recLparams : List Name} (Rroot : RecursorContextWF root recLparams)
    {Us : List Name} {P : FVarId → Prop} (hscope : Rroot.typeChecker.UniverseScope Us P)
    {fieldTarget : VExpr}
    (hfield : TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx (.fvar fv) fieldTarget)
    (hinferredU : Hinput.inferredType.levelParamsIn Us = true)
    (hinferredP : Hinput.inferredType.FVarsIn P)
    (Hargs : FreshBoundFVarArray root current args)
    (Hcurrent : BindingContextWF current) (n : Nat) :
    (current.lctx.mkForall args (.sort .zero)).levelParamsIn Us = true ∧
      ∀ e ∈ (exposed.getAppArgs[n:] : Array Expr).toList, e.levelParamsIn Us = true := by
  obtain ⟨inferredTarget, _, _, hinferredTr, hfieldTyping⟩ :=
    inferTypeFVarInRecursorContext.WF Rroot hfield _ Hinput.inference
  have hinferredType : Rroot.venv.IsType recLparams.length
      Rroot.mlctx.vlctx.toCtx inferredTarget :=
    hfieldTyping.isType Rroot.checking.tr.wf Rroot.mlctx_wf.tr.wf.toCtx
  obtain ⟨hnormalizedBelow, hnormalizedTr⟩ :=
    whnfInRecursorContext.scopeWF Rroot hinferredTr _ Hinput.normalization
  have hnormalizedU : Hinput.normalizedType.levelParamsIn Us = true :=
    whnfInRecursorContext.levelsWF Rroot hinferredTr _ Hinput.normalization Us P hscope
      hinferredU hinferredP
  have hnormalizedP : Hinput.normalizedType.FVarsIn P :=
    hnormalizedBelow P hscope.1 hinferredP
  obtain ⟨Rcurrent, P', _, _, _, hsc', hexposedU, _, hargs⟩ :=
    trace.universeSupport hconsume Rroot hscope hnormalizedTr hinferredType
      hnormalizedU hnormalizedP
  refine ⟨?_, ?_⟩
  · have hargTypes : ∀ x ∈ Hargs.fvars, ∀ decl,
        current.lctx.find? x = some decl → decl.type.levelParamsIn Us = true := by
      intro x hx decl hdecl
      have hxArg : Expr.fvar x ∈ args.toList := by
        rw [Hargs.expressions]
        simpa using hx
      obtain ⟨y, hy, hyP⟩ := hargs _ hxArg
      cases hy
      have hdecl' : Rcurrent.typeChecker.lctx'.find? x = some decl := by
        change Rcurrent.mlctx.lctx.find? x = some decl
        rw [Rcurrent.lctx_eq]
        exact hdecl
      exact (hsc'.2 x decl hyP hdecl').1
    exact Hargs.toBoundFVarArray.mkForall_levelParamsIn Hcurrent Hargs.nodup hargTypes
      (by simp [Expr.levelParamsIn, Level.paramsIn])
  · intro e he
    rw [Expr.getAppArgs_slice_toList] at he
    exact Expr.levelParamsIn_of_mem_getAppArgsList hexposedU (List.mem_of_mem_drop he)

end VerifyInductive
end Lean4Lean
