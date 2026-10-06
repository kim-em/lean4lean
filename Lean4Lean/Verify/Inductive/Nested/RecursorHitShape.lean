import Lean4Lean.Verify.Inductive.Nested.HitShape
import Lean4Lean.Verify.Inductive.Recursor.FieldDeclarationTypes
import Lean4Lean.Verify.Inductive.Recursor.ArgumentUniverses
import Lean4Lean.Verify.Inductive.Nested.FinalAssembly

/-! # Hit-shape provenance of generated recursor types and rule right-hand sides

The lowered recursor types and rule right-hand sides of a nested run are restored by
`restoreNested`, which agrees with the abstract restoration exactly when every node headed
by an auxiliary family or constructor (a *hit*) has the parameter variables as its first
`nparams` arguments and the declaration's level parameters as its levels
(`Expr.HitShape`, `Lean4Lean/Verify/Inductive/Nested/HitShape.lean`). This file proves that
the executable's generated recursors have this shape:

* `CompletedRecursorConstruction.recursorTypeHitShape` and `ruleRhsHitShape`: for every owner,
  the recursor type `(lctx.mkForall params motives minors indices major ...).inferImplicit`
  and every rule right-hand side `blueprint.build ...` are `Expr.HitShapeTele heads nparams ls`.
* `CompletedRecursorPhasesResult.generatedHitShape`: the same for each installed
  `GeneratedRecursorEntry`.
* `NestedValidatedRunResult.recursorHitShape` (with projections `recursorTypeHitShape`,
  `ruleRhsHitShape`): the same for the recursor read back by any restoration step of an exact
  validated nested run, at `result.nparams` and `lparams.map Level.param`.

The hits come from three sources.

* (a) Recursor-built hits: the major premise domains `I params indices`, the motives'
  major binders, and the minor premises' constructor applications `c params fields`. These
  are read off `RecInfoMajorTypeShapes`, `RecInfoMotiveTypeShapes` and
  `RecInfoMinorSourceAlignment`; the head is a hit exactly when it is auxiliary, and
  `Expr.HitShape.mkAppN_const_params` treats both cases uniformly.
* (b) Constructor field domains (minor premises and rule field lambdas): the field loop does
  no `whnf`, so each declared field type is the consumed domain of the lowered constructor
  type after instantiating its parameters (`RecursorParamPrefix.hitShape`,
  `RecursorFieldDecisions.fieldDeclsSatisfy` in `Recursor/FieldDeclarationTypes.lean`).
  The lowered constructor types themselves are parameter telescopes in hit shape by
  `LoweredConstructorMapping.hitShapeTele` (from `NestedExprMapping.hitShape`).
* (c) The `whnf`-produced regions: index domains (R1, `loopArgs1`), induction-hypothesis
  binder domains (R2) and their exposed indices (R3, `loopUArgs`). R1 follows along the
  retained `loopArgs1` traces (`RecursorIndexTrace.hitShape`, from the family header), R2
  and R3 along the retained `loopUArgs` traces (`RecursorLoopUArgsPrefix.hitShape`,
  `RecInfoMinorHypothesisTypeOrigin.hitShape`, rooted by
  `RecInfoCallBlueprintOrigins.rooted`), all from the single hypothesis
  `WhnfHitShapeFacts` on the lifted `whnf` calls.

Remaining hypotheses are collected in `CompletedRecursorConstruction.HitShapeInputs`; see
its docstring. -/

namespace Lean.Expr

open Lean4Lean

/-! ### Generic hit-shape lemmas -/

private theorem getAppFn_mkAppList'' (f : Expr) (l : List Expr) :
    (f.mkAppList l).getAppFn = f.getAppFn := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih => simp only [mkAppList]; rw [ih]; rfl

private theorem getAppFn_getAppFn (e : Expr) : e.getAppFn.getAppFn = e.getAppFn := by
  induction e <;> simp_all [getAppFn]

namespace HitShape

variable {heads : List Name} {params : List Expr} {ls : List Level}

/-- Every application argument of a shaped expression is shaped, provided the
parameters are free variables: at a hit the arguments are the parameters and
shaped trailing arguments, and otherwise the spine is traversed structurally. -/
theorem of_mem_getAppArgsList {e : Expr} (H : HitShape heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) :
    ∀ a ∈ e.getAppArgsList, HitShape heads params ls a := by
  by_cases hhit : ∃ c us, e.getAppFn = .const c us ∧ c ∈ heads
  · obtain ⟨c, us, hfn, hc⟩ := hhit
    obtain ⟨-, rest, hargs, hrest⟩ := H.getAppFn_const_hit_inv hfn hc
    rw [hargs]
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨fv, rfl⟩ := hp a ha
      exact .fvar fv
    · exact hrest a ha
  · have H' : HitShape heads params ls (e.getAppFn.mkAppList e.getAppArgsList) := by
      rw [Expr.mkAppList_getAppArgsList]; exact H
    refine (H'.mkAppList_inv fun c us h hc => hhit ⟨c, us, ?_, hc⟩).2
    rwa [getAppFn_getAppFn] at h

/-- The trailing arguments `e.getAppArgs[n:]` of a shaped expression are shaped. -/
theorem getAppArgs_slice {e : Expr} (H : HitShape heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) (n : Nat) :
    ∀ a ∈ (e.getAppArgs[n:] : Array Expr).toList, HitShape heads params ls a := by
  intro a ha
  rw [Lean4Lean.VerifyInductive.Expr.getAppArgs_slice_toList] at ha
  exact H.of_mem_getAppArgsList hp a (List.mem_of_mem_drop ha)

/-- `consumeTypeAnnotationsVerified` returns a subterm reached through
application arguments, so it preserves shape. -/
theorem consumeTypeAnnotationsVerified {e : Expr} (H : HitShape heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) :
    HitShape heads params ls e.consumeTypeAnnotationsVerified := by
  fun_induction Expr.consumeTypeAnnotationsVerified e
  case case1 name us type v _ ih =>
    exact ih (H.of_mem_getAppArgsList hp type (by simp [getAppArgsList]))
  case case2 => exact H
  case case3 name us type _ ih =>
    exact ih (H.of_mem_getAppArgsList hp type (by simp [getAppArgsList]))
  case case4 => exact H
  case case5 => exact H

/-- `mkAppN` with shaped head and arguments. -/
theorem mkAppN {f : Expr} {args : Array Expr} (hf : HitShape heads params ls f)
    (hargs : ∀ a ∈ args.toList, HitShape heads params ls a) :
    HitShape heads params ls (Lean.mkAppN f args) := by
  rw [Lean4Lean.VerifyInductive.Expr.mkAppN_eq_mkAppList]
  exact hf.mkAppList hargs

/-- A spine `c params rest` headed by any constant at the levels `ls`: a hit if
`c ∈ heads`, a traversed constant otherwise. -/
theorem mkAppN_const_params {c : Name} {rest : Array Expr}
    (hrest : ∀ a ∈ rest.toList, HitShape heads params ls a)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) :
    HitShape heads params ls (Lean.mkAppN (Lean.mkAppN (.const c ls) params.toArray) rest) := by
  rw [Lean4Lean.VerifyInductive.Expr.mkAppN_eq_mkAppList,
    Lean4Lean.VerifyInductive.Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append]
  by_cases hc : c ∈ heads
  · exact mkAppList_const_hit hc hrest
  · refine (HitShape.const hc).mkAppList fun a ha => ?_
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨fv, rfl⟩ := hp a ha
      exact .fvar fv
    · exact hrest a ha

/-- `mkAppN_const_params` with the parameters given as an array. -/
theorem mkAppN_const_paramsArray {params : Array Expr} {c : Name} {rest : Array Expr}
    (hrest : ∀ a ∈ rest.toList, HitShape heads params.toList ls a)
    (hp : ∀ p ∈ params.toList, ∃ fv, p = .fvar fv) :
    HitShape heads params.toList ls (Lean.mkAppN (Lean.mkAppN (.const c ls) params) rest) := by
  have := mkAppN_const_params (c := c) hrest hp
  rwa [Array.toArray_toList] at this

/-- Closing a telescope of non-parameter free variables with `mkForall`. -/
theorem mkForall_of_disjoint {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId}
    {b : Expr} (hxs : xs = (ys.map Expr.fvar).toArray) (H : HitShape heads params ls b)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∉ ys)
    (hdecl : ∀ y ∈ ys, ∃ d, lctx.find? y = some d ∧ d.HitShape heads params ls) :
    HitShape heads params ls (lctx.mkForall xs b) := by
  subst hxs
  simpa [LocalContext.mkForall] using
    H.mkBinding_of_disjoint (isLambda := false) (lctx := lctx) hp hdecl

/-- Closing a telescope of non-parameter free variables with `mkLambda`. -/
theorem mkLambda_of_disjoint {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId}
    {b : Expr} (hxs : xs = (ys.map Expr.fvar).toArray) (H : HitShape heads params ls b)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∉ ys)
    (hdecl : ∀ y ∈ ys, ∃ d, lctx.find? y = some d ∧ d.HitShape heads params ls) :
    HitShape heads params ls (lctx.mkLambda xs b) := by
  subst hxs
  simpa [LocalContext.mkLambda] using
    H.mkBinding_of_disjoint (isLambda := true) (lctx := lctx) hp hdecl

end HitShape

/-! ### `inferImplicit` changes binder annotations only -/

namespace HitShapeB

variable {heads : List Name} {n : Nat} {ls : List Level}

theorem forallE_inv {d : Nat} {nm : Name} {t b : Expr} {bi : BinderInfo}
    (H : HitShapeB heads n ls d (.forallE nm t b bi)) :
    HitShapeB heads n ls d t ∧ HitShapeB heads n ls (d + 1) b := by
  generalize he : Expr.forallE nm t b bi = e at H
  cases H with
  | forallE ht hb => cases he; exact ⟨ht, hb⟩
  | hitHead =>
    exfalso
    have := congrArg Expr.getAppFn he
    rw [getAppFn_mkAppList''] at this
    simp [getAppFn] at this
  | _ => cases he

theorem inferImplicit {d : Nat} {e : Expr} (H : HitShapeB heads n ls d e)
    (k : Nat) (f : Bool) : HitShapeB heads n ls d (e.inferImplicit k f) := by
  induction k generalizing e d with
  | zero => cases e <;> simpa [Expr.inferImplicit] using H
  | succ k ih =>
    cases e with
    | forallE nm t b bi =>
      obtain ⟨ht, hb⟩ := H.forallE_inv
      simp only [Expr.inferImplicit, mkForall]
      exact .forallE ht (ih hb)
    | _ => simpa [Expr.inferImplicit] using H

end HitShapeB

theorem LeadingBinders.inferImplicit_hitShape {heads : List Name} {n : Nat}
    {ls : List Level} {m : Nat} {e body : Expr} (H : LeadingBinders m e body)
    (Hb : HitShapeB heads n ls 0 body) (k : Nat) (f : Bool) :
    ∃ body', LeadingBinders m (e.inferImplicit k f) body' ∧
      HitShapeB heads n ls 0 body' := by
  induction H generalizing k with
  | zero => exact ⟨_, .zero _, Hb.inferImplicit k f⟩
  | @forallE m nm t b body bi Hb' ih =>
    cases k with
    | zero => exact ⟨body, by simpa [Expr.inferImplicit] using LeadingBinders.forallE Hb', Hb⟩
    | succ k =>
      obtain ⟨b', hl, hs⟩ := ih Hb k
      exact ⟨b', by simp only [Expr.inferImplicit, mkForall]; exact .forallE hl, hs⟩
  | @lam m nm t b body bi Hb' _ =>
    exact ⟨body, by cases k <;> simpa [Expr.inferImplicit] using LeadingBinders.lam Hb', Hb⟩

theorem HitShapeTele.inferImplicit {heads : List Name} {n : Nat} {ls : List Level}
    {e : Expr} (H : HitShapeTele heads n ls e) (k : Nat) (f : Bool) :
    HitShapeTele heads n ls (e.inferImplicit k f) := by
  obtain ⟨body, hl, hb⟩ := H
  exact hl.inferImplicit_hitShape hb k f

end Lean.Expr

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! ### The whnf hypothesis -/

/-- A hit-shape scope of a recursor-local context: `P` is closed under the
dependencies of its declarations (`IsFVarUpSet`, as for
`TypeChecker.VContext.UniverseScope`) and every declaration of a member of `P`
is in hit shape. This is the hit-shape analogue of `UniverseScope`. -/
def RecursorContextWF.HitShapeScope {c : AddInductive.Context} {recLparams : List Name}
    (Hc : RecursorContextWF c recLparams) (heads : List Name) (params : List Expr)
    (ls : List Level) (P : FVarId → Prop) : Prop :=
  IsFVarUpSet P Hc.mlctx.vlctx ∧ ∀ fv decl, P fv → Hc.mlctx.lctx.find? fv = some decl →
    decl.HitShape heads params ls

/-- **Hypothesis: `whnf` preserves hit shape.** This is everything the recursor
hit-shape provenance needs of the executable's lifted `whnf` calls in the
recursor-construction environment `env`: a well-typed input (in the
recursor-local context `c`) whose free variables lie in a hit-shape scope `P` of
`c` and which is itself in hit shape is normalized to an expression in hit shape.
It is the hit-shape counterpart of `whnfInRecursorContext.levelsWF`
(`TypeChecker.VContext.LevelsBelow`), quantified over the same data; the scope of
the output is already provided by `whnfInRecursorContext.scopeWF`.

`heads` are the auxiliary family and constructor names, `params` the common
parameter free variables `stats.params`, and `ls` the declaration's universe
parameters. `inferType` is not needed as a separate hypothesis: the only lifted
`inferType` call of the recursor pass (`loopUArgs`) is on a constructor field
free variable, which returns the field's declared type (`inferTypeFVarRun.WF`). -/
structure WhnfHitShapeFacts (heads : List Name) (params : List Expr) (ls : List Level)
    (env : Environment) : Prop where
  whnf : ∀ {c : AddInductive.Context} {recLparams : List Name}
      (Hc : RecursorContextWF c recLparams) {P : FVarId → Prop} {e e' : Expr}
      {target : VExpr},
    c.env = env →
    TrExprS Hc.venv recLparams Hc.mlctx.vlctx e target →
    Hc.HitShapeScope heads params ls P →
    e.FVarsIn P → e.HitShape heads params ls →
    (monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c = .ok e' →
    e'.HitShape heads params ls

/-! ### The `loopUArgs` traversal (regions R2 and R3) -/

/-- Hit shape along an exact `loopUArgs.loop` trace: mirrors
`RecursorLoopUArgsPrefix.universeSupport`. If the normalized input type is in
hit shape and lies in a hit-shape scope `P` of a recursor context, then at the
terminal context there is a hit-shape scope containing every opened argument,
and the exposed type is in hit shape and lies in that scope. -/
theorem RecursorLoopUArgsPrefix.hitShape
    {heads : List Name} {params : List Expr} {ls : List Level} {env : Environment}
    (W : WhnfHitShapeFacts heads params ls env)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    {root : AddInductive.Context} {source : Expr}
    {current : AddInductive.Context} {exposed : Expr} {args : Array Expr}
    (trace : RecursorLoopUArgsPrefix root source current exposed args)
    (henv : root.env = env)
    {recLparams : List Name} (Rroot : RecursorContextWF root recLparams)
    {P : FVarId → Prop} (hscope : Rroot.HitShapeScope heads params ls P)
    {sourceTarget : VExpr}
    (hsource : TrExpr Rroot.venv recLparams Rroot.mlctx.vlctx source sourceTarget)
    (hsourceType : Rroot.venv.IsType recLparams.length Rroot.mlctx.vlctx.toCtx
      sourceTarget)
    (hsourceH : source.HitShape heads params ls) (hsourceP : source.FVarsIn P) :
    ∃ (Rcurrent : RecursorContextWF current recLparams) (P' : FVarId → Prop)
      (T : VExpr),
      TrExpr Rcurrent.venv recLparams Rcurrent.mlctx.vlctx exposed T ∧
      Rcurrent.venv.IsType recLparams.length Rcurrent.mlctx.vlctx.toCtx T ∧
      Rcurrent.HitShapeScope heads params ls P' ∧
      exposed.HitShape heads params ls ∧ exposed.FVarsIn P' ∧
      current.env = env ∧
      ∀ a ∈ args.toList, ∃ fv, a = .fvar fv ∧ P' fv := by
  induction trace with
  | root => exact ⟨Rroot, P, _, hsource, hsourceType, hscope, hsourceH, hsourceP, henv,
      by simp⟩
  | @push current next args name domain body normalized bi _previous next_eq
      normalization ih =>
    obtain ⟨R, P', T, htype, htypeType, hsc, hH, hP, hcenv, hargs⟩ := ih
    subst next_eq
    rcases TrExpr.forallE_source htype with
      ⟨sourceDom, sourceBody, hdom, hbody, hdomType, hbodyType, hforallEq⟩
    rcases hconsume current recLparams R hdom hdomType with ⟨consumedDom, Hdom⟩
    rcases Hdom.body R hbody with ⟨consumedBody, hbodyConsumed, hbodyEq⟩
    let x : FVarId := ⟨current.ngen.curr⟩
    let R' := R.withLocalDecl (name := name) (bi := bi) Hdom.consumed Hdom.isType
    have hopened := R.instantiateFresh (name := name) (bi := bi)
      Hdom.consumed Hdom.isType hbodyConsumed
    obtain ⟨hdomH, hbodyH⟩ := hH.forallE_inv
    have hdomP : domain.FVarsIn P' := hP.1
    have hbodyP : body.FVarsIn P' := hP.2
    let P'' : FVarId → Prop := fun fv => fv = x ∨ P' fv
    have hsc' : R'.HitShapeScope heads params ls P'' := by
      refine ⟨?_, ?_⟩
      · have hΔ : R'.mlctx.vlctx =
            (some (x, domain.consumeTypeAnnotationsVerified.fvarsList),
              .vlam consumedDom) :: R.mlctx.vlctx := rfl
        rw [hΔ]
        refine ⟨(IsFVarUpSet.congr (P := P') (Q := P'') R.mlctx_wf.tr.wf.fvwf
          (fun fv h => ⟨Or.inr, fun hq => hq.resolve_left (by
            rintro rfl; exact R.current_not_mem h)⟩)).1 hsc.1,
          fun _ dep hdep => .inr ?_⟩
        exact (fvarsIn_iff.mp
            (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomP)).1 dep hdep
      · intro fv decl hfv hdecl
        by_cases hx : fv = x
        · subst hx
          have hself := R'.mlctx_wf.find?_vlam_self
          change (TypeChecker.MLCtx.vlam x name domain.consumeTypeAnnotationsVerified
            consumedDom bi R.mlctx).lctx.find? x = some decl at hdecl
          rw [hself] at hdecl
          cases hdecl
          exact hdomH.consumeTypeAnnotationsVerified hp
        · have hfind : R'.mlctx.lctx.find? fv = R.mlctx.lctx.find? fv := by
            change (TypeChecker.MLCtx.vlam x name domain.consumeTypeAnnotationsVerified
              consumedDom bi R.mlctx).lctx.find? fv = R.mlctx.lctx.find? fv
            have hwf : (TypeChecker.MLCtx.vlam x name domain.consumeTypeAnnotationsVerified
                consumedDom bi R.mlctx).WF R.venv recLparams := R'.mlctx_wf
            rw [hwf.find?_eq, R.mlctx_wf.find?_eq]
            have hbeq : (fv == x) = false := by simpa using hx
            simp [TypeChecker.MLCtx.decls, LocalDecl.fvarId, hbeq]
          exact hsc.2 fv decl (hfv.resolve_left hx) (hfind ▸ hdecl)
    have hinstH : (body.instantiate1 (.fvar x)).HitShape heads params ls :=
      hbodyH.instantiate1 (.fvar x) hp
    have hinstP : (body.instantiate1 (.fvar x)).FVarsIn P'' := by
      rw [Expr.instantiate1_eq]
      exact (hbodyP.mono fun _ h => Or.inr h).instantiate1 (by
        simp [FVarsIn])
    have hscopeRun := (whnfInRecursorContext.scopeWF R' hopened) normalized normalization
    have hnormH : normalized.HitShape heads params ls :=
      W.whnf R' hcenv hopened hsc' hinstP hinstH normalization
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
      hnormH, hscopeRun.1 P'' hsc'.1 hinstP, hcenv, ?_⟩
    intro a ha
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · obtain ⟨fv, rfl, hfv⟩ := hargs a ha
      exact ⟨fv, rfl, Or.inr hfv⟩
    · exact ⟨x, rfl, Or.inl rfl⟩

/-- The type of a free variable of a recursor context translates. -/
theorem RecursorContextWF.trFVar {c : AddInductive.Context} {recLparams : List Name}
    (Hc : RecursorContextWF c recLparams) {fv : FVarId} (hfv : fv ∈ c.lctx.fvars) :
    ∃ target, TrExprS Hc.venv recLparams Hc.mlctx.vlctx (.fvar fv) target := by
  have hmem : fv ∈ Hc.mlctx.vlctx.fvars := by
    rw [← Hc.mlctx_wf.tr.fvars_eq, Hc.lctx_eq]; exact hfv
  obtain ⟨⟨e, A⟩, hfind⟩ := VLCtx.find?_eq_some.2 hmem
  exact ⟨e, .fvar hfind⟩

/-- **Hit shape of one induction-hypothesis origin** (regions R2 and R3). Given
a recursor-context certificate for the origin's root, a hit-shape scope `P`
containing the recursive field, and the parameters among the root's variables,
every argument declaration opened by `loopUArgs`, the exposed family
application and the hypothesis type are in hit shape. -/
theorem RecInfoMinorHypothesisTypeOrigin.hitShape
    {heads : List Name} {params : List Expr} {ls : List Level} {env : Environment}
    (W : WhnfHitShapeFacts heads params ls env)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    {stats : AddInductive.InductiveStats} {recInfos : Array AddInductive.RecInfo}
    {root : AddInductive.Context} {field type : Expr}
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type)
    (henv : root.env = env)
    {recLparams : List Name} (Rroot : RecursorContextWF root recLparams)
    {P : FVarId → Prop} (hscope : Rroot.HitShapeScope heads params ls P)
    (hfieldP : ∀ fv, field = .fvar fv → P fv)
    (hparamsRoot : ∀ p ∈ params, ∃ fv, p = .fvar fv ∧ fv ∈ root.lctx.fvars) :
    (∀ x ∈ O.arguments_bound.fvars, ∀ decl, O.current.lctx.find? x = some decl →
        decl.HitShape heads params ls) ∧
      O.exposedType.HitShape heads params ls ∧
      type.HitShape heads params ls := by
  have hinference := O.loopInput.inference
  have hnormalization := O.loopInput.normalization
  obtain ⟨fv, hfield, hfvRoot⟩ := O.field_fvar
  have hfvP : P fv := hfieldP fv hfield
  obtain ⟨fieldTarget, hfieldTr⟩ := Rroot.trFVar hfvRoot
  subst hfield
  obtain ⟨inferredTarget, hbelow, _, hinferredTr, hfieldTyping⟩ :=
    inferTypeFVarInRecursorContext.WF Rroot hfieldTr _ hinference
  obtain ⟨decl, hdecl, hty⟩ := inferTypeFVarRun.WF root fv _ hinference
  have hdeclH : decl.HitShape heads params ls :=
    hscope.2 fv decl hfvP (by rw [Rroot.lctx_eq]; exact hdecl)
  have hinferredH : O.loopInput.inferredType.HitShape heads params ls := by
    rw [hty]
    cases decl with
    | cdecl => exact hdeclH
    | ldecl => exact hdeclH.1
  have hfieldPin : (Expr.fvar fv).FVarsIn P := by simpa [FVarsIn] using hfvP
  have hinferredP : O.loopInput.inferredType.FVarsIn P := hbelow P hscope.1 hfieldPin
  have hinferredType : Rroot.venv.IsType recLparams.length
      Rroot.mlctx.vlctx.toCtx inferredTarget :=
    hfieldTyping.isType Rroot.checking.tr.wf Rroot.mlctx_wf.tr.wf.toCtx
  obtain ⟨hnormalizedBelow, hnormalizedTr⟩ :=
    whnfInRecursorContext.scopeWF Rroot hinferredTr _ hnormalization
  have hnormalizedH : O.loopInput.normalizedType.HitShape heads params ls :=
    W.whnf Rroot henv hinferredTr hscope hinferredP hinferredH hnormalization
  have hnormalizedP : O.loopInput.normalizedType.FVarsIn P :=
    hnormalizedBelow P hscope.1 hinferredP
  obtain ⟨Rcurrent, P', _, _, _, hsc', hexposedH, _, _, hargs⟩ :=
    O.loopTrace.hitShape W hp recursorConsumeTypeAnnotationsCompat henv Rroot hscope
      hnormalizedTr hinferredType hnormalizedH hnormalizedP
  have hargDecls : ∀ x ∈ O.arguments_bound.fvars, ∀ decl,
      O.current.lctx.find? x = some decl → decl.HitShape heads params ls := by
    intro x hx decl hdecl
    have hxArg : Expr.fvar x ∈ O.args.toList := by
      rw [O.arguments_bound.expressions]
      simpa using hx
    obtain ⟨y, hy, hyP⟩ := hargs _ hxArg
    cases hy
    exact hsc'.2 x decl hyP (by rw [Rcurrent.lctx_eq]; exact hdecl)
  refine ⟨hargDecls, hexposedH, ?_⟩
  obtain ⟨m, hm, _⟩ := O.motive_is_fvar
  rw [O.type_eq]
  refine Expr.HitShape.mkForall_of_disjoint O.arguments_bound.expressions ?_ ?_ ?_
  · refine .app (Expr.HitShape.mkAppN (by rw [hm]; exact .fvar m)
      (hexposedH.getAppArgs_slice hp _)) (Expr.HitShape.mkAppN (.fvar fv) ?_)
    intro a ha
    rw [O.arguments_bound.expressions] at ha
    simp only [List.mem_map] at ha
    obtain ⟨y, -, rfl⟩ := ha
    exact .fvar y
  · intro p hp'
    obtain ⟨pv, rfl, hpv⟩ := hparamsRoot p hp'
    exact ⟨pv, rfl, fun h => O.arguments_bound.fresh pv h hpv⟩
  · intro y hy
    have hyCur : y ∈ O.current.lctx.fvars := O.arguments_bound.members y hy
    obtain ⟨index, name, ty, bi, kind, hfind⟩ := O.current_wf.findCDecl y hyCur
    exact ⟨_, hfind, hargDecls y hy _ hfind⟩

/-! ### The `loopArgs1` traversal (region R1) -/

/-- Hit shape of the output of one retained recursor `whnf` call, given that
the declarations of every variable admitted by `Q` (read in `final`) and the
input are in hit shape. -/
theorem RecursorWhnfCallAt.hitShape
    {heads : List Name} {params : List Expr} {ls : List Level} {env : Environment}
    (W : WhnfHitShapeFacts heads params ls env)
    {final : AddInductive.Context} (henv : final.env = env)
    {Q : FVarId → Prop} {input output : Expr}
    (H : RecursorWhnfCallAt final Q input output)
    (hQ : ∀ fv, Q fv → ∀ d, final.lctx.find? fv = some d →
      d.HitShape heads params ls)
    (hin : input.HitShape heads params ls) :
    output.HitShape heads params ls := by
  obtain ⟨ctx, recLparams, Rc, P, target, hle, htr, hup, hP, hinP, hrun⟩ := H
  refine W.whnf Rc (hle.env_eq.symm.trans henv) htr
    ⟨hup, fun fv decl hPfv hfind => ?_⟩ hinP hin hrun
  rw [Rc.lctx_eq] at hfind
  obtain ⟨hQfv, hmem⟩ := hP fv hPfv
  exact hQ fv hQfv decl (by rw [hle.declarations fv hmem]; exact hfind)

/-- **Hit shape along a retained `loopArgs1` trace** (region R1). If the
family header is in hit shape and the parameter declarations of `final` are,
then so is every normalized type of the trace and every opened index
declaration. -/
theorem RecursorIndexTrace.hitShape
    {heads : List Name} {ls : List Level} {env : Environment}
    {stats : AddInductive.InductiveStats}
    (W : WhnfHitShapeFacts heads stats.params.toList ls env)
    (hp : ∀ p ∈ stats.params.toList, ∃ fv, p = .fvar fv)
    {final : AddInductive.Context} (henv : final.env = env)
    (hparamDecls : ∀ fv ∈ ExprArrayFVarIds stats.params, ∀ d,
      final.lctx.find? fv = some d → d.HitShape heads stats.params.toList ls)
    {header : Expr} (hheader : header.HitShape heads stats.params.toList ls)
    {i : Nat} {type : Expr} {indices : Array Expr}
    (T : RecursorIndexTrace stats final header i type indices) :
    type.HitShape heads stats.params.toList ls ∧
      ∀ fv ∈ ExprArrayFVarIds indices, ∀ d, final.lctx.find? fv = some d →
        d.HitShape heads stats.params.toList ls := by
  induction T with
  | start call =>
    exact ⟨call.hitShape W henv (fun _ h => h.elim) hheader,
      by simp [ExprArrayFVarIds]⟩
  | @param i name dom body normalized bi _ hi call ih =>
    obtain ⟨hty, -⟩ := ih
    obtain ⟨-, hbody⟩ := hty.forallE_inv
    have hparam : (stats.params[i]!).HitShape heads stats.params.toList ls := by
      have hmem : stats.params[i]! ∈ stats.params.toList := by
        rw [getElem!_pos stats.params i hi]
        exact Array.getElem_mem_toList hi
      obtain ⟨fv, hfv⟩ := hp _ hmem
      rw [hfv]
      exact .fvar fv
    exact ⟨call.hitShape W henv hparamDecls (hbody.instantiate1 hparam hp),
      by simp [ExprArrayFVarIds]⟩
  | @index indices name dom body normalized bi x _ member declaration call ih =>
    obtain ⟨hty, hidx⟩ := ih
    obtain ⟨hdom, hbody⟩ := hty.forallE_inv
    have hall : ∀ fv ∈ ExprArrayFVarIds (indices.push (.fvar x)), ∀ d,
        final.lctx.find? fv = some d → d.HitShape heads stats.params.toList ls := by
      rw [ExprArrayFVarIds_push_fvar]
      intro fv hfv d hfind
      rcases List.mem_append.mp hfv with h | h
      · exact hidx fv h d hfind
      · rw [List.mem_singleton.mp h] at hfind
        obtain ⟨index, userName, binderInfo, kind, hx⟩ := declaration
        rw [hx] at hfind
        cases hfind
        exact hdom.consumeTypeAnnotationsVerified hp
    refine ⟨call.hitShape W henv (fun fv hfv d hfind => ?_)
      (hbody.instantiate1 (.fvar x) hp), hall⟩
    rcases hfv with h | h
    · exact hparamDecls fv h d hfind
    · exact hall fv h d hfind

/-! ### Constructor fields (the lowered constructor's syntactic domains) -/

/-- The executable common-parameter prefix replay instantiates the parameter
telescope with the parameter free variables, all at once. -/
theorem RecursorParamPrefix.tail_eq_instantiateRevList
    {stats : AddInductive.InductiveStats} {pfvs : List FVarId}
    (hparams : stats.params = (pfvs.map Expr.fvar).toArray) :
    ∀ {i : Nat} {src tail : Expr}, RecursorParamPrefix stats i src tail →
      ∀ {body : Expr}, Expr.LeadingBinders (pfvs.length - i) src body →
        tail = body.instantiateRevList ((pfvs.drop i).map Expr.fvar) 0 := by
  intro i src tail H
  induction H with
  | @done i tail hi =>
    intro body Hlead
    have hlen : pfvs.length = i := by
      rw [hi, hparams]; simp
    rw [hlen, Nat.sub_self] at Hlead
    cases Hlead
    rw [← hlen, List.drop_length]
    rfl
  | @step i param body tail name dom bi hparam _ ih =>
    intro body' Hlead
    have hi : i < pfvs.length := by
      have := (Array.getElem?_eq_some_iff.mp hparam).1
      rw [hparams] at this; simpa using this
    have hparamEq : param = .fvar pfvs[i] := by
      rw [hparams] at hparam
      simp only [List.getElem?_toArray, List.getElem?_map] at hparam
      rw [List.getElem?_eq_getElem hi] at hparam
      simp only [Option.map_some, Option.some.injEq] at hparam
      exact hparam.symm
    subst hparamEq
    rw [show pfvs.length - i = (pfvs.length - (i + 1)) + 1 by omega] at Hlead
    cases Hlead with
    | forallE Hb =>
      have Hb' := Hb.instantiate1' (.fvar pfvs[i]) 0
      rw [← Expr.instantiate1_eq] at Hb'
      rw [ih Hb', List.drop_eq_getElem_cons hi, List.map_cons]
      have hlenDrop : (pfvs.drop (i + 1)).length = pfvs.length - (i + 1) := by simp
      have := Expr.instantiateRevList_instantiate1'_fvars body' pfvs[i] (pfvs.drop (i + 1)) 0 0
      simp only [Nat.zero_add, Nat.add_zero, hlenDrop] at this
      rw [Nat.zero_add, this]
      rfl

/-- The parameter-instantiated tail of a lowered constructor type in parameter
telescope hit shape is in free-variable hit shape over the parameters. -/
theorem RecursorParamPrefix.hitShape {heads : List Name} {ls : List Level}
    {stats : AddInductive.InductiveStats} {pfvs : List FVarId} {src tail : Expr}
    (H : RecursorParamPrefix stats 0 src tail)
    (hparams : stats.params = (pfvs.map Expr.fvar).toArray)
    (Hsrc : Expr.HitShapeTele heads stats.params.size ls src) :
    tail.HitShape heads stats.params.toList ls := by
  obtain ⟨body, Hlead, Hbody⟩ := Hsrc
  have hsize : stats.params.size = pfvs.length := by rw [hparams]; simp
  rw [hsize] at Hlead Hbody
  rw [H.tail_eq_instantiateRevList hparams (by simpa using Hlead), hparams]
  simpa using Hbody.instantiateRevList_fvars

/-- Every field declaration opened along a retained field-decision trace, and the
terminal expression, are in hit shape when the traversed tail is. -/
theorem RecursorFieldDecisions.hitShape {heads : List Name} {params : List Expr}
    {ls : List Level}
    (H : RecursorFieldDecisions stats root source current terminal fields
      selected positions)
    (Hroot : BindingContextWF root) (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    (Hsource : source.HitShape heads params ls) :
    terminal.HitShape heads params ls ∧
      FieldDeclsSatisfy (fun e => e.HitShape heads params ls) current fields :=
  H.fieldDeclsSatisfy Hroot _ (fun h =>
    ⟨h.forallE_inv.1.consumeTypeAnnotationsVerified hp,
      fun fv => h.forallE_inv.2.instantiate1 (.fvar fv) hp⟩) Hsource

/-! ### Bound free-variable arrays -/

theorem BoundFVarArray.mem_fvars_iff {c : AddInductive.Context} {xs : Array Expr}
    (B : BoundFVarArray c xs) {fv : FVarId} : fv ∈ B.fvars ↔ Expr.fvar fv ∈ xs := by
  rcases B with ⟨fvars, rfl, _⟩
  simp

theorem BoundFVarArray.fvar_of_mem {c : AddInductive.Context} {xs : Array Expr}
    (B : BoundFVarArray c xs) {e : Expr} (he : e ∈ xs) : ∃ fv, e = .fvar fv ∧ fv ∈ B.fvars := by
  rcases B with ⟨fvars, rfl, _⟩
  simp only [List.mem_toArray, List.mem_map] at he
  obtain ⟨fv, hfv, rfl⟩ := he
  exact ⟨fv, rfl, hfv⟩

theorem mem_exprArrayFVarIds_of_fvar_mem {xs : Array Expr} {fv : FVarId}
    (h : Expr.fvar fv ∈ xs) : fv ∈ ExprArrayFVarIds xs := by
  simp only [ExprArrayFVarIds, List.mem_map]
  exact ⟨_, Array.mem_toList_iff.2 h, rfl⟩

/-- Declaration shapes from exact `withLocalDecl` origin types. -/
theorem BoundFVarTypeOrigins.declHitShape {heads : List Name} {params : List Expr}
    {ls : List Level} {c : AddInductive.Context} {xs origins : Array Expr}
    (Ho : BoundFVarTypeOrigins c xs origins)
    (hQ : ∀ i, i < xs.size → origins[i]!.HitShape heads params ls)
    {fv : FVarId} (hfv : Expr.fvar fv ∈ xs) :
    ∃ d, c.lctx.find? fv = some d ∧ d.HitShape heads params ls := by
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hfv
  obtain ⟨D, hD⟩ := Ho.declaration i hi
  have hfvD : D.fvar = fv := by
    have := D.expression.symm.trans hget
    exact (Expr.fvar.inj this)
  subst hfvD
  refine ⟨_, D.declaration, ?_⟩
  show D.type.HitShape heads params ls
  rw [hD]; exact hQ i hi

/-! ### Hypotheses on the completed recursor construction -/

/-- The cached parameters are variables of the context carrying the suffix. -/
theorem RecursorParameterContextSuffix.param_mem {r : AddInductive.Context}
    {recLparams : List Name} {Rr : RecursorContextWF r recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (P : RecursorParameterContextSuffix Rr stats depth) {pv : FVarId}
    (h : Expr.fvar pv ∈ stats.params) : pv ∈ r.lctx.fvars := by
  obtain ⟨fvars, hparams, hdecls⟩ := cachedParameterDecls_fvars P.cached
  have hmem : Expr.fvar pv ∈ stats.params.toList.reverse := by simpa using h
  rw [hparams] at hmem
  simp only [List.mem_map, Expr.fvar.injEq, exists_eq_right] at hmem
  rw [← Rr.lctx_eq, Rr.mlctx_wf.tr.fvars_eq, P.context, VLCtx.fvars_append, hdecls]
  exact List.mem_append_right _ hmem

/-- Selected (recursive) fields are among the opened fields. -/
theorem RecursorFieldDecisions.selected_subset
    (H : RecursorFieldDecisions stats root source current terminal fields
      selected positions) : ∀ e ∈ selected, e ∈ fields := by
  induction H with
  | nil => intro e he; simp at he
  | nonrecursive _ _ ih =>
    intro e he
    exact Array.mem_push.2 (.inl (ih e he))
  | recursive _ _ ih =>
    intro e he
    rcases Array.mem_push.1 he with he | rfl
    · exact Array.mem_push.2 (.inl (ih e he))
    · exact Array.mem_push.2 (.inr rfl)

section Assembly

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
    sourceEnv indTypes ctorEnv}

/-- **Non-`whnf` provenance hypotheses** for the hit shape of a completed
recursor construction, relative to the head set `heads`, the parameter free
variables `stats.params` and the levels `stats.levels`.

* `paramDecls`: the parameter declarations of the recursor context are shaped.
  They are the source parameter domains (opened by the header check in the
  pre-declaration environment), which mention no auxiliary name.
* `familyHeaders`: the family headers `indTypes[i].type` mention no head.
  Source headers mention no `_nested` name; an auxiliary header is the
  parameter telescope followed by the container's index domains, which avoid
  the heads unless a container index type mentions a nested occurrence. The
  header is the input of the first `whnf` call of `mkRecInfos.loopInd1`, so
  this is what `WhnfHitShapeFacts.whnf` needs at the start of the retained
  `loopArgs1` trace (`RecInfoIndexTraces`, retained in
  `CompletedRecursorConstruction.minorSources`).
* `constructorTypes`: the lowered constructor types are parameter telescopes in
  hit shape (from the lowering trace: every hit is
  `mkAppN (.const auxI lvls) As` with untouched source trailing arguments).
* `recursorNames`: generated recursor names are not heads.

The index domains (region R1) and the induction-hypothesis regions (R2, R3)
need no hypothesis beyond these and `WhnfHitShapeFacts`: they follow along the
retained `RecursorIndexTrace`s and the rooted call origins
(`RecInfoCallBlueprintOrigins.rooted`). -/
structure CompletedRecursorConstruction.HitShapeInputs
    (H : CompletedRecursorConstruction R) (heads : List Name) : Prop where
  paramDecls : ∀ fv ∈ H.params.fvars, ∀ d, H.localContext.lctx.find? fv = some d →
    d.HitShape heads stats.params.toList stats.levels
  familyHeaders : ∀ i, i < indTypes.size → (indTypes[i]!.type).AvoidsConsts heads
  constructorTypes : ∀ i, i < indTypes.size → ∀ ctor ∈ indTypes[i]!.ctors,
    Expr.HitShapeTele heads stats.params.size stats.levels ctor.type
  recursorNames : ∀ i, i < stats.indConsts.size → Lean.mkRecName indTypes[i]!.name ∉ heads

namespace CompletedRecursorConstruction

variable (H : CompletedRecursorConstruction R)

include H in
theorem params_fvar : ∀ p ∈ stats.params.toList, ∃ fv, p = .fvar fv := by
  intro p hp
  obtain ⟨fv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.params (Array.mem_toList_iff.1 hp)
  exact ⟨fv, rfl⟩

theorem params_toList : stats.params.toList = H.params.fvars.map Expr.fvar := by
  have h := congrArg Array.toList H.params.expressions
  simpa using h

theorem allFvars_nodup :
    (H.params.fvars ++ (H.bindings.motives.fvars ++ (H.bindings.flatMinors.fvars ++
      (H.bindings.flatIndices.fvars ++ H.bindings.majors.fvars)))).Nodup := by
  have := H.noAlias
  unfold RecInfoBindings.NoAlias at this
  rwa [H.bindings.allFvars_eq H.params] at this

theorem params_nodup : H.params.fvars.Nodup :=
  (List.nodup_append.1 H.allFvars_nodup).1

/-- A parameter is none of the other outer recursor binders. -/
theorem param_not_outer {pv : FVarId} (hpv : pv ∈ H.params.fvars) {e : Expr}
    (he : e ∈ H.recInfos.map (·.motive) ∨ e ∈ H.recInfos.flatMap (·.minors) ∨
      e ∈ H.recInfos.flatMap (·.indices) ∨ e ∈ H.recInfos.map (·.major)) :
    e ≠ .fvar pv := by
  rintro rfl
  have hdisj := (List.nodup_append.1 H.allFvars_nodup).2.2 pv hpv pv
  apply hdisj _ rfl
  simp only [List.mem_append]
  rcases he with he | he | he | he
  · exact .inl (H.bindings.motives.mem_fvars_iff.2 he)
  · exact .inr (.inl (H.bindings.flatMinors.mem_fvars_iff.2 he))
  · exact .inr (.inr (.inl (H.bindings.flatIndices.mem_fvars_iff.2 he)))
  · exact .inr (.inr (.inr (H.bindings.majors.mem_fvars_iff.2 he)))

/-- Disjointness in the form consumed by `HitShape.mkForall_of_disjoint`. -/
theorem params_disjoint {ys : List FVarId}
    (hys : ∀ y ∈ ys, Expr.fvar y ∈ H.recInfos.map (·.motive) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.minors) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.indices) ∨
      Expr.fvar y ∈ H.recInfos.map (·.major)) :
    ∀ p ∈ stats.params.toList, ∃ fv, p = .fvar fv ∧ fv ∉ ys := by
  intro p hp
  rw [H.params_toList] at hp
  simp only [List.mem_map] at hp
  obtain ⟨pv, hpv, rfl⟩ := hp
  exact ⟨pv, rfl, fun hy => H.param_not_outer hpv (hys pv hy) rfl⟩

theorem recInfos_size_eq : H.recInfos.size = decl.types.length := H.cardinality.records

theorem indConst_eq {i : Nat} (hi : i < H.recInfos.size) :
    ∃ n, stats.indConsts[i]! = .const n stats.levels := by
  have hi' : i < decl.types.length := by rw [← H.recInfos_size_eq]; exact hi
  have h := H.validStats.indConstAt hi'
  refine ⟨decl.types[i].name, ?_⟩
  rw [getElem!_def, h]

theorem sourceOwner {owner : Nat} (howner : owner < H.recInfos.size) :
    owner < indTypes.size := by
  have htypes : H.recInfos.size = indTypes.size := by
    rw [H.cardinality.records]
    simpa using (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
  omega

theorem motive_fvar {k : Nat} (hk : k < stats.indConsts.size) :
    ∃ fv, H.recInfos[k]!.motive = .fvar fv := by
  have hk' : k < H.recInfos.size := by
    rw [H.recInfos_size_eq, ← H.validStats.types_size]; exact hk
  have hmem : H.recInfos[k]!.motive ∈ H.recInfos.map (·.motive) := by
    rw [getElem!_pos H.recInfos k hk']
    exact Array.mem_map.2 ⟨_, Array.getElem_mem hk', rfl⟩
  obtain ⟨fv, h, -⟩ := BoundFVarArray.fvar_of_mem H.bindings.motives hmem
  exact ⟨fv, h⟩

/-- **Hit shape of one generated minor**: its field declarations (in the
minor's source context), its declared type, and the call templates of its rule
blueprint. -/
theorem minorHitShape {heads : List Name} (I : H.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads stats.params.toList stats.levels H.localContext.env)
    (owner : Nat) (howner : owner < H.recInfos.size) (localIndex : Nat)
    (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (∀ y ∈ (H.origins.minorShapes owner howner localIndex hlocal).fields_bound.fvars,
      ∃ d, (H.origins.minorShapes owner howner localIndex
          hlocal).sourceFullContext.lctx.find? y = some d ∧
        d.HitShape heads stats.params.toList stats.levels) ∧
    (H.origins.minorShapes owner howner localIndex hlocal).origin.HitShape heads
      stats.params.toList stats.levels ∧
    (∀ j, j < (H.origins.minorShapes owner howner localIndex hlocal).hypotheses.size →
      (H.recInfos[owner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).template.HitShape
        heads stats.params.toList stats.levels ∧
      (H.recInfos[owner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).targetTypeIdx <
        stats.indConsts.size) := by
  have hsourceOwner := H.sourceOwner howner
  have hsrc := H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have hcallRoots : RecInfoRuleBlueprintOriginAt stats
      (H.origins.minorShapes owner howner localIndex hlocal)
      H.recInfos[owner]!.minors[localIndex]!
      H.recInfos[owner]!.ruleBlueprints[localIndex]! :=
    H.blueprints.entry owner howner localIndex hlocal
  have hfresh := H.blueprints.fields_outer_fresh owner howner localIndex hlocal
  obtain ⟨Hsem⟩ := H.blueprintSemantics.entry owner howner localIndex hlocal
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at hsrc hcallRoots hfresh Hsem ⊢
  generalize H.recInfos[owner]!.ruleBlueprints[localIndex]! = B at hcallRoots Hsem ⊢
  obtain ⟨-, -, hsourceCtors, -, traversal, htrav, -, -, -, -, hvalid, hmotiveApp, -, -,
    hsrcLE⟩ := hsrc
  obtain ⟨origins, hshape, hstats, -, F, -⟩ := Hsem
  obtain ⟨-, -, -, -, -, callOrigins, -, hcallShape, -, -, Hcalls⟩ := hcallRoots
  have hcallOrigins : callOrigins = origins :=
    Option.some.inj (hcallShape.symm.trans hshape)
  subst callOrigins
  have hT : traversal = F.traversal := Option.some.inj (htrav.symm.trans F.traversal_eq)
  subst hT
  have hp := H.params_fvar
  have Hroot := F.rootWF.toBindingContextWF
  have hTL : BindingContextLE F.traversal.terminalContext H.localContext :=
    F.terminalExtension.contextLE
  -- Field declarations (the lowered constructor's syntactic domains).
  have Hprefix : RecursorParamPrefix stats 0 S.constructor.type
      F.traversal.parameterTail := by
    have := F.traversal.parameterPrefix
    rwa [F.traversal_stats, F.traversal_constructor] at this
  have hctorMem : S.constructor ∈ indTypes[owner]!.ctors := by
    rw [← hsourceCtors]; exact List.mem_of_getElem? S.sourceConstructor
  have Htail := Hprefix.hitShape H.params.expressions
    (I.constructorTypes owner hsourceOwner _ hctorMem)
  obtain ⟨hterm, hfieldsTerm⟩ := F.traversal.decisions.hitShape Hroot hp Htail
  rw [F.traversal_fields] at hfieldsTerm
  have hfieldDecls : ∀ y ∈ S.fields_bound.fvars, ∃ d,
      S.sourceFullContext.lctx.find? y = some d ∧
        d.HitShape heads stats.params.toList stats.levels := by
    intro y hy
    obtain ⟨fv, index, name, type, bi, kind, hfv, hmem, hfind, htype⟩ :=
      hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hy)
    cases hfv
    refine ⟨.cdecl index y name type bi kind, ?_, htype⟩
    rw [← hsrcLE.declarations y (S.fields_bound.members y hy),
      hTL.declarations y hmem, hfind]
  -- Parameters are variables of the field traversal's terminal context.
  have hparamTerm : ∀ pv, Expr.fvar pv ∈ stats.params →
      pv ∈ F.traversal.terminalContext.lctx.fvars := fun pv h =>
    (F.traversal.decisions.freshBindings Hroot).choose_spec.1.fvars
      (F.parameterSuffix.param_mem h)
  -- Induction hypotheses and recursive calls (regions R2 and R3).
  have hfr : origins.fieldRoot = F.traversal.terminalContext :=
    S.hypothesis_origins_fieldRoot origins F.traversal hshape F.traversal_eq
  have hper : ∀ j, j < S.hypotheses.size →
      (∃ D : BoundFVarDeclarationAt S.sourceFullContext S.hypotheses j,
        D.type.HitShape heads stats.params.toList stats.levels) ∧
      ((B.recursiveCalls[j]!).template.HitShape heads stats.params.toList stats.levels ∧
        (B.recursiveCalls[j]!).targetTypeIdx < stats.indConsts.size) := by
    intro j hj
    obtain ⟨originRoot, sourceType, recL, Rorigin, O, D, hle, hup, hD, hcall⟩ :=
      Hcalls.rooted j hj
    rw [hstats] at hup
    rw [hfr] at hle
    have henv : originRoot.env = H.localContext.env := hle.env_eq.trans hTL.env_eq.symm
    have hscope : Rorigin.HitShapeScope heads stats.params.toList stats.levels
        (fun fv => fv ∈ ExprArrayFVarIds S.fields ∨
          fv ∈ ExprArrayFVarIds stats.params) := by
      refine ⟨hup, fun fv decl hP hfind => ?_⟩
      rw [Rorigin.lctx_eq] at hfind
      rcases hP with hf | hpar
      · rw [S.fields_bound.exprArrayFVarIds] at hf
        obtain ⟨fv', index, name, type, bi, kind, hfv, hmem, hfind', htype⟩ :=
          hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hf)
        cases hfv
        rw [hle.declarations fv hmem, hfind'] at hfind
        cases hfind
        exact htype
      · rw [H.params.exprArrayFVarIds] at hpar
        have hmemP := H.params.mem_fvars_iff.1 hpar
        rw [hle.declarations fv (hparamTerm fv hmemP),
          ← hTL.declarations fv (hparamTerm fv hmemP)] at hfind
        exact I.paramDecls fv hpar decl hfind
    have hjr : j < S.recursiveFields.size := by rw [← S.hypotheses_size]; exact hj
    have hfieldMem : S.recursiveFields[j]! ∈ S.fields := by
      rw [← F.traversal_fields]
      apply F.traversal.decisions.selected_subset
      rw [F.traversal_recursiveFields, getElem!_pos S.recursiveFields j hjr]
      exact Array.getElem_mem hjr
    have hfieldP : ∀ fv, S.recursiveFields[j]! = .fvar fv →
        (fun fv => fv ∈ ExprArrayFVarIds S.fields ∨
          fv ∈ ExprArrayFVarIds stats.params) fv := by
      intro fv hfv
      left
      rw [hfv] at hfieldMem
      exact mem_exprArrayFVarIds_of_fvar_mem hfieldMem
    have hparamsRoot : ∀ p ∈ stats.params.toList, ∃ fv, p = .fvar fv ∧
        fv ∈ originRoot.lctx.fvars := by
      intro p hpm
      obtain ⟨pv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.params (Array.mem_toList_iff.1 hpm)
      exact ⟨pv, rfl, hle.fvars (hparamTerm pv (Array.mem_toList_iff.1 hpm))⟩
    obtain ⟨hargs, hexp, htype⟩ :=
      O.hitShape W hp henv Rorigin hscope hfieldP hparamsRoot
    refine ⟨⟨D, by rw [hD]; exact htype.consumeTypeAnnotationsVerified hp⟩, ?_⟩
    rw [hcall]
    refine ⟨?_, by
      have := (checkPositivityStep.isValidIndApp?_some O.owner_valid).1
      exact hstats ▸ this⟩
    obtain ⟨ffv, hffv, -⟩ := O.field_fvar
    refine Expr.HitShape.mkLambda_of_disjoint O.arguments_bound.expressions ?_ ?_ ?_
    · refine .app (Expr.HitShape.mkAppN (.bvar _) (hexp.getAppArgs_slice hp _))
        (Expr.HitShape.mkAppN (by rw [hffv]; exact .fvar ffv) ?_)
      intro a ha
      rw [O.arguments_bound.expressions] at ha
      simp only [List.mem_map] at ha
      obtain ⟨y, -, rfl⟩ := ha
      exact .fvar y
    · intro p hpm
      obtain ⟨pv, rfl, hpv⟩ := hparamsRoot p hpm
      exact ⟨pv, rfl, fun h => O.arguments_bound.fresh pv h hpv⟩
    · intro y hy
      have hyCur : y ∈ O.current.lctx.fvars := O.arguments_bound.members y hy
      obtain ⟨index, name, ty, bi, kind, hfind⟩ := O.current_wf.findCDecl y hyCur
      exact ⟨_, hfind, hargs y hy _ hfind⟩
  refine ⟨hfieldDecls, ?_, fun j hj => (hper j hj).2⟩
  -- The minor premise type.
  rw [← S.consumed_eq]
  refine Expr.HitShape.consumeTypeAnnotationsVerified ?_ hp
  rw [S.sourceType_eq, ← S.sourceContext_eq]
  refine Expr.HitShape.mkForall_of_disjoint S.fields_bound.expressions ?_ ?_ hfieldDecls
  · refine Expr.HitShape.mkForall_of_disjoint S.hypotheses_bound.expressions ?_ ?_ ?_
    · rw [hmotiveApp]
      simp only [AddInductive.getIIndices]
      have hmo := (checkPositivityStep.isValidIndApp?_some hvalid).1
      obtain ⟨mfv, hmfv⟩ := H.motive_fvar hmo
      refine .app (Expr.HitShape.mkAppN ?_ (hterm.getAppArgs_slice hp _))
        (Expr.HitShape.mkAppN_const_paramsArray ?_ hp)
      · simp only [AddInductive.getIIndices] at hmfv
        rw [hmfv]; exact .fvar mfv
      · intro a ha
        obtain ⟨y, rfl, -⟩ := BoundFVarArray.fvar_of_mem S.fields_bound
          (Array.mem_toList_iff.1 ha)
        exact .fvar y
    · intro p hpm
      obtain ⟨pv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.params (Array.mem_toList_iff.1 hpm)
      refine ⟨pv, rfl, fun hy => ?_⟩
      have hpvP : pv ∈ ExprArrayFVarIds origins.stats.params := by
        rw [hstats]; exact mem_exprArrayFVarIds_of_fvar_mem (Array.mem_toList_iff.1 hpm)
      apply origins.hypotheses_outer_fresh pv (List.mem_append_left _ hpvP)
      rw [S.hypotheses_bound.exprArrayFVarIds]; exact hy
    · intro y hy
      obtain ⟨j, hjl, hjy⟩ := List.mem_iff_getElem.1 hy
      have hj : j < S.hypotheses.size := by
        have := congrArg Array.size S.hypotheses_bound.expressions
        simp at this; omega
      obtain ⟨D, hDshape⟩ := (hper j hj).1
      have hDy : D.fvar = y := by
        obtain ⟨_, hget⟩ := S.hypotheses_bound.getElem_eq_fvar j hj
        have := D.expression.symm.trans hget
        rw [← hjy]; exact Expr.fvar.inj this
      subst hDy
      exact ⟨_, D.declaration, hDshape⟩
  · intro p hpm
    obtain ⟨pv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.params (Array.mem_toList_iff.1 hpm)
    refine ⟨pv, rfl, fun hy => hfresh pv hy ?_⟩
    exact List.mem_append_left _ (List.mem_append_left _
      (mem_exprArrayFVarIds_of_fvar_mem (Array.mem_toList_iff.1 hpm)))

section Outer

variable {heads : List Name}

theorem paramCDecls : ∀ x ∈ H.params.fvars, ∃ i fv n ty bi kind,
    H.localContext.lctx.find? x = some (.cdecl i fv n ty bi kind) := by
  intro x hx
  obtain ⟨index, name, type, bi, kind, hfind⟩ :=
    H.localWF.findCDecl x (H.params.members x hx)
  exact ⟨index, x, name, type, bi, kind, hfind⟩

theorem mem_recInfos {k : Nat} (hk : k < H.recInfos.size) : H.recInfos[k]! ∈ H.recInfos := by
  rw [getElem!_pos H.recInfos k hk]; exact Array.getElem_mem hk

/-- Index declarations of every family (region R1): along the retained
`loopArgs1` trace of the family, from the header. -/
theorem indexDeclHitShape (I : H.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads stats.params.toList stats.levels H.localContext.env)
    {k : Nat} (hk : k < H.recInfos.size) {y : FVarId}
    (hy : Expr.fvar y ∈ H.recInfos[k]!.indices) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.HitShape heads stats.params.toList stats.levels := by
  obtain ⟨type, T⟩ := H.minorSources.traces k hk
  have hparamDecls : ∀ fv ∈ ExprArrayFVarIds stats.params, ∀ d,
      H.localContext.lctx.find? fv = some d →
        d.HitShape heads stats.params.toList stats.levels := by
    intro fv hfv d hfind
    rw [H.params.exprArrayFVarIds] at hfv
    exact I.paramDecls fv hfv d hfind
  obtain ⟨-, hidx⟩ := T.hitShape W H.params_fvar rfl hparamDecls
    (Expr.HitShape.of_avoidsConsts (I.familyHeaders k (H.sourceOwner hk)))
  have hyMem : y ∈ (H.bindings.indices k hk).fvars :=
    (H.bindings.indices k hk).mem_fvars_iff.2 hy
  obtain ⟨index, name, ty, bi, kind, hfind⟩ :=
    H.localWF.findCDecl y ((H.bindings.indices k hk).members y hyMem)
  refine ⟨_, hfind, hidx y ?_ _ hfind⟩
  rw [(H.bindings.indices k hk).exprArrayFVarIds]
  exact hyMem

/-- Major premise declarations: `I params indices`, a hit exactly for
auxiliary families. -/
theorem majorDeclHitShape {y : FVarId} (hy : Expr.fvar y ∈ H.recInfos.map (·.major)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.HitShape heads stats.params.toList stats.levels := by
  refine H.origins.majors.declHitShape (fun i hi => ?_) hy
  have hi' : i < H.recInfos.size := by simpa using hi
  rw [H.majorShapes.shape i hi']
  refine Expr.HitShape.consumeTypeAnnotationsVerified ?_ H.params_fvar
  obtain ⟨n, hn⟩ := H.indConst_eq hi'
  rw [hn]
  refine Expr.HitShape.mkAppN_const_paramsArray (fun a ha => ?_) H.params_fvar
  obtain ⟨fv, rfl, -⟩ := BoundFVarArray.fvar_of_mem (H.bindings.indices i hi')
    (Array.mem_toList_iff.1 ha)
  exact .fvar fv

theorem indices_outer {k : Nat} (hk : k < H.recInfos.size) :
    ∀ y ∈ (H.bindings.indices k hk).fvars,
      Expr.fvar y ∈ H.recInfos.map (·.motive) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.minors) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.indices) ∨
      Expr.fvar y ∈ H.recInfos.map (·.major) := by
  intro y hy
  exact .inr (.inr (.inl (Array.mem_flatMap.2 ⟨_, H.mem_recInfos hk,
    (H.bindings.indices k hk).mem_fvars_iff.1 hy⟩)))

theorem major_outer {k : Nat} (hk : k < H.recInfos.size) :
    ∀ y ∈ (H.bindings.major k hk).fvars,
      Expr.fvar y ∈ H.recInfos.map (·.motive) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.minors) ∨
      Expr.fvar y ∈ H.recInfos.flatMap (·.indices) ∨
      Expr.fvar y ∈ H.recInfos.map (·.major) := by
  intro y hy
  have h := (H.bindings.major k hk).mem_fvars_iff.1 hy
  simp only [List.mem_toArray, List.mem_singleton] at h
  refine .inr (.inr (.inr ?_))
  rw [h]
  exact Array.mem_map.2 ⟨_, H.mem_recInfos hk, rfl⟩

/-- Motive declarations: `∀ indices, ∀ (t : I params indices), Sort u`. -/
theorem motiveDeclHitShape (I : H.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads stats.params.toList stats.levels H.localContext.env)
    {y : FVarId}
    (hy : Expr.fvar y ∈ H.recInfos.map (·.motive)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.HitShape heads stats.params.toList stats.levels := by
  refine H.origins.motives.declHitShape (fun i hi => ?_) hy
  have hi' : i < H.recInfos.size := by simpa using hi
  rw [H.motiveShapes.shape i hi']
  refine Expr.HitShape.mkForall_of_disjoint (H.bindings.indices i hi').expressions ?_
    (H.params_disjoint (H.indices_outer hi')) (fun y hy => H.indexDeclHitShape I W hi'
      ((H.bindings.indices i hi').mem_fvars_iff.1 hy))
  refine Expr.HitShape.mkForall_of_disjoint (H.bindings.major i hi').expressions (.sort _)
    (H.params_disjoint (H.major_outer hi')) (fun y hy => H.majorDeclHitShape ?_)
  have h := (H.bindings.major i hi').mem_fvars_iff.1 hy
  simp only [List.mem_toArray, List.mem_singleton] at h
  rw [h]
  exact Array.mem_map.2 ⟨_, H.mem_recInfos hi', rfl⟩

/-- Minor premise declarations. -/
theorem minorDeclHitShape (I : H.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads stats.params.toList stats.levels H.localContext.env)
    {y : FVarId} (hy : Expr.fvar y ∈ H.recInfos.flatMap (·.minors)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.HitShape heads stats.params.toList stats.levels := by
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hy
  obtain ⟨D⟩ := H.bindings.flatMinors.declarationAt H.localWF i hi
  obtain ⟨Fm⟩ := H.origins.flatMinorOrigin D
  have hDy : D.fvar = y := Expr.fvar.inj (D.expression.symm.trans hget)
  subst hDy
  refine ⟨_, D.declaration, ?_⟩
  show D.type.HitShape heads stats.params.toList stats.levels
  rw [Fm.originType_eq]
  have howner := Fm.owner_lt
  have hlocal : Fm.localIndex < H.origins.minorTypes[Fm.owner]!.size := by
    rw [(H.origins.minors Fm.owner howner).size_eq, getElem!_pos H.recInfos Fm.owner howner]
    exact Fm.local_lt
  have hsrc := H.minorSources.rows Fm.owner howner (H.sourceOwner howner) Fm.localIndex hlocal
  rw [← hsrc.1]
  exact (H.minorHitShape I W Fm.owner howner Fm.localIndex hlocal).2.1

/-- **Declarations of the recursor-construction context.** Every outer binder
of the generated recursors (parameters, motives, minor premises, indices and
major premises) is declared in the recursor context with a type in hit shape. -/
theorem outerDeclHitShape (I : H.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads stats.params.toList stats.levels H.localContext.env) :
    ∀ fv ∈ H.bindings.allFvars H.params, ∃ d, H.localContext.lctx.find? fv = some d ∧
      d.HitShape heads stats.params.toList stats.levels := by
  intro fv hfv
  rw [H.bindings.allFvars_eq H.params] at hfv
  simp only [List.mem_append] at hfv
  rcases hfv with hp | hm | hmi | hi | hma
  · obtain ⟨index, name, type, bi, kind, hfind⟩ :=
      H.localWF.findCDecl fv (H.params.members fv hp)
    exact ⟨_, hfind, I.paramDecls fv hp _ hfind⟩
  · exact H.motiveDeclHitShape I W (H.bindings.motives.mem_fvars_iff.1 hm)
  · exact H.minorDeclHitShape I W (H.bindings.flatMinors.mem_fvars_iff.1 hmi)
  · have h := H.bindings.flatIndices.mem_fvars_iff.1 hi
    obtain ⟨info, hinfo, hmem⟩ := Array.mem_flatMap.1 h
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hinfo
    refine H.indexDeclHitShape I W hk ?_
    rw [getElem!_pos H.recInfos k hk]; exact hmem
  · exact H.majorDeclHitShape (H.bindings.majors.mem_fvars_iff.1 hma)

end Outer

/-- **Generated recursor types are parameter telescopes in hit shape.** For
every owner, the executable recursor type
`(declareRecursors.recursorType stats recInfos lctx owner).inferImplicit 1000 false`
(as recorded in `GeneratedRecursorEntry.type`) is `HitShapeTele heads nparams ls`. -/
theorem recursorTypeHitShape {heads : List Name} (I : H.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads stats.params.toList stats.levels H.localContext.env)
    (owner : Nat) (howner : owner < H.recInfos.size) :
    Expr.HitShapeTele heads stats.params.size stats.levels
      ((H.localContext.lctx.mkForall stats.params <|
        H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
        H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
        H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
        H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
          (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
            H.recInfos[owner]!.major)).inferImplicit 1000 false) := by
  have hp := H.params_fvar
  refine Expr.HitShapeTele.inferImplicit ?_ 1000 false
  refine Expr.HitShape.mkForall_params ?_ H.params_toList H.params_nodup H.paramCDecls
  have hownerC : owner < stats.indConsts.size := by
    rw [H.validStats.types_size, ← H.recInfos_size_eq]; exact howner
  obtain ⟨mfv, hmfv⟩ := H.motive_fvar hownerC
  have hmajorMem : H.recInfos[owner]!.major ∈ #[H.recInfos[owner]!.major] := by simp
  obtain ⟨jfv, hjfv, -⟩ := BoundFVarArray.fvar_of_mem (H.bindings.major owner howner) hmajorMem
  -- body
  have hbody : (Expr.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
      H.recInfos[owner]!.major).HitShape heads stats.params.toList stats.levels := by
    refine .app (Expr.HitShape.mkAppN (by rw [hmfv]; exact .fvar mfv) fun a ha => ?_)
      (by rw [hjfv]; exact .fvar jfv)
    obtain ⟨fv, rfl, -⟩ := BoundFVarArray.fvar_of_mem (H.bindings.indices owner howner)
      (Array.mem_toList_iff.1 ha)
    exact .fvar fv
  refine Expr.HitShape.mkForall_of_disjoint H.bindings.motives.expressions ?_
    (H.params_disjoint fun y hy => .inl (H.bindings.motives.mem_fvars_iff.1 hy))
    (fun y hy => H.motiveDeclHitShape I W (H.bindings.motives.mem_fvars_iff.1 hy))
  refine Expr.HitShape.mkForall_of_disjoint H.bindings.flatMinors.expressions ?_
    (H.params_disjoint fun y hy => .inr (.inl (H.bindings.flatMinors.mem_fvars_iff.1 hy)))
    (fun y hy => H.minorDeclHitShape I W (H.bindings.flatMinors.mem_fvars_iff.1 hy))
  refine Expr.HitShape.mkForall_of_disjoint (H.bindings.indices owner howner).expressions ?_
    (H.params_disjoint (H.indices_outer howner))
    (fun y hy => H.indexDeclHitShape I W howner
      ((H.bindings.indices owner howner).mem_fvars_iff.1 hy))
  refine Expr.HitShape.mkForall_of_disjoint (H.bindings.major owner howner).expressions hbody
    (H.params_disjoint (H.major_outer howner)) (fun y hy => H.majorDeclHitShape ?_)
  have h := (H.bindings.major owner howner).mem_fvars_iff.1 hy
  simp only [List.mem_toArray, List.mem_singleton] at h
  rw [h]
  exact Array.mem_map.2 ⟨_, H.mem_recInfos howner, rfl⟩

/-- **Generated rule right-hand sides are parameter telescopes in hit shape.**
For every owner and every retained rule blueprint, the executable rule
right-hand side `(blueprint.build indTypes stats motives minors lvls lctx).rhs`
(as recorded in `GeneratedRecursorEntry.rules_eq`) is
`HitShapeTele heads nparams ls`: a `lam` telescope over the parameters around
`fun motives minors fields => minor fields (calls)` in bound-variable hit shape.
The generated recursor heads `.const (mkRecName I) lvls` of the recursive calls
are not heads (`HitShapeInputs.recursorNames`), so `lvls` is arbitrary. -/
theorem ruleRhsHitShape {heads : List Name} (I : H.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads stats.params.toList stats.levels H.localContext.env)
    (owner : Nat) (howner : owner < H.recInfos.size) (lvls : List Level)
    (blueprint : AddInductive.RecRuleBlueprint)
    (hmem : blueprint ∈ H.recInfos[owner]!.ruleBlueprints.toList) :
    Expr.HitShapeTele heads stats.params.size stats.levels
      (blueprint.build indTypes stats (H.recInfos.map (·.motive))
        (H.recInfos.flatMap (·.minors)) lvls H.localContext.lctx).rhs := by
  have hp := H.params_fvar
  obtain ⟨localIndex, hlocalB, hget⟩ := List.mem_iff_getElem.1 hmem
  have hlocalB' : localIndex < H.recInfos[owner]!.ruleBlueprints.size := by simpa using hlocalB
  have hlocal : localIndex < H.origins.minorTypes[owner]!.size := by
    rw [← H.blueprints.rows_size owner howner]; exact hlocalB'
  have hB : H.recInfos[owner]!.ruleBlueprints[localIndex]! = blueprint := by
    rw [getElem!_pos _ localIndex hlocalB']; simpa using hget
  obtain ⟨hfieldDecls, -, hcalls⟩ := H.minorHitShape I W owner howner localIndex hlocal
  have hentry := H.blueprints.entry owner howner localIndex hlocal
  rw [hB] at hcalls hentry
  obtain ⟨-, hBfields, hBlctx, hBminor, traversal, origins, -, hshape, -, -, hcallOrigins⟩ :=
    hentry
  have hcallsSize := hcallOrigins.size_eq
  have hfresh := H.blueprints.fields_outer_fresh owner howner localIndex hlocal
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at *
  -- the minor variable
  have hminorsSize : localIndex < H.recInfos[owner]!.minors.size := by
    rw [← (H.origins.minors owner howner).size_eq]; exact hlocal
  have hminorMem : blueprint.minor ∈ H.recInfos[owner]!.minors := by
    rw [hBminor, getElem!_pos _ localIndex hminorsSize]; exact Array.getElem_mem hminorsSize
  obtain ⟨minorFv, hminorFv, -⟩ :=
    BoundFVarArray.fvar_of_mem (H.bindings.minors owner howner) hminorMem
  simp only [AddInductive.RecRuleBlueprint.build]
  refine Expr.HitShape.mkLambda_params ?_ H.params_toList H.params_nodup H.paramCDecls
  refine Expr.HitShape.mkLambda_of_disjoint H.bindings.motives.expressions ?_
    (H.params_disjoint fun y hy => .inl (H.bindings.motives.mem_fvars_iff.1 hy))
    (fun y hy => H.motiveDeclHitShape I W (H.bindings.motives.mem_fvars_iff.1 hy))
  refine Expr.HitShape.mkLambda_of_disjoint H.bindings.flatMinors.expressions ?_
    (H.params_disjoint fun y hy => .inr (.inl (H.bindings.flatMinors.mem_fvars_iff.1 hy)))
    (fun y hy => H.minorDeclHitShape I W (H.bindings.flatMinors.mem_fvars_iff.1 hy))
  rw [hBlctx, hBfields]
  refine Expr.HitShape.mkLambda_of_disjoint S.fields_bound.expressions ?_ ?_ hfieldDecls
  · refine Expr.HitShape.mkAppN (Expr.HitShape.mkAppN (by rw [hminorFv]; exact .fvar _)
      fun a ha => ?_) fun a ha => ?_
    · obtain ⟨y, rfl, -⟩ := BoundFVarArray.fvar_of_mem S.fields_bound
        (Array.mem_toList_iff.1 ha)
      exact .fvar y
    · simp only [Array.toList_map, List.mem_map] at ha
      obtain ⟨call, hcall, rfl⟩ := ha
      obtain ⟨j, hj, hcallj⟩ := List.mem_iff_getElem.1 hcall
      have hj' : j < blueprint.recursiveCalls.size := by simpa using hj
      have hcallEq : blueprint.recursiveCalls[j]! = call := by
        rw [getElem!_pos _ j hj']; simpa using hcallj
      obtain ⟨htemplate, htarget⟩ := hcalls j (by rw [← hcallsSize]; exact hj')
      rw [hcallEq] at htemplate htarget
      simp only [AddInductive.RecCallBlueprint.build]
      refine htemplate.instantiate1 ?_ hp
      refine Expr.HitShape.mkAppN (Expr.HitShape.mkAppN
        (Expr.HitShape.mkAppN (.const (I.recursorNames _ htarget)) fun a ha => ?_)
          fun a ha => ?_) fun a ha => ?_
      · obtain ⟨fv, rfl⟩ := hp a ha
        exact .fvar fv
      · obtain ⟨fv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.bindings.motives
          (Array.mem_toList_iff.1 ha)
        exact .fvar fv
      · obtain ⟨fv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.bindings.flatMinors
          (Array.mem_toList_iff.1 ha)
        exact .fvar fv
  · intro p hpm
    obtain ⟨pv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.params (Array.mem_toList_iff.1 hpm)
    exact ⟨pv, rfl, fun hy => hfresh pv hy (List.mem_append_left _ (List.mem_append_left _
      (mem_exprArrayFVarIds_of_fvar_mem (Array.mem_toList_iff.1 hpm))))⟩

end CompletedRecursorConstruction

/-! ### Installed generated recursors -/

/-- Hit shape of the type and of every rule right-hand side of each generated
recursor entry of a completed recursor phase. -/
theorem CompletedRecursorPhasesResult.generatedHitShape
    {outEnv : Environment} (C : CompletedRecursorPhasesResult R outEnv)
    {heads : List Name} (I : C.toCompletedRecursorConstruction.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads stats.params.toList stats.levels C.localContext.env)
    (i : Nat) (hi : i < C.entries.length) :
    Expr.HitShapeTele heads stats.params.size stats.levels (C.generated.entry i hi).info.type ∧
      ∀ rule ∈ (C.generated.entry i hi).info.rules,
        Expr.HitShapeTele heads stats.params.size stats.levels rule.rhs := by
  have howner : i < C.recInfos.size := by rw [← C.generated.length]; exact hi
  refine ⟨?_, ?_⟩
  · rw [(C.generated.entry i hi).type]
    exact C.toCompletedRecursorConstruction.recursorTypeHitShape I W i howner
  · intro rule hrule
    rw [(C.generated.entry i hi).rules_eq] at hrule
    simp only [List.mem_map] at hrule
    obtain ⟨blueprint, hmem, rfl⟩ := hrule
    exact C.toCompletedRecursorConstruction.ruleRhsHitShape I W i howner _ blueprint hmem

end Assembly

/-! ### Exact validated nested runs -/

/-- The auxiliary heads of a nested run: the names of the lowered families after
the source families, each followed by the names of its constructors. This is
the head list `auxiliaries.flatMap (·.headNames)` of the run's container
specialisations (`NestedValidatedRunResult.loweredConstructorLevels_heads`).
The theorems below are stated for an arbitrary head list; this is the intended
instance. -/
def NestedValidatedRunResult.auxHeads
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) : List Name :=
  InductiveSignature.familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length)

section Run

variable {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)

/-- The production statistics carry the declaration's universe parameters. -/
theorem NestedValidatedRunResult.statsLevels :
    E.production.stats.levels = lparams.map Level.param := by
  have h := E.production.headers.materialized.levelParams
  rwa [E.production_c, E.productionContext_lparams] at h

/-- The production statistics carry exactly the lowered run's parameters. -/
theorem NestedValidatedRunResult.statsParamsSize :
    E.production.stats.params.size = result.nparams := by
  obtain ⟨_, Hrun, _, _⟩ := E.lowering
  rw [Hrun.resultNParams, E.production.production.cardinality.params,
    E.production.constructors.core.nparams, E.production_nparams]

/-- The generated entry of an owner is the recursor read back by any
restoration step at the owner's recursor name. -/
theorem NestedValidatedRunResult.generatedEntryOfStep
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.production.production.completed.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    ∃ hi : owner.val < E.production.production.completed.entries.length,
      (E.production.production.completed.generated.entry owner.val hi).info =
        Hstep.oldInfo := by
  rcases E.production.production.completed.metadataRealization owner with
    ⟨rec, hrec, _, M⟩
  have hlen : owner.val < E.production.production.completed.entries.length := by
    rw [E.production.production.completed.entries_length_eq]
    exact owner.isLt
  refine ⟨hlen, ?_⟩
  have hmem := List.getElem_mem (l := E.production.production.entries)
    (n := owner.val) hlen
  have hfind := E.production.production.findRecursorOfMem
    (info := (E.production.production.entries[owner.val]'hlen).1) hmem
  have hrec' : (E.production.production.entries[owner.val]'hlen).1 = .recInfo rec := hrec
  rw [hrec'] at hfind
  change E.loweredEnv.find? rec.name = some (.recInfo rec) at hfind
  have h2 : some (ConstantInfo.recInfo rec) = some (.recInfo Hstep.oldInfo) := by
    rw [← hfind, M.name]
    exact Hstep.lookup
  have heq : rec = Hstep.oldInfo := by
    injection h2 with h
    injection h
  have hG := (E.production.production.completed.generated.entry owner.val hlen).source_eq
  rw [hrec] at hG
  injection hG with hG
  rw [← heq, hG]

/-- **Hit shape of the lowered recursor type and rule right-hand sides of an
exact validated nested run.** For every generated owner and every executable
restoration step at the owner's lowered recursor name, the stored recursor type
and every stored rule right-hand side are closed parameter telescopes of
`result.nparams` binders whose body is in bound-variable hit shape for the
auxiliary heads at the levels `lparams.map Level.param`.

Hypotheses: `W` (the `whnf` hit-shape preservation fact, see
`WhnfHitShapeFacts`) and `I` (the non-`whnf` provenance, see
`CompletedRecursorConstruction.HitShapeInputs`). -/
theorem NestedValidatedRunResult.recursorHitShape
    {heads : List Name}
    (I : E.production.production.completed.toCompletedRecursorConstruction.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads E.production.stats.params.toList (lparams.map Level.param)
      E.production.production.localContext.env)
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.production.production.completed.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    Expr.HitShapeTele heads result.nparams (lparams.map Level.param) Hstep.oldInfo.type ∧
      ∀ rule ∈ Hstep.oldInfo.rules,
        Expr.HitShapeTele heads result.nparams (lparams.map Level.param) rule.rhs := by
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  rw [← E.statsLevels] at W ⊢
  rw [← E.statsParamsSize]
  have H := E.production.production.completed.generatedHitShape I W owner.val hi
  rw [hinfo] at H
  exact H

/-- `recursorHitShape`, type component. -/
theorem NestedValidatedRunResult.recursorTypeHitShape
    {heads : List Name}
    (I : E.production.production.completed.toCompletedRecursorConstruction.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads E.production.stats.params.toList (lparams.map Level.param)
      E.production.production.localContext.env)
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.production.production.completed.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    Expr.HitShapeTele heads result.nparams (lparams.map Level.param) Hstep.oldInfo.type :=
  (E.recursorHitShape I W owner Hstep).1

/-- `recursorHitShape`, rule component. -/
theorem NestedValidatedRunResult.ruleRhsHitShape
    {heads : List Name}
    (I : E.production.production.completed.toCompletedRecursorConstruction.HitShapeInputs heads)
    (W : WhnfHitShapeFacts heads E.production.stats.params.toList (lparams.map Level.param)
      E.production.production.localContext.env)
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {auxRec : NameMap Name} {allIndNames : List Name}
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.production.production.completed.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    ∀ rule ∈ Hstep.oldInfo.rules,
      Expr.HitShapeTele heads result.nparams (lparams.map Level.param) rule.rhs :=
  (E.recursorHitShape I W owner Hstep).2

end Run

/-! ### Lowered constructor types -/

theorem _root_.Lean.Expr.AvoidsConsts.of_mem_getAppArgsList {names : List Name}
    {e : Expr} (h : e.AvoidsConsts names) :
    ∀ a ∈ e.getAppArgsList, a.AvoidsConsts names := by
  induction h with
  | app _ _ _ hx ihf _ =>
    intro a ha
    rw [Expr.getAppArgsList_app] at ha
    rcases List.mem_append.1 ha with ha | ha
    · exact ihf a ha
    · rw [List.mem_singleton.1 ha]; exact hx
  | _ => intro a ha; simp [Expr.getAppArgsList] at ha

/-- **Lowering hits are in hit shape.** The semantic lowering map of an input
that mentions no head produces an output in free-variable hit shape over the
opened parameters `As`: every replacement is
`mkAppN (.const auxName state.lvls) As` applied to untouched source arguments,
with `auxName` an auxiliary family (a key of `aux2nested`). -/
theorem NestedExprMapping.hitShape {heads : List Name} {ls : List Level}
    {env : Environment} {lctx : LocalContext} {params As : Array Expr}
    {finalResult : Lean4Lean.ElimNestedInductive.Result}
    {input : Expr} {state : Lean4Lean.ElimNestedInductive.State}
    {out : Expr × Lean4Lean.ElimNestedInductive.State}
    (H : NestedExprMapping env lctx params As finalResult input state out)
    (hkeys : ∀ auxName nested, finalResult.aux2nested.find? auxName = some nested →
      auxName ∈ heads)
    (hin : input.AvoidsConsts heads) (hlvls : state.lvls = ls) :
    out.1.HitShape heads As.toList ls := by
  induction H with
  | hit Hnode =>
    rcases Hnode.mapping with
      ⟨value, targetName, levels, auxName, auxLevels, nested,
        Hcandidate, hauxLevels, hhead, hlowered, hnested, hlookup⟩
    rw [hlowered, Expr.mkAppRange_to_end _ _ _ Hcandidate.parameters.arity,
      Lean4Lean.VerifyInductive.Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append,
      hauxLevels, hlvls]
    refine Expr.HitShape.mkAppList_const_hit (hkeys _ _ hlookup) fun a ha => ?_
    refine Expr.HitShape.of_avoidsConsts (hin.of_mem_getAppArgsList a ?_)
    rw [← Expr.getAppArgs_toList]
    exact List.mem_of_mem_drop ha
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => cases hin with | const _ _ h => exact .const h
  | lit => exact .lit _
  | app Hnode Hfn Harg ihFn ihArg =>
    cases hin with
    | app _ _ hf ha =>
      simpa [Expr.updateApp!] using
        Expr.HitShape.app (ihFn hf hlvls) (ihArg ha (Hfn.lvls.trans hlvls))
  | lam Hnode Hdom Hbody ihDom ihBody =>
    cases hin with
    | lam _ _ _ _ hd hb =>
      simpa [Expr.updateLambdaE!] using
        Expr.HitShape.lam (ihDom hd hlvls) (ihBody hb (Hdom.lvls.trans hlvls))
  | forallE Hnode Hdom Hbody ihDom ihBody =>
    cases hin with
    | forallE _ _ _ _ hd hb =>
      simpa [Expr.updateForallE!] using
        Expr.HitShape.forallE (ihDom hd hlvls) (ihBody hb (Hdom.lvls.trans hlvls))
  | letE Hnode Htype Hvalue Hbody ihType ihValue ihBody =>
    cases hin with
    | letE _ _ _ _ _ ht hv hb =>
      simpa [Expr.updateLet!] using
        Expr.HitShape.letE (ihType ht hlvls) (ihValue hv (Htype.lvls.trans hlvls))
          (ihBody hb (Hvalue.lvls.trans (Htype.lvls.trans hlvls)))
  | mdata Hnode Hbody ihBody =>
    cases hin with
    | mdata _ _ hb => simpa [Expr.updateMData!] using Expr.HitShape.mdata (ihBody hb hlvls)
  | proj Hnode Hbody ihBody =>
    cases hin with
    | proj _ _ _ hb => simpa [Expr.updateProj!] using Expr.HitShape.proj (ihBody hb hlvls)

theorem _root_.Lean.Expr.AvoidsConsts.instantiate1'_fvar {names : List Name} {e : Expr}
    (h : e.AvoidsConsts names) (fv : FVarId) (k : Nat) :
    (e.instantiate1' (.fvar fv) k).AvoidsConsts names := by
  induction h generalizing k with
  | bvar i =>
    simp only [Expr.instantiate1']
    split
    · exact .bvar _
    · split
      · simp only [Expr.liftLooseBVars']; exact .fvar _
      · exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const _ _ h => exact .const _ _ h
  | app _ _ _ _ ihf iha => exact .app _ _ (ihf k) (iha k)
  | lam _ _ _ _ _ _ iht ihb => exact .lam _ _ _ _ (iht k) (ihb (k + 1))
  | forallE _ _ _ _ _ _ iht ihb => exact .forallE _ _ _ _ (iht k) (ihb (k + 1))
  | letE _ _ _ _ _ _ _ _ iht ihv ihb =>
    exact .letE _ _ _ _ _ (iht k) (ihv k) (ihb (k + 1))
  | lit _ h _ => exact .lit _ h
  | mdata _ _ _ ih => exact .mdata _ _ (ih k)
  | proj _ _ _ _ ih => exact .proj _ _ _ (ih k)

/-- Opening a parameter telescope with free variables keeps name avoidance. -/
theorem NestedParamOpening.tailAvoidsConsts {names : List Name}
    {lctx : LocalContext} {params : Array Expr} {type : Expr} {n : Nat}
    {outLctx : LocalContext} {tail : Expr} {outParams : Array Expr}
    (H : NestedParamOpening lctx params type n outLctx tail outParams)
    (h : type.AvoidsConsts names) : tail.AvoidsConsts names := by
  induction H with
  | done => exact h
  | step _ ih =>
    cases h with
    | forallE _ _ _ _ _ hb =>
      apply ih
      rw [Expr.instantiate1_eq]
      exact hb.instantiate1'_fvar _ 0

/-- **Lowered constructor types are parameter telescopes in hit shape**, given
that the constructor's source type mentions no head, every key of the final
`aux2nested` map is a head, and the lowering state carries the levels `ls`. -/
theorem LoweredConstructorMapping.hitShapeTele {heads : List Name} {ls : List Level}
    {env : Environment} {params : Array Expr} {nparams : Nat}
    {finalResult : Lean4Lean.ElimNestedInductive.Result}
    {source : Constructor} {state : Lean4Lean.ElimNestedInductive.State}
    {out : Constructor × Lean4Lean.ElimNestedInductive.State}
    (H : LoweredConstructorMapping env params nparams finalResult source state out)
    (hkeys : ∀ auxName nested, finalResult.aux2nested.find? auxName = some nested →
      auxName ∈ heads)
    (hsource : source.type.AvoidsConsts heads) (hlvls : state.lvls = ls) :
    Expr.HitShapeTele heads nparams ls out.1.type := by
  obtain ⟨lctx, tail, As, lowered, openedState, Hopen, -, Hselection, hnodup, -, -, -,
    hsize, Hmap, htype⟩ := H.mapped
  have hopenedLvls : openedState.lvls = ls := by
    rw [← Hmap.lvls, H.lvls, hlvls]
  have Hlowered := Hmap.hitShape hkeys (Hopen.tailAvoidsConsts hsource) hopenedLvls
  rw [htype, ← hsize]
  refine Expr.HitShape.mkForall_params Hlowered
    (by have h := congrArg Array.toList Hselection.expressions; simpa using h)
    hnodup fun x hx => ?_
  obtain ⟨index, name, type, bi, kind, hfind⟩ := Hselection.declarations x hx
  exact ⟨index, x, name, type, bi, kind, hfind⟩

private theorem not_mem_of_not_reserved {heads : List Name}
    (hheads : ∀ h ∈ heads, (`_nested).isPrefixOf h = true) {c : Name}
    (hc : (`_nested).isPrefixOf c = false) : c ∉ heads := fun h => by
  rw [hheads c h] at hc; cases hc

/-- Literals expand to constructor applications of `Nat`, `Char`, `List` and
`String`, none of which is reserved. -/
theorem avoidsConsts_lit_of_reserved {heads : List Name}
    (hheads : ∀ h ∈ heads, (`_nested).isPrefixOf h = true) (l : Literal) :
    (Expr.lit l).AvoidsConsts heads := by
  have hnat : ∀ n : Nat, (Expr.lit (.natVal n)).AvoidsConsts heads := by
    intro n
    induction n with
    | zero =>
      exact .lit _ (.const _ _ (not_mem_of_not_reserved hheads (by decide)))
    | succ n ih =>
      exact .lit _ (.app _ _ (.const _ _ (not_mem_of_not_reserved hheads (by decide))) ih)
  cases l with
  | natVal n => exact hnat n
  | strVal s =>
    refine .lit _ ?_
    simp only [Literal.toConstructor, Expr.strLitToConstructor]
    refine .app _ _ (.const _ _ (not_mem_of_not_reserved hheads (by decide))) ?_
    induction s.toList with
    | nil =>
      exact .app _ _ (.const _ _ (not_mem_of_not_reserved hheads (by decide)))
        (.const _ _ (not_mem_of_not_reserved hheads (by decide)))
    | cons ch rest ih =>
      exact .app _ _ (.app _ _ (.app _ _
        (.const _ _ (not_mem_of_not_reserved hheads (by decide)))
        (.const _ _ (not_mem_of_not_reserved hheads (by decide))))
        (.app _ _ (.const _ _ (not_mem_of_not_reserved hheads (by decide))) (hnat _))) ih

/-- Source syntax that mentions no constant of the reserved `_nested` namespace
avoids every head in that namespace. -/
theorem NoNestedAux.avoidsConsts {heads : List Name}
    (hheads : ∀ h ∈ heads, (`_nested).isPrefixOf h = true) :
    ∀ {e : Expr}, NoNestedAux e → e.AvoidsConsts heads
  | .bvar _, _ => .bvar _
  | .fvar _, _ => .fvar _
  | .mvar _, _ => .mvar _
  | .sort _, _ => .sort _
  | .lit l, _ => avoidsConsts_lit_of_reserved hheads l
  | .const c _, H => by
    refine .const _ _ fun hc => ?_
    have := hheads c hc
    simp [NoNestedAux, Expr.findAny, this] at H
  | .app f a, H => by
    simp only [NoNestedAux, Expr.findAny, Bool.or_eq_false_iff] at H
    exact .app _ _ (NoNestedAux.avoidsConsts hheads H.1.2) (NoNestedAux.avoidsConsts hheads H.2)
  | .lam _ t b _, H => by
    simp only [NoNestedAux, Expr.findAny, Bool.or_eq_false_iff] at H
    exact .lam _ _ _ _ (NoNestedAux.avoidsConsts hheads H.1.2)
      (NoNestedAux.avoidsConsts hheads H.2)
  | .forallE _ t b _, H => by
    simp only [NoNestedAux, Expr.findAny, Bool.or_eq_false_iff] at H
    exact .forallE _ _ _ _ (NoNestedAux.avoidsConsts hheads H.1.2)
      (NoNestedAux.avoidsConsts hheads H.2)
  | .letE _ t v b _, H => by
    simp only [NoNestedAux, Expr.findAny, Bool.or_eq_false_iff] at H
    exact .letE _ _ _ _ _ (NoNestedAux.avoidsConsts hheads H.1.1.2)
      (NoNestedAux.avoidsConsts hheads H.1.2) (NoNestedAux.avoidsConsts hheads H.2)
  | .mdata _ e, H => by
    simp only [NoNestedAux, Expr.findAny, Bool.or_eq_false_iff] at H
    exact .mdata _ _ (NoNestedAux.avoidsConsts hheads H.2)
  | .proj _ _ e, H => by
    simp only [NoNestedAux, Expr.findAny, Bool.or_eq_false_iff] at H
    exact .proj _ _ _ (NoNestedAux.avoidsConsts hheads H.2)

end VerifyInductive
end Lean4Lean
