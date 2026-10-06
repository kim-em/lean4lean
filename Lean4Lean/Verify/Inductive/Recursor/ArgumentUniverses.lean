import Lean4Lean.Verify.Inductive.Recursor.ConsumedGenerationAssembly
import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldUniverses
import Lean4Lean.Verify.Inductive.Recursor.LoopUniverses

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
  let RF := Rroot.withCheckLCtx (loopUArgsCheckLCtx root (.fvar fv))
    (Rroot.restrictTo _).1 (Rroot.restrictTo _).2
  obtain ⟨inferredTarget, hbelow, _, hinferredTr, hfieldTyping⟩ :=
    getTypeFVarInRecursorContext.WF Rroot hfield _ hinference
  have hfieldP : (Expr.fvar fv).FVarsIn P := by simpa [FVarsIn] using hfvP
  have hinferredU : O.loopInput.inferredType.levelParamsIn Us = true :=
    getTypeFVarInRecursorContext.levelsWF Rroot hfield _ hinference Us P hscope rfl hfieldP
  have hinferredP : O.loopInput.inferredType.FVarsIn P := hbelow P hscope.1 hfieldP
  have hinferredType : Rroot.venv.IsType recLparams.length
      Rroot.mlctx.vlctx.toCtx inferredTarget :=
    hfieldTyping.isType Rroot.checking.tr.wf Rroot.mlctx_wf.tr.wf.toCtx
  obtain ⟨hnormalizedBelow, hnormalizedTr⟩ :=
    whnfInRecursorContext.scopeWF RF hinferredTr _ hnormalization
  have hnormalizedU : O.loopInput.normalizedType.levelParamsIn Us = true :=
    whnfInRecursorContext.levelsWF RF hinferredTr _ hnormalization Us P hscope
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

/-- The universe support of every retained recursive call, read off the
producer's semantic call rows (`RecInfoCallBlueprintSemanticOrigin.universes`).
Every row's root context extends the recursor context and so has the
declaration's universe parameters. -/
theorem CompletedRecursorConstruction.argumentUniverses (H : CompletedRecursorConstruction R) :
    H.ArgumentUniverses := by
  intro owner howner localIndex hlocal
  dsimp only
  intro j hj
  obtain ⟨⟨_, _, _, _, F, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨HcallAt⟩⟩⟩ :=
    H.blueprintSemantics.entry owner howner localIndex hlocal
  have hj' : j < (H.origins.minorShapes owner howner localIndex hlocal).hypotheses.size := by
    rw [← HcallAt.size_eq]
    exact hj
  obtain ⟨originRoot, Rorigin, prior, Hprior, _, ⟨Csem⟩⟩ := HcallAt.entry j hj'
  have hl : originRoot.lparams = c.lparams := by
    rw [Hprior.contextLE.lparams_eq, ← F.terminalExtension.contextLE.lparams_eq,
      H.localExtends.lparams_eq]
  have hU := Csem.universes
  rw [hl] at hU
  exact hU

end

end Lean4Lean.VerifyInductive
