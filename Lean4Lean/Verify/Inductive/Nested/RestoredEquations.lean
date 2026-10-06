import Lean4Lean.Verify.Inductive.Nested.RestoredBlockAssembly

/-! Restored equations of the canonical restored block of a validated nested
run.

`Instance.restoredEquations` restores the left-hand side, right-hand side and
type of every generated equation. The right-hand side of a restored rule is
produced by the executable (`restoreRule`, whose right-hand side is
`restoreNested` of the lowered rule's right-hand side); this file proves that
its translation is the abstract restoration of the generated equation's
right-hand side, using the hit shape of the lowered right-hand sides
(`NestedValidatedRunResult.recursorHitShape'`, whose only hypothesis beyond the
run is `hprims`). The lowered right-hand side is a
lambda telescope, so we first prove the lambda analogue of
`NestedRestoration.restorationCommutes'`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### Commutation for lambda telescopes -/

theorem restoration_expr_wrapLams' {r : Restoration} :
    ∀ {D₁ D₂ : List VExpr}, List.Forall₂ (fun x y => r.expr x = some y) D₁ D₂ →
      ∀ {body body' : VExpr}, r.expr body = some body' →
        r.expr (VExpr.wrapLams D₁ body) = some (VExpr.wrapLams D₂ body')
  | _, _, .nil, _, _, h => by simpa [VExpr.wrapLams] using h
  | _, _, .cons hd t, _, _, h => by
    have := restoration_expr_wrapLams' t h
    simp only [VExpr.wrapLams, List.foldr_cons] at this ⊢
    exact restoration_expr_lam hd this

/-- The unchanged parameter prefix of a lambda restoration: the translated
domains of the input and of the output are related by restoration. -/
theorem Expr.SameLambdaPrefix.translatedDomains_restore {r : Restoration}
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    {envS envT : VEnv} {Us : List Name}
    (Hfresh : ∀ n ∈ r.restorableNames, envT.constants n = none)
    {n : Nat} {left right : Expr} (Hsame : Expr.SameLambdaPrefix n left right) :
    ∀ {Δ₁ Δ₂ : VLCtx} {D₁ D₂ : List VExpr} {X₁ X₂ : VExpr},
      RestoreCtxRel r Δ₁ Δ₂ →
      TrExprS envS Us Δ₁ left (VExpr.wrapLams D₁ X₁) →
      TrExprS envT Us Δ₂ right (VExpr.wrapLams D₂ X₂) →
      D₁.length = n → D₂.length = n →
      List.Forall₂ (fun x y => r.expr x = some y) D₁ D₂ := by
  induction Hsame with
  | nil =>
    intro Δ₁ Δ₂ D₁ D₂ X₁ X₂ _ _ _ h₁ h₂
    rw [List.eq_nil_of_length_eq_zero h₁, List.eq_nil_of_length_eq_zero h₂]
    exact .nil
  | cons _ ih =>
    intro Δ₁ Δ₂ D₁ D₂ X₁ X₂ Hctx H₁ H₂ h₁ h₂
    cases D₁ with
    | nil => simp at h₁
    | cons d₁ D₁ =>
    cases D₂ with
    | nil => simp at h₂
    | cons d₂ D₂ =>
    simp only [VExpr.wrapLams, List.foldr_cons] at H₁ H₂
    cases H₁ with
    | lam _ hd₁ hb₁ =>
    cases H₂ with
    | lam _ hd₂ hb₂ =>
    exact .cons
      (Hctx.translate_avoids hc (checkPositivityStep.TrExprS.sourceAvoidsFresh Hfresh hd₂)
        hd₁ hd₂)
      (ih Hctx.vlam hb₁ hb₂ (by simpa using h₁) (by simpa using h₂))

private theorem fvarIdsIn_of_trExprS_abstractForallContext''
    {env : VEnv} {Us : List Name} {domains : List VExpr} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us (abstractForallContext domains []) e e') (P : FVarId → Prop) :
    e.FVarIdsIn P := by
  apply FVarsIn_to_FVarIdsIn
  apply H.fvarsIn.mono
  intro fv hfv
  simp [abstractForallContext, VLCtx.fvars] at hfv

/-- A lambda telescope stripped by `LeadingBinders` is the telescope's
residual. -/
theorem Expr.LambdaTelescope.leadingBinders_eq {e suffix body : Expr} {n : Nat}
    (Htel : Expr.LambdaTelescope e n suffix) (Hlead : Expr.LeadingBinders n e body) :
    body = suffix := by
  induction Htel generalizing body with
  | nil => cases Hlead; rfl
  | cons _ ih => cases Hlead with | lam Hb => exact ih Hb

/-- `LeadingBinders` of a term translating to a lambda telescope at least as
long are lambda binders. -/
theorem _root_.Lean.Expr.LeadingBinders.lambdaTelescope_of_tr {env : VEnv} {Us : List Name}
    {n : Nat} {e body : Expr} (H : Expr.LeadingBinders n e body) :
    ∀ {Δ : VLCtx} {D : List VExpr} {X : VExpr},
      TrExprS env Us Δ e (VExpr.wrapLams D X) → n ≤ D.length →
      Expr.LambdaTelescope e n body := by
  induction H with
  | zero => intros; exact .nil _
  | forallE _ _ =>
    intro Δ D X Htr hn
    cases D with
    | nil => simp at hn
    | cons d D =>
      simp only [VExpr.wrapLams, List.foldr_cons] at Htr
      cases Htr
  | lam _ ih =>
    intro Δ D X Htr hn
    cases D with
    | nil => simp at hn
    | cons d D =>
      simp only [VExpr.wrapLams, List.foldr_cons] at Htr
      cases Htr with
      | lam _ _ hb =>
        exact .cons (ih (D := D) (X := X) (by simpa [VExpr.wrapLams] using hb)
          (by simpa using hn))

/-- The restored body of an opening of a lambda telescope is closed when its
residual is. -/
theorem NestedRestorationOpening.restoredBody_closed_lam {decl : VInductDecl}
    {auxiliaries : List InductiveSignature.ContainerSpecialization}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {Us₀ : List Name}
    (D : RestorationTableData decl auxiliaries result env auxRec Us₀)
    {input output suffix : Expr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (Htel : Expr.LambdaTelescope input result.nparams suffix)
    (hsuffix : Closed suffix result.nparams) : Closed Hopen.restoredBody := by
  rcases Hopen.opening.lambdaResidualData Htel with ⟨fvars, hAs, hlen, hbody⟩
  have hparams : Hopen.params.toList = fvars.map Expr.fvar := by simpa using hAs
  have HAs : ∀ a ∈ Hopen.params.toList, ∃ fv, a = .fvar fv := by
    intro a ha
    rw [hparams] at ha
    rcases List.mem_map.mp ha with ⟨fv, _, rfl⟩
    exact ⟨fv, rfl⟩
  have hsize : Hopen.params.size = result.nparams := by
    rw [← Array.length_toList, hparams, List.length_map, hlen]
  have hbodyClosed : Closed Hopen.body := by
    rw [hbody]
    apply Closed.instantiateRevList
    · intro b hb
      rcases List.mem_map.mp hb with ⟨fv, _, rfl⟩
      trivial
    · simpa [hlen] using hsuffix
  exact Hopen.replacement.closed
    (fun t out k h ht => restoreNestedNode_closed (D.restoreHead_closed HAs hsize) h ht)
    0 hbodyClosed

/-- **Closed-term commutation for lambda telescopes** under the hit-shape
condition (generated rule right-hand sides). -/
theorem NestedRestorationOpening.restorationCommutesLam'
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {input output suffix : Expr}
    {s t : VExpr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hc : ∀ h ∈ r.heads, ∀ e ∈ h.arguments, e.ClosedN h.nparams)
    (Hfresh : ∀ n ∈ r.restorableNames, targetEnv.constants n = none)
    (Hshape : Hopen.body.HitShape (r.heads.map (·.auxiliary)) Hopen.params.toList auxLevels)
    (Htel : Expr.LambdaTelescope input result.nparams suffix)
    (hnotForall : input.isForall = false)
    (Hinput : input.FVarsIn fun _ => False) (hclosed : Closed input)
    (hrestored : Closed Hopen.restoredBody)
    (Hs : TrExprS sourceEnv Us [] input s) (Ht : TrExprS targetEnv Us [] output t) :
    r.expr s = some t := by
  have hnodup := Hopen.selectionNodup
  have hlen : Hopen.selection.fvars.length = result.nparams :=
    Hopen.selection.size.symm.trans Hopen.opening.initial_size
  have hparams := Hopen.selection.expressions
  have HAs : ∀ a ∈ Hopen.params.toList, ∃ fv, a = .fvar fv := by
    intro a ha
    rw [hparams] at ha
    simp at ha
    rcases ha with ⟨fv, _, rfl⟩
    exact ⟨fv, rfl⟩
  have hsize : Hopen.params.size = result.nparams := by
    rw [hparams]; simpa using hlen
  rcases Hopen.opening.lambdaResidualData Htel with ⟨fvars', hAs, _, hbody⟩
  have hfvars : fvars'.map Expr.fvar = Hopen.selection.fvars.map Expr.fvar := by
    have h1 : Hopen.params.toList = Hopen.selection.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList hparams
    rw [h1] at hAs
    simpa using hAs.symm
  rw [hfvars] at hbody
  rcases TrExprS.lambdaTelescope_shape_with_context Htel Hs with
    ⟨Ds, sR, hDs, rfl, HsR⟩
  have HbodyS := TrExprS.instantiateRevFVars Hopen.selection.fvars Ds [] suffix sR
    (hlen.trans hDs.symm) hnodup
    (fvarIdsIn_of_trExprS_abstractForallContext'' HsR _) HsR
  rw [← hbody, List.append_nil] at HbodyS
  have houtput : output = Hopen.lctx.mkLambda Hopen.params Hopen.restoredBody := by
    simpa [hnotForall] using Hopen.output_eq
  have HoutTel : Expr.LambdaTelescope output Hopen.selection.fvars.length
      (Hopen.restoredBody.abstractList Hopen.selection.fvars) := by
    have Htelescope := LocalContext.mkLambda_fvars_lambdaTelescopeList
      (body := Hopen.restoredBody) Hopen.selection.declarations hnodup hrestored
    simpa only [← Hopen.selection.expressions, ← houtput] using Htelescope
  rcases TrExprS.lambdaTelescope_shape_with_context HoutTel Ht with ⟨Dt, tR, hDt, rfl, HtR⟩
  have HbodyT := TrExprS.instantiateRevFVars Hopen.selection.fvars Dt [] _ tR
    hDt.symm hnodup
    (fvarIdsIn_of_trExprS_abstractForallContext'' HtR _) HtR
  rw [TypeChecker.Expr.abstractList_instantiateRevList_eq_self hnodup hrestored,
    List.append_nil, Hopen.replacement.eq_replace] at HbodyT
  have Hbody := _root_.Lean4Lean.VerifyInductive.restorationCommutes' A hc HAs hsize Hfresh
    Hshape (fvarScope_vlamShape _ Ds Dt (hDs.trans (hlen.symm.trans hDt.symm))).restoreCtxRel
    HbodyS HbodyT
  have hinput : Hopen.lctx.mkLambda Hopen.params Hopen.body = input :=
    Hopen.opening.root_mkLambda_tail Hopen.lctxWF Htel (FVarsIn_to_FVarIdsIn Hinput) hclosed
  have Hsame : Expr.SameLambdaPrefix Hopen.params.size input output := by
    have := Hopen.selection.sameLambdaPrefix hnodup Hopen.body Hopen.restoredBody
    rwa [hinput, ← houtput] at this
  rw [hsize] at Hsame
  exact restoration_expr_wrapLams'
    (Hsame.translatedDomains_restore hc Hfresh .nil Hs Ht hDs (hDt.trans hlen)) Hbody

/-- A closed lambda telescope has a residual closed at the depth of its
binders. -/
theorem Expr.LambdaTelescope.closed_result' {outer result : Expr} {arity depth : Nat}
    (H : Expr.LambdaTelescope outer arity result) (Houter : Closed outer depth) :
    Closed result (depth + arity) := by
  induction H generalizing depth with
  | nil => simpa using Houter
  | cons _ ih =>
    have Hresult := ih Houter.2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hresult

/-- **Hit shape of every opening** of a stored lambda telescope whose
parameter prefix is in bound-variable hit shape. -/
theorem NestedRestorationOpening.hitShape_of_lowered_lam
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {heads : List Name} {auxLevels : List Level}
    {input output suffix : Expr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (Htel : Expr.LambdaTelescope input result.nparams suffix)
    (Hshape : Expr.HitShapeTele heads result.nparams auxLevels input) :
    Hopen.body.HitShape heads Hopen.params.toList auxLevels := by
  rcases Hopen.opening.lambdaResidualData Htel with ⟨fvars, hAs, hlen, hbody⟩
  have hparams : Hopen.params.toList = fvars.map Expr.fvar := by simpa using hAs
  obtain ⟨body, Hlead, HB⟩ := Hshape
  cases Htel.leadingBinders_eq Hlead
  rw [hbody, hparams]
  rw [← hlen] at HB
  exact HB.instantiateRevList_fvars

/-- A term translating to a nonempty lambda telescope is not a `forallE`. -/
theorem TrExprS.isForall_false_of_wrapLams {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {d : VExpr} {D : List VExpr} {X : VExpr}
    (H : TrExprS env Us Δ e (VExpr.wrapLams (d :: D) X)) : e.isForall = false := by
  cases e with
  | forallE => simp only [VExpr.wrapLams, List.foldr_cons] at H; cases H
  | _ => rfl

/-- **The restored right-hand side of one rule.** Given `hprims` (see
`NestedValidatedRunResult.recursorHitShape'`), the translation of the right-hand side of the `j`-th
restored rule of the restoration step at a generated owner's lowered recursor
name, in an environment in which the restorable names are fresh, is the
abstract restoration of the right-hand side of the generated equation at the
flattened constructor index of that rule. -/
theorem NestedValidatedRunResult.restoredRuleRhs_of_hitShape
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hprims : ∀ n ∈ hitPrimNames, n ∉ E.mainCtorNames)
    {auxiliaries : List ContainerSpecialization}
    (hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    {trEnv : VEnv}
    (Hfresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      trEnv.constants n = none)
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.production.completed.canonicalGeneration.recursorName owner) s t)
    (j : Nat) (hj : j < Hstep.restored.newInfo.rules.length)
    (k : Fin E.production.production.completed.generationSignature.constructors.size)
    (hk : k.val = recursorMinorOffset E.production.indTypes owner.val + j)
    {rhs : VExpr}
    (Ht : TrExprS trEnv Hstep.restored.newInfo.levelParams []
      (Hstep.restored.newInfo.rules[j]'hj).rhs rhs) :
    (compilationRestoration sourceDecl auxiliaries).expr
      (E.production.production.completed.canonicalGeneration.equation k).rhs = some rhs := by
  let P := E.production.production.completed
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have hlenRules := Hstep.restored.restoration.rules.length
  have hjOld : j < Hstep.oldInfo.rules.length := hlenRules ▸ hj
  have hjGen : j < (P.generated.entry owner.val hi).info.rules.length := by
    rw [hinfo]; exact hjOld
  have hkb : recursorMinorOffset E.production.indTypes owner.val + j <
      P.generationSignature.constructors.size := hk ▸ k.isLt
  have Hs0 := P.ruleRhsTranslations owner.val hi j hjGen hkb
  have hkfin : (⟨recursorMinorOffset E.production.indTypes owner.val + j, hkb⟩ :
      Fin P.generationSignature.constructors.size) = k := Fin.ext hk.symm
  rw [hkfin] at Hs0
  have hlevels : (P.generated.entry owner.val hi).info.levelParams =
      AddInductive.getRecLevelParams P.elimLevel E.production.c.lparams := by
    rw [(P.generated.entry owner.val hi).levels, P.localExtends.lparams_eq]
  rw [← hlevels] at Hs0
  have Hs : TrExprS P.outVEnv Hstep.oldInfo.levelParams []
      (Hstep.oldInfo.rules[j]'hjOld).rhs (P.canonicalGeneration.equation k).rhs := by
    have key : ∀ (info : RecursorVal) (h : j < info.rules.length),
        info = Hstep.oldInfo →
        TrExprS P.outVEnv info.levelParams [] (info.rules[j]'h).rhs
          (P.canonicalGeneration.equation k).rhs →
        TrExprS P.outVEnv Hstep.oldInfo.levelParams []
          (Hstep.oldInfo.rules[j]'hjOld).rhs (P.canonicalGeneration.equation k).rhs := by
      intro info h hinfo' H
      subst hinfo'
      exact H
    exact key _ hjGen hinfo Hs0
  -- the rule restoration
  have Hrule := Hstep.restored.restoration.rules.entry j hjOld hj
  rcases Hrule.rhs.opening hparamsSize with ⟨Hopen⟩
  -- the telescope
  have Hshape := (E.recursorHitShape' wf Hsources hprims owner Hstep).2 _ (List.getElem_mem hjOld)
  rw [← hheads] at Hshape
  have hnp : result.nparams = P.generationSignature.params.length := by
    rw [← E.statsParamsSize]; exact P.params_size_eq
  have hfam : 0 < P.generationSignature.families.size :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) owner.isLt
  obtain ⟨d, Ds, X, hrhsEq, hlenD⟩ : ∃ d Ds X,
      (P.canonicalGeneration.equation k).rhs = VExpr.wrapLams (d :: Ds) X ∧
        result.nparams ≤ (d :: Ds).length := by
    have hlen : P.generationSignature.params.length + 1 ≤
        (P.canonicalGeneration.params ++ P.canonicalGeneration.motives ++
          P.canonicalGeneration.minors ++
          insertBinders ((P.generationSignature.fieldTypes
            P.generationSignature.constructors[k]).map
            (·.instL P.canonicalGeneration.levels))
            (P.generationSignature.families.size +
              P.generationSignature.constructors.size)).length := by
      simp only [List.length_append, Instance.params, Instance.motives, List.length_map,
        List.length_zipIdx, Array.length_toList]
      omega
    obtain ⟨X, hX⟩ : ∃ X, (P.canonicalGeneration.equation k).rhs =
        VExpr.wrapLams (P.canonicalGeneration.params ++ P.canonicalGeneration.motives ++
          P.canonicalGeneration.minors ++
          insertBinders ((P.generationSignature.fieldTypes
            P.generationSignature.constructors[k]).map
            (·.instL P.canonicalGeneration.levels))
            (P.generationSignature.families.size +
              P.generationSignature.constructors.size)) X := ⟨_, rfl⟩
    revert hlen hX
    generalize (P.canonicalGeneration.params ++ P.canonicalGeneration.motives ++
          P.canonicalGeneration.minors ++
          insertBinders ((P.generationSignature.fieldTypes
            P.generationSignature.constructors[k]).map
            (·.instL P.canonicalGeneration.levels))
            (P.generationSignature.families.size +
              P.generationSignature.constructors.size)) = L
    intro hlen hX
    cases L with
    | nil => simp at hlen
    | cons d Ds => exact ⟨d, Ds, X, hX, by simp only [List.length_cons] at hlen ⊢; omega⟩
  rw [hrhsEq] at Hs
  obtain ⟨body, Hlead, HB⟩ := Hshape
  have Htel := Hlead.lambdaTelescope_of_tr Hs hlenD
  have hclosed : Closed (Hstep.oldInfo.rules[j]'hjOld).rhs := by
    simpa [VLCtx.bvars] using Hs.closed
  have Hinput : (Hstep.oldInfo.rules[j]'hjOld).rhs.FVarsIn fun _ => False :=
    Hs.fvarsIn.mono fun _ h => by simp [VLCtx.fvars] at h
  have HbodyShape := Hopen.hitShape_of_lowered_lam Htel ⟨body, Hlead, HB⟩
  have hrestored := Hopen.restoredBody_closed_lam D Htel
    (by simpa using Htel.closed_result' hclosed)
  have Ht' : TrExprS trEnv Hstep.oldInfo.levelParams []
      (Hstep.restored.newInfo.rules[j]'hj).rhs rhs := by
    rw [← Hstep.restored.restoration.levelParams]; exact Ht
  rw [hrhsEq]
  exact Hopen.restorationCommutesLam' (D.agreement trEnv _) hscoped.argumentsClosed Hfresh
    HbodyShape Htel (TrExprS.isForall_false_of_wrapLams Hs) Hinput hclosed hrestored Hs Ht'

/-! ### The restored equation list -/

/-- **Realization of one restored equation.** The abstract equation `rule`
at generated constructor index `k` realizes the executable restored rule: for
some generated owner, restoration step at the owner's lowered recursor name,
and position `j` of that step's restored rule list with `k` the flattened
index of the rule (`recursorMinorOffset` of the owner plus `j`),

* `rule.uvars` is the generated equation's universe count;
* `rule.rhs` is the translation, in `trEnv`, of the right-hand side of the
  executable restored rule (`restoreRule`, i.e. `restoreNested` of the lowered
  rule's right-hand side) at the restored recursor's level parameters;
* `rule.lhs` and `rule.type` are the abstract restorations of the generated
  equation's left-hand side and type. The executable `RecursorRule` carries
  no left-hand side or type, so these two components have no executable
  counterpart to be translated. -/
def NestedValidatedRunResult.RestoredRuleRealization
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (r : Restoration) (trEnv : VEnv)
    (k : Fin E.production.production.completed.generationSignature.constructors.size)
    (rule : VDefEq) : Prop :=
  ∃ (owner : Fin E.production.production.completed.generationSignature.families.size)
    (j : Nat) (s t : Environment)
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.production.completed.canonicalGeneration.recursorName owner) s t)
    (hj : j < Hstep.restored.newInfo.rules.length),
    k.val = recursorMinorOffset E.production.indTypes owner.val + j ∧
    rule.uvars = (E.production.production.completed.canonicalGeneration.equation k).uvars ∧
    TrExprS trEnv Hstep.restored.newInfo.levelParams []
      (Hstep.restored.newInfo.rules[j]'hj).rhs rule.rhs ∧
    r.expr (E.production.production.completed.canonicalGeneration.equation k).lhs =
      some rule.lhs ∧
    r.expr (E.production.production.completed.canonicalGeneration.equation k).type =
      some rule.type

/-- **Realization of a restored equation list.** In some translation
environment in which the restorable names are fresh, the `k`-th abstract
equation realizes the executable restored rule at generated constructor
index `k`, for every `k`. -/
def NestedValidatedRunResult.RestoredRulesRealization
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (r : Restoration) (rules : List VDefEq) : Prop :=
  ∃ trEnv : VEnv, (∀ n ∈ r.restorableNames, trEnv.constants n = none) ∧
    List.Forall₂ (E.RestoredRuleRealization r trEnv)
      (List.finRange
        E.production.production.completed.generationSignature.constructors.size)
      rules

/-- **One restored equation.** A realizing abstract equation is the abstract
restoration of the generated equation. -/
theorem NestedValidatedRunResult.restoredEquation_of_realization
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hprims : ∀ n ∈ hitPrimNames, n ∉ E.mainCtorNames)
    {auxiliaries : List ContainerSpecialization}
    (hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    {trEnv : VEnv}
    (Hfresh : ∀ n ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames,
      trEnv.constants n = none)
    (k : Fin E.production.production.completed.generationSignature.constructors.size)
    {rule : VDefEq}
    (H : E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries) trEnv k
      rule) :
    (compilationRestoration sourceDecl auxiliaries).equation
      (E.production.production.completed.canonicalGeneration.equation k) = some rule := by
  obtain ⟨owner, j, s, t, Hstep, hj, hk, huvars, Ht, hlhs, htype⟩ := H
  have hrhs := E.restoredRuleRhs_of_hitShape wf Hsources hprims hheads hparamsSize D hscoped Hfresh owner
    Hstep j hj k hk Ht
  simp only [Restoration.equation, hlhs, hrhs, htype, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq]
  cases rule
  simp only at huvars
  rw [huvars]

/-- **The restored equation list.** If an abstract equation list realizes the
executable restored rules, it is the restored generated equation list. -/
theorem NestedValidatedRunResult.restoredEquations_of_realization
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hprims : ∀ n ∈ hitPrimNames, n ∉ E.mainCtorNames)
    {auxiliaries : List ContainerSpecialization}
    (hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    {rules : List VDefEq}
    (H : E.RestoredRulesRealization (compilationRestoration sourceDecl auxiliaries) rules) :
    E.production.compilationInstance.restoredEquations
      (compilationRestoration sourceDecl auxiliaries) = some rules := by
  obtain ⟨trEnv, Hfresh, HF⟩ := H
  show List.mapM _ ((List.finRange _).map _) = _
  rw [List.mapM_map]
  exact List.mapM_eq_some.mpr (Lean4Lean.List.Forall₂.imp (fun k _ h =>
    E.restoredEquation_of_realization wf Hsources hprims hheads hparamsSize D hscoped Hfresh k h) HF)

/-! ### The canonical restored block -/

/-- **The `equations` field of `NestedCompilationPending`.** If the rule
lists of the final assembly shape realize the executable restored rules
(`RestoredRulesRealization`), the restored generated equation list of the
lowered declaration is exactly the rule list of the canonical restored block,
given `hprims` (see `NestedValidatedRunResult.recursorHitShape'`). -/
theorem NestedValidatedRunResult.restoredEquations_of_hitShape
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hprims : ∀ n ∈ hitPrimNames, n ∉ E.mainCtorNames)
    {auxiliaries : List ContainerSpecialization}
    (hheads : (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) =
      E.auxHeads)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (hCrules : E.RestoredRulesRealization (compilationRestoration sourceDecl auxiliaries)
      (C.primaryRules ++ C.auxiliaryRules)) :
    E.production.compilationInstance.restoredEquations
        (compilationRestoration sourceDecl auxiliaries) =
      some (canonicalRestoredBlock sourceDecl C.primaryRecursors
        C.auxiliaryRecursors C.primaryRules C.auxiliaryRules).rules :=
  E.restoredEquations_of_realization wf Hsources hprims hheads hparamsSize D hscoped hCrules

/-- **`CompilationData` of a validated nested run with the final assembly
shape's own rule lists.** For the specializations of
`restorationTablesRestoringAll`:

* the restored generated recursor list is the recursor list of the canonical
  restored block (`restoredRecursors_of_hitShape`);
* if the shape's rule lists realize the executable restored rules for the
  run's restoration (`RestoredRulesRealization`), the restored generated
  equation list is the canonical restored block's rule list
  (`restoredEquations_of_hitShape`);
* given moreover totality of restoration on the normalized constructor types
  (`normalizedTotal`), the canonical restored block of the shape is the block
  of a `CompilationData`.

The realization hypothesis mentions the run's restoration, which is chosen
here, so it appears under the existential. -/
theorem NestedValidatedRunResult.compilationData_of_hitShape'
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WF sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (C : NestedFinalAssemblyShape E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hC : C.production = E.production)
    (hprims : ∀ n ∈ hitPrimNames, n ∉ E.mainCtorNames) :
    ∃ (envTypes : VEnv) (auxiliaries : List ContainerSpecialization),
      (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
        sourceDecl.typeConstants = some envTypes ∧
      envTypes.WF ∧
      auxiliaries.map (·.auxiliary) =
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map
          (·.name) ∧
      auxiliaries.flatMap (·.headNames) =
        familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length) ∧
      CertifiedSpecializations (ves.venv (if isUnsafe then .unsafe else .safe))
        auxiliaries ∧
      (∀ params : List VExpr,
        VEnv.IsDefEqCtx envTypes sourceDecl.uvars [] params.reverse
          E.production.headers.commonParameterContext →
        ∀ a ∈ auxiliaries, a.WellFormed envTypes sourceDecl params) ∧
      (∀ a ∈ auxiliaries, a.WellFormed envTypes sourceDecl
        E.production.constructors.completed.parameterScope.toCtx.reverse) ∧
      (compilationRestoration sourceDecl auxiliaries).Scoped ∧
      (∀ (U : Nat) (params : List VExpr), ∃ direct,
        auxiliaries.mapM (fun a => a.directFamily U params) = some direct ∧
        List.Forall₂ (DirectFamilyShape U) auxiliaries direct) ∧
      (∀ a ∈ auxiliaries, ∀ ctor ∈ a.source.ctors,
        result.restoreCtorName E.loweredEnv (a.constructorName ctor) =
          (compilationRestoration sourceDecl auxiliaries).restoredHeadName
            (a.constructorName ctor)) ∧
      (∀ name, (compilationRestoration sourceDecl auxiliaries).recursorName name =
        ((Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2.find? name).getD
          name) ∧
      (E.production.compilationInstance.restoredRecursors
          (compilationRestoration sourceDecl auxiliaries) =
        some (canonicalRestoredBlock sourceDecl C.primaryRecursors
          C.auxiliaryRecursors C.primaryRules C.auxiliaryRules).recursors ∧
      (E.RestoredRulesRealization (compilationRestoration sourceDecl auxiliaries)
          (C.primaryRules ++ C.auxiliaryRules) →
        E.production.compilationInstance.restoredEquations
            (compilationRestoration sourceDecl auxiliaries) =
          some (canonicalRestoredBlock sourceDecl C.primaryRecursors
            C.auxiliaryRecursors C.primaryRules C.auxiliaryRules).rules) ∧
      ((∀ normalized ∈ E.production.compilationSignature.declaration.types,
          ∀ ctor ∈ normalized.ctors, ∃ restored,
            (compilationRestoration sourceDecl auxiliaries).expr ctor.type = some restored) →
        E.RestoredRulesRealization (compilationRestoration sourceDecl auxiliaries)
          (C.primaryRules ++ C.auxiliaryRules) →
        Nonempty (CompilationData (ves.venv (if isUnsafe then .unsafe else .safe))
          sourceDecl E.production.loweredDecl E.production.compilationSignature
          E.production.compilationInstance auxiliaries
          (canonicalRestoredBlock sourceDecl C.primaryRecursors
            C.auxiliaryRecursors C.primaryRules C.auxiliaryRules)))) := by
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, Hrestoring, HauxRestoring⟩
  let r := compilationRestoration sourceDecl auxiliaries
  have hfreshAll := E.restorableNames_fresh hadded Haux Hexpansion hnodup
  have hfresh : ∀ name ∈ r.heads.map (·.auxiliary), envTypes.constants name = none :=
    fun name hname => hfreshAll name (List.mem_append_left _ hname)
  have hrecFresh : ∀ p ∈ r.recursors, envTypes.constants p.1 = none :=
    fun p hp => hfreshAll p.1 (List.mem_append_right _ (List.mem_map_of_mem hp))
  have hP := E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  obtain ⟨-, -, hnames, hheadNames, -, -, hwellFormed, hscoped, hdirect, -⟩ := hP
  have hlevels := E.loweredConstructorLevels_heads wf Hsources hheadNames
  have hrecursors := E.restoredRecursors_of_hitShape C hC wf Hsources hprims hadded Haux Hexpansion
    hnodup hparamsSize D hscoped
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hequations : E.RestoredRulesRealization r (C.primaryRules ++ C.auxiliaryRules) →
      E.production.compilationInstance.restoredEquations r =
        some (canonicalRestoredBlock sourceDecl C.primaryRecursors
          C.auxiliaryRecursors C.primaryRules C.auxiliaryRules).rules :=
    fun H => E.restoredEquations_of_hitShape C wf Hsources hprims hheads hparamsSize D hscoped H
  refine ⟨envTypes, auxiliaries,
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D
      ⟨hrecursors, hequations, ?_⟩⟩
  intro htotal hrealization
  have HsourceCtors := E.sourceConstructors_of_evidence wf hadded henvTypes Haux Hexpansion
    hnodup hfresh hrecFresh
    ⟨E.loweredConstructors_of_evidence hadded henvTypes hfreshAll Hrestoring hlevels,
      fun n hn => htotal n (List.mem_of_mem_take hn)⟩
  have HauxFamilies := E.auxiliaryFamiliesField_of_evidence wf hadded henvTypes Haux
    Hexpansion
    (E.auxiliaryConstructors_of_evidence wf Hsources hadded henvTypes Haux Hexpansion
      HauxRestoring hnodup (fun n hn => htotal n (List.mem_of_mem_drop hn)))
  exact ⟨E.compilationData_of_specializations C hC hadded hnames hwellFormed hscoped hdirect
    { sourceConstructors := HsourceCtors
      auxiliaryFamilies := HauxFamilies
      recursors := hrecursors
      equations := hequations hrealization }⟩

end VerifyInductive
end Lean4Lean
