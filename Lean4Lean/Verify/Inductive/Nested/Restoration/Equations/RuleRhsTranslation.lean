import Lean4Lean.Verify.Inductive.Nested.Restoration.AuxiliaryProjections
import Lean4Lean.Verify.Inductive.Nested.Restoration.Equations.RuleTranslation
import Lean4Lean.Verify.Inductive.Nested.Restoration.HeadTranslation
import Lean4Lean.Verify.Inductive.Nested.Restoration.RestorableNameAvoidance

/-! # The restored rule right-hand sides of a nested run translate

`NestedValidatedRunResult.restoredRuleRhs_translates`: in the final abstract
environment of an assembly base of a nested run, the right-hand side of every
restored recursor rule translates, to the restoration of the generated
right-hand side. It instantiates `NestedRestorationOpening.translatesLambdaTrail`
with the renaming restoration substitution of the run
(`restoredEquationSubstitution`), the lowered rule translations of the
ordinary pipeline (`ruleRhsTranslations`), and the validated nested
auxiliaries for the replacement heads (`RestorationTableData.restoreHeadsTranslate`).

This is a route to the right-hand-side translation that does not read it off
the executable check of the restored rules, so that the check could run in the
complete restored environment as in the C++ kernel. It is not used by the final
assembly yet: it assumes `HF`, that the trailing arguments of auxiliary nodes and
the parameter domains of the lowered rules avoid the auxiliary family names
(`LoweredRulesAvoidAll.lean` proves the avoidance of every other restorable
name). `HF` is not proved; it needs the lowering invariant that the arguments
after the parameters at every auxiliary-family occurrence are copied source
syntax, and the positivity facts on induction-hypothesis domains.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### Contexts of opened parameters -/

theorem fvarScope_eq_map : ∀ (ats : List FVarId) (doms : List VExpr),
    ats.length = doms.length →
    fvarScope ats doms = ((ats.zip doms).map fun p =>
      ((some (p.1, []), VLocalDecl.vlam p.2) :
        Option (FVarId × List FVarId) × VLocalDecl)).reverse
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | f :: fs, d :: ds, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [fvarScope, fvarScope_eq_map fs ds h]

private theorem vlamMap_fvars : ∀ (L : List (FVarId × VExpr)),
    VLCtx.fvars (L.map fun p =>
      ((some (p.1, []), VLocalDecl.vlam p.2) :
        Option (FVarId × List FVarId) × VLocalDecl)) = L.map Prod.fst
  | [] => rfl
  | p :: L => by simp [vlamMap_fvars L]

private theorem vlamMap_toCtx : ∀ (L : List (FVarId × VExpr)),
    VLCtx.toCtx (L.map fun p =>
      ((some (p.1, []), VLocalDecl.vlam p.2) :
        Option (FVarId × List FVarId) × VLocalDecl)) = L.map Prod.snd
  | [] => rfl
  | p :: L => by simp [VLCtx.toCtx, vlamMap_toCtx L]

private theorem vlamCtx_wf {env : VEnv} {U : Nat} :
    ∀ (L : List (FVarId × VExpr)), (L.map Prod.fst).Nodup →
      OnCtx (L.map Prod.snd) (env.IsType U) →
      VLCtx.WF env U (L.map fun p =>
        ((some (p.1, []), VLocalDecl.vlam p.2) :
          Option (FVarId × List FVarId) × VLocalDecl))
  | [], _, _ => trivial
  | (f, d) :: L, hnd, hon => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine ⟨vlamCtx_wf L hnd.2 hon.1, ?_, ?_⟩
    · intro fv deps h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by rw [vlamMap_fvars]; exact hnd.1, by simp⟩
    · show env.IsType U _ d
      rw [vlamMap_toCtx]
      exact hon.2

theorem fvarScope_toCtx : ∀ (ats : List FVarId) (doms : List VExpr),
    ats.length = doms.length → (fvarScope ats doms).toCtx = doms.reverse
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | f :: fs, d :: ds, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [fvarScope, fvarScope_toCtx fs ds h, VLCtx.toCtx]

/-- Pointwise definitionally equal parameter domains give definitionally equal
opened parameter contexts. -/
theorem fvarScope_isDefEq {env : VEnv} {U : Nat} {ats : List FVarId} {l r : List VExpr}
    (hnodup : ats.Nodup) (hl : ats.length = l.length) (hr : ats.length = r.length)
    (H : VEnv.IsDefEqCtx env U [] l.reverse r.reverse) :
    VLCtx.IsDefEq env U (fvarScope ats l) (fvarScope ats r) := by
  refine VLCtx.IsDefEq.ofKeysCtx ?_ ?_ ?_ ?_ ?_
  · rw [fvarScope_eq_map _ _ hl, fvarScope_eq_map _ _ hr]
    simp only [List.map_reverse, List.map_map]
    congr 1
    rw [show ((Prod.fst ∘ fun p : FVarId × VExpr =>
        ((some (p.1, []), VLocalDecl.vlam p.2) :
          Option (FVarId × List FVarId) × VLocalDecl))) =
        (fun f : FVarId => (some (f, []) : Option (FVarId × List FVarId))) ∘ Prod.fst from rfl,
      ← List.map_map, ← List.map_map, List.map_fst_zip (by omega),
      List.map_fst_zip (by omega)]
  · intro e he
    rw [fvarScope_eq_map _ _ hl] at he
    simp only [List.mem_reverse, List.mem_map] at he
    obtain ⟨p, -, rfl⟩ := he
    exact ⟨_, _, rfl⟩
  · intro e he
    rw [fvarScope_eq_map _ _ hr] at he
    simp only [List.mem_reverse, List.mem_map] at he
    obtain ⟨p, -, rfl⟩ := he
    exact ⟨_, _, rfl⟩
  · rw [fvarScope_eq_map _ _ hl, ← List.map_reverse]
    refine vlamCtx_wf _ ?_ ?_
    · rw [List.map_reverse, List.map_fst_zip (by omega)]
      exact List.nodup_reverse.mpr hnodup
    · rw [List.map_reverse, List.map_snd_zip (by omega)]
      exact H.isType
  · rw [fvarScope_toCtx _ _ hl, fvarScope_toCtx _ _ hr]
    exact H

/-- Translation at the declaration's universe parameters gives translation at
the universe parameters of its recursors, in the context instantiated at the
abstract declaration levels of the recursors. -/
theorem TrExprS.toRecLevels {env : VEnv} {lparams : List Name} {elim : Level}
    (Helim : AddInductive.AdmissibleElimLevel lparams elim) {Δ : VLCtx} {e : Expr}
    {e' : VExpr} (hΔ : VLCtx.WF env lparams.length Δ) (H : TrExprS env lparams Δ e e') :
    ∃ v, TrExprS env (AddInductive.getRecLevelParams elim lparams)
      (Δ.instL (recursorDeclarationAbstractLevels lparams Helim)) e v := by
  cases elim with
  | zero =>
    refine ⟨e', ?_⟩
    simp only [AddInductive.getRecLevelParams, recursorDeclarationAbstractLevels]
    rw [hΔ.instL_id]
    exact H
  | param u =>
    have H' := TrExprS.prependLevelParam_of_fresh (fresh := u) Helim H
    rw [recursorDeclarationAbstractLevels_param Helim rfl]
    exact ⟨_, H'⟩
  | succ _ | max _ _ | imax _ _ | mvar _ =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem Expr.mkAppList_const_inj {c c' : Name} {ls ls' : List Level} {args args' : List Expr}
    (h : Expr.mkAppList (.const c ls) args = Expr.mkAppList (.const c' ls') args') :
    c = c' ∧ ls = ls' ∧ args = args' := by
  have h1 := congrArg Expr.getAppFn h
  have h2 := congrArg Expr.getAppArgsList h
  rw [Expr.getAppFn_mkAppList_const, Expr.getAppFn_mkAppList_const] at h1
  rw [Expr.getAppArgsList_mkAppList_const, Expr.getAppArgsList_mkAppList_const] at h2
  cases h1
  exact ⟨rfl, rfl, h2⟩

theorem List.forall₂_eq_of_fixed {f : α → Option α} :
    ∀ {l l' : List α}, List.Forall₂ (fun x y => f x = some y) l l' →
      (∀ x ∈ l, f x = some x) → l' = l
  | [], [], .nil, _ => rfl
  | x :: _, _ :: _, .cons h t, hfix => by
    rw [hfix x List.mem_cons_self] at h
    cases h
    rw [List.forall₂_eq_of_fixed t (fun y hy => hfix y (List.mem_cons_of_mem _ hy))]

theorem VExpr.wrapLams_prefix :
    ∀ {A B : List VExpr} {x y : VExpr}, VExpr.wrapLams A x = VExpr.wrapLams B y →
      A.length ≤ B.length → A = B.take A.length
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, h => by simp at h
  | a :: A, b :: B, x, y, h, hl => by
    change VExpr.lam a (VExpr.wrapLams A x) = VExpr.lam b (VExpr.wrapLams B y) at h
    injection h with h1 h2
    subst h1
    simp only [List.length_cons, Nat.add_le_add_iff_right] at hl
    rw [List.length_cons, List.take_succ_cons, ← VExpr.wrapLams_prefix h2 hl]

/-! ### The replacement heads of a nested run -/

/-- The universe and parameter data of the canonical generation of a nested
run, at the declaration's universe parameters `lparams`. -/
theorem NestedValidatedRunResult.canonicalGenerationLevels
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv) :
    ∃ Helim : AddInductive.AdmissibleElimLevel lparams E.production.production.elimLevel,
      AddInductive.getRecLevelParams E.production.production.elimLevel
          E.production.c.lparams =
        AddInductive.getRecLevelParams E.production.production.elimLevel lparams ∧
      E.production.production.canonicalGeneration.params =
        E.production.headers.commonParameterContext.reverse.map
          (VExpr.instL (recursorDeclarationAbstractLevels lparams Helim)) := by
  have hlp : E.production.c.lparams = lparams :=
    (congrArg AddInductive.Context.lparams E.production_c).trans E.productionContext_lparams
  have h1 := E.production.production.toRecursorConstruction.elimLevelAdmissible
  have h2 := E.production.production.toRecursorConstruction.generator.levels
  have h3 := E.production.production.toRecursorConstruction.generator.params
  have hscope := OrdinaryConstructorCheck.completed_parameterScope_toCtx E.production.constructors
  have key : ∀ (ps : List Name) (hps : E.production.c.lparams = ps),
      ∃ Helim : AddInductive.AdmissibleElimLevel ps E.production.production.elimLevel,
        AddInductive.getRecLevelParams E.production.production.elimLevel
            E.production.c.lparams =
          AddInductive.getRecLevelParams E.production.production.elimLevel ps ∧
        E.production.production.canonicalGeneration.params =
          E.production.headers.commonParameterContext.reverse.map
            (VExpr.instL (recursorDeclarationAbstractLevels ps Helim)) := by
    intro ps hps
    subst hps
    refine ⟨h1, rfl, ?_⟩
    change (E.production.production.toRecursorConstruction.generator.signature.params).map
      (VExpr.instL E.production.production.toRecursorConstruction.generator.generation.levels) = _
    rw [h2, h3, hscope]
  exact key lparams hlp

/-- **The replacement heads of a nested run translate** at the universe
parameters of its recursors, over the opened canonical parameters: the
recorded container applications translate in the source header environment
(`restorationTablesRestoringAllSpec`), at parameter domains definitionally
equal to the canonical ones. -/
theorem NestedValidatedRunResult.restoredHeadsTranslate
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    {auxRec : NameMap Name}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv auxRec lparams)
    (HauxSpec : ∀ a ∈ auxiliaries, ∃ nested,
      result.aux2nested.find? a.auxiliary = some nested ∧
      AuxNestedSpecAt envTypes E.production.headers.commonParameterContext result lparams
        nested a)
    {envT : VEnv} (hT : envT.WF) (hle : envTypes ≤ envT)
    {ats : List FVarId} (hnodup : ats.Nodup) (hlen : ats.length = result.nparams)
    {Δt0 : VLCtx}
    (hsame : VLCtx.SameUpToDeps
      (fvarScope ats E.production.production.canonicalGeneration.params) Δt0) :
    RestoreHeadsTranslate (compilationRestoration sourceDecl auxiliaries) result
      E.loweredEnv envT
      (AddInductive.getRecLevelParams E.production.production.elimLevel lparams)
      (lparams.map Level.param) ⟨ats.map .fvar⟩ Δt0 := by
  obtain ⟨Helim, -, hcp⟩ := E.canonicalGenerationLevels
  have hLwf := recursorDeclarationAbstractLevels_wf Helim
  have hbaseLE : ves.venv (if isUnsafe then .unsafe else .safe) ≤ envT :=
    (VEnv.addConstVals_le hadded).trans hle
  refine D.restoreHeadsTranslate hT ?_ ?_ hnodup hlen hsame
  · intro name nested hfind c lvls Ys hab
    obtain ⟨a, ha, rfl, -⟩ := D.familyKey _ nested hfind
    obtain ⟨nested', hfind', domains, lvls', Ys', hdlen, hctx, hab', -, hYs'⟩ := HauxSpec a ha
    rw [hfind] at hfind'
    cases hfind'
    rw [hab] at hab'
    obtain ⟨-, -, rfl⟩ := Expr.mkAppList_const_inj hab'
    have hclen : E.production.headers.commonParameterContext.length = domains.length := by
      have := hctx.length_eq
      simpa using this.symm
    refine ⟨domains.map (·.instL (recursorDeclarationAbstractLevels lparams Helim)),
      by simp [hdlen], ?_, ?_⟩
    · intro Y hY
      obtain ⟨y, -, hy⟩ := Lean4Lean.List.Forall₂.forall_exists_l hYs' Y hY
      have hwf : VLCtx.WF envTypes lparams.length (abstractForallContext domains []) :=
        (abstractForallContext.isDefEq
          (right := E.production.headers.commonParameterContext.reverse)
          (by simpa using hctx)).wf
      obtain ⟨v, hv⟩ := TrExprS.toRecLevels Helim hwf hy
      rw [VLCtx.instL_abstractForallContext] at hv
      exact ⟨v, by simpa [VLCtx.instL] using hv.mono hle⟩
    · rw [hcp]
      refine fvarScope_isDefEq hnodup (by simp [hlen, hdlen]) (by simp [hlen, hdlen, hclen]) ?_
      have H := (VEnv.IsDefEqCtx.instL hLwf hctx).mono hle
      simpa [List.map_reverse] using H
  · intro a ha
    obtain ⟨g, -, hev⟩ := Lean4Lean.List.Forall₂.forall_exists_l Haux a ha
    have hfam := hev.installed.familyConstant a.family a.family.isLt
    refine ⟨⟨_, hbaseLE.constants hfam, ?_⟩, ?_⟩
    · rw [hev.levelsLength]
      exact hev.installed.typeUvars _ (List.getElem_mem _)
    · intro ctor hctor
      have hsrc : a.source ∈ a.container.types := List.getElem_mem _
      refine ⟨_, hbaseLE.constants (hev.installed.constructorConstant_mem hsrc hctor), ?_⟩
      rw [hev.levelsLength]
      exact hev.installed.constructorUvars _
        (List.mem_flatMap.mpr ⟨_, hsrc, hctor⟩)

theorem NestedValidatedRunResult.restoredRuleRhs_translates
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (HF : E.LoweredRulesAvoid E.auxHeads E.auxFamilyNames)
    (B : NestedFinalAssemblyBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hB : B.production = E.production)
    (hV : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.finalBaseVEnv)
    (owner : Fin E.production.production.generationSignature.families.size)
    {s t : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.production.canonicalGeneration.recursorName owner) s t)
    (j : Nat) (hj : j < Hstep.restored.newInfo.rules.length) :
    ∃ target, TrExprS B.finalBaseVEnv Hstep.restored.newInfo.levelParams []
        (Hstep.restored.newInfo.rules[j]'hj).rhs target ∧
      ∀ (k : Fin E.production.production.generationSignature.constructors.size),
        k.val = recursorMinorOffset E.production.indTypes owner.val + j →
      ∀ auxiliaries : List ContainerSpecialization,
        RestorationTableData sourceDecl auxiliaries result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams →
        (compilationRestoration sourceDecl auxiliaries).expr
          (E.production.production.canonicalGeneration.equation k).rhs = some target := by
  let P := E.production.production
  rcases E.restorationTablesRestoringAllSpec wf Hsources with
    ⟨envTypes, generated, aux, hadded, henvTypes, Haux, Hexpansion, hparamsSize, D,
      Hrestoring, -, HauxSpec⟩
  have G := E.restoredEquationGaps wf Hsources aux D B hB hV
  have S := E.restoredEquationSubstitution wf Hsources hadded henvTypes Haux Hexpansion
    hparamsSize D Hrestoring B hB hV G
  have hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  have hheads : (compilationRestoration sourceDecl aux).heads.map (·.auxiliary) =
      E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hTwf : B.finalBaseVEnv.WF := hV.tr.wf
  -- the lowered rule
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have hlenRules := Hstep.restored.restoration.rules.length
  have hjOld : j < Hstep.oldInfo.rules.length := hlenRules ▸ hj
  have hmap := P.ownedConstructors_map_val owner hi
  have hlenOwned : (P.generationSignature.ownedConstructors owner).length =
      Hstep.oldInfo.rules.length := by
    have h := congrArg List.length hmap
    simp only [List.length_map, List.length_range'] at h
    rw [h, hinfo]
  have hjOwned : j < (P.generationSignature.ownedConstructors owner).length := by
    rw [hlenOwned]; exact hjOld
  let k := (P.generationSignature.ownedConstructors owner)[j]
  have hk : k.val = recursorMinorOffset E.production.indTypes owner.val + j :=
    RuleAssembly.getElem_of_map_val_eq hmap j hjOwned
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
  have Hrule := Hstep.restored.restoration.rules.entry j hjOld hj
  rcases Hrule.rhs.opening hparamsSize with ⟨Hopen⟩
  have Hshape := (E.recursorHitShape' wf Hsources owner Hstep).2 _ (List.getElem_mem hjOld)
  rw [← hheads] at Hshape
  have hnp : result.nparams = P.generationSignature.params.length := by
    rw [← E.statsParamsSize]; exact P.params_size_eq
  let Lfull := P.canonicalGeneration.params ++ P.canonicalGeneration.motives ++
    P.canonicalGeneration.minors ++
    insertBinders ((P.generationSignature.fieldTypes
      P.generationSignature.constructors[k]).map
      (·.instL P.canonicalGeneration.levels))
      (P.generationSignature.families.size + P.generationSignature.constructors.size)
  have hcpLen : P.canonicalGeneration.params.length = result.nparams := by
    simp only [Instance.params, List.length_map]; exact hnp.symm
  have hlen : P.generationSignature.params.length + 1 ≤ Lfull.length := by
    have hfam : 0 < P.generationSignature.families.size :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) owner.isLt
    simp only [Lfull, List.length_append, Instance.params, Instance.motives, List.length_map,
      List.length_zipIdx, Array.length_toList]
    omega
  obtain ⟨X, hX⟩ : ∃ X, (P.canonicalGeneration.equation k).rhs = VExpr.wrapLams Lfull X :=
    ⟨_, rfl⟩
  have htakeL : Lfull.take result.nparams = P.canonicalGeneration.params := by
    simp only [Lfull, List.append_assoc]
    exact List.take_left' hcpLen
  obtain ⟨d, Ds, hL⟩ : ∃ d Ds, Lfull = d :: Ds := by
    cases h : Lfull with
    | nil => rw [h] at hlen; simp at hlen
    | cons d Ds => exact ⟨d, Ds, rfl⟩
  have hrhsEq : (P.canonicalGeneration.equation k).rhs = VExpr.wrapLams (d :: Ds) X :=
    hL ▸ hX
  have hlenD : result.nparams ≤ (d :: Ds).length := by
    rw [← hL]; omega
  rw [hrhsEq] at Hs
  obtain ⟨body, Hlead, HB⟩ := Hshape
  have Htel := Hlead.lambdaTelescope_of_tr Hs hlenD
  have HL := E.loweredRulesAvoid_restorable_of_families wf Hsources D E.auxHeads HF owner
    Hstep.oldInfo Hstep.lookup _ (List.getElem_mem hjOld)
  rw [← hheads] at HL
  have HP := E.loweredRules_projsOK wf Hsources D owner Hstep.oldInfo Hstep.lookup _
    (List.getElem_mem hjOld)
  rw [Hstep.restored.restoration.levelParams] at *
  -- literals
  have hres := E.restorableNames_reserved D
  have hkept : ∀ c, (`_nested).isPrefixOf c = false →
      P.outVEnv.contains c → B.finalBaseVEnv.contains c := by
    intro c hc ⟨ci, hci⟩
    obtain ⟨ci', hci', -⟩ := RenamingRestorationSubstitutionOnCtx.kept_of_not_mem S hci
      (fun hm => by rw [hres c hm] at hc; cases hc)
    exact ⟨ci', hci'⟩
  have Hlits : ∀ l, P.outVEnv.ContainsLits l → B.finalBaseVEnv.ContainsLits l := by
    intro l hl
    cases l with
    | natVal => exact hkept _ (by decide) hl
    | strVal => exact ⟨hkept _ (by decide) hl.1, hkept _ (by decide) hl.2⟩
  -- the canonical parameters are fixed by restoration
  have hle : envTypes ≤ B.finalBaseVEnv := by
    have hvenvTypes : B.canonical.venvTypes = envTypes := by
      have h1 := B.canonical.abstract_types
      rw [B.typeValues, hadded] at h1
      exact (Option.some.inj h1).symm
    have hctorsAdded := B.canonical.abstract_ctors
    rw [B.constructorValues, hvenvTypes] at hctorsAdded
    exact (VEnv.addConstVals_le hctorsAdded).trans
      (VEnv.addEliminators_addProjections_le.trans B.canonical.recursorsAdded.le)
  have hfixed : ∀ x ∈ P.canonicalGeneration.params,
      (compilationRestoration sourceDecl aux).expr x = some x := by
    obtain ⟨Helim, -, hcp⟩ := E.canonicalGenerationLevels
    intro x hx
    apply Restoration.expr_of_avoid
    rw [hcp] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [VExpr.containsAnyConst_instL]
    have hfresh := E.restorableNames_fresh hadded Haux Hexpansion hnodup
    have hctx := (E.commonParameterContext_refl wf).isType
    have hvesFresh : ∀ name ∈ (compilationRestoration sourceDecl aux).restorableNames,
        (ves.venv (if isUnsafe then .unsafe else .safe)).constants name = none :=
      fun name hn => (VEnv.addConstVals_le hadded).constants_eq_none_left (hfresh name hn)
    exact (wf.tr (safety := if isUnsafe then .unsafe else .safe)).wf.ordered.ctxNoFreshConsts
      hvesFresh hctx y (List.mem_reverse.mp hy)
  have hpsel : Hopen.params = ⟨Hopen.selection.fvars.map .fvar⟩ := by
    have h := Hopen.selection.expressions
    exact h.trans rfl
  have hselLen : Hopen.selection.fvars.length = result.nparams :=
    Hopen.selectionLength.trans hparamsSize
  obtain ⟨Helim, hUs, -⟩ := E.canonicalGenerationLevels
  have hUs' : Hstep.oldInfo.levelParams =
      AddInductive.getRecLevelParams P.elimLevel lparams := by
    rw [← hinfo, hlevels, hUs]
  rw [hUs'] at Hs
  obtain ⟨target, Ht, -, hr⟩ := Hopen.translatesLambdaTrail S D rfl
    E.production.production.outVEnvWF hTwf
    hTwf.betaSubjectReduction hscoped.argumentsClosed Hlits (E.restorableNames_lit D)
    (fun Ds' Dt Δt0 sR hs hDlen hF hsame => by
      have hDs : Ds' = P.canonicalGeneration.params := by
        have h := VExpr.wrapLams_prefix hs.symm (by omega)
        rw [h, hDlen, ← hL, htakeL]
      subst hDs
      have hDt := List.forall₂_eq_of_fixed hF hfixed
      subst hDt
      rw [hpsel]
      exact E.restoredHeadsTranslate hadded Haux D HauxSpec hTwf hle
        Hopen.selectionNodup hselLen hsame)
    Htel ⟨body, Hlead, HB⟩ HL.1 HL.2 HP Hs
  refine ⟨target, hUs' ▸ Ht, fun k' hk' auxiliaries D₁ => ?_⟩
  have hkk : k' = k := Fin.ext (hk'.trans hk.symm)
  subst hkk
  rw [← D.expr_eq D₁, hrhsEq]
  exact hr

/-- **Realization of a restored generated equation over an assembly base**,
without the rule validator: the right-hand side of the executable restored
rule translates (`restoredRuleRhs_translates`) to the restored generated
right-hand side. -/
theorem NestedValidatedRunResult.restoredRuleRealization_base
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (HF : E.LoweredRulesAvoid E.auxHeads E.auxFamilyNames)
    (B : NestedFinalAssemblyBase E.restoration
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe))
    (hB : B.production = E.production)
    (hV : CheckingEnv.Valid (if isUnsafe then .unsafe else .safe)
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)) B.finalBaseVEnv)
    {auxiliaries : List ContainerSpecialization}
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (k : Fin E.production.production.generationSignature.constructors.size)
    {rule : VDefEq}
    (hrule : (compilationRestoration sourceDecl auxiliaries).equation
      (E.production.production.canonicalGeneration.equation k) = some rule) :
    E.RestoredRuleRealization (compilationRestoration sourceDecl auxiliaries)
      B.finalBaseVEnv k rule := by
  let P := E.production.production
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes, generated, aux', hadded, henvTypes, Haux, Hexpansion, hparamsSize, D', -, -⟩
  have hnodup :
      (familyNames E.production.loweredDecl.types ++
        E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with
      ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  obtain ⟨-, -, -, -, -, -, -, hscoped, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D' True.intro
  have hwf : sourceProdEnv.constants.WF := (wf.tr (safety := .safe)).map_wf
  have hinfos := E.restoredRecursorEntryInfos B hB wf Hsources hadded Haux Hexpansion
    hnodup hparamsSize D' hscoped hwf
  let owner := P.generationSignature.constructors[k].owner
  obtain ⟨entry, -, s, t, Hstep, -, -, -⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l hinfos owner (List.mem_finRange owner)
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have hmap := P.ownedConstructors_map_val owner hi
  have hmem : k ∈ P.generationSignature.ownedConstructors owner := by
    simp [InductiveSignature.ownedConstructors, owner]
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hmem
  have hval := RuleAssembly.getElem_of_map_val_eq hmap j hj
  rw [hjk] at hval
  have hlenOwned : (P.generationSignature.ownedConstructors owner).length =
      Hstep.oldInfo.rules.length := by
    have h := congrArg List.length hmap
    simp only [List.length_map, List.length_range'] at h
    rw [h, hinfo]
  have hjNew : j < Hstep.restored.newInfo.rules.length := by
    rw [Hstep.restored.restoration.rules.length, ← hlenOwned]
    exact hj
  obtain ⟨target, Ht, hrhs⟩ := E.restoredRuleRhs_translates wf Hsources HF B hB hV
    owner Hstep j hjNew
  have hrhs := hrhs k hval auxiliaries D
  obtain ⟨huvars, hlhs, hrhs', htype⟩ := Restoration.equation_eq_some hrule
  have htarget : target = rule.rhs := Option.some.inj (hrhs.symm.trans hrhs')
  subst htarget
  exact ⟨owner, j, s, t, Hstep, hjNew, hval, huvars, Ht, hlhs, htype⟩

end VerifyInductive
end Lean4Lean
