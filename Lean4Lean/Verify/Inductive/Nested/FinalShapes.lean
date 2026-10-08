import Lean4Lean.Verify.Inductive.Nested.StrippedValidity
import Lean4Lean.Verify.Inductive.Nested.RestoredBlockAssembly

/-!
# Recursor shapes of the stripped restoration environment

`RestoredNestedDeclarationsResult.finalValidOfStaged_of_shapes`
(`Nested/StrippedValidity.lean`) proves validity of the stripped-rule
restoration environment from a premise `Hshapes` about every fresh recursor
of that environment. This file discharges `Hshapes` for the exact nested run,
from the hit shape of the lowered recursor types given by
`NestedValidatedRunResult.recursorHitShape'`, which needs nothing besides the
run.

The fresh recursors of the stripped environment are exactly the rule-free
copies of the restoration steps' recursors. For each of them:

* its type, counts and K flag are those of `RestoredRecursorShapeInputs`
  (`NestedValidatedRunResult.restoredRecursorShapeFields`, restated here for
  the staged block from which the final assembly shape is built); the K flag
  is false because the expanded block has an auxiliary family;
* its major inductive (`getMajorInduct`, read from the concrete restored
  type) is the head of the restored major family application: the source
  family for a source owner, the container for an auxiliary owner. Both are
  inductive types of the stripped environment.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open InductiveSignature
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-! ### Forall binders under instantiation and replacement -/

theorem Expr.ForallBinderAt.instantiate1'
    (H : Expr.ForallBinderAt source i domain) (a : Expr) (k : Nat := 0) :
    Expr.ForallBinderAt (source.instantiate1' a k) i
      (domain.instantiate1' a (k + i)) := by
  induction H generalizing k with
  | @here name domain body bi =>
      simpa [Expr.instantiate1'] using
        (Expr.ForallBinderAt.here (name := name)
          (body := body.instantiate1' a (k + 1))
          (bi := bi) (domain := domain.instantiate1' a k))
  | @there body i domain name outerDomain bi H ih =>
      have Htail := ih (k + 1)
      have Hresult := Expr.ForallBinderAt.there
        (name := name) (outerDomain := outerDomain.instantiate1' a k)
        (bi := bi) Htail
      simpa [Expr.instantiate1', Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using Hresult

theorem Expr.ForallBinderAt.instantiateRevList
    (H : Expr.ForallBinderAt source i domain) (as : List Expr) (k : Nat := 0) :
    Expr.ForallBinderAt (source.instantiateRevList as k) i
      (domain.instantiateRevList as (k + i)) := by
  induction as with
  | nil => simpa using H
  | cons a as ih =>
      simpa only [Expr.instantiateRevList] using ih.instantiate1' a k

theorem Expr.getAppFn_instantiateRevList_of_const {e : Expr} {as : List Expr}
    {k : Nat} {n : Name} {ls : List Level} (H : e.getAppFn = .const n ls) :
    (e.instantiateRevList as k).getAppFn = .const n ls := by
  induction as with
  | nil => simpa using H
  | cons a as ih =>
      simp only [Expr.instantiateRevList]
      exact Expr.getAppFn_instantiate1'_of_const ih

/-- A forall prefix followed by a binder selects that binder of the
residual. -/
theorem Expr.ForallTelescope.dropBinderAt
    (Hprefix : Expr.ForallTelescope outer n middle)
    (Hbinder : Expr.ForallBinderAt outer (n + i) domain) :
    Expr.ForallBinderAt middle i domain := by
  induction Hprefix with
  | nil => simpa using Hbinder
  | @cons body arity result name dom bi Hprefix ih =>
      have : arity + 1 + i = (arity + i) + 1 := by omega
      rw [this] at Hbinder
      cases Hbinder with
      | there H => exact ih H

/-- A replacement which never fires at a forall node keeps every forall
binder, replacing its domain. -/
theorem ExprReplacement.binderAt
    (Hnone : ∀ name dom body bi,
      replaceNode (.forallE name dom body bi) = none)
    (Hreplace : ExprReplacement replaceNode input output)
    (Hbinder : Expr.ForallBinderAt input i domain) :
    ∃ domain', Expr.ForallBinderAt output i domain' ∧
      ExprReplacement replaceNode domain domain' := by
  induction Hbinder generalizing output with
  | @here name dom body bi =>
      cases Hreplace with
      | hit h => rw [Hnone] at h; contradiction
      | forallE h hdom hbody =>
          refine ⟨_, ?_, hdom⟩
          simpa [Expr.updateForallE!] using
            (Expr.ForallBinderAt.here (name := name) (body := _) (bi := bi)
              (domain := _))
  | @there body i domain name outerDomain bi H ih =>
      cases Hreplace with
      | hit h => rw [Hnone] at h; contradiction
      | forallE h hdom hbody =>
          rcases ih hbody with ⟨domain', Hd, Hr⟩
          refine ⟨domain', ?_, Hr⟩
          simpa [Expr.updateForallE!] using
            (Expr.ForallBinderAt.there (name := name) (outerDomain := _)
              (bi := bi) Hd)

/-- The application head of a replaced expression: a constant head `c`
satisfying `Good` stays a constant head satisfying `Good`, provided every hit
on the spine produces such a head. -/
theorem ExprReplacement.constHead {Good : Name → Prop}
    (Hhit : ∀ t out, (∃ ls, t.getAppFn = .const c ls) →
      replaceNode t = some out → ∃ c' ls', out.getAppFn = .const c' ls' ∧ Good c')
    (hc : Good c)
    (Hreplace : ExprReplacement replaceNode input output)
    (hhead : input.getAppFn = .const c ls) :
    ∃ c' ls', output.getAppFn = .const c' ls' ∧ Good c' := by
  induction Hreplace with
  | hit h => exact Hhit _ _ ⟨ls, hhead⟩ h
  | @const name levels h =>
      exact ⟨name, levels, rfl, by
        simp only [Expr.getAppFn, Expr.const.injEq] at hhead
        rw [hhead.1]; exact hc⟩
  | @app fn arg fn' arg' h hfn harg ihfn _ =>
      have hfnHead : fn.getAppFn = .const c ls := by
        simpa [Expr.getAppFn] using hhead
      rcases ihfn hfnHead with ⟨c', ls', hout, hgood⟩
      exact ⟨c', ls', by simpa [Expr.updateApp!, Expr.getAppFn] using hout, hgood⟩
  | bvar | fvar | mvar | sort | lit | lam | forallE | letE | mdata | proj =>
      simp [Expr.getAppFn] at hhead

/-- A translated concrete expression with a constant application head
translates to an application spine of the same constant. -/
theorem TrExprS.constHead_eq {env : VEnv} {Us : List Name} {Δ : VLCtx}
    {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e')
    (hfn : e.getAppFn = .const c ls)
    (he' : e' = VExpr.mkApps (.const n us) args) : c = n := by
  rw [← Expr.mkAppList_getAppArgsList e, hfn] at H
  rcases checkPositivityStep.TrExprS.mkAppList_inv H with ⟨fn', args', hfn', -, rfl⟩
  cases hfn' with
  | const _ _ _ =>
    have h := congrArg VExpr.getAppFnArgs he'
    rw [VExpr.getAppFnArgs_mkApps_const, VExpr.getAppFnArgs_mkApps_const] at h
    simp only [Prod.mk.injEq, VExpr.const.injEq] at h
    exact h.1.1

/-! ### The major binder of a generated recursor -/

/-- The domain at the major position of a generated recursor type is an
application of the owner family constant. -/
theorem CompletedRecursorPhasesResult.generated_majorBinder
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    ∃ domain, Expr.ForallBinderAt (H.generated.entry owner howner).info.type
        (H.generated.entry owner howner).info.getMajorIdx domain ∧
      domain.getAppFn = .const (decl.types[owner]'(by
        rw [← H.cardinality.records, ← H.generated.length]; exact howner)).name
        stats.levels := by
  have hrecInfo : owner < H.recInfos.size := by
    rw [← H.generated.length]; exact howner
  let E := H.generated.entry owner howner
  let S := H.bindings.toRecursorLocalSelections H.localWF H.params owner hrecInfo
  have hnoalias : S.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  obtain ⟨D⟩ := (H.bindings.major owner hrecInfo).declarationAt H.localWF 0 (by simp)
  have Hbinder := S.majorBinderAt hnoalias D
  dsimp only at Hbinder
  rw [← E.type] at Hbinder
  have hidx : E.info.getMajorIdx = stats.params.size + (H.recInfos.map (·.motive)).size +
      (H.recInfos.flatMap (·.minors)).size + H.recInfos[owner]!.indices.size := by
    simp only [Lean.RecursorVal.getMajorIdx, E.numParams, E.numMotives, E.numMinors,
      E.numIndices, H.arities owner hrecInfo]
  rw [← hidx] at Hbinder
  refine ⟨_, Hbinder, ?_⟩
  apply Expr.getAppFn_abstractN_const
  rw [H.majorSourceType owner hrecInfo D]
  simp [Expr.getAppFn_mkAppN, Expr.getAppFn]

theorem _root_.Lean.Expr.HitShape.binderAt {heads : List Name} {params : List Expr}
    {ls : List Level} {e : Expr} (H : e.HitShape heads params ls)
    (Hbinder : Expr.ForallBinderAt e i domain) : domain.HitShape heads params ls := by
  induction Hbinder with
  | here => exact H.forallE_inv.1
  | there _ ih => exact ih H.forallE_inv.2

/-! ### The major inductive of a restored recursor -/

section MajorHead

variable {result : Lean4Lean.ElimNestedInductive.Result}
  {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
  {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
  {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
  {outEnv : Environment}

/-- The domain at the major position of a restored recursor's concrete type
is an application of a constant: the owner family itself when it is not a
restoration head, and otherwise the head of the nested occurrence recorded
for the owner family by lowering. -/
theorem NestedValidatedRunResult.restoredMajorHead {ves : VEnvs}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {r : Restoration} {auxRec : NameMap Name} {targetEnv : VEnv} {Us : List Name}
    {auxLevels : List Level}
    (A : RestorationMapAgreement r result E.loweredEnv auxRec targetEnv Us auxLevels)
    (hheads : r.heads.map (·.auxiliary) = E.auxHeads)
    (hparamsSize : result.params.size = result.nparams)
    (hparamsFVars : ∃ xs : List FVarId, result.params = ⟨xs.map .fvar⟩)
    (hnestedHead : ∀ name nested, result.aux2nested.find? name = some nested →
      ∃ c ls, nested.getAppFn = .const c ls)
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {allIndNames : List Name} {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv auxRec allIndNames
      (E.production.production.completed.canonicalGeneration.recursorName owner)
      stepSource stepTarget)
    (hfamRec : ∀ hi, (E.production.loweredDecl.types[owner.val]'hi).name ∉
      r.recursors.map Prod.fst)
    (hfamKey : ∀ hi, (E.production.loweredDecl.types[owner.val]'hi).name ∈
      r.heads.map (·.auxiliary) →
      ∃ nested, result.aux2nested.find? (E.production.loweredDecl.types[owner.val]'hi).name =
        some nested) :
    ∃ (hi : owner.val < E.production.loweredDecl.types.length) (domain : Expr) (c : Name)
      (ls : List Level),
      Expr.ForallBinderAt Hstep.restored.newInfo.type Hstep.restored.newInfo.getMajorIdx
        domain ∧
      domain.getAppFn = .const c ls ∧
      (((E.production.loweredDecl.types[owner.val]'hi).name ∉ r.heads.map (·.auxiliary) ∧
          c = (E.production.loweredDecl.types[owner.val]'hi).name) ∨
        ∃ nested ls', result.aux2nested.find?
            (E.production.loweredDecl.types[owner.val]'hi).name = some nested ∧
          nested.getAppFn = .const c ls') := by
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  obtain ⟨Dfull, Hfull, hDfull⟩ :=
    E.production.production.completed.generated_majorBinder owner.val hi
  have hnp := (E.production.production.completed.generated.entry owner.val hi).numParams
  rw [hinfo] at Hfull hnp
  have hdecl : owner.val < E.production.loweredDecl.types.length := by
    have h := E.production.production.completed.generated.length
    rw [E.production.production.completed.cardinality.records] at h
    rw [← h]; exact hi
  refine ⟨hdecl, ?_⟩
  have hfamRec' := hfamRec hdecl
  have hfamKey' := hfamKey hdecl
  clear hfamRec hfamKey
  generalize (E.production.loweredDecl.types[owner.val]'hdecl).name = fam
    at hDfull hfamRec' hfamKey' ⊢
  have R := Hstep.restored.restoration
  have hidx : Hstep.restored.newInfo.getMajorIdx = Hstep.oldInfo.getMajorIdx := by
    simp only [Lean.RecursorVal.getMajorIdx, R.numParams, R.numMotives, R.numMinors,
      R.numIndices]
  rw [E.statsParamsSize] at hnp
  obtain ⟨k, hk⟩ : ∃ k, Hstep.oldInfo.getMajorIdx = result.nparams + k :=
    ⟨Hstep.oldInfo.getMajorIdx - result.nparams, by
      simp only [Lean.RecursorVal.getMajorIdx] at *; omega⟩
  rw [hk] at Hfull
  rw [hidx, hk]
  obtain ⟨suffix, Htel⟩ := E.loweredRecursorParameterTelescope owner Hstep
  have Hsuffix := Htel.dropBinderAt Hfull
  obtain ⟨Hopen⟩ := R.type.opening hparamsSize
  obtain ⟨fvars, _hAs, _hlen, hbody⟩ := Hopen.opening.forallResidualData Htel
  have Hbody : Expr.ForallBinderAt Hopen.body k
      (Dfull.instantiateRevList (fvars.map Expr.fvar) k) := by
    rw [hbody]
    simpa using Hsuffix.instantiateRevList (fvars.map Expr.fvar) 0
  have hold : (Dfull.instantiateRevList (fvars.map Expr.fvar) k).getAppFn =
      .const fam E.production.stats.levels :=
    Expr.getAppFn_instantiateRevList_of_const hDfull
  obtain ⟨newDom, HnewB, Hrep⟩ := ExprReplacement.binderAt
    (fun _ _ _ _ => restoreNestedNode_forall result E.loweredEnv Hopen.params auxRec)
    Hopen.replacement Hbody
  have HnewFull := (Hopen.outputPrefixTelescope Htel).prependBinderAt
    (HnewB.abstractN Hopen.selection.fvars 0)
  simp only [Nat.zero_add] at HnewFull
  suffices Hhead : ∃ c ls, newDom.getAppFn = .const c ls ∧
      ((fam ∉ r.heads.map (·.auxiliary) ∧ c = fam) ∨
        ∃ nested ls', result.aux2nested.find? fam = some nested ∧
          nested.getAppFn = .const c ls') by
    obtain ⟨c, ls, hc, hgood⟩ := Hhead
    exact ⟨_, c, ls, HnewFull, Expr.getAppFn_abstractN_const hc, hgood⟩
  by_cases hmem : fam ∈ r.heads.map (·.auxiliary)
  · obtain ⟨nested, hnested⟩ := hfamKey' hmem
    obtain ⟨I0, lsI, hnestedFn⟩ := hnestedHead fam nested hnested
    have Hshape := (E.recursorHitShape' wf Hsources owner Hstep).1
    rw [← hheads] at Hshape
    obtain ⟨HbodyShape, hsize, -⟩ := Hopen.hitShape_of_lowered Htel Hshape
    have HdomShape := HbodyShape.binderAt Hbody
    obtain ⟨-, rest, hargs, -⟩ := HdomShape.getAppFn_const_hit_inv hold hmem
    have hH : restoreHead result E.loweredEnv Hopen.params fam =
        some ((nested.abstract result.params).instantiateRev Hopen.params) := by
      simp [restoreHead, hnested]
    have hnotrec : ∀ c ls, Dfull.instantiateRevList (fvars.map Expr.fvar) k = .const c ls →
        auxRec.find? c = none := by
      intro c ls h
      have hc : c = fam := by
        rw [h] at hold; simp only [Expr.getAppFn, Expr.const.injEq] at hold; exact hold.1
      subst hc
      exact A.notRecursor_of_head (by rw [hH]; simp)
    have hnode := restoreNestedNode_eq_of_restoreHead result E.loweredEnv Hopen.params auxRec
      _ hnotrec hold hH (by rw [hargs]; simp; omega)
    have hout := Hrep.output_of_hit hnode
    refine ⟨I0, lsI, ?_, Or.inr ⟨nested, lsI, hnested, hnestedFn⟩⟩
    rw [hout, Expr.getAppFn_mkAppList]
    obtain ⟨xs, hxs⟩ := hparamsFVars
    rw [hxs, Expr.abstractN_eq, Expr.instantiateRev_eq, Expr.instantiate_eq]
    exact Expr.getAppFn_instantiateList_of_const (Expr.getAppFn_abstractN_const hnestedFn)
  · have hrecName : ∀ new, auxRec.find? fam = some new → new = fam := by
      intro new hnew
      have h1 := A.recursorName fam
      rw [Restoration.recursorName_of_not_mem hfamRec', hnew] at h1
      exact h1.symm
    have hnoneHead : restoreHead result E.loweredEnv Hopen.params fam = none :=
      A.restoreHead_eq_none hmem
    have Hhit : ∀ t out, (∃ ls, t.getAppFn = .const fam ls) →
        result.restoreNestedNode E.loweredEnv Hopen.params auxRec t = some out →
        ∃ c' ls', out.getAppFn = .const c' ls' ∧ c' = fam := by
      rintro t out ⟨ls0, hfn⟩ hsome
      by_cases ht : ∃ ls1, t = .const fam ls1
      · obtain ⟨ls1, rfl⟩ := ht
        cases hrec : auxRec.find? fam with
        | none =>
          rw [restoreNestedNode_eq_none_of_restoreHead result E.loweredEnv Hopen.params auxRec _
            (fun c ls h => by cases h; exact hrec)
            (fun c ls h => by
              simp only [Expr.getAppFn, Expr.const.injEq] at h
              rw [← h.1]; exact hnoneHead)] at hsome
          cases hsome
        | some new =>
          rw [restoreNestedNode_recursor result E.loweredEnv Hopen.params auxRec fam new ls1
            hrec] at hsome
          cases hsome
          exact ⟨new, ls1, rfl, hrecName new hrec⟩
      · rw [restoreNestedNode_eq_none_of_restoreHead result E.loweredEnv Hopen.params auxRec t
          (fun c ls h => by
            exfalso; apply ht
            subst h
            simp only [Expr.getAppFn, Expr.const.injEq] at hfn
            exact ⟨ls, by rw [hfn.1]⟩)
          (fun c ls h => by
            rw [hfn] at h; cases h; exact hnoneHead)] at hsome
        cases hsome
    obtain ⟨c', ls', hc', hgood⟩ := ExprReplacement.constHead (Good := (· = fam)) Hhit rfl
      Hrep hold
    exact ⟨c', ls', hc', Or.inl ⟨hmem, hgood⟩⟩

/-- Every nested occurrence recorded by lowering is headed by an inductive
type of the source production environment. -/
theorem NestedValidatedRunResult.auxNestedHead {ves : VEnvs}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {name : Name} {nested : Expr} (hfind : result.aux2nested.find? name = some nested) :
    ∃ I ls info, nested.getAppFn = .const I ls ∧
      sourceProdEnv.find? I = some (.inductInfo info) := by
  rcases E.lowering with ⟨finalState, Hrun, _Hcache, _Hparams⟩
  rcases Hrun.finalCachedGeneratedFamilyOriginOfLookup
      (VEnvs.WFCore.environmentTypesClosed wf) wf.inductivesClosed Hsources rfl rfl hfind with
    ⟨O⟩
  have hhead := O.origin.generated.built.nested_getAppFn O.origin.generated.selection
    O.origin.generated.argsArity
  rw [O.nested_eq] at hhead
  exact ⟨_, _, _, hhead, O.origin.generated.built.lookup⟩

/-- A nested run with a recorded nested occurrence generates an auxiliary
family, so its expanded block has more than one family. -/
theorem NestedValidatedRunResult.one_lt_familiesSize
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    (hnested : result.aux2nested.size ≠ 0) :
    1 < E.production.production.completed.generationSignature.families.size := by
  rcases E.lowering with ⟨finalState, Hrun, _, _⟩
  have hmap := Hrun.resultAuxMap
  have hne : finalState.nestedAux.size ≠ 0 := by
    intro h
    apply hnested
    rw [hmap, Array.size_eq_zero_iff.mp h]
    rfl
  have hentry := Array.getElem_mem (xs := finalState.nestedAux) (i := 0) (by omega)
  obtain ⟨j, hj, hinit, -⟩ := (Hrun.finalAuxFamilyPosition rfl).position _ _ hentry
  rcases Hrun.source with
    ⟨first, rest, _tail, _paramsState, _lctx, _params, htypes, _Hopening,
      _hnewTypes, _hinitialAux, _hnextIdx, _hprefix, _Hctx, _Hselection, Hqueue⟩
  have hresult : result.types.length = finalState.newTypes.size := by
    rw [Hqueue.resultTypes]; simp
  have hN : E.production.production.completed.generationSignature.families.size =
      result.types.length := by
    rw [← E.production.production.completed.entries_length_eq]
    change E.production.production.entries.length = _
    rw [E.production.production.generated.length,
      E.production.production.cardinality.records,
      ← Lean4Lean.VerifyInductive.TrInductDeclCore.types_length
        E.production.constructors.core, E.production_indTypes]
  have hj' : j < finalState.newTypes.size := hj
  have hinit' : sourceTypes.length ≤ j := by simpa using hinit
  have hlen : 1 ≤ sourceTypes.length := by rw [htypes]; simp
  rw [hN, hresult]
  omega

private theorem forall₂_map_eq_fs {R : α → β → Prop} {f : α → γ} {g : β → γ}
    (hR : ∀ a b, R a b → f a = g b) :
    ∀ {l : List α} {r : List β}, List.Forall₂ R l r → l.map f = r.map g
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp only [List.map_cons, hR _ _ h, forall₂_map_eq_fs hR t]

/-- The source family names are the names of the source prefix of the
lowered declaration. -/
theorem NestedValidatedRunResult.sourceNames_eq
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    sourceTypes.map (·.name) =
      (E.production.loweredDecl.types.take sourceTypes.length).map (·.name) :=
  forall₂_map_eq_fs (fun _ _ h => h.name.symm) E.nativeSource.sourceHeaders

/-- A source family is installed in the lowered environment under its own
name. -/
theorem NestedValidatedRunResult.loweredSourceKeyed
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv)
    {t : InductiveType} (ht : t ∈ sourceTypes) {info : InductiveVal}
    (hfind : E.loweredEnv.find? t.name = some (.inductInfo info)) :
    info.name = t.name := by
  have hloweredNames : E.production.indTypes.toList.map (·.name) =
      E.production.loweredDecl.types.map (·.name) :=
    forall₂_map_eq_fs (fun _ _ h => h.header.name.symm) E.production.constructors.core.types
  have hmem : t.name ∈ E.production.indTypes.toList.map (·.name) := by
    rw [hloweredNames]
    have h := List.mem_map_of_mem (f := (·.name)) ht
    rw [E.sourceNames_eq, List.map_take] at h
    exact List.mem_of_mem_take h
  obtain ⟨u, hu, hun⟩ := List.mem_map.mp hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
  have hi' : i < E.production.indTypes.size := by simpa using hi
  have Hc : ContextWF E.production.c := by
    rw [E.production_c]; exact E.productionContextWF
  obtain ⟨info', hfind', hname', -⟩ :=
    E.production.production.findSourceHeaderAt Hc i hi'
  simp only [Array.getElem_toList] at hun
  rw [hun] at hfind'
  rw [hfind] at hfind'
  cases hfind'
  rw [hname', hun]

end MajorHead

/-! ### The fresh recursors of a nested restoration -/

/-- A restored constructor fold installs no recursor. -/
theorem StateForMTrace.constructorFreshTraceNoRec
    (H : StateForMTrace (RestoredConstructorStep result loweredEnv)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      ∀ e ∈ entries, ∀ r, e ≠ .recInfo r := by
  induction H with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons Hstep Htail ih =>
    let ci : ConstantInfo := .ctorInfo Hstep.restored.newInfo
    have hfresh := find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries, hrec⟩
    refine ⟨ci :: entries, .cons hfresh Hentries, ?_⟩
    intro e he r
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · nofun
    · exact hrec e he r

/-- The recursors installed by a restoration step are those of the step. -/
def RecursorEntriesOfSteps (result : Lean4Lean.ElimNestedInductive.Result)
    (loweredEnv : Environment) (auxRec : NameMap Name) (allIndNames : List Name)
    (oldRecNames : List Name) (entries : List ConstantInfo) : Prop :=
  ∀ e ∈ entries, ∀ r, e = .recInfo r →
    ∃ oldRecName ∈ oldRecNames, ∃ (s t : Environment)
      (Hstep : RestoredRecursorStep result loweredEnv auxRec allIndNames oldRecName s t),
      r = Hstep.restored.newInfo

theorem RecursorEntriesOfSteps.append
    (H₁ : RecursorEntriesOfSteps result loweredEnv auxRec allIndNames names₁ entries₁)
    (H₂ : RecursorEntriesOfSteps result loweredEnv auxRec allIndNames names₂ entries₂) :
    RecursorEntriesOfSteps result loweredEnv auxRec allIndNames (names₁ ++ names₂)
      (entries₁ ++ entries₂) := by
  intro e he r hr
  rcases List.mem_append.mp he with he | he
  · obtain ⟨n, hn, h⟩ := H₁ e he r hr
    exact ⟨n, List.mem_append_left _ hn, h⟩
  · obtain ⟨n, hn, h⟩ := H₂ e he r hr
    exact ⟨n, List.mem_append_right _ hn, h⟩

theorem RestoredInductiveDeclResult.freshTraceRecursorSteps
    (H : RestoredInductiveDeclResult result loweredEnv sourceEnv auxRec
      allIndNames indType oldInfo ((), targetEnv))
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      RecursorEntriesOfSteps result loweredEnv auxRec allIndNames
        [Lean.mkRecName indType.name] entries ∧
      .inductInfo H.header.newInfo ∈ entries := by
  let header : ConstantInfo := .inductInfo H.header.newInfo
  have hheaderEnv : H.headerEnv = sourceEnv.add header :=
    congrArg Prod.snd H.header.output
  have hheaderFresh : sourceEnv.find? header.name = none :=
    find?_none_of_contains_false hwf H.header.fresh
  have hwfHeader := constantsWF_add_checked hwf hheaderFresh
  have Hconstructors' : StateForMTrace
      (RestoredConstructorStep result loweredEnv) oldInfo.ctors
      (sourceEnv.add header) H.constructorEnv := by
    rw [← hheaderEnv]
    exact H.constructors
  rcases Hconstructors'.constructorFreshTraceNoRec hwfHeader with
    ⟨constructors, Hconstructors, hnorec⟩
  have hwfConstructors : H.constructorEnv.constants.WF :=
    Hconstructors.targetWF hwfHeader
  let recursor : ConstantInfo := .recInfo H.recursor.restored.newInfo
  have htarget : targetEnv = H.constructorEnv.add recursor :=
    congrArg Prod.snd H.recursor.restored.output
  have hrecFresh : H.constructorEnv.find? recursor.name = none :=
    find?_none_of_contains_false hwfConstructors H.recursor.restored.fresh
  refine ⟨header :: constructors ++ [recursor], ?_, ?_, by simp [header]⟩
  · rw [htarget]
    exact FreshConstantTrace.cons hheaderFresh
      (Hconstructors.append (.cons hrecFresh .nil))
  · intro e he r hr
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | he | rfl
    · simp [header] at hr
    · exact absurd hr (hnorec e he r)
    · simp only [recursor, ConstantInfo.recInfo.injEq] at hr
      subst hr
      exact ⟨_, List.mem_singleton_self _, _, _, H.recursor, rfl⟩

theorem StateForMTrace.inductiveFreshTraceRecursorSteps
    (H : StateForMTrace
      (RestoredInductiveStep result loweredEnv auxRec allIndNames)
      types sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      RecursorEntriesOfSteps result loweredEnv auxRec allIndNames
        (types.map fun t => Lean.mkRecName t.name) entries ∧
      ∀ t ∈ types, ∃ (s t' : Environment)
        (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames t s t'),
        .inductInfo Hstep.restored.header.newInfo ∈ entries := by
  induction H with
  | nil => exact ⟨[], .nil, by simp [RecursorEntriesOfSteps], by simp⟩
  | cons Hstep _Htail ih =>
    rcases Hstep.restored.freshTraceRecursorSteps hwf with
      ⟨headEntries, Hhead, hhead, hheader⟩
    rcases ih (Hhead.targetWF hwf) with ⟨tailEntries, Htail, htail, htailHeaders⟩
    refine ⟨headEntries ++ tailEntries, Hhead.append Htail, hhead.append htail, ?_⟩
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨_, _, Hstep, List.mem_append_left _ hheader⟩
    · obtain ⟨s, t', H', hmem⟩ := htailHeaders t ht
      exact ⟨s, t', H', List.mem_append_right _ hmem⟩

theorem StateForMTrace.recursorFreshTraceRecursorSteps
    (H : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv)
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries targetEnv ∧
      RecursorEntriesOfSteps result loweredEnv auxRec allIndNames names entries := by
  induction H with
  | nil => exact ⟨[], .nil, by simp [RecursorEntriesOfSteps]⟩
  | @cons head src mid tl tgt Hstep Htail ih =>
    let ci : ConstantInfo := .recInfo Hstep.restored.newInfo
    have hfresh := find?_none_of_contains_false hwf Hstep.restored.fresh
    have htarget := congrArg Prod.snd Hstep.restored.output
    simp only at htarget
    rw [htarget] at Htail ih
    rcases ih (constantsWF_add_checked hwf hfresh) with ⟨entries, Hentries, hsteps⟩
    refine ⟨ci :: entries, .cons hfresh Hentries, ?_⟩
    have hhead : RecursorEntriesOfSteps result loweredEnv auxRec allIndNames [head] [ci] := by
      intro e he r hr
      simp only [List.mem_singleton] at he
      subst he
      simp only [ci, ConstantInfo.recInfo.injEq] at hr
      subst hr
      exact ⟨_, List.mem_singleton_self _, _, _, Hstep, rfl⟩
    simpa using hhead.append hsteps

/-- Every recursor installed by a nested restoration is the restored
recursor of one of its steps. -/
theorem RestoredNestedDeclarationsResult.freshTraceRecursorSteps
    (H : RestoredNestedDeclarationsResult result loweredEnv sourceEnv auxRec
      allIndNames types auxRecNames ((), outEnv))
    (hwf : sourceEnv.constants.WF) :
    ∃ entries, FreshConstantTrace sourceEnv entries outEnv ∧
      RecursorEntriesOfSteps result loweredEnv auxRec allIndNames
        (types.map (fun t => Lean.mkRecName t.name) ++ auxRecNames) entries ∧
      ∀ t ∈ types, ∃ (s t' : Environment)
        (Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames t s t'),
        .inductInfo Hstep.restored.header.newInfo ∈ entries := by
  rcases H.inductives.inductiveFreshTraceRecursorSteps hwf with
    ⟨primaryEntries, Hprimary, hprimary, hheaders⟩
  rcases H.auxiliaries.recursorFreshTraceRecursorSteps (Hprimary.targetWF hwf) with
    ⟨auxiliaryEntries, Hauxiliary, hauxiliary⟩
  refine ⟨_, Hprimary.append Hauxiliary, hprimary.append hauxiliary, ?_⟩
  intro t ht
  obtain ⟨s, t', Hstep, hmem⟩ := hheaders t ht
  exact ⟨s, t', Hstep, List.mem_append_left _ hmem⟩

/-! ### The restored recursors of the staged block -/

/-- The auxiliary recursors of an auxiliary recursor trace, one per restored
recursor name, each the translation of the restored recursor at that name. -/
theorem RestoredAuxiliaryRecursorTrace.recursorSteps
    {result : Lean4Lean.ElimNestedInductive.Result}
    {loweredEnv : Environment} {auxRec : NameMap Name} {allIndNames : List Name}
    {names : List Name} {sourceEnv targetEnv : Environment}
    {Htrace : StateForMTrace
      (RestoredRecursorStep result loweredEnv auxRec allIndNames)
      names sourceEnv targetEnv}
    (H : RestoredAuxiliaryRecursorTrace safety trEnv recursorEnv Htrace
      priorRecursors finalRecursors) :
    ∃ added, finalRecursors = priorRecursors ++ added ∧
      List.Forall₂ (fun (name : Name) (w : VConstVal) =>
          ∃ (s t : Environment) (Hstep : RestoredRecursorStep result loweredEnv
            auxRec allIndNames name s t),
            RestoredRecursorStepValue trEnv Hstep w)
        names added := by
  induction H with
  | nil => exact ⟨[], by simp, .nil⟩
  | cons Hstep Htail Hhead Hrest ih =>
    obtain ⟨added, hfinal, Hadded⟩ := ih
    obtain ⟨⟨_, huvars, htype⟩, hname⟩ := Hhead.translated
    refine ⟨Hhead.recursor :: added, by simp [hfinal], .cons ⟨_, _, Hstep,
      ?_, huvars, htype⟩ Hadded⟩
    rw [← Hstep.restored.restoration.name]
    exact hname.symm

/-! ### The restored major family application -/

private theorem vars_map_liftN (n k : Nat) :
    (vars n 0).map (fun arg => arg.liftN k) = vars n k := by
  simp only [vars, List.map_map]
  apply List.map_congr_left
  intro i _
  simp [VExpr.liftN, Nat.add_comm]

private theorem vars_closedN (n : Nat) : ∀ arg ∈ vars n 0, arg.ClosedN n := by
  intro arg harg
  simp only [vars, List.mem_map, List.mem_reverse, List.mem_range] at harg
  obtain ⟨i, hi, rfl⟩ := harg
  simpa [VExpr.ClosedN] using hi

/-- A restored generated major domain is a constant applied to arguments
scoped by the common parameters, followed by the index variables. -/
theorem Restoration.expr_recursorMajor_head (r : Restoration) {s : InductiveSignature}
    (g : Instance s) (owner : Fin s.families.size) {major : VExpr}
    (hmajor : r.expr (g.recursorMajor owner) = some major)
    (hheads : ∀ h ∈ r.heads, h.nparams = s.params.length ∧
      ∀ arg ∈ h.arguments, arg.ClosedN h.nparams) :
    ∃ head : RestoredFamilyHead,
      (∀ arg ∈ head.arguments, arg.ClosedN s.params.length) ∧
      major = VExpr.mkApps (.const head.name head.levels)
        (head.arguments.map (fun arg => arg.liftN
          (s.families.size + s.constructors.size + s.families[owner].indices.length)) ++
          vars s.families[owner].indices.length 0) := by
  cases hf : r.heads.find? (fun h => h.auxiliary == s.families[owner].name) with
  | none =>
    have hval : r.expr (g.recursorMajor owner) = some (VExpr.mkApps
        (.const (r.recursorName s.families[owner].name) g.levels)
        (vars s.params.length
          (s.families.size + s.constructors.size + s.families[owner].indices.length) ++
          vars s.families[owner].indices.length 0)) := by
      simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp]
      rw [r.expr_mkApps, List.mapM_append, r.mapM_expr_vars, r.mapM_expr_vars]
      simp only [Fin.getElem_fin] at hf
      simp [Restoration.expr.go, hf]
    rw [hval] at hmajor
    cases hmajor
    refine ⟨⟨r.recursorName s.families[owner].name, g.levels, vars s.params.length 0⟩,
      vars_closedN _, ?_⟩
    simp only [vars_map_liftN]
  | some h =>
    obtain ⟨hnp, hcl⟩ := hheads h (List.mem_of_find?_eq_some hf)
    have hlevels : g.levels.length = h.uvars := by
      simp only [Instance.recursorMajor, Instance.familyApp, InductiveSignature.familyApp]
        at hmajor
      rw [r.expr_mkApps, List.mapM_append, r.mapM_expr_vars, r.mapM_expr_vars] at hmajor
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some,
        Restoration.expr.go] at hmajor
      rw [hf] at hmajor
      simp only [HeadSpecialization.apply] at hmajor
      by_contra hne
      simp [hne] at hmajor
    rw [r.expr_recursorMajor_auxiliary g owner hf hlevels hnp hcl] at hmajor
    cases hmajor
    refine ⟨⟨h.target, h.levels.map (·.inst g.levels), h.arguments.map (·.instL g.levels)⟩,
      ?_, ?_⟩
    · intro arg harg
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp harg
      rw [← hnp]
      exact (hcl a ha).instL
    · simp only [List.map_map, Function.comp_def]

section StagedShapes

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
  {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
  {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
  {isUnsafe : Bool} {outEnv : Environment}

/-- `restoredRecursorEntries_of_hitShape` for an arbitrary recursor list
produced by the two restoration folds, before the final assembly shape is
built: each entry is the abstract restoration of the owner's generated
recursor. -/
theorem NestedValidatedRunResult.restoredRecursorEntries_of_steps
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (hctorNames : ∀ c ∈ sourceDecl.constructorConstants,
      c.name ∈ familyNames (E.production.loweredDecl.types.take sourceDecl.types.length))
    {envCtors : VEnv} {es : List (Name × InductiveSignature.CaseSchema)}
    (hctors : envTypes.addConstVals sourceDecl.constructorConstants = some envCtors)
    (hnonempty : sourceTypes ≠ [])
    {recursors : List VConstVal}
    (Hall : List.Forall₂ (fun (name : Name) (w : VConstVal) =>
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) name s t),
          RestoredRecursorStepValue
            ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries) Hstep w)
      (sourceTypes.map (fun t => Lean.mkRecName t.name) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)
      recursors) :
    List.Forall₂ (fun owner w =>
        (compilationRestoration sourceDecl auxiliaries).recursor
          (E.production.production.completed.canonicalGeneration.recursor owner) = some w ∧
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name))
          (E.production.production.completed.canonicalGeneration.recursorName owner) s t),
          RestoredRecursorStepValue
            ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries) Hstep w)
      (List.finRange
        E.production.production.completed.generationSignature.families.size)
      recursors := by
  let r := compilationRestoration sourceDecl auxiliaries
  let trEnv := (envCtors.addEliminators es).addProjections sourceDecl.projectionEntries
  have Hfresh : ∀ n ∈ r.restorableNames, trEnv.constants n = none := by
    intro n hn
    simp only [trEnv, VEnv.addEliminators_constants, VEnv.addProjections_constants]
    exact E.restorableNames_fresh_ctors hadded Haux Hexpansion hnodup hctorNames
      hctors n hn
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  rw [← E.recursorNames_order hnonempty, List.forall₂_map_left_iff] at Hall
  refine Lean4Lean.List.Forall₂.imp ?_ Hall
  rintro owner w ⟨s, t, Hstep, Hw⟩
  have Hshape := (E.recursorHitShape' wf Hsources owner Hstep).1
  rw [← hheads] at Hshape
  exact ⟨E.restoredRecursor_of_step hparamsSize D hscoped owner Hstep rfl Hshape
    Hfresh Hw, s, t, Hstep, Hw⟩

/-- **One stripped recursor.** The rule-free copy of the restored recursor of
a restoration step at a generated owner's lowered recursor name satisfies
`RestoredRecursorShapeInputs` in any abstract environment containing the
restored recursor list. Its major inductive is either the owner family (not a
restoration head) or the head of the nested occurrence recorded by lowering
for an auxiliary family. -/
theorem NestedValidatedRunResult.strippedRecursorOfStep
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (hadded : (ves.venv (if isUnsafe then .unsafe else .safe)).addConstVals
      sourceDecl.typeConstants = some envTypes)
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup)
    (hparamsSize : result.params.size = result.nparams)
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams)
    (hscoped : (compilationRestoration sourceDecl auxiliaries).Scoped)
    (hctorNames : ∀ c ∈ sourceDecl.constructorConstants,
      c.name ∈ familyNames (E.production.loweredDecl.types.take sourceDecl.types.length))
    {envCtors : VEnv} {es : List (Name × InductiveSignature.CaseSchema)}
    (hctors : envTypes.addConstVals sourceDecl.constructorConstants = some envCtors)
    (hnonempty : sourceTypes ≠ [])
    {recursors : List VConstVal}
    (Hall : List.Forall₂ (fun (name : Name) (w : VConstVal) =>
        ∃ (s t : Environment) (Hstep : RestoredRecursorStep result E.loweredEnv
          (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          (sourceTypes.map (·.name)) name s t),
          RestoredRecursorStepValue
            ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries) Hstep w)
      (sourceTypes.map (fun t => Lean.mkRecName t.name) ++
        (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)
      recursors)
    {finalVEnv : VEnv}
    (hfinal : ∀ w ∈ recursors, finalVEnv.constants w.name = some w.toVConstant)
    (hfamilies : 1 < E.production.production.completed.generationSignature.families.size)
    (hnestedHead : ∀ name nested, result.aux2nested.find? name = some nested →
      ∃ c ls, nested.getAppFn = .const c ls)
    (owner : Fin E.production.production.completed.generationSignature.families.size)
    {stepSource stepTarget : Environment}
    (Hstep : RestoredRecursorStep result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (·.name))
      (E.production.production.completed.canonicalGeneration.recursorName owner)
      stepSource stepTarget) :
    RestoredRecursorShapeInputs E.production.production.completed.canonicalGeneration
        (compilationRestoration sourceDecl auxiliaries) finalVEnv owner
        { Hstep.restored.newInfo with rules := [] } ∧
      ∃ hi : owner.val < E.production.loweredDecl.types.length,
        ((E.production.loweredDecl.types[owner.val]'hi).name ∉
            (compilationRestoration sourceDecl auxiliaries).heads.map (·.auxiliary) ∧
          Hstep.restored.newInfo.getMajorInduct =
            (E.production.loweredDecl.types[owner.val]'hi).name) ∨
        ∃ name nested ls, result.aux2nested.find? name = some nested ∧
          nested.getAppFn = .const Hstep.restored.newInfo.getMajorInduct ls := by
  let r := compilationRestoration sourceDecl auxiliaries
  let g := E.production.production.completed.canonicalGeneration
  have Hentries := E.restoredRecursorEntries_of_steps wf Hsources hadded Haux Hexpansion hnodup
    hparamsSize D hscoped hctorNames hctors hnonempty Hall
  obtain ⟨w, hw, hrec, s', t', Hstep', hwname, hwuvars, Htr⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_l Hentries owner (List.mem_finRange owner)
  obtain ⟨-, hnew⟩ := Hstep'.info_eq Hstep
  have M := E.recursorMetadataOfStep owner Hstep
  have R := Hstep.restored.restoration
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfStep owner Hstep
  have hnp := (E.production.production.completed.generated.entry owner.val hi).numParams
  rw [hinfo, E.statsParamsSize] at hnp
  have hparamsLen : E.production.production.completed.generationSignature.params.length =
      result.nparams := M.numParams.symm.trans hnp
  simp only [Restoration.recursor, InductiveSignature.Instance.recursor,
    Option.bind_eq_bind, Option.pure_def] at hrec
  cases ht : r.expr (g.recursorType owner) with
  | none => simp [r, g, ht] at hrec
  | some type =>
  simp only [r, g, ht, Option.bind_some, Option.some.injEq] at hrec
  have hwtype : w.type = type := by rw [← hrec]
  have hname : Hstep.restored.newInfo.name = w.name := by
    rw [hwname, ← hnew, Hstep'.restored.restoration.name]
  have hconst := hfinal w hw
  -- the restored major family application
  obtain ⟨pre, major, hpre, hm, htypeEq⟩ := r.expr_recursorType_eq_some ht
  have hheadsR : ∀ h ∈ r.heads, h.nparams =
      E.production.production.completed.generationSignature.params.length ∧
      ∀ arg ∈ h.arguments, arg.ClosedN h.nparams := by
    intro h hh
    refine ⟨?_, (hscoped.2.2.1 h hh).2⟩
    obtain ⟨a, _, hh⟩ := List.mem_flatMap.mp hh
    have hn : h.nparams = sourceDecl.nparams := by
      simp only [ContainerSpecialization.heads, List.mem_cons, List.mem_map] at hh
      rcases hh with rfl | ⟨_, _, rfl⟩ <;> rfl
    rw [hn, D.nparams, hparamsLen]
  obtain ⟨head, hargs, hmajorEq⟩ := Restoration.expr_recursorMajor_head r g owner hm hheadsR
  -- the concrete major inductive
  have hheads : r.heads.map (·.auxiliary) = E.auxHeads := by
    rw [compilationRestoration_heads_auxiliary]
    exact auxiliarySpecializations_headNames Haux Hexpansion
  have hfamNodup : (familyNames (E.production.loweredDecl.types.take sourceDecl.types.length) ++
      familyNames (E.production.loweredDecl.types.drop sourceDecl.types.length)).Nodup := by
    have h := (List.nodup_append.mp hnodup).1
    rw [← List.take_append_drop sourceDecl.types.length E.production.loweredDecl.types] at h
    simpa only [familyNames, List.flatMap_append] using h
  have hfamRec : ∀ hi, (E.production.loweredDecl.types[owner.val]'hi).name ∉
      r.recursors.map Prod.fst := by
    intro hi hmem
    rw [compilationRestoration_recursors_fst] at hmem
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hmem
    have haux : a.auxiliary ∈
        (E.production.loweredDecl.types.drop sourceDecl.types.length).map (·.name) := by
      rw [← auxiliarySpecializations_names Haux Hexpansion]
      exact List.mem_map_of_mem ha
    obtain ⟨t, ht, hta⟩ := List.mem_map.mp haux
    have h1 : (E.production.loweredDecl.types[owner.val]'hi).name ∈
        familyNames E.production.loweredDecl.types :=
      mem_familyNames_of_type (List.getElem_mem hi)
    have h2 : (E.production.loweredDecl.types[owner.val]'hi).name ∈
        E.production.loweredDecl.types.map (fun t => t.name.str "rec") := by
      rw [← heq, ← hta]
      exact List.mem_map_of_mem (f := fun t : VInductiveType => t.name.str "rec")
        (List.mem_of_mem_drop ht)
    exact (List.nodup_append.mp hnodup).2.2 _ h1 _ h2 rfl
  have hfamKey : ∀ hi, (E.production.loweredDecl.types[owner.val]'hi).name ∈
      r.heads.map (·.auxiliary) →
      ∃ nested, result.aux2nested.find?
        (E.production.loweredDecl.types[owner.val]'hi).name = some nested := by
    intro hi hmem
    rw [hheads] at hmem
    by_cases hlt : owner.val < sourceDecl.types.length
    · exfalso
      have htake : E.production.loweredDecl.types[owner.val]'hi ∈
          E.production.loweredDecl.types.take sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val, by simp; omega, by simp⟩
      exact (List.nodup_append.mp hfamNodup).2.2 _ (mem_familyNames_of_type htake) _ hmem rfl
    · have hdrop : E.production.loweredDecl.types[owner.val]'hi ∈
          E.production.loweredDecl.types.drop sourceDecl.types.length :=
        List.mem_iff_getElem.mpr ⟨owner.val - sourceDecl.types.length, by simp; omega, by
          simp only [List.getElem_drop]; congr 1; omega⟩
      have hname := List.mem_map_of_mem (f := (·.name)) hdrop
      rw [← auxiliarySpecializations_names Haux Hexpansion] at hname
      obtain ⟨a, ha, haeq⟩ := List.mem_map.mp hname
      obtain ⟨nested, hnested⟩ := D.familyLookup a ha
      exact ⟨nested, haeq ▸ hnested⟩
  obtain ⟨hi', domain, c, ls, Hbinder, hc, hdisj⟩ := E.restoredMajorHead wf Hsources
    (D.agreement finalVEnv lparams) hheads hparamsSize D.paramsFVars hnestedHead owner Hstep
    hfamRec hfamKey
  have Htr' : TrExprS ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries)
      Hstep.restored.newInfo.levelParams [] Hstep.restored.newInfo.type
      (VExpr.wrapForalls (pre ++ [major]) (g.recursorBody owner)) := by
    rw [← htypeEq, ← hwtype, ← hnew]
    exact Htr
  have hprelen : pre.length = E.production.production.completed.generationSignature.params.length +
      E.production.production.completed.generationSignature.families.size +
      E.production.production.completed.generationSignature.constructors.size +
      E.production.production.completed.generationSignature.families[owner].indices.length := by
    rw [← g.recursorPrefix_length owner]
    exact (Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.mp hpre)).symm
  have hidx : Hstep.restored.newInfo.getMajorIdx = pre.length := by
    simp only [Lean.RecursorVal.getMajorIdx, R.numParams.trans M.numParams,
      R.numMotives.trans M.numMotives, R.numMinors.trans M.numMinors,
      R.numIndices.trans M.numIndices, hprelen]
  have hlt : Hstep.restored.newInfo.getMajorIdx < (pre ++ [major]).length := by
    simp [hidx]
  have Hdom := Hbinder.translation Htr' hlt
  have hmaj : (pre ++ [major])[Hstep.restored.newInfo.getMajorIdx]'hlt = major := by
    simp [hidx]
  rw [hmaj] at Hdom
  have hcname : c = head.name := TrExprS.constHead_eq Hdom hc hmajorEq
  have hmi : Hstep.restored.newInfo.getMajorInduct = c := by
    rw [RecursorVal.getMajorInduct_of_binderAt _ Hbinder, hc]
    rfl
  refine ⟨⟨?_, R.numParams.trans M.numParams, R.numIndices.trans M.numIndices,
    R.numMotives.trans M.numMotives, R.numMinors.trans M.numMinors, ?_, ?_⟩, hi', ?_⟩
  · refine ⟨type, ht, ?_⟩
    change finalVEnv.constants Hstep.restored.newInfo.name =
      some ⟨Hstep.restored.newInfo.levelParams.length, type⟩
    rw [hname, hconst, ← hnew, hwuvars, ← hwtype]
  · change Hstep.restored.newInfo.k = false
    cases hk : Hstep.restored.newInfo.k with
    | false => rfl
    | true =>
      have := (M.k (R.k.symm.trans hk)).1
      omega
  · refine ⟨head, ?_, ?_, ?_⟩
    · change Hstep.restored.newInfo.getMajorInduct = head.name
      rw [hmi, hcname]
    · exact hargs
    · rw [← hmajorEq]
      exact hm
  · rcases hdisj with ⟨hnot, hceq⟩ | ⟨nested, ls', hfind, hfn⟩
    · exact Or.inl ⟨hnot, hmi.trans hceq⟩
    · exact Or.inr ⟨_, nested, ls', hfind, hmi ▸ hfn⟩

end StagedShapes

private theorem forall₂_take_fs {R : α → β → Prop} :
    ∀ {l : List α} {r : List β} (_ : List.Forall₂ R l r) (k : Nat),
      List.Forall₂ R (l.take k) (r.take k)
  | _, _, .nil, _ => by simp
  | _, _, .cons _ _, 0 => by simp
  | _, _, .cons h t, k + 1 => by
    simp only [List.take_succ_cons]
    exact .cons h (forall₂_take_fs t k)

/-- The source constructor names are constructor names of the source prefix
of the expanded declaration. -/
theorem NestedFormationAssembly.sourceConstructorNames
    (H : NestedFormationAssembly env decl) {loweredDecl : VInductDecl}
    (hexpanded : H.expanded = loweredDecl) :
    ∀ c ∈ decl.constructorConstants,
      c.name ∈ familyNames (loweredDecl.types.take decl.types.length) := by
  intro c hc
  obtain ⟨src, hsrc, hcsrc⟩ := List.mem_flatMap.mp hc
  have HT := forall₂_take_fs H.types decl.types.length
  rw [List.take_left' rfl, hexpanded] at HT
  obtain ⟨t, ht, hT⟩ := Lean4Lean.List.Forall₂.forall_exists_l HT src hsrc
  obtain ⟨c', hc', hcc⟩ := Lean4Lean.List.Forall₂.forall_exists_l hT.constructors c hcsrc
  rw [← hcc.name]
  exact mem_familyNames_of_ctor ht hc'

/-! ### Validity of the stripped environment of the exact run -/

/-- **Validity of the stripped-rule restoration environment** of the exact
nested run, from the hit shape of `recursorHitShape'` and the
executable fact that lowering recorded a nested occurrence (`hnested`, the
condition under which `addInductiveAfterLowering` restores at all). The
remaining arguments are those of `finalValidOfStaged_of_shapes`, together
with the two restoration traces from which the staged recursor list is
built. -/
theorem NestedValidatedRunResult.finalValidOfStaged_of_hitShape
    {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (hnested : result.aux2nested.size ≠ 0)
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams' depth : Nat} {isUnsafe' : Bool}
    {sourceVEnv envTypes envCtors : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams' isUnsafe'
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State} {fuel : Nat}
    {actualEntries : List ConstantInfo}
    {types ctors recursors : List (ConstantInfo × VConstVal)}
    {canonicalProdEnv : Environment} {finalVEnv : VEnv}
    (Hlower : NestedLoweringResultClosed c.env fuel nparams' sourceTypes
      { initialState with newTypes := sourceTypes.toArray } result)
    (Hc : ContextWF c) (Hprod : RecursorPhasesResult R E.loweredEnv)
    (Hsource : TrInductDeclCore sourceVEnv c.lparams nparams' sourceTypes
      isUnsafe' sourceDecl envTypes envCtors)
    (Hmetadata : MaterializedInductivePrefix sourceDecl loweredDecl)
    (Harity : sourceDecl.ConstructorArityPrefix loweredDecl)
    (hempty : initialState.nestedAux = #[])
    (Hrestored : RestoredNestedDeclarationsResult result E.loweredEnv c.env
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
      (sourceTypes.map (fun type => type.name)) sourceTypes
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 ((), outEnv))
    (Hactual : FreshConstantTrace c.env actualEntries outEnv)
    (canonical : StagedBlock c.safety c.env sourceVEnv types ctors recursors
      sourceDecl.projectionEntries canonicalProdEnv finalVEnv)
    (hperm : actualEntries ~ (types ++ ctors ++ recursors).map Prod.fst)
    (htypeValues : types.map Prod.snd = sourceDecl.typeConstants)
    (hctorValues : ctors.map Prod.snd = sourceDecl.constructorConstants)
    (hvalidSource : CheckingEnv.Valid c.safety c.env sourceVEnv)
    (henv : c.env = sourceProdEnv)
    (hsourceVEnv : sourceVEnv = ves.venv (if isUnsafe then .unsafe else .safe))
    (hctorNames : ∀ ct ∈ sourceDecl.constructorConstants,
      ct.name ∈ familyNames (E.production.loweredDecl.types.take sourceDecl.types.length))
    {lp : List Name} {sf sf' : DefinitionSafety} {sv envTypes' recEnv : VEnv}
    {owners : List VInductiveType} {primaryRecursors auxiliaryRecursors : List VConstVal}
    {es : List (Name × InductiveSignature.CaseSchema)}
    (HsourceTrace : RestoredSourceInductiveSemanticTrace sourceDecl lp sf sv envTypes'
      ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries) Hrestored.inductives
      owners primaryRecursors)
    (HauxTrace : RestoredAuxiliaryRecursorTrace sf'
      ((envCtors.addEliminators es).addProjections sourceDecl.projectionEntries) recEnv
      Hrestored.auxiliaries [] auxiliaryRecursors)
    (hrecValues : recursors.map Prod.snd = primaryRecursors ++ auxiliaryRecursors)
    (hcorner : ProjectionCorner c.safety outEnv finalVEnv) :
    CheckingEnv.Valid c.safety
      (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          sourceTypes (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1))
      finalVEnv := by
  refine Hrestored.finalValidOfStaged_of_shapes Hlower Hc Hprod Hsource Hmetadata Hsources
    Harity hempty Hactual canonical hperm htypeValues hctorValues hvalidSource ?_ hcorner
  intro name rec hfind _hs hnone
  -- the restoration tables of the run
  have hnodup : (familyNames E.production.loweredDecl.types ++
      E.production.loweredDecl.types.map (fun t => t.name.str "rec")).Nodup := by
    rcases E.containerSpecializations wf Hsources with ⟨_, _, _, _, _, _, _, h, _⟩
    exact h
  rcases E.restorationTablesRestoringAll wf Hsources with
    ⟨envTypes₀, generated, auxiliaries, hadded, henvTypes, Haux, Hexpansion,
      hparamsSize, D, -, -⟩
  obtain ⟨-, -, -, hheadNames, -, -, -, hscoped, -⟩ :=
    E.restorationPrefix_of wf hadded henvTypes Haux Hexpansion hnodup D True.intro
  have htypesAdded := Hsource.typesAdded
  rw [hsourceVEnv, hadded] at htypesAdded
  cases htypesAdded
  have hctors := Hsource.ctorsAdded
  have hnonempty : sourceTypes ≠ [] := by
    rcases E.lowering with ⟨_finalState, Hrun, _Hcache, _Hparams⟩
    rcases Hrun.source with
      ⟨first, tail, _tail, _paramsState, _lctx, _params, hsource, _⟩
    rw [hsource]
    simp
  have hsourceLength : sourceTypes.length = sourceDecl.types.length :=
    TrInductDeclCore.types_length Hsource
  -- the restored recursor list, in recursor-name order
  have Hprimary := HsourceTrace.recursorSteps
  obtain ⟨added, hadded', Hadded⟩ := HauxTrace.recursorSteps
  simp only [List.nil_append] at hadded'
  rw [← hadded'] at Hadded
  have Hall := Lean4Lean.List.Forall₂.append_of_left (by
      rw [List.length_map]; exact Lean4Lean.List.Forall₂.length_eq Hprimary) |>.mpr
    ⟨List.forall₂_map_left_iff.mpr Hprimary, Hadded⟩
  have hfinal : ∀ w ∈ primaryRecursors ++ auxiliaryRecursors,
      finalVEnv.constants w.name = some w.toVConstant := by
    intro w hw
    have hadd := canonical.recursorsAdded.abstract
    rw [hrecValues] at hadd
    exact VEnv.addConstVals_get hadd hw
  have hnestedHead : ∀ name nested, result.aux2nested.find? name = some nested →
      ∃ c ls, nested.getAppFn = .const c ls := by
    intro name nested h
    obtain ⟨I, ls, _, hfn, _⟩ := E.auxNestedHead wf Hsources h
    exact ⟨I, ls, hfn⟩
  -- the stripped lookups
  obtain ⟨hcore, -, -⟩ :=
    Hrestored.finalLocalValidOfStaged Hlower Hc Hprod Hsource Hmetadata Hsources
      Harity hempty Hactual canonical hperm htypeValues hctorValues hvalidSource
  have hsourceWF : c.env.constants.WF := Hc.checking.tr.map_wf
  have houtWF : outEnv.constants.WF := hcore.tr.map_wf
  have hfresh : ∀ x ∈ Lean4Lean.restoredRecursorNames
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1,
      c.env.constants.find? x = none := by
    intro x hx
    have := Hrestored.restoredRecursorNamesFresh hsourceWF hx
    rwa [Kernel.Environment.find?_eq_constants hsourceWF] at this
  have hov : ∀ x ∈ Lean4Lean.restoredRecursorNames
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1,
      SMapOverwritable outEnv.constants x := fun x hx =>
    Hactual.overwritable (SMapOverwritable.of_find?_none (hfresh x hx))
  obtain ⟨-, -, hspec⟩ := stripRecursorRules_spec _ outEnv hcore.tr.aligned hov
  -- the restoration step installing the recursor
  obtain ⟨r0, hr0⟩ : ∃ r0, outEnv.constants.find? name = some (.recInfo r0) := by
    rcases stripLookup_cases hspec hfind with h | ⟨_, r0, h, _⟩
    · exact ⟨rec, h⟩
    · exact ⟨r0, h⟩
  obtain ⟨entries, Htrace, hsteps, hheaders⟩ := Hrestored.freshTraceRecursorSteps hsourceWF
  have hr0' : outEnv.find? name = some (.recInfo r0) := by
    rw [Kernel.Environment.find?_eq_constants houtWF]; exact hr0
  rcases Htrace.entryOrigin hsourceWF hr0' with hold | ⟨entry, hentry, hname, hfound⟩
  · rw [Kernel.Environment.find?_eq_constants hsourceWF, hnone] at hold
    cases hold
  obtain ⟨oldRecName, hold, s, t, Hstep, hr0eq⟩ := hsteps entry hentry r0 hfound.symm
  subst hr0eq
  have hnameMem : name ∈ Lean4Lean.restoredRecursorNames
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 sourceTypes
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1 := by
    have h1 : name = Hstep.restored.newInfo.name := by rw [hname, ← hfound]; rfl
    rw [h1, Hstep.restored.restoration.name, Hstep.restored.mappedName]
    simp only [Lean4Lean.restoredRecursorNames]
    exact List.mem_map_of_mem hold
  have hrec : rec = { Hstep.restored.newInfo with rules := [] } := by
    rw [hspec, if_pos hnameMem, hr0] at hfind
    simp only [stripRulesOpt, Option.some.injEq, ConstantInfo.recInfo.injEq] at hfind
    exact hfind.symm
  subst hrec
  rw [← E.recursorNames_order hnonempty] at hold
  obtain ⟨owner, -, rfl⟩ := List.mem_map.mp hold
  obtain ⟨Hshape, hi, hhead⟩ := E.strippedRecursorOfStep wf Hsources hadded Haux Hexpansion hnodup
    hparamsSize D hscoped hctorNames hctors hnonempty Hall hfinal
    (E.one_lt_familiesSize hnested) hnestedHead owner Hstep
  refine ⟨Hshape.alignmentCore, Hshape.kLike _, ?_⟩
  -- the major inductive is an inductive type of the stripped environment
  have hnonrec : ∀ {x info}, outEnv.constants.find? x = some (.inductInfo info) →
      ∃ info, (Lean4Lean.stripRecursorRules outEnv
        (Lean4Lean.restoredRecursorNames (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2
          sourceTypes (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).1)).constants.find? x =
        some (.inductInfo info) :=
    fun h => ⟨_, stripLookup_nonrec hspec h (fun _ h => by cases h)⟩
  have hmajor : ({ Hstep.restored.newInfo with rules := [] } : Lean.RecursorVal).getMajorInduct =
      Hstep.restored.newInfo.getMajorInduct := rfl
  rw [hmajor]
  rcases hhead with ⟨hnot, hmi⟩ | ⟨nm, nested, ls, hfindN, hfn⟩
  · have hlt : owner.val < sourceDecl.types.length := by
      by_contra hge
      apply hnot
      rw [compilationRestoration_heads_auxiliary,
        auxiliarySpecializations_headNames Haux Hexpansion]
      apply mem_familyNames_of_type
      exact List.mem_iff_getElem.mpr ⟨owner.val - sourceDecl.types.length, by simp; omega, by
        simp only [List.getElem_drop]; congr 1; omega⟩
    have hmemNames : (E.production.loweredDecl.types[owner.val]'hi).name ∈
        sourceTypes.map (·.name) := by
      rw [E.sourceNames_eq]
      exact List.mem_map_of_mem
        (List.mem_iff_getElem.mpr ⟨owner.val, by simp; omega, by simp⟩)
    obtain ⟨t0, ht0, ht0name⟩ := List.mem_map.mp hmemNames
    obtain ⟨s1, t1, Hind, hmemH⟩ := hheaders t0 ht0
    have hfindH := Htrace.findEntry hsourceWF hmemH
    have hhname : (ConstantInfo.inductInfo Hind.restored.header.newInfo).name = t0.name := by
      change Hind.restored.header.newInfo.name = t0.name
      rw [Hind.restored.header.restored]
      exact (E.loweredSourceKeyed ht0 Hind.lookup : Hind.oldInfo.name = t0.name)
    rw [hhname, Kernel.Environment.find?_eq_constants houtWF] at hfindH
    rw [hmi, ← ht0name]
    exact hnonrec hfindH
  · obtain ⟨I0, ls0, info0, hfn0, hfind0⟩ := E.auxNestedHead wf Hsources hfindN
    rw [hfn] at hfn0
    simp only [Expr.const.injEq] at hfn0
    rw [hfn0.1]
    rw [← henv, Kernel.Environment.find?_eq_constants hsourceWF] at hfind0
    exact hnonrec (Hactual.preservesSourceMapFind hsourceWF hfind0)

end VerifyInductive
end Lean4Lean
