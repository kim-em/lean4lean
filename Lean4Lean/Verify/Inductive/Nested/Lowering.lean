import Lean4Lean.Verify.Inductive.Run.Formation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- The first executable check on every source inductive header is an ordinary
type-checker run. At an empty local context its successful result already
provides both the source translation and the abstract typing derivation; later
stages must transport the same statement through the common-parameter local
context. -/
theorem checkType_closed.WF
    (hvalid : CheckingEnv.Valid safety env venv)
    (hclosed : e.FVarsIn fun _ => False) :
    (TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType e)).WF
      fun ty => ∃ e' ty', TrTyping venv lparams [] e ty e' ty' := by
  have hfvars : e.FVarsIn fun fv => fv ∈ VLCtx.fvars ([] : VLCtx) :=
    hclosed.mono fun _ h => False.elim h
  exact TypeChecker.M.WF.runCheckingValid
    (wf := hvalid) (lparams := lparams) (fuel := fuel)
    (TypeChecker.checkType.WF hfvars)

/-- Semantic postcondition of the production nested-auxiliary validation pass:
every witness stored in `aux2nested` has a translated typing derivation in the
restored parameter context. -/
def ValidatedNestedAuxiliaries (venv : VEnv) (lparams : List Name)
    (vlctx : VLCtx) (res : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∀ name e, res.aux2nested.find? name = some e →
    ∃ ty e' ty', TrTyping venv lparams vlctx e ty e' ty' ∧
      venv.IsType lparams.length vlctx.toCtx e'

/-- Context-independent form of nested-auxiliary validation.  Each open
witness is closed using the exact parameter telescope retained by lowering,
so later restoration may choose fresh binder names without changing the
statement that must be translated. -/
def ClosedValidatedNestedAuxiliaries (venv : VEnv) (lparams : List Name)
    (res : Lean4Lean.ElimNestedInductive.Result) : Prop :=
  ∀ name e, res.aux2nested.find? name = some e →
    ∃ e', TrExprS venv lparams [] (res.lctx.mkForall res.params e) e' ∧
      venv.IsType lparams.length [] e'

/-- De-Bruijn form of one closed auxiliary witness.  It records both the
closed translation and the residual translation obtained by inverting its
parameter forall telescope, so no production free-variable identifier occurs
in the semantic context. -/
structure ClosedNestedAuxiliaryTranslation
    (venv : VEnv) (lparams : List Name)
    (res : Lean4Lean.ElimNestedInductive.Result)
    (selection : LocalForallSelection res.lctx res.params)
    (e : Expr) where
  closedTarget : VExpr
  domains : List VExpr
  residualTarget : VExpr
  arity : domains.length = res.params.size
  closed : TrExprS venv lparams []
    (res.lctx.mkForall res.params e) closedTarget
  closedType : venv.IsType lparams.length [] closedTarget
  target : closedTarget = VExpr.wrapForalls domains residualTarget
  residual : TrExprS venv lparams (abstractForallContext domains [])
    (e.abstractList selection.fvars) residualTarget
  residualType : venv.IsType lparams.length
    (abstractForallContext domains []).toCtx residualTarget

/-- The expression inserted by a family hit in `restoreNestedNode` closes to
the same de-Bruijn auxiliary body retained by `residual`, independently of
the fresh free-variable names chosen by restoration.  This is the alpha-
conversion bridge between executable restoration and the canonical closed
auxiliary translation. -/
theorem ClosedNestedAuxiliaryTranslation.restorationAlpha
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e)
    (Hscope : e.FVarsIn (· ∈ selection.fvars))
    (restoreSelection : LocalForallSelection restoreLctx restoreAs)
    (hrestoreNodup : restoreSelection.fvars.Nodup) :
    (((e.abstract res.params).instantiateRev restoreAs).abstract restoreAs) =
      e.abstractList selection.fvars := by
  have hlowered : e.abstract res.params =
      e.abstractList selection.fvars := by
    calc
      e.abstract res.params =
          e.abstract (selection.fvars.map Expr.fvar).toArray :=
        congrArg e.abstract selection.expressions
      _ = e.abstractList selection.fvars := Expr.abstract_eq _ _
  have Hclosed : (e.abstractList selection.fvars).FVarsIn
      (fun _ => False) := by
    apply FVarsIn.abstractList_of
    exact Hscope.mono fun fv hfv => Or.inl hfv
  have Haway : (e.abstractList selection.fvars).FVarsIn
      (fun fv => fv ∉ restoreSelection.fvars) :=
    Hclosed.mono fun _ hfalse => False.elim hfalse
  have Hcancel := Haway.abstract_instantiateRev_fvarArray restoreAs
    restoreSelection.fvars restoreSelection.expressions hrestoreNodup
  rw [hlowered]
  exact Hcancel

/-- Depth-general form of `restorationAlpha`, for auxiliary occurrences
encountered underneath the remaining recursor binders. -/
theorem ClosedNestedAuxiliaryTranslation.restorationAlphaAt
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e)
    (Hscope : e.FVarsIn (· ∈ selection.fvars))
    (hselectionNodup : selection.fvars.Nodup)
    (restoreSelection : LocalForallSelection restoreLctx restoreAs)
    (hrestoreNodup : restoreSelection.fvars.Nodup)
    (hsize : restoreSelection.fvars.length = selection.fvars.length)
    (k : Nat) :
    ((e.abstract res.params).instantiateRev restoreAs).abstractList
        restoreSelection.fvars k =
      e.abstractList selection.fvars k := by
  have hopen : (e.abstract res.params).instantiateRev restoreAs =
      Expr.reopenFVarsAt e selection.fvars restoreSelection.fvars k := by
    symm
    exact Expr.reopenFVarsAt_eq_reopenParams hselectionNodup hsize
      selection.expressions restoreSelection.expressions e k
  rw [hopen]
  unfold Expr.reopenFVarsAt
  apply FVarsIn.abstractList_instantiateRevList
  · have Hclosed : (e.abstractList selection.fvars k).FVarsIn
        (fun _ => False) := by
      apply FVarsIn.abstractList_of
      exact Hscope.mono fun fv hfv => Or.inl hfv
    exact Hclosed.mono fun _ hfalse => False.elim hfalse
  · exact hrestoreNodup

/-- The closed auxiliary witness itself is a binder-by-binder typed
telescope, using the same certificate language as restored recursor types. -/
theorem ClosedNestedAuxiliaryTranslation.telescopeTyped
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e) :
    Expr.ForallTelescopeTypeTranslation venv lparams []
      (res.lctx.mkForall res.params e) res.params.size H.closedTarget := by
  have Htel := selection.forallTelescope e
  exact Expr.ForallTelescopeTypeTranslation.ofTrExprS Htel H.closed
    H.closedType

/-- The open auxiliary witness contains no pre-existing loose bound
variables.  This is derived from the residual translation's scoping theorem,
not imposed as an additional executable validation condition. -/
theorem ClosedNestedAuxiliaryTranslation.sourceClosed
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e) :
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

/-- The residual auxiliary translation remains valid underneath any suffix
of freshly introduced recursor binders.  The concrete source is presented at
the actual binder depth used by restoration rather than as an opaque lift. -/
theorem ClosedNestedAuxiliaryTranslation.residualUnder
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e)
    (henv : venv.Ordered) (hselectionNodup : selection.fvars.Nodup)
    (suffixDomains : List VExpr) :
    TrExprS venv lparams
      (abstractForallContext suffixDomains
        (abstractForallContext H.domains []))
      (e.abstractList selection.fvars suffixDomains.length)
      (H.residualTarget.liftN suffixDomains.length 0) := by
  have Hweak := H.residual.weakBV henv
    (abstractForallContext.bvLift suffixDomains
      (abstractForallContext H.domains []))
  rw [← Expr.abstractList_add_eq_liftLooseBVars H.sourceClosed
    hselectionNodup] at Hweak
  simpa using Hweak

/-- Typehood is weakened through the same suffix context as `residualUnder`.
Together the two theorems provide exactly the leaf payload required by
`ForallTelescopeTypeTranslation`. -/
theorem ClosedNestedAuxiliaryTranslation.residualTypeUnder
    (H : ClosedNestedAuxiliaryTranslation venv lparams res selection e)
    (henv : venv.Ordered) (suffixDomains : List VExpr) :
    venv.IsType lparams.length
      (abstractForallContext suffixDomains
        (abstractForallContext H.domains [])).toCtx
      (H.residualTarget.liftN suffixDomains.length 0) := by
  exact H.residualType.weakN henv
    (abstractForallContext.bvLift suffixDomains
      (abstractForallContext H.domains [])).toCtx

def ClosedNestedAuxiliaryTranslations
    (venv : VEnv) (lparams : List Name)
    (res : Lean4Lean.ElimNestedInductive.Result)
    (selection : LocalForallSelection res.lctx res.params) : Prop :=
  ∀ name e, res.aux2nested.find? name = some e →
    Nonempty (ClosedNestedAuxiliaryTranslation venv lparams res selection e)

/-- Telescope inversion turns every context-independent validated witness
into the canonical bound-variable representation used beneath restored
recursor parameter binders. -/
theorem ClosedValidatedNestedAuxiliaries.residualTranslations
    (H : ClosedValidatedNestedAuxiliaries venv lparams res)
    (henv : venv.WF)
    (selection : LocalForallSelection res.lctx res.params) :
    ClosedNestedAuxiliaryTranslations venv lparams res selection := by
  intro name e hfind
  rcases H name e hfind with ⟨closedTarget, Hclosed, HclosedType⟩
  have Htel := selection.forallTelescope e
  rcases TrExprS.forallTelescope_typed_shape_with_context henv Htel Hclosed
      HclosedType with
    ⟨domains, residualTarget, harity, htarget, Hresidual, HresidualType⟩
  exact ⟨⟨closedTarget, domains, residualTarget, harity, Hclosed,
    HclosedType, htarget, Hresidual, HresidualType⟩⟩

private theorem checkNestedAuxiliaryList.WF
    {c : TypeChecker.VContext} {s : TypeChecker.VState}
    (items : List (Name × Expr))
    (hfvars : ∀ item ∈ items,
      item.2.FVarsIn (· ∈ c.vlctx.fvars)) :
    (items.forM fun item => do
      let type ← TypeChecker.checkType item.2
      _ ← TypeChecker.ensureSort type item.2).WF c s fun _ _ =>
        ∀ item ∈ items, ∃ ty e' ty',
          TrTyping c.venv c.lparams c.vlctx item.2 ty e' ty' ∧
          c.venv.IsType c.lparams.length c.vlctx.toCtx e' := by
  induction items generalizing s with
  | nil =>
    rw [List.forM]
    exact .pure fun item hitem => by simp at hitem
  | cons head tail ih =>
    rw [List.forM]
    have Hhead : (do
        let type ← TypeChecker.checkType head.2
        _ ← TypeChecker.ensureSort type head.2).WF c s fun _ _ =>
          ∃ ty e' ty', TrTyping c.venv c.lparams c.vlctx
            head.2 ty e' ty' ∧
            c.venv.IsType c.lparams.length c.vlctx.toCtx e' := by
      refine (TypeChecker.checkType.WF (hfvars head (by simp))).bind
        fun ty _ _ htyping => ?_
      rcases htyping with ⟨e', ty', htyping⟩
      rcases htyping with ⟨hbelow, hexpr, htype, hhasType⟩
      refine (TypeChecker.ensureSort.WF htype).bind
        fun _ _ _ ⟨⟨_, hsort, hdefeq⟩, hsortEq⟩ => .pure ?_
      obtain ⟨u, rfl⟩ := hsortEq
      cases hsort with
      | sort hu =>
        exact ⟨ty, e', ty', ⟨hbelow, hexpr, htype, hhasType⟩,
          ⟨_, hhasType.defeqU_r c.Ewf c.Δwf hdefeq.symm⟩⟩
    have htail : ∀ item ∈ tail,
        item.2.FVarsIn (· ∈ c.vlctx.fvars) := by
      intro item hitem
      exact hfvars item (by simp [hitem])
    exact Hhead.bind fun _ _ _ hhead =>
      (ih htail).mono fun _ _ _ hall item hitem => by
        rcases List.mem_cons.mp hitem with heq | hitem
        · subst item
          exact hhead
        · exact hall item hitem

/-- The executable `validateNestedAuxiliaries` loop establishes its concrete
typing postcondition, assuming the restored environment and parameter local
context already refine their abstract counterparts. -/
theorem validateNestedAuxiliaries.WF
    (hvalid : CheckingEnv.Valid safety env venv)
    (mlctx : TypeChecker.MLCtx) (hmlctx : mlctx.WF venv lparams)
    (hlctx : mlctx.lctx = res.lctx)
    (hfresh : ∀ fv ∈ mlctx.vlctx.fvars,
      ({} : TypeChecker.State).ngen.Reserves fv)
    (hfvars : ∀ name e, res.aux2nested.find? name = some e →
      e.FVarsIn (· ∈ mlctx.vlctx.fvars)) :
    (Lean4Lean.validateNestedAuxiliaries env lparams safety fuel res).WF
      fun _ => ValidatedNestedAuxiliaries venv lparams mlctx.vlctx res := by
  unfold Lean4Lean.validateNestedAuxiliaries
  rw [← hlctx]
  change (TypeChecker.M.run env safety mlctx.lctx lparams fuel
    ((show Std.TreeMap Name Expr Name.quickCmp from res.aux2nested).forM
      fun _ e => do
        let type ← TypeChecker.checkType e
        _ ← TypeChecker.ensureSort type e)).WF _
  rw [Std.TreeMap.forM_eq_forM, Std.TreeMap.forM_eq_forM_toList]
  refine TypeChecker.M.WF.runCheckingValidMLC
    (wf := hvalid) (mlctx_wf := hmlctx) hfresh ?_
  refine (checkNestedAuxiliaryList.WF
    (c := TypeChecker.VContext.mkCheckingValidMLC hvalid mlctx hmlctx fuel)
    (s := {}) res.aux2nested.toList ?_).mono ?_
  · intro item hitem
    apply hfvars item.1 item.2
    change (show Std.TreeMap Name Expr Name.quickCmp from
      res.aux2nested)[item.1]? = some item.2
    exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hitem
  · intro _ _ _ hall name e hfind
    apply hall (name, e)
    apply Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr
    change (show Std.TreeMap Name Expr Name.quickCmp from
      res.aux2nested)[name]? = some e
    exact hfind

/-- Exact parameter-telescope path followed by nested lowering. The relation
retains both the growing local context and the array of corresponding free
variables, making the later restoration substitution auditable. -/
inductive NestedParamOpening : LocalContext → Array Expr → Expr → Nat →
    LocalContext → Expr → Array Expr → Prop
  | done : NestedParamOpening lctx params type 0 lctx type params
  | step {id : FVarId} {name : Name} {dom body : Expr} {bi : BinderInfo} :
      NestedParamOpening
        (lctx.mkLocalDecl id name dom bi) (params.push (.fvar id))
        (body.instantiate1 (.fvar id)) n outLctx tail outParams →
      NestedParamOpening lctx params (.forallE name dom body bi) (n + 1)
        outLctx tail outParams

/-- Fresh local-context invariant for the `_nested_fresh` name generator used
by `ElimNestedInductive.withParams`. -/
structure NestedBindingContextWF (lctx : LocalContext)
    (ngen : NameGenerator) where
  wf : lctx.WF
  fresh : ∀ fv ∈ lctx.fvars, ngen.Reserves fv
  findCDecl : ∀ fv ∈ lctx.fvars, ∃ index name type bi kind,
    lctx.find? fv = some (.cdecl index fv name type bi kind)

def NestedBindingContextWF.empty (ngen : NameGenerator) :
    NestedBindingContextWF {} ngen :=
  ⟨.nil, by
    intro fv hmem
    have hempty :
        ((.empty : PersistentArray (Option LocalDecl)).toList') = [] := rfl
    have htoList : ({} : LocalContext).toList = [] := by
      unfold LocalContext.toList
      change ((.empty : PersistentArray (Option LocalDecl)).toList').reverse.filterMap id = []
      rw [hempty]
      rfl
    rw [LocalContext.fvars, htoList] at hmem
    simp at hmem, by
    intro fv hmem
    have hempty :
        ((.empty : PersistentArray (Option LocalDecl)).toList') = [] := rfl
    have htoList : ({} : LocalContext).toList = [] := by
      unfold LocalContext.toList
      change ((.empty : PersistentArray (Option LocalDecl)).toList').reverse.filterMap id = []
      rw [hempty]
      rfl
    rw [LocalContext.fvars, htoList] at hmem
    simp at hmem⟩

def NestedBindingContextWF.withLocalDecl
    (H : NestedBindingContextWF lctx ngen)
    (name : Name) (type : Expr) (bi : BinderInfo) :
    NestedBindingContextWF
      (lctx.mkLocalDecl ⟨ngen.curr⟩ name type bi) ngen.next where
  wf := H.wf.mkLocalDecl <| by
    rw [H.wf.find?_eq_find?_toList]
    by_contra hne
    rcases Option.ne_none_iff_exists.mp hne with ⟨d, hfind⟩
    exact ngen.not_reserves_self (H.fresh _ <| by
      rw [LocalContext.fvars]
      apply List.mem_map.mpr
      have hp := List.find?_some hfind.symm
      have heq : ⟨ngen.curr⟩ = d.fvarId := by simpa using hp
      exact ⟨d, List.mem_of_find?_eq_some hfind.symm, heq.symm⟩)
  fresh := by
    intro fv hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact ngen.next_reserves_self
    · exact (H.fresh _ hmem).mono NameGenerator.LE.next
  findCDecl := by
    intro fv hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · refine ⟨lctx.decls.size, name, type, bi, .default, ?_⟩
      simp [LocalContext.mkLocalDecl, LocalContext.find?,
        H.wf.map_wf.find?_insert]
    · rcases H.findCDecl fv hmem with
        ⟨index, oldName, oldType, oldBi, kind, hfind⟩
      refine ⟨index, oldName, oldType, oldBi, kind, ?_⟩
      simp only [LocalContext.mkLocalDecl, LocalContext.find?,
        H.wf.map_wf.find?_insert]
      rw [if_neg]
      · exact hfind
      · intro heq
        have : fv = ⟨ngen.curr⟩ :=
          (LawfulBEq.eq_of_beq heq).symm
        subst fv
        exact ngen.not_reserves_self (H.fresh _ hmem)

/-- Exact free-variable array threaded alongside the nested local context. -/
structure NestedBoundParams (lctx : LocalContext) (params : Array Expr) where
  fvars : List FVarId
  expressions : params = (fvars.map Expr.fvar).toArray
  members : ∀ fv ∈ fvars, fv ∈ lctx.fvars
  nodup : fvars.Nodup

def NestedBoundParams.empty : NestedBoundParams {} #[] :=
  ⟨[], by simp, by simp, by simp⟩

def NestedBoundParams.push
    (H : NestedBoundParams lctx params)
    (Hctx : NestedBindingContextWF lctx ngen)
    (name : Name) (type : Expr) (bi : BinderInfo) :
    NestedBoundParams (lctx.mkLocalDecl ⟨ngen.curr⟩ name type bi)
      (params.push (.fvar ⟨ngen.curr⟩)) where
  fvars := H.fvars ++ [⟨ngen.curr⟩]
  expressions := by simp [H.expressions]
  members := by
    intro fv hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    rcases hmem with hold | rfl
    · exact Or.inr (H.members fv hold)
    · exact Or.inl rfl
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨H.nodup, by simp, ?_⟩
    intro fv hfv fresh hfresh
    simp only [List.mem_singleton] at hfresh
    subst fresh
    intro heq
    subst fv
    exact ngen.not_reserves_self <| Hctx.fresh _ (H.members _ hfv)

def NestedBoundParams.toSelection
    (H : NestedBoundParams lctx params) (Hctx : NestedBindingContextWF lctx ngen) :
    LocalForallSelection lctx params where
  fvars := H.fvars
  expressions := H.expressions
  declarations fv hfv := Hctx.findCDecl fv (H.members fv hfv)

/-- Parameter contexts opened by nested lowering can close any expression
whose free variables are among the opened parameters. This strengthens the
plain local-context/selection witnesses with the exact fact needed when a
generated auxiliary family is itself processed by the dynamic queue. -/
structure NestedClosingContext (lctx : LocalContext) (params : Array Expr)
    (ngen : NameGenerator) where
  binding : NestedBindingContextWF lctx ngen
  selection : LocalForallSelection lctx params
  nodup : selection.fvars.Nodup
  close : ∀ body, body.FVarsIn (· ∈ selection.fvars) →
    (lctx.mkForall params body).FVarsIn fun _ => False

def NestedClosingContext.empty (ngen : NameGenerator) :
    NestedClosingContext {} #[] ngen where
  binding := NestedBindingContextWF.empty ngen
  selection := {
    fvars := []
    expressions := by simp
    declarations := by simp }
  nodup := by simp
  close := by
    intro body Hbody
    have Hbody' : body.FVarsIn (fun _ => False) := by
      simpa [Lean4Lean.FVarsIn] using Hbody
    rw [show (#[] : Array Expr) = ([].map Expr.fvar).toArray from rfl,
      LocalContext.mkForall, LocalContext.mkBinding_eq]
    simpa only [LocalContext.mkBindingList_nil] using Hbody'

def NestedClosingContext.push
    (H : NestedClosingContext lctx params ngen)
    (name : Name) (dom : Expr) (bi : BinderInfo)
    (Hdom : dom.FVarsIn (· ∈ H.selection.fvars)) :
    NestedClosingContext
      (lctx.mkLocalDecl ⟨ngen.curr⟩ name dom bi)
      (params.push (.fvar ⟨ngen.curr⟩)) ngen.next := by
  let id : FVarId := ⟨ngen.curr⟩
  let nextLctx := lctx.mkLocalDecl id name dom bi
  let nextParams := params.push (.fvar id)
  have hidNotMem : id ∉ H.selection.fvars := by
    intro hid
    rcases H.selection.declarations id hid with
      ⟨index, oldName, oldType, oldBi, kind, hfind⟩
    exact ngen.not_reserves_self (H.binding.fresh id <| by
      rw [LocalContext.fvars]
      apply List.mem_map.mpr
      rw [H.binding.wf.find?_eq_find?_toList] at hfind
      exact ⟨.cdecl index id oldName oldType oldBi kind,
        List.mem_of_find?_eq_some hfind, rfl⟩)
  let nextSelection : LocalForallSelection nextLctx nextParams := {
    fvars := H.selection.fvars ++ [id]
    expressions := by
      simp [nextParams, H.selection.expressions]
    declarations := by
      intro fv hfv
      simp only [List.mem_append, List.mem_singleton] at hfv
      rcases hfv with hold | rfl
      · rcases H.selection.declarations fv hold with
          ⟨index, oldName, oldType, oldBi, kind, hfind⟩
        refine ⟨index, oldName, oldType, oldBi, kind, ?_⟩
        simp only [nextLctx, LocalContext.mkLocalDecl, LocalContext.find?,
          H.binding.wf.map_wf.find?_insert]
        rw [if_neg]
        · exact hfind
        · intro heq
          exact hidNotMem (by
            have heq' : id = fv := beq_iff_eq.mp heq
            exact heq' ▸ hold)
      · refine ⟨lctx.decls.size, name, dom, bi, .default, ?_⟩
        simp [nextLctx, LocalContext.mkLocalDecl, LocalContext.find?,
          H.binding.wf.map_wf.find?_insert] }
  refine {
    binding := H.binding.withLocalDecl name dom bi
    selection := nextSelection
    nodup := by
      simp only [nextSelection]
      apply List.nodup_append.mpr
      refine ⟨H.nodup, by simp, ?_⟩
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hidNotMem (heq ▸ hfv)
    close := ?_ }
  intro body Hbody
  have hnextDecls : ∀ fv ∈ nextSelection.fvars, ∃ decl,
      nextLctx.find? fv = some decl := by
    intro fv hfv
    rcases nextSelection.declarations fv hfv with
      ⟨index, declName, type, declBi, kind, hfind⟩
    exact ⟨.cdecl index fv declName type declBi kind, hfind⟩
  have holdDecls : ∀ fv ∈ H.selection.fvars, ∃ decl,
      nextLctx.find? fv = some decl := by
    intro fv hfv
    exact hnextDecls fv (by simp [nextSelection, hfv])
  have hfindOld : ∀ fv ∈ H.selection.fvars,
      nextLctx.find? fv = lctx.find? fv := by
    intro fv hfv
    simp only [nextLctx, LocalContext.mkLocalDecl, LocalContext.find?,
      H.binding.wf.map_wf.find?_insert]
    rw [if_neg]
    intro heq
    exact hidNotMem (by
      have heq' : id = fv := beq_iff_eq.mp heq
      exact heq' ▸ hfv)
  have happend :
      LocalContext.mkBindingList false nextLctx nextSelection.fvars body =
        LocalContext.mkBindingList false nextLctx H.selection.fvars
          (.forallE name dom (body.abstract1 id) bi) := by
    rw [LocalContext.mkBindingList_eq_fold hnextDecls (by
      simp only [nextSelection]
      apply List.nodup_append.mpr
      refine ⟨H.nodup, by simp, ?_⟩
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hidNotMem (heq ▸ hfv))]
    rw [LocalContext.mkBindingList_eq_fold holdDecls H.nodup]
    simp only [nextSelection, List.foldr_append, List.foldr_cons,
      List.foldr_nil]
    simp [LocalContext.mkBindingList1, nextLctx,
      LocalContext.mkLocalDecl, LocalContext.find?,
      H.binding.wf.map_wf.find?_insert]
  have hcloseEq :
      nextLctx.mkForall nextParams body =
        lctx.mkForall params (.forallE name dom (body.abstract1 id) bi) := by
    rw [show nextParams = (nextSelection.fvars.map Expr.fvar).toArray from
      nextSelection.expressions]
    rw [show params = (H.selection.fvars.map Expr.fvar).toArray from
      H.selection.expressions]
    rw [LocalContext.mkForall, LocalContext.mkBinding_eq,
      LocalContext.mkForall, LocalContext.mkBinding_eq, happend]
    exact LocalContext.mkBindingList_congr hfindOld
  rw [hcloseEq]
  apply H.close
  constructor
  · exact Hdom
  · apply FVarsIn.abstract1_of
    exact Hbody.mono fun fv hfv => by
      simp only [nextSelection, List.mem_append, List.mem_singleton] at hfv
      rcases hfv with hfv | hfv
      · exact Or.inr hfv
      · exact Or.inl hfv

theorem NestedParamOpening.params_size
    (H : NestedParamOpening lctx params type n outLctx tail outParams) :
    outParams.size = params.size + n := by
  induction H with
  | done => simp
  | step _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem NestedParamOpening.forallTelescope
    (H : NestedParamOpening lctx As e n outLctx tail outAs) :
    ∃ residual, Expr.ForallTelescope e n residual := by
  induction H with
  | done => exact ⟨_, .nil _⟩
  | step Hnext ih =>
    rcases ih with ⟨openedResidual, Hopened⟩
    rw [Expr.instantiate1_eq] at Hopened
    rcases Hopened.reflect_instantiate1'_fvar with
      ⟨sourceResidual, Hsource⟩
    exact ⟨sourceResidual, .cons Hsource⟩

theorem NestedParamOpening.params_extension
    (H : NestedParamOpening lctx params type n outLctx tail outParams) :
    ∃ suffix, outParams.toList = params.toList ++ suffix ∧
      suffix.length = n := by
  induction H with
  | done => exact ⟨[], by simp⟩
  | @step lctx params name dom body bi id n outLctx tail outParams H ih =>
    rcases ih with ⟨suffix, heq, hlength⟩
    refine ⟨(.fvar id) :: suffix, ?_, by simp [hlength]⟩
    simpa [heq, List.append_assoc]

theorem NestedParamOpening.tailFVarsIn
    (H : NestedParamOpening lctx params type n outLctx tail outParams)
    (Hselection : LocalForallSelection outLctx outParams)
    (Htype : type.FVarsIn (· ∈ Hselection.fvars)) :
    tail.FVarsIn (· ∈ Hselection.fvars) := by
  induction H with
  | done => exact Htype
  | @step lctx params name dom body bi id n outLctx tail outParams Hnext ih =>
    apply ih Hselection
    rw [Expr.instantiate1_eq]
    apply Htype.2.instantiate1
    simp only [Lean4Lean.FVarsIn]
    apply Hselection.fvar_mem
    rcases Hnext.params_extension with ⟨suffix, hsuffix, _⟩
    apply Array.mem_toList_iff.mp
    rw [hsuffix]
    simp

theorem NestedParamOpening.initial_size
    (H : NestedParamOpening {} #[] type n outLctx tail outParams) :
    outParams.size = n := by simpa using H.params_size

/-- A production recursor-parameter replay is the same syntactic opening as
`NestedParamOpening`, with the already allocated cached parameter variables
used in place of freshly generated ones.  This bridge lets later equation
proofs reuse the alpha-invariant residual lemmas developed for nested
restoration rather than reimplementing simultaneous closing. -/
theorem RecursorParamPrefix.toNestedParamOpening
    (H : RecursorParamPrefix stats 0 source tail)
    (Hparams : BoundFVarArray c stats.params) :
    ∃ outLctx, NestedParamOpening {} #[] source stats.params.size
      outLctx tail stats.params := by
  have go : ∀ {i source tail},
      RecursorParamPrefix stats i source tail →
      ∀ (lctx : LocalContext) (opened : Array Expr),
        opened.toList = stats.params.toList.take i →
        ∃ outLctx, NestedParamOpening lctx opened source
          (stats.params.size - i) outLctx tail stats.params := by
    intro i source tail Hprefix
    induction Hprefix with
    | @done i tail hi =>
      intro lctx opened hopened
      have hopenedFull : opened = stats.params := by
        apply Array.toList_inj.mp
        rw [hopened, hi]
        change stats.params.toList.take stats.params.toList.length =
          stats.params.toList
        exact List.take_length
      subst opened
      have hzero : stats.params.size - i = 0 := by omega
      rw [hzero]
      exact ⟨lctx, NestedParamOpening.done⟩
    | @step i param tail name dom body bi hparam Hnext ih =>
      intro lctx opened hopened
      obtain ⟨hi, hparamGet⟩ := Array.getElem?_eq_some_iff.mp hparam
      rcases Hparams.getElem_eq_fvar i hi with ⟨_hiFvars, hparamFVar⟩
      have hparamEq : param = .fvar Hparams.fvars[i] := by
        exact hparamGet.symm.trans hparamFVar
      subst param
      have hopenedNext :
          (opened.push (.fvar Hparams.fvars[i])).toList =
            stats.params.toList.take (i + 1) := by
        rw [Array.toList_push, hopened,
          List.take_succ_eq_append_getElem (by simpa using hi)]
        simpa using congrArg
          (fun e => stats.params.toList.take i ++ [e]) hparamFVar.symm
      rcases ih (lctx.mkLocalDecl Hparams.fvars[i] name dom bi)
          (opened.push (.fvar Hparams.fvars[i])) hopenedNext with
        ⟨outLctx, Hopening⟩
      refine ⟨outLctx, ?_⟩
      rw [hparamFVar] at Hopening
      have Hstep := NestedParamOpening.step Hopening
      have hcount : stats.params.size - (i + 1) + 1 =
          stats.params.size - i := by omega
      rw [hcount] at Hstep
      exact Hstep
  simpa using go H {} #[] (by simp)

private theorem nestedWithParamsLoop_refines {α : Type}
    (k : LocalContext → Expr → Array Expr →
      Lean4Lean.ElimNestedInductive.M α)
    (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State)
    (Q : α × Lean4Lean.ElimNestedInductive.State → Prop)
    (Hk : ∀ outLctx tail outParams outState,
      NestedParamOpening lctx params type n outLctx tail outParams →
      (k outLctx tail outParams env outState).WF Q) :
    (Lean4Lean.ElimNestedInductive.withParams.loop
      k lctx type params n env state).WF Q := by
  induction n generalizing lctx type params state with
  | zero =>
    simpa [Lean4Lean.ElimNestedInductive.withParams.loop] using
      Hk lctx type params state .done
  | succ n ih =>
    cases type with
    | forallE name dom body bi =>
      simp only [Lean4Lean.ElimNestedInductive.withParams.loop]
      simp only [mkFreshId, getNGen, setNGen,
        Lean4Lean.ElimNestedInductive.instMonadNameGeneratorM,
        StateT.get, StateT.set, StateT.modifyGet,
        bind, StateT.bind, ReaderT.bind, pure, StateT.pure, ReaderT.pure]
      apply ih
      intro outLctx tail outParams outState Hresult
      exact Hk outLctx tail outParams outState (.step Hresult)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj =>
      exact Except.WF.throw

private theorem nestedWithParamsLoop_refinesSelected {α : Type}
    (k : LocalContext → Expr → Array Expr →
      Lean4Lean.ElimNestedInductive.M α)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (Hctx : NestedBindingContextWF lctx state.ngen)
    (Hparams : NestedBoundParams lctx params)
    (Q : α × Lean4Lean.ElimNestedInductive.State → Prop)
    (Hk : ∀ outLctx tail outParams outState,
      NestedParamOpening lctx params type n outLctx tail outParams →
      NestedBindingContextWF outLctx outState.ngen →
      (Hselection : LocalForallSelection outLctx outParams) →
      Hselection.fvars.Nodup →
      outState.newTypes = state.newTypes →
      outState.nestedAux = state.nestedAux →
      outState.nextIdx = state.nextIdx →
      (k outLctx tail outParams env outState).WF Q) :
    (Lean4Lean.ElimNestedInductive.withParams.loop
      k lctx type params n env state).WF Q := by
  induction n generalizing lctx type params state with
  | zero =>
    simpa [Lean4Lean.ElimNestedInductive.withParams.loop] using
      Hk lctx type params state .done Hctx (Hparams.toSelection Hctx)
        Hparams.nodup rfl rfl rfl
  | succ n ih =>
    cases type with
    | forallE name dom body bi =>
      simp only [Lean4Lean.ElimNestedInductive.withParams.loop]
      simp only [mkFreshId, getNGen, setNGen,
        Lean4Lean.ElimNestedInductive.instMonadNameGeneratorM,
        StateT.get, StateT.set, StateT.modifyGet,
        bind, StateT.bind, ReaderT.bind, pure, StateT.pure, ReaderT.pure]
      apply ih
        (Hctx := Hctx.withLocalDecl name dom bi)
        (Hparams := Hparams.push Hctx name dom bi)
      intro outLctx tail outParams outState Hresult HresultCtx Hselection
        hnodup hnewTypes hnestedAux hnextIdx
      exact Hk outLctx tail outParams outState (.step Hresult) HresultCtx
        Hselection hnodup (by simpa using hnewTypes) (by simpa using hnestedAux)
        (by simpa using hnextIdx)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => exact Except.WF.throw

/-- Strengthened parameter opening for a closed source telescope.  Besides
the operational opening trace, the continuation receives a certificate that
re-closing an expression open over exactly those parameters is closed. -/
private theorem nestedWithParamsLoop_refinesClosing {α : Type}
    (k : LocalContext → Expr → Array Expr →
      Lean4Lean.ElimNestedInductive.M α)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (Hclosing : NestedClosingContext lctx params state.ngen)
    (Htype : type.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Q : α × Lean4Lean.ElimNestedInductive.State → Prop)
    (Hk : ∀ outLctx tail outParams outState,
      NestedParamOpening lctx params type n outLctx tail outParams →
      (HoutClosing :
        NestedClosingContext outLctx outParams outState.ngen) →
      tail.FVarsIn (· ∈ HoutClosing.selection.fvars) →
      outState.newTypes = state.newTypes →
      outState.nestedAux = state.nestedAux →
      outState.nextIdx = state.nextIdx →
      (k outLctx tail outParams env outState).WF Q) :
    (Lean4Lean.ElimNestedInductive.withParams.loop
      k lctx type params n env state).WF Q := by
  induction n generalizing lctx type params state with
  | zero =>
    simpa [Lean4Lean.ElimNestedInductive.withParams.loop] using
      Hk lctx type params state .done Hclosing Htype rfl rfl rfl
  | succ n ih =>
    cases type with
    | forallE name dom body bi =>
      simp only [Lean4Lean.ElimNestedInductive.withParams.loop]
      simp only [mkFreshId, getNGen, setNGen,
        Lean4Lean.ElimNestedInductive.instMonadNameGeneratorM,
        StateT.get, StateT.set, StateT.modifyGet,
        bind, StateT.bind, ReaderT.bind, pure, StateT.pure, ReaderT.pure]
      let HnextClosing := Hclosing.push name dom bi Htype.1
      have HnextType :
          (body.instantiate1 (.fvar ⟨state.ngen.curr⟩)).FVarsIn
            (· ∈ HnextClosing.selection.fvars) := by
        rw [Expr.instantiate1_eq]
        have HbodyNext :
            body.FVarsIn (· ∈ HnextClosing.selection.fvars) := by
          apply Htype.2.mono
          intro fv hfv
          change fv ∈ Hclosing.selection.fvars ++ [⟨state.ngen.curr⟩]
          simp [hfv]
        apply HbodyNext.instantiate1
        simp only [Lean4Lean.FVarsIn]
        change (⟨state.ngen.curr⟩ : FVarId) ∈
          Hclosing.selection.fvars ++ [⟨state.ngen.curr⟩]
        simp
      apply ih (Hclosing := HnextClosing) (Htype := HnextType)
      intro outLctx tail outParams outState Hresult HresultClosing Htail
        hnewTypes hnestedAux hnextIdx
      exact Hk outLctx tail outParams outState (.step Hresult)
        HresultClosing Htail (by simpa using hnewTypes)
        (by simpa using hnestedAux) (by simpa using hnextIdx)
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => exact Except.WF.throw

theorem ElimNestedInductive.withParams.refinesSelected {α : Type}
    (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr →
      Lean4Lean.ElimNestedInductive.M α)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (Q : α × Lean4Lean.ElimNestedInductive.State → Prop)
    (Hk : ∀ lctx tail params outState,
      NestedParamOpening {} #[] type nparams lctx tail params →
      NestedBindingContextWF lctx outState.ngen →
      (Hselection : LocalForallSelection lctx params) →
      Hselection.fvars.Nodup →
      outState.newTypes = state.newTypes →
      outState.nestedAux = state.nestedAux →
      outState.nextIdx = state.nextIdx →
      (k lctx tail params env outState).WF Q) :
    (Lean4Lean.ElimNestedInductive.withParams
      type nparams k env state).WF Q := by
  exact nestedWithParamsLoop_refinesSelected k env state
    (NestedBindingContextWF.empty state.ngen) NestedBoundParams.empty Q Hk

theorem ElimNestedInductive.withParams.refinesClosing {α : Type}
    (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr →
      Lean4Lean.ElimNestedInductive.M α)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (Htype : type.FVarsIn fun _ => False)
    (Q : α × Lean4Lean.ElimNestedInductive.State → Prop)
    (Hk : ∀ lctx tail params outState,
      NestedParamOpening {} #[] type nparams lctx tail params →
      (HoutClosing : NestedClosingContext lctx params outState.ngen) →
      tail.FVarsIn (· ∈ HoutClosing.selection.fvars) →
      outState.newTypes = state.newTypes →
      outState.nestedAux = state.nestedAux →
      outState.nextIdx = state.nextIdx →
      (k lctx tail params env outState).WF Q) :
    (Lean4Lean.ElimNestedInductive.withParams
      type nparams k env state).WF Q := by
  let Hclosing := NestedClosingContext.empty state.ngen
  apply nestedWithParamsLoop_refinesClosing k env state Hclosing
  · exact Htype.mono fun fv hfalse => False.elim hfalse
  · exact Hk

theorem ElimNestedInductive.withParams.refines {α : Type}
    (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr →
      Lean4Lean.ElimNestedInductive.M α)
    (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State)
    (Q : α × Lean4Lean.ElimNestedInductive.State → Prop)
    (Hk : ∀ lctx tail params outState,
      NestedParamOpening {} #[] type nparams lctx tail params →
      (k lctx tail params env outState).WF Q) :
    (Lean4Lean.ElimNestedInductive.withParams
      type nparams k env state).WF Q := by
  exact nestedWithParamsLoop_refines k env state Q Hk

/-- Successful parameter instantiation has consumed exactly the requested
number of leading forall binders; the returned term is precisely the exposed
residual instantiated with the supplied parameter array. -/
private theorem stripForallList_refines
    (indices : List Nat) (e : Expr) :
    ((forIn indices e fun _ current =>
      match current with
      | .forallE _ _ body _ => pure (ForInStep.yield body)
      | _ => do
        throw Lean4Lean.ElimNestedInductive.illFormed
        pure (ForInStep.yield current)) :
        Except Exception Expr).WF
      fun tail => Expr.ForallTelescope e indices.length tail := by
  induction indices generalizing e with
  | nil => exact Except.WF.pure (Expr.ForallTelescope.nil e)
  | cons i indices ih =>
    cases e with
    | forallE name dom body bi =>
      have Hrest := (ih body).mono fun tail H =>
        Expr.ForallTelescope.cons (name := name) (dom := dom) (bi := bi) H
      rw [List.forIn_cons]
      exact Except.WF.pureBind Hrest
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
      | proj => exact Except.WF.throw

theorem instantiateForallParams_refines
    (e : Expr) (n : Nat) (params : Array Expr) :
    (Lean4Lean.ElimNestedInductive.instantiateForallParams e n params).WF
      fun out => ∃ tail, Expr.ForallTelescope e n tail ∧
        out = tail.instantiateRevRange 0 n params := by
  unfold Lean4Lean.ElimNestedInductive.instantiateForallParams
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  change (((fun tail =>
      tail.instantiateRevRange 0 n params) <$>
    (forIn (List.range' 0 n) e fun _ current =>
      match current with
      | .forallE _ _ body _ => pure (ForInStep.yield body)
      | _ => do
        throw Lean4Lean.ElimNestedInductive.illFormed
        pure (ForInStep.yield current))) : Except Exception Expr).WF _
  exact Except.WF.map
    (f := fun tail => tail.instantiateRevRange 0 n params)
    (R := fun out => ∃ residual, Expr.ForallTelescope e n residual ∧
      out = residual.instantiateRevRange 0 n params)
    (stripForallList_refines (List.range' 0 n) e)
    (fun tail Htail =>
      (⟨tail, by simpa using Htail, rfl⟩ :
        ∃ residual, Expr.ForallTelescope e n residual ∧
          tail.instantiateRevRange 0 n params =
            residual.instantiateRevRange 0 n params))

theorem replaceNestedParamsCore_refines
    (params : Array Expr) (e : Expr) (args : Array Expr)
    (hsize : args.size = params.size) :
    (Lean4Lean.ElimNestedInductive.replaceParamsCore params e args).WF
      fun out => out = (e.abstract args).instantiateRev params := by
  unfold Lean4Lean.ElimNestedInductive.replaceParamsCore
  simp [hsize]
  exact Except.WF.pure rfl

/-- Parameter replacement cannot truncate either side of the substitution:
success records exact arity equality and the concrete simultaneous
abstraction/instantiation result. -/
theorem replaceNestedParams_refines
    (params : Array Expr) (e : Expr) (args : Array Expr)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : args.size = params.size) :
    (Lean4Lean.ElimNestedInductive.replaceParams params e args env state).WF
      fun out => out.1 = (e.abstract args).instantiateRev params := by
  unfold Lean4Lean.ElimNestedInductive.replaceParams
    Lean4Lean.ElimNestedInductive.replaceParamsCore
  simp [hsize]
  exact Except.WF.pure rfl

theorem replaceNestedParams_state_refines
    (params : Array Expr) (e : Expr) (args : Array Expr)
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hsize : args.size = params.size) :
    (Lean4Lean.ElimNestedInductive.replaceParams params e args env state).WF
      fun out => out = ((e.abstract args).instantiateRev params, state) := by
  unfold Lean4Lean.ElimNestedInductive.replaceParams
    Lean4Lean.ElimNestedInductive.replaceParamsCore
  simp [hsize]
  exact Except.WF.pure rfl

/-- The executable fresh-name search records the numeric suffix it selected,
never moves backwards from its initial counter, and returns a name absent from
the current environment. -/
structure FreshNestedName (env : Environment) (base : Name) (start : Nat)
    (name : Name) (nextIdx : Nat) : Prop where
  index : ∃ i, start ≤ i ∧ name = base.appendIndexAfter i ∧ nextIdx = i + 1
  fresh : env.contains name = false

/-- Intended injectivity law for the numeric suffix used by generated names.
Lean 4.33 defines `Name.appendIndexAfter` through opaque
`String.Internal.append`, but exports no specification theorem connecting that
primitive to proved string append laws. Keeping this as a named boundary
avoids smuggling the missing primitive fact into the inductive proof. -/
def AppendIndexAfterIndexFaithful : Prop :=
  ∀ (firstBase secondBase : Name) (firstIndex secondIndex : Nat),
    firstBase.appendIndexAfter firstIndex =
      secondBase.appendIndexAfter secondIndex →
    firstIndex = secondIndex

theorem appendIndexAfterIndexFaithful : AppendIndexAfterIndexFaithful :=
  Lean.Name.appendIndexAfter_index_injective

/-- Generated cache names are unique and each retained name records a suffix
index strictly below the state's next fresh-name counter. -/
structure NestedAuxNamesWF
    (state : Lean4Lean.ElimNestedInductive.State) : Prop where
  nodup : (state.nestedAux.toList.map Prod.snd).Nodup
  indexed : ∀ (nested : Expr) (name : Name),
    (nested, name) ∈ state.nestedAux →
    ∃ (base : Name) (index : Nat),
      name = base.appendIndexAfter index ∧ index < state.nextIdx
  reserved : ∀ (nested : Expr) (name : Name),
    (nested, name) ∈ state.nestedAux →
    (`_nested).isPrefixOf name = true

def NestedAuxNamesFresh (env : Environment)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ nested name, (nested, name) ∈ state.nestedAux →
    env.contains name = false

theorem NestedAuxNamesFresh.empty
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (hempty : state.nestedAux = #[]) : NestedAuxNamesFresh env state := by
  intro nested name hentry
  rw [hempty] at hentry
  simp at hentry

theorem NestedAuxNamesFresh.ofCacheEq
    (H : NestedAuxNamesFresh env source)
    (haux : target.nestedAux = source.nestedAux) :
    NestedAuxNamesFresh env target := by
  intro nested name hentry
  apply H nested name
  simpa [haux] using hentry

theorem nested_isPrefix_appendIndexAfter
    (sourceName : Name) (index : Nat) :
    (`_nested).isPrefixOf
      ((`_nested ++ sourceName).appendIndexAfter index) = true := by
  have hprefixScopes : (`_nested : Name).hasMacroScopes = false := by
    native_decide
  exact Lean.Name.isPrefixOf_append_appendIndexAfter
    `_nested sourceName index hprefixScopes

theorem NestedAuxNamesWF.empty
    (state : Lean4Lean.ElimNestedInductive.State)
    (hempty : state.nestedAux = #[]) : NestedAuxNamesWF state := by
  constructor
  · simpa [hempty]
  · intro nested name hentry
    rw [hempty] at hentry
    simp at hentry
  · intro nested name hentry
    rw [hempty] at hentry
    simp at hentry

theorem NestedAuxNamesWF.ofCacheCounterEq
    (H : NestedAuxNamesWF source)
    (haux : target.nestedAux = source.nestedAux)
    (hnext : target.nextIdx = source.nextIdx) : NestedAuxNamesWF target := by
  constructor
  · simpa [haux] using H.nodup
  · intro nested name hentry
    have hold : (nested, name) ∈ source.nestedAux := by
      simpa [haux] using hentry
    rcases H.indexed nested name hold with ⟨base, index, hname, hindex⟩
    exact ⟨base, index, hname, by simpa [hnext] using hindex⟩
  · intro nested name hentry
    apply H.reserved nested name
    simpa [haux] using hentry

theorem findUniqueName_refines
    (env : Environment) (base : Name) (start fuel : Nat) :
    (Lean4Lean.ElimNestedInductive.findUniqueName env base start fuel).WF
      fun out => FreshNestedName env base start out.1 out.2 := by
  induction fuel generalizing start with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [Lean4Lean.ElimNestedInductive.findUniqueName]
    split
    next hcontains =>
      exact (ih (start := start + 1)).mono fun out H => ⟨
        ⟨H.index.choose, Nat.le_trans (Nat.le_add_right start 1)
          H.index.choose_spec.1, H.index.choose_spec.2⟩,
        H.fresh⟩
    next hcontains =>
      have hfresh : env.contains (base.appendIndexAfter start) = false := by
        cases h : env.contains (base.appendIndexAfter start) <;> simp_all
      exact Except.WF.pure ⟨⟨start, Nat.le_refl _, rfl, rfl⟩, hfresh⟩

/-- `mkUniqueName` is a state-preserving wrapper around the pure search: only
the fresh-name counter changes. -/
theorem mkUniqueName_refines
    (env : Environment) (state : Lean4Lean.ElimNestedInductive.State)
    (base : Name) :
    (Lean4Lean.ElimNestedInductive.mkUniqueName base env state).WF fun out =>
      ∃ nextIdx,
        FreshNestedName env base state.nextIdx out.1 nextIdx ∧
        out.2 = { state with nextIdx } := by
  unfold Lean4Lean.ElimNestedInductive.mkUniqueName
  exact (findUniqueName_refines env base state.nextIdx
    (env.constants.toList.length + 1)).bind fun out H =>
      Except.WF.pure ⟨out.2, H, rfl⟩

private theorem environmentGet_refines (env : Environment) (name : Name) :
    (env.get name).WF fun info => env.find? name = some info := by
  unfold Lean.Kernel.Environment.get
  split
  next h => exact Except.WF.pure h
  next => exact Except.WF.throw

/-- One generated constructor is obtained from the named source declaration by
level instantiation, exact removal of the source parameters, and re-closing over
the new mutual block parameters. -/
def EnvironmentTypesClosed (env : Environment) : Prop :=
  ∀ name info, env.find? name = some info →
    info.type.FVarsIn fun _ => False

theorem VEnvs.WF.environmentTypesClosed
    (H : VEnvs.WF env ves) : EnvironmentTypesClosed env := by
  intro name info hfind
  rcases (H.tr (safety := .unsafe)).find? hfind
      DefinitionSafety.unsafe_le with ⟨vinfo, _hvfind, Htr⟩
  exact Htr.2.2.fvarsIn.mono fun fv hfv => by simp at hfv

theorem Expr.ForallTelescope.resultFVarsIn
    (H : Expr.ForallTelescope outer arity result)
    (Houter : outer.FVarsIn P) : result.FVarsIn P := by
  induction H with
  | nil => exact Houter
  | cons _ ih => exact ih Houter.2

structure BuiltAuxConstructor
    (env : Environment) (lctx : LocalContext) (As : Array Expr)
    (levels : List Level) (nparams : Nat) (args : Array Expr)
    (sourceFamily auxFamily sourceName : Name) (target : Constructor) : Prop where
  source : ∃ sourceInfo sourceTail,
    env.find? sourceName = some sourceInfo ∧
    Expr.ForallTelescope
      (sourceInfo.type.instantiateLevelParams sourceInfo.levelParams levels)
      nparams sourceTail ∧
    target.name = sourceName.replacePrefix sourceFamily auxFamily ∧
    target.type = lctx.mkForall As
      (sourceTail.instantiateRevRange 0 nparams args)

theorem BuiltAuxConstructor.closed
    (H : BuiltAuxConstructor env lctx As levels nparams args sourceFamily
      auxFamily sourceName target)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars)) :
    target.type.FVarsIn fun _ => False := by
  rcases H.source with
    ⟨sourceInfo, sourceTail, hfind, Htelescope, _hname, htype⟩
  rw [htype]
  apply Hclosing.close
  apply FVarsIn.instantiateRevRange
  · apply Htelescope.resultFVarsIn
    apply ((Henv sourceName sourceInfo hfind).mono fun fv hfalse =>
      False.elim hfalse).instantiateLevelParams
    exact Hlevels
  · exact Hargs

inductive BuiltAuxConstructors
    (env : Environment) (lctx : LocalContext) (As : Array Expr)
    (levels : List Level) (nparams : Nat) (args : Array Expr)
    (sourceFamily auxFamily : Name) : List Name → List Constructor → Prop
  | nil : BuiltAuxConstructors env lctx As levels nparams args
      sourceFamily auxFamily [] []
  | cons : BuiltAuxConstructor env lctx As levels nparams args sourceFamily
      auxFamily sourceName target →
      BuiltAuxConstructors env lctx As levels nparams args sourceFamily
        auxFamily sourceNames targets →
      BuiltAuxConstructors env lctx As levels nparams args sourceFamily
        auxFamily (sourceName :: sourceNames) (target :: targets)

theorem BuiltAuxConstructors.closed
    (H : BuiltAuxConstructors env lctx As levels nparams args sourceFamily
      auxFamily sourceNames targets)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars)) :
    ∀ target ∈ targets, target.type.FVarsIn fun _ => False := by
  induction H with
  | nil => simp
  | cons Hhead Htail ih =>
    intro target htarget
    simp only [List.mem_cons] at htarget
    rcases htarget with rfl | htail
    · exact Hhead.closed Henv Hclosing Hlevels Hargs
    · exact ih target htail

private theorem buildAuxConstructors_refines
    (env : Environment) (lctx : LocalContext) (As : Array Expr)
    (levels : List Level) (nparams : Nat) (args : Array Expr)
    (sourceFamily auxFamily : Name) (sourceNames : List Name) :
    (sourceNames.mapM fun sourceName => do
      let sourceInfo ← env.get sourceName
      let targetName := sourceName.replacePrefix sourceFamily auxFamily
      let sourceType := sourceInfo.type.instantiateLevelParams
        sourceInfo.levelParams levels
      let targetType ← Lean4Lean.ElimNestedInductive.instantiateForallParams
        sourceType nparams args
      return ({ name := targetName, type := lctx.mkForall As targetType } :
        Constructor)).WF fun targets =>
          BuiltAuxConstructors env lctx As levels nparams args sourceFamily
            auxFamily sourceNames targets := by
  induction sourceNames with
  | nil => exact Except.WF.pure .nil
  | cons sourceName sourceNames ih =>
    rw [List.mapM_cons]
    have Hhead : (do
        let sourceInfo ← env.get sourceName
        let targetName := sourceName.replacePrefix sourceFamily auxFamily
        let sourceType := sourceInfo.type.instantiateLevelParams
          sourceInfo.levelParams levels
        let targetType ←
          Lean4Lean.ElimNestedInductive.instantiateForallParams
            sourceType nparams args
        return ({ name := targetName, type := lctx.mkForall As targetType } :
          Constructor)).WF fun target =>
            BuiltAuxConstructor env lctx As levels nparams args sourceFamily
              auxFamily sourceName target :=
      (environmentGet_refines env sourceName).bind fun sourceInfo hlookup =>
      (instantiateForallParams_refines
        (sourceInfo.type.instantiateLevelParams sourceInfo.levelParams levels)
        nparams args).bind fun targetType Htype => Except.WF.pure
          ⟨⟨sourceInfo, Htype.choose, hlookup, Htype.choose_spec.1,
            rfl, congrArg (lctx.mkForall As) Htype.choose_spec.2⟩⟩
    exact Hhead.bind fun _ Htarget =>
      ih.bind fun _ Htargets => Except.WF.pure (.cons Htarget Htargets)

/-- Pure auxiliary construction retains an independently inspectable account
of the source family, its opened family type, parameter substitution, and every
generated constructor. -/
structure BuiltAuxiliary
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (levels : List Level) (nparams : Nat) (args : Array Expr)
    (sourceName auxName : Name) (sourceInfo : InductiveVal)
    (data : Lean4Lean.ElimNestedInductive.AuxiliaryData) : Prop where
  lookup : env.find? sourceName = some (.inductInfo sourceInfo)
  opening : ∃ sourceTail,
    Expr.ForallTelescope
      (sourceInfo.type.instantiateLevelParams sourceInfo.levelParams levels)
      nparams sourceTail ∧
    data.type.type = lctx.mkForall As
      (sourceTail.instantiateRevRange 0 nparams args)
  arity : As.size = params.size
  nested : data.nested =
    ((mkAppRange (.const sourceName levels) 0 nparams args).abstract As).instantiateRev params
  name : data.type.name = auxName
  constructors : BuiltAuxConstructors env lctx As levels nparams args
    sourceName auxName sourceInfo.ctors data.type.ctors

def InductiveConstructorsClosed (type : InductiveType) : Prop :=
  ∀ ctor ∈ type.ctors, ctor.type.FVarsIn fun _ => False

theorem BuiltAuxiliary.constructorsClosed
    (H : BuiltAuxiliary env lctx params As levels nparams args sourceName
      auxName sourceInfo data)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars)) :
    InductiveConstructorsClosed data.type := by
  exact H.constructors.closed Henv Hclosing Hlevels Hargs

/-- Every cached nested witness is open only over the retained outer
parameter context selected by the lowering run. -/
def NestedAuxFVarsIn (P : FVarId → Prop)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ nested name, (nested, name) ∈ state.nestedAux → nested.FVarsIn P

theorem BuiltAuxiliary.nestedFVarsIn
    (H : BuiltAuxiliary env lctx params As levels nparams args sourceName
      auxName sourceInfo data)
    (HAs : LocalForallSelection lctx As)
    (hnparams : nparams ≤ args.size)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P) :
    data.nested.FVarsIn P := by
  rw [H.nested]
  apply FVarsIn.instantiateRev
  · apply FVarsIn.abstract_fvarArray_of HAs.fvars As HAs.expressions
    apply FVarsIn.mkAppRange_zero hnparams
    · simpa [Lean4Lean.FVarsIn] using Hlevels
    · exact Hargs
  · exact Hparams

theorem buildAuxiliary_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (levels : List Level) (nparams : Nat) (args : Array Expr)
    (sourceName auxName : Name) (sourceInfo : InductiveVal)
    (hlookup : env.find? sourceName = some (.inductInfo sourceInfo)) :
    As.size = params.size →
    (Lean4Lean.ElimNestedInductive.buildAuxiliary env lctx params As levels
      nparams args sourceName auxName).WF fun data =>
        BuiltAuxiliary env lctx params As levels nparams args sourceName auxName
          sourceInfo data := by
  intro hsize
  unfold Lean4Lean.ElimNestedInductive.buildAuxiliary
  simp only [Lean.Kernel.Environment.get, hlookup]
  exact (instantiateForallParams_refines
    (sourceInfo.type.instantiateLevelParams sourceInfo.levelParams levels)
    nparams args).bind fun targetType Htype =>
      (replaceNestedParamsCore_refines params
        (mkAppRange (.const sourceName levels) 0 nparams args) As hsize).bind
        fun nested Hnested =>
          (buildAuxConstructors_refines env lctx As levels nparams args
            sourceName auxName sourceInfo.ctors).bind fun targets Htargets =>
              Except.WF.pure ⟨hlookup,
                ⟨Htype.choose, Htype.choose_spec.1,
                  congrArg (lctx.mkForall As) Htype.choose_spec.2⟩,
                hsize, Hnested, rfl, Htargets⟩

/-- A single fresh-family generation step pairs the cache entry and generated
family through the same fresh name, and otherwise changes only the fresh-name
counter and the two append-only arrays. -/
structure GeneratedAuxiliary
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (nparams : Nat)
    (args : Array Expr) (sourceName : Name) (sourceInfo : InductiveVal)
    (state : Lean4Lean.ElimNestedInductive.State)
    (out : Option Expr × Lean4Lean.ElimNestedInductive.State) : Prop where
  generated : ∃ auxName nextIdx data,
    FreshNestedName env (`_nested ++ sourceName) state.nextIdx auxName nextIdx ∧
    BuiltAuxiliary env lctx params As levels nparams args sourceName auxName
      sourceInfo data ∧
    out.1 = (if sourceName == targetName then
      some (mkAppRange (mkAppN (.const auxName state.lvls) As)
        nparams args.size args)
    else none) ∧
    out.2 = { state with
      nextIdx := nextIdx
      nestedAux := state.nestedAux.push (data.nested, auxName)
      newTypes := state.newTypes.push data.type }

theorem generateAuxiliary_refines
    (env : Environment) (lctx : LocalContext) (params As : Array Expr)
    (targetName : Name) (levels : List Level) (nparams : Nat)
    (args : Array Expr) (sourceName : Name) (sourceInfo : InductiveVal)
    (state : Lean4Lean.ElimNestedInductive.State)
    (hlookup : env.find? sourceName = some (.inductInfo sourceInfo))
    (hsize : As.size = params.size) :
    (Lean4Lean.ElimNestedInductive.generateAuxiliary lctx params As targetName
      levels nparams args sourceName env state).WF fun out =>
        GeneratedAuxiliary env lctx params As targetName levels nparams args
          sourceName sourceInfo state out := by
  unfold Lean4Lean.ElimNestedInductive.generateAuxiliary
  simp only [read, ReaderT.read, bind, ReaderT.bind]
  exact (mkUniqueName_refines env state (`_nested ++ sourceName)).bind
    fun unique Hunique => by
      rcases unique with ⟨auxName, nextState⟩
      simp only at Hunique ⊢
      rcases Hunique with ⟨nextIdx, Hfresh, hstate⟩
      subst nextState
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift,
        StateT.instMonadLift, ReaderT.instMonadLift, StateT.lift,
        StateT.modifyGet, modify, get, StateT.get,
        bind, StateT.bind, ReaderT.bind, pure, StateT.pure, ReaderT.pure]
      have Hbuild :
          ((Lean4Lean.ElimNestedInductive.buildAuxiliary env lctx params As
            levels nparams args sourceName auxName).bind fun data =>
              Except.pure (data, { state with nextIdx })).WF fun out =>
            BuiltAuxiliary env lctx params As levels nparams args sourceName
              auxName sourceInfo out.1 ∧ out.2 = { state with nextIdx } :=
        (buildAuxiliary_refines env lctx params As levels nparams args
          sourceName auxName sourceInfo hlookup hsize).bind fun _ Hdata =>
            Except.WF.pure ⟨Hdata, rfl⟩
      exact Hbuild.bind fun built Hbuilt => by
        rcases built with ⟨data, buildState⟩
        rcases Hbuilt with ⟨Hdata, hbuildState⟩
        simp only at Hdata hbuildState ⊢
        subst buildState
        simp only [modifyGet, getThe, StateT.modifyGet, StateT.get,
          bind, StateT.bind, ReaderT.bind, pure, StateT.pure, ReaderT.pure]
        split <;> rename_i heq <;>
          exact Except.WF.pure ⟨⟨auxName, nextIdx, data, Hfresh, Hdata,
            by simp [heq], rfl⟩⟩

theorem GeneratedAuxiliary.auxFVarsIn
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (HAs : LocalForallSelection lctx As)
    (hnparams : nparams ≤ args.size)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (fun fv => fv ∈ HAs.fvars ∨ P fv))
    (Hparams : ∀ param ∈ params, param.FVarsIn P)
    (Hstate : NestedAuxFVarsIn P state) :
    NestedAuxFVarsIn P out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, _Hfresh, Hbuilt, _hresult, hstate⟩
  rw [hstate]
  intro nested name hentry
  simp only [Array.mem_push] at hentry
  rcases hentry with hold | hnew
  · exact Hstate nested name hold
  · cases hnew
    exact Hbuilt.nestedFVarsIn HAs hnparams Hlevels Hargs Hparams

/-- Constructor closedness for every queue entry at or beyond a cursor.  Slots
strictly behind the cursor have already been lowered and need not be processed
again; newly appended auxiliary families must satisfy this invariant. -/
def PendingNewTypesClosed (cursor : Nat)
    (state : Lean4Lean.ElimNestedInductive.State) : Prop :=
  ∀ j, cursor ≤ j → (hj : j < state.newTypes.size) →
    InductiveConstructorsClosed state.newTypes[j]

theorem GeneratedAuxiliary.pendingNewTypesClosed
    (H : GeneratedAuxiliary env lctx params As targetName levels nparams args
      sourceName sourceInfo state out)
    (Henv : EnvironmentTypesClosed env)
    (Hclosing : NestedClosingContext lctx As ngen)
    (Hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (Hargs : ∀ arg ∈ args,
      arg.FVarsIn (· ∈ Hclosing.selection.fvars))
    (Hstate : PendingNewTypesClosed cursor state) :
    PendingNewTypesClosed cursor out.2 := by
  rcases H.generated with
    ⟨auxName, nextIdx, data, _Hfresh, Hbuilt, _hresult, hstate⟩
  rw [hstate]
  intro j hcursor hj
  simp only [Array.size_push] at hj
  by_cases hold : j < state.newTypes.size
  · simpa [Array.getElem_push, hold] using Hstate j hcursor hold
  · have heq : j = state.newTypes.size := by omega
    subst j
    simpa [Array.getElem_push] using
      Hbuilt.constructorsClosed Henv Hclosing Hlevels Hargs

/-- A successful cache lookup is backed by an actual previously recorded
auxiliary entry with the requested nested expression and returned name. -/
structure CachedNestedAux
    (nestedAux : Array (Expr × Name)) (nested : Expr) (auxName : Name) : Prop where
  entry : ∃ item ∈ nestedAux, (item.1 == nested) = true ∧ item.2 = auxName

theorem findCachedAux?_refines
    (nestedAux : Array (Expr × Name)) (nested : Expr) (auxName : Name)
    (hfind : Lean4Lean.ElimNestedInductive.findCachedAux?
      nestedAux nested = some auxName) :
    CachedNestedAux nestedAux nested auxName := by
  unfold Lean4Lean.ElimNestedInductive.findCachedAux? at hfind
  rcases Array.exists_of_findSome?_eq_some hfind with
    ⟨⟨found, foundName⟩, hmem, hentry⟩
  by_cases heq : (found == nested) = true
  · simp [heq] at hentry
    cases hentry
    exact ⟨⟨(found, auxName), hmem, heq, rfl⟩⟩
  · have heqFalse : (found == nested) = false := by
      cases h : found == nested <;> simp_all
    simp [heqFalse] at hentry

/-- Source constructors may not mention the private namespace used for
lowering-generated auxiliary families or projections. -/
def NoNestedAux (e : Expr) : Prop :=
  (e.find? fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false).isNone

/-- Source-side disjointness required by restoration: no constant occurring
in the source expression is already an auxiliary family or an auxiliary
constructor in the final lowered environment. -/
def RestoreSourceDisjoint
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment) :
    Expr → Prop
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => True
  | .const name _ =>
      result.aux2nested.find? name = none ∧
      result.getNestedIfAuxCtor env name = none
  | .app fn arg =>
      RestoreSourceDisjoint result env fn ∧
      RestoreSourceDisjoint result env arg
  | .lam _ dom body _ | .forallE _ dom body _ =>
      RestoreSourceDisjoint result env dom ∧
      RestoreSourceDisjoint result env body
  | .letE _ type value body _ =>
      RestoreSourceDisjoint result env type ∧
      RestoreSourceDisjoint result env value ∧
      RestoreSourceDisjoint result env body
  | .mdata _ body | .proj _ _ body =>
      RestoreSourceDisjoint result env body

/-- Every concrete constant occurring syntactically in an expression resolves
in the abstract environment used to translate it. Projections deliberately
follow the translated body only, matching `RestoreSourceDisjoint`. -/
def _root_.Lean.Expr.ConstantsDefined (env : VEnv) : Expr → Prop
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => True
  | .const name _ => env.constants name ≠ none
  | .app fn arg => fn.ConstantsDefined env ∧ arg.ConstantsDefined env
  | .lam _ dom body _ | .forallE _ dom body _ =>
      dom.ConstantsDefined env ∧ body.ConstantsDefined env
  | .letE _ type value body _ =>
      type.ConstantsDefined env ∧ value.ConstantsDefined env ∧
        body.ConstantsDefined env
  | .mdata _ body | .proj _ _ body => body.ConstantsDefined env

theorem _root_.Lean4Lean.TrExprS.constantsDefined
    (H : TrExprS env Us Δ source target) : source.ConstantsDefined env := by
  induction H <;> simp_all [Expr.ConstantsDefined]

/-- Any name recognized as an auxiliary constructor was absent from the
abstract environment in which the independent source expression was
translated. -/
def RestoreAuxConstructorsFresh
    (result : Lean4Lean.ElimNestedInductive.Result)
    (prodEnv : Environment) (sourceVEnv : VEnv) : Prop :=
  ∀ name nested auxFamily,
    result.getNestedIfAuxCtor prodEnv name = some (nested, auxFamily) →
    sourceVEnv.constants name = none

/-- Input production environments do not contain dangling constructor
metadata: every constructor's recorded owner is itself present. -/
def ConstructorOwnersPresent (env : Environment) : Prop :=
  ∀ name info, env.find? name = some (.ctorInfo info) →
    ∃ owner, env.find? info.induct = some (.inductInfo owner)

/-- Every auxiliary family recorded by lowering was fresh in the production
environment from which the inductive block was built. -/
def RestoreAuxFamiliesFresh
    (result : Lean4Lean.ElimNestedInductive.Result)
    (sourceEnv : Environment) : Prop :=
  ∀ name nested, result.aux2nested.find? name = some nested →
    sourceEnv.find? name = none

/-- Every name that the concrete restoration callback treats as an
auxiliary family or constructor lies in the namespace rejected by the source
syntax check.  This separates the name-generation argument from the
expression-level restoration inverse. -/
structure RestoreNamesReserved
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment) : Prop
    where
  family : ∀ name nested, result.aux2nested.find? name = some nested →
    (`_nested).isPrefixOf name = true
  constructor : ∀ name nested auxFamily,
    result.getNestedIfAuxCtor env name = some (nested, auxFamily) →
    (`_nested).isPrefixOf name = true

theorem NoNestedAux.findAny_false (H : NoNestedAux e) :
    e.findAny (fun
      | .const c _ => (`_nested).isPrefixOf c
      | .proj s _ _ => (`_nested).isPrefixOf s
      | _ => false) = false := by
  unfold NoNestedAux at H
  rw [← Expr.find?_isSome_eq_findAny]
  cases hfind : e.find? fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false <;> simp_all

theorem NoNestedAux.restoreSourceDisjoint
    (H : NoNestedAux e) (Hreserved : RestoreNamesReserved result env) :
    RestoreSourceDisjoint result env e := by
  let p : Expr → Bool := fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false
  have orFalse : ∀ a b : Bool, (a || b) = false →
      a = false ∧ b = false := by
    intro a b h
    cases a <;> cases b <;> simp_all
  have go : ∀ source, source.findAny p = false →
      RestoreSourceDisjoint result env source := by
    intro source Hfind
    induction source with
    | bvar | fvar | mvar | sort | lit => trivial
    | const name levels =>
      have hprefix : (`_nested).isPrefixOf name = false := by
        simpa [Expr.findAny, p] using Hfind
      constructor
      · cases hfamily : result.aux2nested.find? name with
        | none => rfl
        | some nested =>
          have := Hreserved.family name nested hfamily
          simp_all
      · cases hctor : result.getNestedIfAuxCtor env name with
        | none => rfl
        | some pair =>
          rcases pair with ⟨nested, auxFamily⟩
          have := Hreserved.constructor name nested auxFamily hctor
          simp_all
    | app fn arg ihFn ihArg =>
      simp only [Expr.findAny, p, Bool.false_or] at Hfind
      rcases orFalse _ _ Hfind with ⟨hfn, harg⟩
      exact ⟨ihFn hfn, ihArg harg⟩
    | lam name dom body bi ihDom ihBody =>
      simp only [Expr.findAny, p, Bool.false_or] at Hfind
      rcases orFalse _ _ Hfind with ⟨hdom, hbody⟩
      exact ⟨ihDom hdom, ihBody hbody⟩
    | forallE name dom body bi ihDom ihBody =>
      simp only [Expr.findAny, p, Bool.false_or] at Hfind
      rcases orFalse _ _ Hfind with ⟨hdom, hbody⟩
      exact ⟨ihDom hdom, ihBody hbody⟩
    | letE name type value body nondep ihType ihValue ihBody =>
      simp only [Expr.findAny, p, Bool.false_or] at Hfind
      rcases orFalse _ _ Hfind with ⟨htypeValue, hbody⟩
      rcases orFalse _ _ htypeValue with ⟨htype, hvalue⟩
      exact ⟨ihType htype, ihValue hvalue, ihBody hbody⟩
    | mdata data body ihBody =>
      simpa only [RestoreSourceDisjoint] using ihBody Hfind
    | proj name idx body ihBody =>
      simp only [Expr.findAny, p] at Hfind
      rcases orFalse _ _ Hfind with ⟨hprefix, hbody⟩
      simpa only [RestoreSourceDisjoint] using ihBody hbody
  apply go e
  simpa only [p] using H.findAny_false

/-- Derive semantic restoration disjointness without assuming generated
constructor names live below `_nested`. Family collisions are rejected by
the source syntax namespace check; constructor collisions contradict source
translation and freshness of the lowered block. -/
theorem NoNestedAux.restoreSourceDisjointOfFresh
    (H : NoNestedAux e)
    (Hdefined : e.ConstantsDefined sourceVEnv)
    (Hfamilies : ∀ name nested,
      result.aux2nested.find? name = some nested →
      (`_nested).isPrefixOf name = true)
    (Hconstructors : RestoreAuxConstructorsFresh result prodEnv sourceVEnv) :
    RestoreSourceDisjoint result prodEnv e := by
  let p : Expr → Bool := fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false
  have orFalse : ∀ a b : Bool, (a || b) = false →
      a = false ∧ b = false := by
    intro a b h
    cases a <;> cases b <;> simp_all
  have go : ∀ source, source.findAny p = false →
      source.ConstantsDefined sourceVEnv →
      RestoreSourceDisjoint result prodEnv source := by
    intro source
    induction source with
    | bvar | fvar | mvar | sort | lit =>
      intro _Hfind _HsourceDefined
      trivial
    | const name levels =>
      intro Hfind HsourceDefined
      have hprefix : (`_nested).isPrefixOf name = false := by
        simpa [Expr.findAny, p] using Hfind
      constructor
      · cases hfamily : result.aux2nested.find? name with
        | none => rfl
        | some nested =>
          have hreserved := Hfamilies name nested hfamily
          simp_all
      · cases hctor : result.getNestedIfAuxCtor prodEnv name with
        | none => rfl
        | some pair =>
          rcases pair with ⟨nested, auxFamily⟩
          have hfresh := Hconstructors name nested auxFamily hctor
          exact False.elim (HsourceDefined hfresh)
    | app fn arg ihFn ihArg =>
      intro Hfind HsourceDefined
      simp only [Expr.findAny, p, Bool.false_or] at Hfind
      rcases orFalse _ _ Hfind with ⟨hfn, harg⟩
      exact ⟨ihFn hfn HsourceDefined.1, ihArg harg HsourceDefined.2⟩
    | lam name dom body bi ihDom ihBody
        | forallE name dom body bi ihDom ihBody =>
      intro Hfind HsourceDefined
      simp only [Expr.findAny, p, Bool.false_or] at Hfind
      rcases orFalse _ _ Hfind with ⟨hdom, hbody⟩
      exact ⟨ihDom hdom HsourceDefined.1,
        ihBody hbody HsourceDefined.2⟩
    | letE name type value body nondep ihType ihValue ihBody =>
      intro Hfind HsourceDefined
      simp only [Expr.findAny, p, Bool.false_or] at Hfind
      rcases orFalse _ _ Hfind with ⟨htypeValue, hbody⟩
      rcases orFalse _ _ htypeValue with ⟨htype, hvalue⟩
      exact ⟨ihType htype HsourceDefined.1,
        ihValue hvalue HsourceDefined.2.1,
        ihBody hbody HsourceDefined.2.2⟩
    | mdata data body ihBody =>
      intro Hfind HsourceDefined
      simpa only [RestoreSourceDisjoint] using
        ihBody Hfind HsourceDefined
    | proj structName idx body ihBody =>
      intro Hfind HsourceDefined
      simp only [Expr.findAny, p] at Hfind
      exact ihBody (orFalse _ _ Hfind).2 HsourceDefined
  apply go e
  · simpa only [p] using H.findAny_false
  · exact Hdefined

theorem RestoreSourceDisjoint.getAppFn
    (H : RestoreSourceDisjoint result env e)
    (hhead : e.getAppFn = .const name levels) :
    result.aux2nested.find? name = none ∧
      result.getNestedIfAuxCtor env name = none := by
  induction e with
  | const sourceName sourceLevels =>
    change (Expr.const sourceName sourceLevels) = .const name levels at hhead
    cases hhead
    exact H
  | app fn arg ihFn ihArg =>
    exact ihFn H.1 (by simpa [Expr.getAppFn] using hhead)
  | bvar | fvar | mvar | sort | lam | forallE | letE | lit | mdata | proj =>
    simp [Expr.getAppFn] at hhead

theorem RestoreSourceDisjoint.instantiate1'_fvar
    (H : RestoreSourceDisjoint result env e) (fv : FVarId) (k : Nat) :
    RestoreSourceDisjoint result env (e.instantiate1' (.fvar fv) k) := by
  induction e generalizing k with
  | bvar i =>
    by_cases hlt : i < k
    · simp [Expr.instantiate1', hlt, RestoreSourceDisjoint]
    · by_cases heq : i = k
      · simp only [Expr.instantiate1', hlt, heq, ↓reduceIte]
        simp only [Nat.lt_irrefl, ↓reduceIte]
        change RestoreSourceDisjoint result env (.fvar fv)
        trivial
      · simp [Expr.instantiate1', hlt, heq, RestoreSourceDisjoint]
  | fvar | mvar | sort | const | lit =>
    simpa [Expr.instantiate1', RestoreSourceDisjoint] using H
  | app fn arg ihFn ihArg =>
    simp only [Expr.instantiate1', RestoreSourceDisjoint] at H ⊢
    exact ⟨ihFn H.1 k, ihArg H.2 k⟩
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.instantiate1', RestoreSourceDisjoint] at H ⊢
    exact ⟨ihDom H.1 k, ihBody H.2 (k + 1)⟩
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.instantiate1', RestoreSourceDisjoint] at H ⊢
    exact ⟨ihDom H.1 k, ihBody H.2 (k + 1)⟩
  | letE name type value body nondep ihType ihValue ihBody =>
    simp only [Expr.instantiate1', RestoreSourceDisjoint] at H ⊢
    exact ⟨ihType H.1 k, ihValue H.2.1 k, ihBody H.2.2 (k + 1)⟩
  | mdata data body ihBody =>
    simpa only [Expr.instantiate1', RestoreSourceDisjoint] using ihBody H k
  | proj name idx body ihBody =>
    simpa only [Expr.instantiate1', RestoreSourceDisjoint] using ihBody H k

theorem RestoreSourceDisjoint.instantiate1_fvar
    (H : RestoreSourceDisjoint result env e) (fv : FVarId) :
    RestoreSourceDisjoint result env (e.instantiate1 (.fvar fv)) := by
  rw [Expr.instantiate1_eq]
  exact H.instantiate1'_fvar fv 0

theorem NestedParamOpening.tailRestoreSourceDisjoint
    (Hopen : NestedParamOpening lctx params source n outLctx tail outParams)
    (Hsource : RestoreSourceDisjoint result env source) :
    RestoreSourceDisjoint result env tail := by
  induction Hopen with
  | done => exact Hsource
  | step Hnext ih =>
    apply ih
    exact Hsource.2.instantiate1_fvar _

theorem checkNoNestedAux_refines (name : Name) (e : Expr) :
    (Lean4Lean.checkNoNestedAux name e).WF fun _ => NoNestedAux e := by
  unfold Lean4Lean.checkNoNestedAux NoNestedAux
  cases hfind : e.find? fun
    | .const c _ => (`_nested).isPrefixOf c
    | .proj s _ _ => (`_nested).isPrefixOf s
    | _ => false
  · exact Except.WF.pure (by simp [hfind])
  · exact Except.WF.throw

/-- Source constructor syntax retained before nested lowering rewrites its type. -/
structure SourceConstructorSyntax (ctor : Constructor) : Prop where
  closed : ctor.type.FVarsIn fun _ => False
  noNestedAux : NoNestedAux ctor.type

/-- Pointwise source-syntax certificates for a constructor list. -/
inductive SourceConstructorSyntaxes : List Constructor → Prop where
  | nil : SourceConstructorSyntaxes []
  | cons : SourceConstructorSyntax ctor → SourceConstructorSyntaxes ctors →
      SourceConstructorSyntaxes (ctor :: ctors)

/-- Source inductive syntax retained before nested lowering rewrites the declaration. -/
structure SourceInductiveSyntax (type : InductiveType) : Prop where
  closed : type.type.FVarsIn fun _ => False
  constructors : SourceConstructorSyntaxes type.ctors

/-- The source-level closure and reserved-prefix checks for a mutual block. -/
inductive SourceSyntaxChecks : List InductiveType → Prop where
  | nil : SourceSyntaxChecks []
  | cons : SourceInductiveSyntax type → SourceSyntaxChecks types →
      SourceSyntaxChecks (type :: types)

theorem SourceConstructorSyntaxes.getElem
    (H : SourceConstructorSyntaxes ctors) (i : Nat)
    (hi : i < ctors.length) : SourceConstructorSyntax ctors[i] := by
  induction H generalizing i with
  | nil => simp at hi
  | cons Hhead Htail ih =>
    cases i with
    | zero => exact Hhead
    | succ i =>
      apply ih i

theorem SourceConstructorSyntaxes.of_mem
    (H : SourceConstructorSyntaxes ctors) (hctor : ctor ∈ ctors) :
    SourceConstructorSyntax ctor := by
  induction H with
  | nil => simp at hctor
  | cons Hhead Htail ih =>
    rcases List.mem_cons.mp hctor with rfl | htail
    · exact Hhead
    · exact ih htail

theorem SourceSyntaxChecks.getElem
    (H : SourceSyntaxChecks types) (i : Nat)
    (hi : i < types.length) : SourceInductiveSyntax types[i] := by
  induction H generalizing i with
  | nil => simp at hi
  | cons Hhead Htail ih =>
    cases i with
    | zero => exact Hhead
    | succ i =>
      apply ih i

theorem SourceConstructorSyntaxes.closed
    (H : SourceConstructorSyntaxes ctors) :
    ∀ ctor ∈ ctors, ctor.type.FVarsIn fun _ => False := by
  induction H with
  | nil => simp
  | cons Hhead Htail ih =>
    intro ctor hctor
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | htail
    · exact Hhead.closed
    · exact ih ctor htail

theorem SourceSyntaxChecks.typeClosed
    (H : SourceSyntaxChecks types) (hmem : type ∈ types) :
    type.type.FVarsIn fun _ => False := by
  induction H with
  | nil => simp at hmem
  | cons Hhead Htail ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact Hhead.closed
    · exact ih htail

theorem SourceSyntaxChecks.constructorsClosed
    (H : SourceSyntaxChecks types) (hmem : type ∈ types) :
    InductiveConstructorsClosed type := by
  induction H with
  | nil => simp at hmem
  | cons Hhead Htail ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact Hhead.constructors.closed
    · exact ih htail

private theorem checkConstructorSources_refines
    (env : Environment) (ctors : List Constructor) :
    (Lean4Lean.checkConstructorSources env ctors).WF fun _ =>
      SourceConstructorSyntaxes ctors := by
  induction ctors with
  | nil => exact Except.WF.pure .nil
  | cons ctor ctors ih =>
    rw [Lean4Lean.checkConstructorSources]
    have Hclosed : (env.checkNoMVarNoFVar ctor.name ctor.type).WF
        fun _ => ctor.type.FVarsIn fun _ => False := by
      intro _ h
      exact checkNoMVarNoFVar.closed (env := env) (name := ctor.name) h
    exact Hclosed.bind fun _ hclosed =>
      (checkNoNestedAux_refines ctor.name ctor.type).bind fun _ hreserved =>
        ih.mono fun _ htail =>
          .cons ⟨hclosed, hreserved⟩ htail

theorem checkInductiveSources_refines
    (env : Environment) (types : List InductiveType) :
    (Lean4Lean.checkInductiveSources env types).WF fun _ =>
      SourceSyntaxChecks types := by
  induction types with
  | nil => exact Except.WF.pure .nil
  | cons type types ih =>
    rw [Lean4Lean.checkInductiveSources]
    have Hclosed : (env.checkNoMVarNoFVar type.name type.type).WF
        fun _ => type.type.FVarsIn fun _ => False := by
      intro _ h
      exact checkNoMVarNoFVar.closed (env := env) (name := type.name) h
    exact Hclosed.bind fun _ hclosed =>
      (checkConstructorSources_refines env type.ctors).bind fun _ hctors =>
        ih.mono fun _ htail =>
          .cons ⟨hclosed, hctors⟩ htail

/-- Independent lookup contract used when restoring a generated auxiliary
constructor to its source constructor family. -/
structure AuxiliaryConstructorLookup
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (ctor : Name) (nested : Expr) (auxFamily : Name) : Prop where
  exists_info : ∃ info : ConstructorVal,
    env.find? ctor = some (.ctorInfo info) ∧
    auxFamily = info.induct ∧
    result.aux2nested.find? info.induct = some nested

theorem getNestedIfAuxCtor_refines
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (ctor : Name) :
    ∀ nested auxFamily,
      result.getNestedIfAuxCtor env ctor = some (nested, auxFamily) →
      AuxiliaryConstructorLookup result env ctor nested auxFamily := by
  intro nested auxFamily hout
  unfold Lean4Lean.ElimNestedInductive.Result.getNestedIfAuxCtor at hout
  cases hfound : env.find? ctor with
  | none => simp [hfound] at hout
  | some info =>
    cases info with
    | ctorInfo ctorInfo =>
      simp only [hfound] at hout
      cases hnested : result.aux2nested.find? ctorInfo.induct with
      | none => simp [hnested] at hout
      | some restored =>
        have hp : (restored, ctorInfo.induct) = (nested, auxFamily) := by
          simpa [hnested] using hout
        cases hp
        exact ⟨⟨ctorInfo, hfound, rfl, hnested⟩⟩
    | _ => simp_all

theorem restoreCtorName_eq
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (ctor auxFamily sourceFamily : Name)
    (nested : Expr) (levels : List Level)
    (hlookup : result.getNestedIfAuxCtor env ctor =
      some (nested, auxFamily))
    (hhead : nested.getAppFn = .const sourceFamily levels) :
    result.restoreCtorName env ctor =
      ctor.replacePrefix auxFamily sourceFamily := by
  unfold Lean4Lean.ElimNestedInductive.Result.restoreCtorName
  simp [hlookup, hhead]
  rfl

theorem restoreNestedNode_recursor
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (name restored : Name) (levels : List Level)
    (hrec : auxRec.find? name = some restored) :
    result.restoreNestedNode env As auxRec (.const name levels) =
      some (.const restored levels) := by
  simp [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode, hrec]

theorem restoreNestedNode_family
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (t nested : Expr) (family : Name) (levels : List Level)
    (happ : t.isApp = true)
    (hhead : t.getAppFn = .const family levels)
    (hfamily : result.aux2nested.find? family = some nested)
    (harity : result.nparams ≤ t.getAppArgs.size) :
    result.restoreNestedNode env As auxRec t = some
      (mkAppRange ((nested.abstract result.params).instantiateRev As)
        result.nparams t.getAppArgs.size t.getAppArgs) := by
  cases t with
  | app fn arg =>
    simp only [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode]
    simp [hhead, hfamily, harity]
  | bvar | fvar | mvar | sort | const | lam | forallE | letE | lit | mdata
      | proj => cases happ

/-- Family restoration including the zero-argument case, where the lowered
family is represented by a bare constant. In that case the production code
consults the auxiliary-recursor map first, so disjointness is an explicit
premise. -/
theorem restoreNestedNode_family_general
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (t nested : Expr) (family : Name) (levels : List Level)
    (hhead : t.getAppFn = .const family levels)
    (hrec : auxRec.find? family = none)
    (hfamily : result.aux2nested.find? family = some nested)
    (harity : result.nparams ≤ t.getAppArgs.size) :
    result.restoreNestedNode env As auxRec t = some
      (mkAppRange ((nested.abstract result.params).instantiateRev As)
        result.nparams t.getAppArgs.size t.getAppArgs) := by
  cases t with
  | const name constLevels =>
    change (.const name constLevels : Expr) = .const family levels at hhead
    cases hhead
    have hargs : (.const family levels : Expr).getAppArgs = #[] := rfl
    rw [hargs] at harity ⊢
    have hnparams : result.nparams = 0 := by simpa using harity
    unfold Lean4Lean.ElimNestedInductive.Result.restoreNestedNode
    simp only [hrec]
    have hfn : (.const family levels : Expr).getAppFn =
        .const family levels := rfl
    rw [hfn]
    simp only
    rw [hfamily, hargs, hnparams]
    rfl
  | app fn arg =>
    exact restoreNestedNode_family result env As auxRec (.app fn arg) nested
      family levels rfl hhead hfamily harity
  | bvar i => cases hhead
  | fvar i => cases hhead
  | mvar i => cases hhead
  | sort level => cases hhead
  | lam name dom body bi => cases hhead
  | forallE name dom body bi => cases hhead
  | letE name type value body nondep => cases hhead
  | lit literal => cases hhead
  | mdata data body => cases hhead
  | proj name idx body => cases hhead

/-- Exact-parameter specialization of family restoration.  With no trailing
arguments, the replacement node is precisely the reopened cached witness. -/
theorem restoreNestedNode_family_exactParams
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (t nested : Expr) (family : Name) (levels : List Level)
    (hhead : t.getAppFn = .const family levels)
    (hrec : auxRec.find? family = none)
    (hfamily : result.aux2nested.find? family = some nested)
    (hargs : t.getAppArgs.size = result.nparams) :
    result.restoreNestedNode env As auxRec t = some
      ((nested.abstract result.params).instantiateRev As) := by
  have Hgeneral := restoreNestedNode_family_general result env As auxRec t
    nested family levels hhead hrec hfamily (by omega)
  rw [Hgeneral]
  rw [Expr.mkAppRange_to_end _ _ _ (by omega)]
  have hdrop : t.getAppArgs.toList.drop result.nparams = [] := by
    apply List.drop_eq_nil_iff.mpr
    simpa [hargs]
  simp [hdrop]

theorem restoreNestedNode_constructor
    (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (auxRec : NameMap Name)
    (t nested : Expr) (ctorName auxFamily sourceFamily : Name)
    (headLevels sourceLevels : List Level)
    (happ : t.isApp = true)
    (hhead : t.getAppFn = .const ctorName headLevels)
    (hnotFamily : result.aux2nested.find? ctorName = none)
    (hlookup : result.getNestedIfAuxCtor env ctorName =
      some (nested, auxFamily))
    (harity : result.nparams ≤ t.getAppArgs.size)
    (hrestoredHead :
      ((nested.abstract result.params).instantiateRev As).getAppFn =
        .const sourceFamily sourceLevels) :
    result.restoreNestedNode env As auxRec t = some
      (mkAppRange
        (mkAppN (.const (ctorName.replacePrefix auxFamily sourceFamily)
          sourceLevels)
          ((nested.abstract result.params).instantiateRev As).getAppArgs)
        result.nparams t.getAppArgs.size t.getAppArgs) := by
  cases t with
  | app fn arg =>
    simp only [Lean4Lean.ElimNestedInductive.Result.restoreNestedNode]
    simp [hhead, hnotFamily, hlookup, harity, Expr.withApp_eq]
    simp only [Expr.instantiateRev_eq, Expr.instantiate_eq,
      Array.toList_reverse] at hrestoredHead
    rw [hrestoredHead]
  | bvar | fvar | mvar | sort | const | lam | forallE | letE | lit | mdata
      | proj => cases happ


end VerifyInductive
end Lean4Lean
