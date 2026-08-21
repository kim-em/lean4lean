import Lean4Lean.Verify.Inductive.Recursor.Bindings

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Declarative constructor-introduction certificate used by the recursor
second pass.  It deliberately records the exact terminal source expression
and exact generated constructor application: constructor checking must
eventually supply this package, rather than asking recursor generation to
trust a second executable classification. -/
structure RecursorConstructorApplicationAt
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (ctor : Constructor)
    (terminal : Expr) (allFields : Array Expr)
    (terminalTarget : VExpr) : Type where
  ownerIdx : Nat
  owner_valid : AddInductive.isValidIndApp? stats terminal = some ownerIdx
  terminal_type : R.venv.IsType recLparams.length
    R.mlctx.vlctx.toCtx terminalTarget
  introTarget : VExpr
  intro : TrExprS R.venv recLparams R.mlctx.vlctx
    (mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) allFields)
    introTarget
  typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    introTarget terminalTarget

/-- Semantic translations of an executable origin-type array under the
recursor universe list.  This is the universe-parametric counterpart of
`TranslatedOriginTypes`, used for major and motive rows after large
elimination has made `ContextWF` unavailable. -/
structure RecursorTranslatedOriginTypes
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (origins : Array Expr) where
  targets : List VExpr
  translated : List.Forall₂
    (TrExprS R.venv recLparams R.mlctx.vlctx) origins.toList targets
  isType : ∀ target ∈ targets,
    R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx target

/-- Select one translated origin type without exposing the internal target
list representation. -/
theorem RecursorTranslatedOriginTypes.entryAt
    (H : RecursorTranslatedOriginTypes (recLparams := recLparams) R origins)
    (i : Nat) (hi : i < origins.size) :
    ∃ target,
      TrExprS R.venv recLparams R.mlctx.vlctx origins[i] target ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx target := by
  have hlength : origins.toList.length = H.targets.length :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.translated
  have hitargets : i < H.targets.length := by
    simpa using hlength ▸ (by simpa using hi)
  let target := H.targets[i]
  have htr := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    H.translated i (by simpa using hi) hitargets
  refine ⟨target, ?_, H.isType target (List.getElem_mem hitargets)⟩
  simpa [target] using htr

def RecursorTranslatedOriginTypes.empty
    (R : RecursorContextWF c recLparams) :
    RecursorTranslatedOriginTypes R #[] where
  targets := []
  translated := .nil
  isType _ h := by simp at h

/-- Weaken an entire translated-origin row along an arbitrary certified
recursor-context extension.  Constructor fields, generated hypotheses, and
minor premises are introduced in separate traversals, so their composite
extension is more useful here than a consecutive-suffix specialization. -/
def RecursorTranslatedOriginTypes.mono
    (H : RecursorTranslatedOriginTypes Rroot origins)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    RecursorTranslatedOriginTypes Rcurrent origins where
  targets := H.targets.map fun target =>
    target.lift' (Hext.shift.consN 0)
  translated := by
    apply checkPositivityStep.forall₂_map_right H.translated
    intro source target Hsource
    exact Hext.weakTrExprS Hsource
  isType := by
    intro target htarget
    rcases List.mem_map.mp htarget with ⟨oldTarget, hold, rfl⟩
    exact Hext.weakIsType (H.isType oldTarget hold)

/-- Weaken an existing origin-type row through one newly checked recursor
local without appending a new row entry. -/
def RecursorTranslatedOriginTypes.withLocalDecl
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {origins : Array Expr}
    {ty : Expr} {ty' : VExpr} {name : Name} {bi : BinderInfo}
    (H : RecursorTranslatedOriginTypes R origins)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty') :
    let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
      (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty
    RecursorTranslatedOriginTypes R' origins := by
  dsimp only
  let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
    (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  exact {
    targets := H.targets.map fun target => target.liftN 1 0
    translated := by
      apply checkPositivityStep.forall₂_map_right H.translated
      intro source target Hsource
      exact Hsource.weakFV R.checking.tr.wf.ordered W R'.mlctx_wf.tr.wf
    isType := by
      intro target htarget
      rcases List.mem_map.mp htarget with ⟨oldTarget, hold, rfl⟩
      exact (H.isType oldTarget hold).weakN R.checking.tr.wf.ordered W.toCtx }

/-- Append a newly checked origin type while weakening all older entries
through its declaration. -/
def RecursorTranslatedOriginTypes.push
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {origins : Array Expr}
    {ty : Expr} {ty' : VExpr} {name : Name} {bi : BinderInfo}
    (H : RecursorTranslatedOriginTypes R origins)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty') :
    let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
      (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty
    RecursorTranslatedOriginTypes R' (origins.push ty) := by
  dsimp only
  let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
    (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  let liftedTargets := H.targets.map fun target => target.liftN 1 0
  exact {
    targets := liftedTargets ++ [ty'.liftN 1 0]
    translated := by
      rw [Array.toList_push]
      apply checkPositivityStep.forall₂_append
      · apply checkPositivityStep.forall₂_map_right H.translated
        intro source target Hsource
        exact Hsource.weakFV R.checking.tr.wf.ordered W R'.mlctx_wf.tr.wf
      · exact .cons
          (htr.weakFV R.checking.tr.wf.ordered W R'.mlctx_wf.tr.wf) .nil
    isType := by
      intro target htarget
      simp only [liftedTargets, List.mem_append, List.mem_map,
        List.mem_singleton] at htarget
      rcases htarget with ⟨oldTarget, hold, rfl⟩ | rfl
      · exact (H.isType oldTarget hold).weakN
          R.checking.tr.wf.ordered W.toCtx
      · exact hty.weakN R.checking.tr.wf.ordered W.toCtx }

/-- Weaken an origin-type row across the exact consecutive index suffix
opened since `Rroot`. -/
def RecursorTranslatedOriginTypes.weakenRecent
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {indices : Array Expr}
    (H : RecursorTranslatedOriginTypes Rroot origins)
    (Hrecent : RecursorRecentBoundFVarArray Rroot R indices) :
    RecursorTranslatedOriginTypes R origins := by
  let W := R.onlyLams.dropN_fvlift indices.size Hrecent.size_le
  refine {
    targets := H.targets.map fun target => target.liftN indices.size 0
    translated := ?_
    isType := ?_ }
  · apply checkPositivityStep.forall₂_map_right H.translated
    intro source target Hsource
    have Hsource' : TrExprS R.venv recLparams
        (R.mlctx.dropN indices.size Hrecent.size_le).vlctx source target := by
      simpa only [Hrecent.venv_eq, Hrecent.drop_eq] using Hsource
    exact Hsource'.weakFV R.checking.tr.wf.ordered W R.mlctx_wf.tr.wf
  · intro target htarget
    rcases List.mem_map.mp htarget with ⟨oldTarget, hold, rfl⟩
    have htype : R.venv.IsType recLparams.length
        (R.mlctx.dropN indices.size Hrecent.size_le).vlctx.toCtx
        oldTarget := by
      simpa only [Hrecent.venv_eq, Hrecent.drop_eq] using H.isType _ hold
    exact htype.weakN R.checking.tr.wf.ordered W.toCtx

/-- Row-wise semantic translations for the per-family origin arrays retained
by `RecInfoTypeOrigins`. -/
structure RecursorTranslatedOriginTypeRows
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (origins : Array (Array Expr)) where
  rows : ∀ i (hi : i < origins.size),
    RecursorTranslatedOriginTypes R origins[i]

def RecursorTranslatedOriginTypeRows.empty
    (R : RecursorContextWF c recLparams) :
    RecursorTranslatedOriginTypeRows R #[] where
  rows i hi := by simp at hi

/-- Row-wise form of `RecursorTranslatedOriginTypes.mono`. -/
def RecursorTranslatedOriginTypeRows.mono
    (H : RecursorTranslatedOriginTypeRows Rroot origins)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    RecursorTranslatedOriginTypeRows Rcurrent origins where
  rows i hi := (H.rows i hi).mono Hext

def RecursorTranslatedOriginTypeRows.rowAt
    (H : RecursorTranslatedOriginTypeRows R origins)
    (i : Nat) (hi : i < origins.size) :
    RecursorTranslatedOriginTypes R origins[i] :=
  H.rows i hi

/-- Weaken every retained origin row through one semantically checked local. -/
def RecursorTranslatedOriginTypeRows.withLocalDecl
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {origins : Array (Array Expr)}
    {ty : Expr} {ty' : VExpr} {name : Name} {bi : BinderInfo}
    (H : RecursorTranslatedOriginTypeRows R origins)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty') :
    let R' := R.withLocalDecl (c := c) (recLparams := recLparams)
      (ty := ty) (ty' := ty') (name := name) (bi := bi) htr hty
    RecursorTranslatedOriginTypeRows R' origins := by
  dsimp only
  exact {
    rows := fun i hi => (H.rows i hi).withLocalDecl htr hty }

/-- Weaken every retained row across the consecutive index suffix introduced
since the root recursor context. -/
def RecursorTranslatedOriginTypeRows.weakenRecent
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {indices : Array Expr}
    (H : RecursorTranslatedOriginTypeRows Rroot origins)
    (Hrecent : RecursorRecentBoundFVarArray Rroot R indices) :
    RecursorTranslatedOriginTypeRows R origins where
  rows i hi := (H.rows i hi).weakenRecent Hrecent

/-- Append one fully translated family row without changing the ambient
recursor context. -/
def RecursorTranslatedOriginTypeRows.push
    (H : RecursorTranslatedOriginTypeRows R origins)
    (Hrow : RecursorTranslatedOriginTypes R row) :
    RecursorTranslatedOriginTypeRows R (origins.push row) where
  rows i hi := by
    by_cases hold : i < origins.size
    · simpa only [Array.getElem_push_lt hold] using H.rows i hold
    · have hieq : i = origins.size := by
        simp only [Array.size_push] at hi
        omega
      subst i
      simpa using Hrow

def FreshBoundFVarArray.weaken
    (H : FreshBoundFVarArray root c xs)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    FreshBoundFVarArray root { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } xs where
  toBoundFVarArray := H.toBoundFVarArray.weaken name ty bi
  nodup := H.nodup
  fresh := H.fresh

def BoundFVarArray.get
    (H : BoundFVarArray c xs) (i : Nat) (hi : i < xs.size) :
    BoundFVarArray c #[xs[i]] := by
  rcases H with ⟨fvars, rfl, members⟩
  let fv := fvars[i]'(by simpa using hi)
  refine {
    fvars := [fv]
    expressions := ?_
    members := ?_
  }
  · simp [fv]
  · intro fv' hfv'
    simp only [List.mem_singleton] at hfv'
    subst fv'
    exact members fv (List.getElem_mem (by simpa using hi))

/-- Every indexed entry of a bound-fvar array is literally a free variable
present in the retained executable local context. -/
theorem BoundFVarArray.get_eq_fvar
    (H : BoundFVarArray c xs) (i : Nat) (hi : i < xs.size) :
    ∃ fv, xs[i] = .fvar fv ∧ fv ∈ c.lctx.fvars := by
  rcases H with ⟨fvars, rfl, members⟩
  have hifvars : i < fvars.length := by simpa using hi
  refine ⟨fvars[i], ?_, members fvars[i] (List.getElem_mem hifvars)⟩
  simp

theorem BoundFVarArray.avoidsConsts
    (H : BoundFVarArray c xs) (e : Expr) (he : e ∈ xs) :
    e.AvoidsConsts names := by
  rcases Array.mem_iff_getElem.mp he with ⟨i, hi, heq⟩
  rcases H.get_eq_fvar i hi with ⟨fv, hfv, _⟩
  rw [← heq, hfv]
  exact Lean.Expr.AvoidsConsts.fvar fv

/-- The retained free variable at one array position together with the exact
ordinary local declaration which introduced it. -/
structure BoundFVarDeclarationAt
    (c : AddInductive.Context) (xs : Array Expr) (i : Nat) where
  inBounds : i < xs.size
  fvar : FVarId
  expression : xs[i] = .fvar fvar
  member : fvar ∈ c.lctx.fvars
  index : Nat
  userName : Name
  type : Expr
  binderInfo : BinderInfo
  kind : LocalDeclKind
  declaration : c.lctx.find? fvar = some
    (.cdecl index fvar userName type binderInfo kind)

theorem BoundFVarArray.declarationAt
    (H : BoundFVarArray c xs) (Hc : BindingContextWF c)
    (i : Nat) (hi : i < xs.size) :
    Nonempty (BoundFVarDeclarationAt c xs i) := by
  rcases H.get_eq_fvar i hi with ⟨fv, hexpression, hfv⟩
  rcases Hc.findCDecl fv hfv with
    ⟨index, userName, type, binderInfo, kind, hdeclaration⟩
  exact ⟨{
    inBounds := hi
    fvar := fv
    expression := hexpression
    member := hfv
    index := index
    userName := userName
    type := type
    binderInfo := binderInfo
    kind := kind
    declaration := hdeclaration }⟩

/-- A retained array position has only one local declaration type. -/
theorem BoundFVarDeclarationAt.type_unique
    (D₁ D₂ : BoundFVarDeclarationAt c xs i) : D₁.type = D₂.type := by
  have hfvar : D₁.fvar = D₂.fvar := by
    apply Expr.fvar.inj
    exact D₁.expression.symm.trans D₂.expression
  have hfind : c.lctx.find? D₁.fvar = c.lctx.find? D₂.fvar :=
    congrArg c.lctx.find? hfvar
  have hdeclaration := Option.some.inj
    (D₁.declaration.symm.trans (hfind.trans D₂.declaration))
  exact congrArg LocalDecl.type hdeclaration

/-- Recover the semantic translation of a retained concrete declaration
type from the verified recursor local context containing it.  This is the
direct bridge from first-pass declaration provenance to the abstract local
context; no re-analysis of the declaration expression is involved. -/
theorem RecursorContextWF.translatedDeclarationType
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (D : BoundFVarDeclarationAt c xs i) :
    ∃ target,
      TrExprS R.venv recLparams R.mlctx.vlctx D.type target := by
  let decl : LocalDecl := .cdecl D.index D.fvar D.userName D.type
    D.binderInfo D.kind
  have hfind : c.lctx.find? D.fvar = some decl := by
    simpa [decl] using D.declaration
  have hfind' : R.mlctx.lctx.find? D.fvar = some decl := by
    rw [R.lctx_eq]
    exact hfind
  have hlist := hfind'
  rw [R.mlctx_wf.tr.1.find?_eq_find?_toList] at hlist
  have hmem : decl ∈ R.mlctx.lctx.toList :=
    List.mem_of_find?_eq_some hlist
  rcases R.mlctx_wf.tr.find?_of_mem R.checking.tr.wf hmem with
    ⟨_value, target, _hlookup, _hvalueBelow, _htypeBelow,
      _hvalue, Htype⟩
  refine ⟨target, ?_⟩
  change TrExprS R.venv recLparams R.mlctx.vlctx D.type target at Htype
  exact Htype

/-- Exact declaration provenance survives a verified binding-context
extension.  In particular the declaration type cannot silently change while
the retained free variable is threaded through later `mkRecInfos` passes. -/
def BoundFVarDeclarationAt.mono
    (D : BoundFVarDeclarationAt c xs i) (H : BindingContextLE c c') :
    BoundFVarDeclarationAt c' xs i where
  inBounds := D.inBounds
  fvar := D.fvar
  expression := D.expression
  member := H D.member
  index := D.index
  userName := D.userName
  type := D.type
  binderInfo := D.binderInfo
  kind := D.kind
  declaration := by
    rw [H.declarations D.fvar D.member]
    exact D.declaration

def BoundFVarDeclarationAt.pushArray
    (D : BoundFVarDeclarationAt c xs i) (value : Expr) :
    BoundFVarDeclarationAt c (xs.push value) i where
  inBounds := by
    simp only [Array.size_push]
    have := D.inBounds
    omega
  fvar := D.fvar
  expression := by
    rw [Array.getElem_push_lt D.inBounds]
    exact D.expression
  member := D.member
  index := D.index
  userName := D.userName
  type := D.type
  binderInfo := D.binderInfo
  kind := D.kind
  declaration := D.declaration

/-- Parallel origin types for a retained free-variable array.  Unlike plain
`BoundFVarArray`, this certificate remembers the exact type used at each
`withLocalDecl`, and the strengthened context-extension relation makes that
fact stable in all later contexts. -/
structure BoundFVarTypeOrigins (c : AddInductive.Context)
    (xs origins : Array Expr) where
  bound : BoundFVarArray c xs
  size_eq : origins.size = xs.size
  declaration : ∀ i (hi : i < xs.size),
    ∃ D : BoundFVarDeclarationAt c xs i, D.type = origins[i]!

/-- Semantic translations of the exact declaration-origin expressions in
the current executable context.  Targets are retained explicitly because
later recursor restoration must weaken them beneath subsequently introduced
mutual binders. -/
structure TranslatedOriginTypes (Hc : ContextWF c)
    (origins : Array Expr) where
  targets : List VExpr
  translated : List.Forall₂
    (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx)
    origins.toList targets
  isType : ∀ target ∈ targets,
    Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx target

def TranslatedOriginTypes.empty (Hc : ContextWF c) :
    TranslatedOriginTypes Hc #[] where
  targets := []
  translated := .nil
  isType _ h := by simp at h

/-- Append a newly consumed declaration domain and weaken all earlier origin
translations through the corresponding fresh local declaration. -/
def TranslatedOriginTypes.push
    (H : TranslatedOriginTypes Hc origins)
    (Hdom : Hc.ConsumedDomain dom sourceTarget consumedTarget)
    (name : Name) (bi : BinderInfo) :
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
      Hdom.consumed Hdom.isType
    TranslatedOriginTypes Hc' (origins.push dom.consumeTypeAnnotations) := by
  dsimp only
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  let liftedTargets := H.targets.map fun target => target.liftN 1 0
  refine {
    targets := liftedTargets ++ [consumedTarget.liftN 1 0]
    translated := ?_
    isType := ?_ }
  · rw [Array.toList_push]
    apply checkPositivityStep.forall₂_append
    · apply checkPositivityStep.forall₂_map_right H.translated
      intro source target Hsource
      exact Hsource.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf
    · apply List.Forall₂.cons
      · exact Hdom.consumed.weakFV Hc.checking.tr.wf.ordered W
          Hc'.mlctx_wf.tr.wf
      · exact .nil
  · intro target htarget
    simp only [liftedTargets, List.mem_append, List.mem_map,
      List.mem_singleton] at htarget
    rcases htarget with ⟨oldTarget, hold, rfl⟩ | rfl
    · exact (H.isType oldTarget hold).weakN Hc.checking.tr.wf.ordered
        (.one : Ctx.LiftN 1 0 Hc.mlctx.vlctx.toCtx
          (consumedTarget :: Hc.mlctx.vlctx.toCtx))
    · exact Hdom.isType.weakN Hc.checking.tr.wf.ordered
        (.one : Ctx.LiftN 1 0 Hc.mlctx.vlctx.toCtx
          (consumedTarget :: Hc.mlctx.vlctx.toCtx))

/-- Two retained declarations for the same expression in one local context
have the same declaration type.  This deliberately permits different source
arrays and indices: the free-variable identity, rather than an incidental
array presentation, determines the local declaration. -/
theorem BoundFVarDeclarationAt.type_eq_of_expression
    (D : BoundFVarDeclarationAt c xs i)
    (E : BoundFVarDeclarationAt c ys j)
    (hexpression : xs[i]'D.inBounds = ys[j]'E.inBounds) :
    D.type = E.type := by
  have hfvarExpr : Expr.fvar D.fvar = Expr.fvar E.fvar :=
    D.expression.symm.trans (hexpression.trans E.expression)
  have hfvar : D.fvar = E.fvar := Expr.fvar.inj hfvarExpr
  have hdeclaration := E.declaration
  rw [← hfvar, D.declaration] at hdeclaration
  exact congrArg LocalDecl.type (Option.some.inj hdeclaration)

/-- Recover the exact production origin type from any declaration witness for
the same retained array position. -/
theorem BoundFVarTypeOrigins.type_eq
    (H : BoundFVarTypeOrigins c xs origins)
    (D : BoundFVarDeclarationAt c xs i) :
    D.type = origins[i]! := by
  rcases H.declaration i D.inBounds with ⟨E, htype⟩
  exact (D.type_eq_of_expression E (by rfl)).trans htype

def BoundFVarTypeOrigins.empty (c : AddInductive.Context) :
    BoundFVarTypeOrigins c #[] #[] where
  bound := BoundFVarArray.empty c
  size_eq := rfl
  declaration i hi := by simp at hi

def BoundFVarTypeOrigins.mono
    (H : BoundFVarTypeOrigins c xs origins)
    (hle : BindingContextLE c c') :
    BoundFVarTypeOrigins c' xs origins where
  bound := H.bound.mono hle
  size_eq := H.size_eq
  declaration i hi := by
    rcases H.declaration i hi with ⟨D, htype⟩
    exact ⟨D.mono hle, htype⟩

def BoundFVarTypeOrigins.pushCurrent
    (H : BoundFVarTypeOrigins c xs origins)
    (Hc : BindingContextWF c)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    BoundFVarTypeOrigins
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      (xs.push (.fvar ⟨c.ngen.curr⟩)) (origins.push ty) := by
  let c' : AddInductive.Context := { c with
    ngen := c.ngen.next
    lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
  let hstep := BindingContextLE.withLocalDecl c Hc name ty bi
  refine {
    bound := H.bound.pushCurrent name ty bi
    size_eq := by simpa using H.size_eq
    declaration := ?_ }
  intro i hi
  by_cases hilast : i = xs.size
  · subst i
    let D : BoundFVarDeclarationAt c'
        (xs.push (.fvar ⟨c.ngen.curr⟩)) xs.size := {
      inBounds := by simpa
      fvar := ⟨c.ngen.curr⟩
      expression := by simp
      member := by
        simp only [c', LocalContext.fvars, LocalContext.mkLocalDecl_toList,
          List.map_cons, LocalDecl.fvarId, List.mem_cons]
        exact Or.inl trivial
      index := c.lctx.decls.size
      userName := name
      type := ty
      binderInfo := bi
      kind := .default
      declaration := by
        simp [c', LocalContext.mkLocalDecl, LocalContext.find?,
          Hc.wf.map_wf.find?_insert] }
    refine ⟨D, ?_⟩
    change ty = (origins.push ty)[xs.size]!
    rw [show xs.size = origins.size from H.size_eq.symm]
    simp
  · have hiOld : i < xs.size := by
      have : i < xs.size + 1 := by simpa using hi
      omega
    rcases H.declaration i hiOld with ⟨D, htype⟩
    refine ⟨(D.pushArray (.fvar ⟨c.ngen.curr⟩)).mono hstep, ?_⟩
    have hsizes := H.size_eq
    have hiOrigins : i < origins.size := by omega
    change D.type = (origins.push ty)[i]!
    rw [Array.getElem!_eq_getD] at htype ⊢
    unfold Array.getD at htype ⊢
    rw [dif_pos hiOrigins] at htype
    have hiPush : i < (origins.push ty).size := by
      simp only [Array.size_push]
      omega
    rw [dif_pos hiPush]
    have heq : (origins.push ty)[i]'hiPush = origins[i]'hiOrigins :=
      Array.getElem_push_lt hiOrigins
    exact htype.trans heq.symm

theorem BoundFVarArray.getElem_eq_fvar
    (H : BoundFVarArray c xs) (i : Nat) (hi : i < xs.size) :
    ∃ hiFvars : i < H.fvars.length,
      xs[i] = .fvar H.fvars[i] := by
  rcases H with ⟨fvars, rfl, members⟩
  refine ⟨by simpa using hi, by simp⟩

/-- A selected free-variable array occupying a known slice of a larger
binder list translates, after simultaneous abstraction, to the corresponding
canonical de Bruijn slice. -/
theorem BoundFVarArray.abstractedTranslationAt
    (H : BoundFVarArray c xs)
    (binders before after : List FVarId)
    (hsplit : binders = before ++ H.fvars ++ after)
    (hnodup : binders.Nodup)
    (domains : List VExpr) (Δ : VLCtx)
    (hdomains : domains.length = binders.length) :
    List.Forall₂
      (TrExprS env Us (abstractForallContext domains Δ))
      ((xs.map fun arg => arg.abstractList binders).toList)
      (List.ofFn fun i : Fin xs.size =>
        VExpr.bvar (binders.length - 1 - (before.length + i))) := by
  subst binders
  apply List.forall₂_of_getElem (by simp)
  intro i hsource htarget
  have hi : i < xs.size := by simpa using hsource
  rcases H.getElem_eq_fvar i hi with ⟨hiFvars, harg⟩
  have hposition : before.length + i <
      (before ++ H.fvars ++ after).length := by
    simp only [List.length_append]
    omega
  have hselected :
      (before ++ H.fvars ++ after)[before.length + i] = H.fvars[i] := by
    simp [hiFvars]
  have habstract := Expr.abstractList_fvar_getElem hnodup
    (before.length + i) hposition (k := 0)
  rw [hselected] at habstract
  simp only [Array.getElem_toList, Array.getElem_map,
    List.getElem_ofFn]
  rw [harg, habstract]
  have hbound :
      (before ++ H.fvars ++ after).length - 1 - (before.length + i) <
        domains.length := by
    rw [hdomains]
    omega
  simpa using TrExprS.bvar_of_abstractForallContext
    (env := env) (Us := Us) domains Δ
    ((before ++ H.fvars ++ after).length - 1 - (before.length + i))
    hbound

theorem BoundFVarArray.length_fvars
    (H : BoundFVarArray c xs) : H.fvars.length = xs.size := by
  have := congrArg Array.size H.expressions
  simpa using this.symm

theorem BoundFVarArray.get_fvars_sublist
    (H : BoundFVarArray c xs) (i : Nat) (hi : i < xs.size) :
    (H.get i hi).fvars <+ H.fvars := by
  rcases H with ⟨fvars, rfl, members⟩
  simp [BoundFVarArray.get, List.getElem_mem]

theorem BoundFVarArray.fvars_eq
    (H₁ : BoundFVarArray c xs) (H₂ : BoundFVarArray c ys)
    (hxy : xs = ys) : H₁.fvars = H₂.fvars := by
  have harr : (H₁.fvars.map Expr.fvar).toArray =
      (H₂.fvars.map Expr.fvar).toArray := by
    rw [← H₁.expressions, ← H₂.expressions, hxy]
  have hlist : H₁.fvars.map Expr.fvar = H₂.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList harr
  exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist

/-- Binder identity is determined by the represented expression array, even
when the two retained certificates are indexed by different contexts. -/
theorem BoundFVarArray.fvars_eq_of_array_eq
    (H₁ : BoundFVarArray c₁ xs) (H₂ : BoundFVarArray c₂ ys)
    (hxy : xs = ys) : H₁.fvars = H₂.fvars := by
  have harr : (H₁.fvars.map Expr.fvar).toArray =
      (H₂.fvars.map Expr.fvar).toArray := by
    rw [← H₁.expressions, ← H₂.expressions, hxy]
  have hlist : H₁.fvars.map Expr.fvar = H₂.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList harr
  exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlist

/-- Ordered selection of one bound-fvar array from another implies the
corresponding inclusion of retained free-variable identifiers. -/
theorem BoundFVarArray.fvars_subset_of_sublist
    (H₁ : BoundFVarArray c xs) (H₂ : BoundFVarArray c ys)
    (hxy : xs.toList.Sublist ys.toList) : H₁.fvars ⊆ H₂.fvars := by
  intro fv hfv
  have hx : Expr.fvar fv ∈ xs.toList := by
    rw [H₁.expressions]
    simpa using hfv
  have hy : Expr.fvar fv ∈ ys.toList := hxy.subset hx
  rw [H₂.expressions] at hy
  simpa using hy

/-- Any ordered subarray of an array of retained free variables is itself a
retained free-variable array.  The selected identifier list is recovered
from the `List.Sublist` derivation, so this does not assume an auxiliary
index map or re-run the executable classifier. -/
theorem BoundFVarArray.ofSublist
    (H : BoundFVarArray c ys) (hxy : xs.toList.Sublist ys.toList) :
    Nonempty (BoundFVarArray c xs) := by
  have extract : ∀ {es : List Expr} {fvars : List FVarId},
      es.Sublist (fvars.map Expr.fvar) →
      ∃ selected : List FVarId,
        es = selected.map Expr.fvar ∧ selected.Sublist fvars := by
    intro es fvars
    induction fvars generalizing es with
    | nil =>
      intro h
      have hes : es = [] := List.sublist_nil.mp (by simpa using h)
      subst es
      exact ⟨[], rfl, .slnil⟩
    | cons fv fvars ih =>
      intro h
      cases h with
      | cons _ htail =>
        rcases ih htail with ⟨selected, hes, hselected⟩
        exact ⟨selected, hes, .cons _ hselected⟩
      | cons_cons _ htail =>
        rcases ih htail with ⟨selected, hes, hselected⟩
        exact ⟨fv :: selected, by simp [hes], .cons_cons _ hselected⟩
  have hy : ys.toList = H.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList H.expressions
  have hsource : xs.toList.Sublist (H.fvars.map Expr.fvar) := by
    rwa [← hy]
  rcases extract hsource with ⟨selected, hselectedExprs, hselected⟩
  exact ⟨{
    fvars := selected
    expressions := by
      apply Array.toList_inj.mp
      simpa using hselectedExprs
    members := fun fv hfv =>
      H.members fv (hselected.subset hfv) }⟩

theorem BoundFVarArray.exprArrayFVarIds
    (H : BoundFVarArray c xs) : ExprArrayFVarIds xs = H.fvars := by
  calc
    ExprArrayFVarIds xs =
        ExprArrayFVarIds ((H.fvars.map Expr.fvar).toArray) :=
      congrArg ExprArrayFVarIds H.expressions
    _ = H.fvars := by
      simp [ExprArrayFVarIds, recursorFVarId, Function.comp_def]

/-- All local free-variable arrays retained by the executable recursor-info
records, aligned with the production array operations. -/
structure RecInfoBindings (c : AddInductive.Context)
    (recInfos : Array AddInductive.RecInfo) where
  motives : BoundFVarArray c (recInfos.map (·.motive))
  majors : BoundFVarArray c (recInfos.map (·.major))
  indices : ∀ i (hi : i < recInfos.size),
    BoundFVarArray c recInfos[i]!.indices
  minors : ∀ i (hi : i < recInfos.size),
    BoundFVarArray c recInfos[i]!.minors

/-- Structural trace of the constructor traversal which produced one minor.
The raw binding-only proof may omit this payload; the semantic second pass
retains it and the final source-alignment invariant rules that omission out. -/
structure RecInfoMinorTraversalShape where
  constructor : Constructor
  rootContext : AddInductive.Context
  terminalContext : AddInductive.Context
  terminal : Expr
  fields : Array Expr
  recursiveFields : Array Expr
  stats : AddInductive.InductiveStats
  recursivePositions : List Nat
  recursivePositions_ordered : recursivePositions.Pairwise (· < ·)
  recursivePositions_lt : ∀ position ∈ recursivePositions,
    position < fields.size
  recursivePositions_length : recursivePositions.length = recursiveFields.size
  parameterTail : Expr
  parameterTail_fvars : parameterTail.FVarsIn (· ∈ rootContext.lctx.fvars)
  decisions : RecursorFieldDecisions stats rootContext parameterTail
    terminalContext terminal fields recursiveFields recursivePositions
  parameterPrefix : RecursorParamPrefix stats 0 constructor.type parameterTail
  fieldFVars : List FVarId
  fields_eq : fields = (fieldFVars.map Expr.fvar).toArray
  fieldFVars_nodup : fieldFVars.Nodup
  fieldResidual : Expr
  fieldTelescope : Expr.ForallTelescope parameterTail fields.size fieldResidual
  fieldClosed : terminal.abstractList fieldFVars = fieldResidual
  fieldResidual_not_forall : fieldResidual.isForall = false

/-- The traversal's retained opening identifiers are uniquely determined by
the concrete field array, independently of the fresh names chosen by the
checker run. -/
theorem RecInfoMinorTraversalShape.fieldFVars_eq_bound
    (T : RecInfoMinorTraversalShape)
    (B : BoundFVarArray c T.fields) :
    T.fieldFVars = B.fvars := by
  have harrays : (T.fieldFVars.map Expr.fvar).toArray =
      (B.fvars.map Expr.fvar).toArray :=
    T.fields_eq.symm.trans B.expressions
  have hlists : T.fieldFVars.map Expr.fvar =
      B.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList harrays
  exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlists

/-- Close a retained traversal using any bound-field certificate for its
literal field array. -/
theorem RecInfoMinorTraversalShape.fieldClosed_of_bound
    (T : RecInfoMinorTraversalShape)
    (B : BoundFVarArray c T.fields) :
    T.terminal.abstractList B.fvars = T.fieldResidual := by
  rw [← T.fieldFVars_eq_bound B]
  exact T.fieldClosed

/-- Stable source construction for one installed recursive-hypothesis
declaration.  This compact form is stored with the generated minor after the
operational `loopU` accumulator itself has gone out of scope. -/
structure RecursorLoopUArgsTrace where
  ownerIdx : Nat
  localArity : Nat
  localTelescope : Expr
  motive : Expr
  indices : Array Expr

structure RecInfoMinorHypothesisTypeOrigin
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (root : AddInductive.Context) (field type : Expr) where
  current : AddInductive.Context
  current_wf : BindingContextWF current
  current_extends : BindingContextLE root current
  exposedType : Expr
  args : Array Expr
  arguments_bound : FreshBoundFVarArray root current args
  field_fvar : ∃ fv, field = .fvar fv ∧ fv ∈ root.lctx.fvars
  ownerIdx : Nat
  owner_valid : AddInductive.isValidIndApp? stats exposedType = some ownerIdx
  motive_is_fvar : ∃ fv,
    recInfos[ownerIdx]!.motive = .fvar fv ∧ fv ∈ root.lctx.fvars
  type_eq :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[ownerIdx]!.motive itIndices)
      (mkAppN field args)
    type = current.lctx.mkForall args motiveApp

/-- The exact higher-order telescope retained by a minor hypothesis before
the installed declaration consumes top-level annotations. -/
theorem RecInfoMinorHypothesisTypeOrigin.sourceTelescope
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type) :
    let indices : Array Expr :=
      O.exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[O.ownerIdx]!.motive indices)
      (mkAppN field O.args)
    Expr.ForallTelescope type O.args.size
      (motiveApp.abstractList O.arguments_bound.fvars) := by
  cases O with
  | mk current current_wf _current_extends exposedType args
      arguments_bound _field_fvar ownerIdx _owner_valid _motive_is_fvar
      type_eq =>
    dsimp only at type_eq ⊢
    rw [type_eq]
    exact arguments_bound.toBoundFVarArray.mkForall_forallTelescope
      current_wf _

/-- Closing the fresh higher-order arguments turns the selected field
application into its canonical de Bruijn spine.  This is the first-pass
counterpart of `BoundGeneratedRecursiveCall.abstractedMajor`. -/
theorem RecInfoMinorHypothesisTypeOrigin.abstractedMotiveApp_eq
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type) :
    let indices : Array Expr :=
      O.exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[O.ownerIdx]!.motive indices)
      (mkAppN field O.args)
    motiveApp.abstractList O.arguments_bound.fvars =
      Expr.app
        (mkAppN
          (recInfos[O.ownerIdx]!.motive.abstractList
            O.arguments_bound.fvars)
          (indices.map fun e =>
            e.abstractList O.arguments_bound.fvars))
        (mkAppN (field.abstractList O.arguments_bound.fvars)
          (List.ofFn (fun i : Fin O.arguments_bound.fvars.length =>
            Expr.bvar (O.arguments_bound.fvars.length - 1 - i))).toArray) := by
  dsimp only
  have hlocal :
      O.args.map (fun e => e.abstractList O.arguments_bound.fvars) =
        (List.ofFn (fun i : Fin O.arguments_bound.fvars.length =>
          Expr.bvar
            (O.arguments_bound.fvars.length - 1 - i))).toArray := by
    calc
      O.args.map (fun e => e.abstractList O.arguments_bound.fvars) =
          ((O.arguments_bound.fvars.map Expr.fvar).toArray.map fun e =>
            e.abstractList O.arguments_bound.fvars) := by
        exact congrArg (Array.map fun e =>
          e.abstractList O.arguments_bound.fvars)
            O.arguments_bound.expressions
      _ = _ := by
        simpa using Expr.abstractList_fvarArray
          O.arguments_bound.fvars 0 O.arguments_bound.nodup
  simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
  rw [hlocal]

def RecInfoMinorHypothesisTypeOrigin.localIndices
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type) :
    List Nat :=
  List.ofFn fun i : Fin O.arguments_bound.fvars.length =>
    O.arguments_bound.fvars.length - 1 - i

def RecInfoMinorHypothesisTypeOrigin.abstractedField
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type) :
    Expr :=
  mkAppN (field.abstractList O.arguments_bound.fvars)
    (O.localIndices.map Expr.bvar).toArray

def RecInfoMinorHypothesisTypeOrigin.outerAbstractedField
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type)
    (binders : List FVarId) : Expr :=
  O.abstractedField.abstractList binders O.args.size

/-- Alpha-normalized payload of the first-pass `loopUArgs` run.  Closing the
fresh higher-order suffix and then the constructor fields removes allocation
identities while retaining exactly the owner, local arity, and index spine
which determine the generated induction-hypothesis type. -/
def RecInfoMinorHypothesisTypeOrigin.replayTrace
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type)
    (fieldBinders : List FVarId) : RecursorLoopUArgsTrace where
  ownerIdx := O.ownerIdx
  localArity := O.args.size
  localTelescope :=
    (O.current.lctx.mkForall O.args (.sort .zero)).abstractList fieldBinders
  motive :=
    (recInfos[O.ownerIdx]!.motive.abstractList
      O.arguments_bound.fvars).abstractList fieldBinders O.args.size
  indices :=
    ((O.exposedType.getAppArgs[stats.params.size:] : Array Expr).map
      fun index =>
        (index.abstractList O.arguments_bound.fvars).abstractList
          fieldBinders O.args.size)

/-- The first-pass hypothesis result after closing its higher-order arguments
and all constructor fields.  This is the exact motive application payload;
the surrounding forall telescope is handled separately. -/
def RecInfoMinorHypothesisTypeOrigin.outerAbstractedMotiveApp
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type)
    (fieldBinders : List FVarId) : Expr :=
  Expr.app
    (mkAppN (O.replayTrace fieldBinders).motive
      (O.replayTrace fieldBinders).indices)
    (O.outerAbstractedField fieldBinders)

theorem RecInfoMinorHypothesisTypeOrigin.outerAbstractedMotiveApp_eq
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type)
    (fieldBinders : List FVarId) :
    let indices : Array Expr :=
      O.exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[O.ownerIdx]!.motive indices)
      (mkAppN field O.args)
    (motiveApp.abstractList O.arguments_bound.fvars).abstractList
        fieldBinders O.args.size =
      O.outerAbstractedMotiveApp fieldBinders := by
  dsimp only
  rw [O.abstractedMotiveApp_eq]
  simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
  simp [RecInfoMinorHypothesisTypeOrigin.outerAbstractedMotiveApp,
    RecInfoMinorHypothesisTypeOrigin.replayTrace,
    RecInfoMinorHypothesisTypeOrigin.outerAbstractedField,
    Array.map_map, Function.comp_def]
  unfold RecInfoMinorHypothesisTypeOrigin.abstractedField
    RecInfoMinorHypothesisTypeOrigin.localIndices
  rw [Expr.abstractList_mkAppN]
  simp [List.map_ofFn, Function.comp_def]

/-- After also closing an outer binder list, the selected first-pass field
is the canonical outer de Bruijn variable shifted beneath its higher-order
arguments and applied to their canonical local spine. -/
theorem RecInfoMinorHypothesisTypeOrigin.outerAbstractedField_eq_bvar
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type)
    (hfieldEq : field = .fvar fv)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup) (hfield : fv ∈ binders) :
    ∃ fieldVar,
      fieldVar < binders.length ∧
      (Expr.fvar fv).abstractList binders = .bvar fieldVar ∧
      O.outerAbstractedField binders =
        mkAppN (.bvar (O.args.size + fieldVar))
          (O.localIndices.map Expr.bvar).toArray := by
  subst field
  rcases List.mem_iff_getElem.mp hfield with ⟨i, hi, hget⟩
  let fieldVar := binders.length - 1 - i
  have hfresh : fv ∉ O.arguments_bound.fvars := by
    intro hmem
    exact O.arguments_bound.fresh fv hmem hfieldRoot
  have hfieldLocal :
      (Expr.fvar fv).abstractList O.arguments_bound.fvars = .fvar fv :=
    Expr.abstractList_fvar_of_not_mem hfresh
  have hlocalSize : O.args.size = O.arguments_bound.fvars.length := by
    have h := congrArg Array.size O.arguments_bound.expressions
    simpa using h
  have hfieldOuter := Expr.abstractList_fvar_getElem
    hbinders i hi (k := O.args.size)
  rw [hget] at hfieldOuter
  have hfieldOuter' :
      (Expr.fvar fv).abstractList binders O.args.size =
        .bvar (O.args.size + fieldVar) := by
    simpa [fieldVar] using hfieldOuter
  have hfieldBase := Expr.abstractList_fvar_getElem
    hbinders i hi (k := 0)
  rw [hget] at hfieldBase
  have hfieldBase' : (Expr.fvar fv).abstractList binders =
      .bvar fieldVar := by
    simpa [fieldVar] using hfieldBase
  have hsourceArgs :
      (List.ofFn fun i : Fin O.arguments_bound.fvars.length =>
        Expr.bvar (O.arguments_bound.fvars.length - 1 - i)) =
      O.localIndices.map Expr.bvar := by
    simp [RecInfoMinorHypothesisTypeOrigin.localIndices,
      List.map_ofFn, Function.comp_def]
  refine ⟨fieldVar, by omega, hfieldBase', ?_⟩
  unfold RecInfoMinorHypothesisTypeOrigin.outerAbstractedField
    RecInfoMinorHypothesisTypeOrigin.abstractedField
  rw [Expr.abstractList_mkAppN, hfieldLocal, hfieldOuter']
  apply congrArg (mkAppN (.bvar (O.args.size + fieldVar)))
  rw [← hsourceArgs]
  apply Array.ext
  · simp
  · intro j hjLeft hjRight
    simp only [Array.getElem_map, List.getElem_toArray,
      List.getElem_map, List.getElem_ofFn]
    apply Expr.abstractList_bvar_lt
    have hj : j < O.arguments_bound.fvars.length := by
      simpa [RecInfoMinorHypothesisTypeOrigin.localIndices] using hjRight
    omega

/-- Positional form of `outerAbstractedField_eq_bvar`.  When the retained
field is known to occupy binder position `i`, its de Bruijn index is no
longer existential: it is exactly the reverse ordinal of that position. -/
theorem RecInfoMinorHypothesisTypeOrigin.outerAbstractedField_eq_bvar_at
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type)
    (hfieldEq : field = .fvar fv)
    (hfieldRoot : fv ∈ root.lctx.fvars)
    (hbinders : binders.Nodup) (hi : i < binders.length)
    (hget : binders[i] = fv) :
    O.outerAbstractedField binders =
      mkAppN (.bvar (O.args.size + (binders.length - 1 - i)))
        (O.localIndices.map Expr.bvar).toArray := by
  have hmem : fv ∈ binders := by
    rw [← hget]
    exact List.getElem_mem hi
  rcases O.outerAbstractedField_eq_bvar hfieldEq hfieldRoot hbinders hmem with
    ⟨fieldVar, _hfieldVar, habstract, houter⟩
  have hexact := Expr.abstractList_fvar_getElem hbinders i hi (k := 0)
  rw [hget] at hexact
  have hfieldVarExact : fieldVar = binders.length - 1 - i := by
    have hexact' : (Expr.fvar fv).abstractList binders =
        .bvar (binders.length - 1 - i) := by
      simpa only [Nat.zero_add] using hexact
    exact Expr.bvar.inj (habstract.symm.trans hexact')
  simpa [hfieldVarExact] using houter

/-- The constructed hypothesis origin cannot itself be a top-level parameter
annotation: a nonempty local suffix produces a forall, while the empty case
is the explicit motive application. -/
theorem RecInfoMinorHypothesisTypeOrigin.consumeTypeAnnotations_eq_self
    (O : RecInfoMinorHypothesisTypeOrigin stats recInfos root field type) :
    type.consumeTypeAnnotations = type := by
  let itIndices := O.exposedType.getAppArgs[stats.params.size:]
  let motiveApp := Expr.app
    (mkAppN recInfos[O.ownerIdx]!.motive itIndices)
    (mkAppN field O.args)
  rw [O.type_eq]
  by_cases hpos : 0 < O.args.size
  · have Htelescope :=
      O.arguments_bound.toBoundFVarArray.mkForall_forallTelescope
        O.current_wf motiveApp
    exact Htelescope.consumeTypeAnnotations_eq_self_of_pos hpos
  · have hsize : O.args.size = 0 := by omega
    have hargs : O.args = #[] := Array.eq_empty_of_size_eq_zero hsize
    rw [hargs]
    rw [LocalContext.mkForall_empty]
    rcases O.motive_is_fvar with ⟨motiveFVar, hmotive, _hmotiveRoot⟩
    have hhead :
        (Expr.app
          (mkAppN recInfos[O.ownerIdx]!.motive itIndices)
          (mkAppN field #[])).getAppFn = .fvar motiveFVar := by
      simp only [Expr.getAppFn, Expr.getAppFn_mkAppN, hmotive]
    apply Expr.consumeTypeAnnotations_eq_self
    · change (Expr.app _ _).isAppOfArity `optParam 2 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change (Expr.app _ _).isAppOfArity `autoParam 2 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change (Expr.app _ _).isAppOfArity `outParam 1 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change (Expr.app _ _).isAppOfArity `semiOutParam 1 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _

/-- Completed pointwise origin data retained by one generated minor. -/
structure RecInfoMinorHypothesisTypeOrigins
    (c : AddInductive.Context) (fields hypotheses : Array Expr) where
  stats : AddInductive.InductiveStats
  recInfos : Array AddInductive.RecInfo
  hypotheses_outer_fresh : ∀ fv,
    fv ∈ ExprArrayFVarIds stats.params ++
        ExprArrayFVarIds (recInfos.map (·.motive)) →
      fv ∉ ExprArrayFVarIds hypotheses
  entry : ∀ j (hj : j < hypotheses.size),
    ∃ root sourceType,
      Nonempty (RecInfoMinorHypothesisTypeOrigin
        stats recInfos root fields[j]! sourceType) ∧
      ∃ D : BoundFVarDeclarationAt c hypotheses j,
        D.type = sourceType.consumeTypeAnnotations

/-- The exact source construction retained for one generated minor domain.
The source local context is intentionally stored in the certificate: after
`mkForall` closes the freshly introduced fields and recursive hypotheses, the
resulting expression is stable under every later ambient-context extension. -/
structure RecInfoMinorTypeShape where
  localIndex : Nat
  origin : Expr
  constructor : Constructor
  sourceConstructors : List Constructor
  sourceConstructor : sourceConstructors[localIndex]? = some constructor
  sourceFullContext : AddInductive.Context
  sourceFullWF : BindingContextWF sourceFullContext
  sourceContext : LocalContext
  sourceContext_eq : sourceFullContext.lctx = sourceContext
  fields : Array Expr
  fields_bound : BoundFVarArray sourceFullContext fields
  fields_nodup : fields_bound.fvars.Nodup
  recursiveFields : Array Expr
  hypotheses : Array Expr
  hypotheses_bound : BoundFVarArray sourceFullContext hypotheses
  hypotheses_nodup : hypotheses_bound.fvars.Nodup
  hypotheses_fields_fresh : ∀ fv ∈ hypotheses_bound.fvars,
    fv ∉ fields_bound.fvars
  hypothesis_type_origins : Option
    (RecInfoMinorHypothesisTypeOrigins
      sourceFullContext recursiveFields hypotheses)
  hypotheses_size : hypotheses.size = recursiveFields.size
  traversal : Option RecInfoMinorTraversalShape
  motiveApp : Expr
  sourceType : Expr
  sourceType_eq : sourceType =
    sourceContext.mkForall fields
      (sourceContext.mkForall hypotheses motiveApp)
  consumed_eq : sourceType.consumeTypeAnnotations = origin

/-- A semantic minor retained its completed hypothesis-origin table, and the
table was produced with the expected inductive statistics. -/
def RecInfoMinorTypeShape.HasHypothesisTypeOrigins
    (S : RecInfoMinorTypeShape) (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) : Prop :=
  match S.hypothesis_type_origins with
  | none => False
  | some origins => origins.stats = stats ∧
      origins.recInfos.map (·.motive) = recInfos.map (·.motive)

theorem RecInfoMinorTypeShape.hypothesisTypeOrigins_exists
    (S : RecInfoMinorTypeShape) (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo)
    (H : S.HasHypothesisTypeOrigins stats recInfos) :
    ∃ origins, S.hypothesis_type_origins = some origins ∧
      origins.stats = stats ∧
        origins.recInfos.map (·.motive) = recInfos.map (·.motive) := by
  cases h : S.hypothesis_type_origins with
  | none => simp [RecInfoMinorTypeShape.HasHypothesisTypeOrigins, h] at H
  | some origins =>
      exact ⟨origins, rfl, by
        simpa [RecInfoMinorTypeShape.HasHypothesisTypeOrigins, h] using H⟩

/-- The retained first-pass hypothesis array is the exact inner forall
telescope of the generated minor source type.  Its residual is expressed
after simultaneous abstraction by the corresponding retained hypothesis
identifiers, matching the representation used for generated rule bodies. -/
theorem RecInfoMinorTypeShape.hypothesisTelescope
    (S : RecInfoMinorTypeShape) :
    Expr.ForallTelescope
      (S.sourceContext.mkForall S.hypotheses S.motiveApp)
      S.hypotheses.size
      (S.motiveApp.abstractList S.hypotheses_bound.fvars) := by
  let B := S.hypotheses_bound
  have hsize : B.fvars.length = S.hypotheses.size := by
    have h := congrArg Array.size B.expressions
    simpa using h.symm
  have Htelescope := LocalContext.mkForall_fvars_forallTelescope
    (lctx := S.sourceFullContext.lctx) (body := S.motiveApp)
    (fvs := B.fvars) (by
      intro fv hfv
      exact S.sourceFullWF.findCDecl fv (B.members fv hfv))
  have houter : S.sourceContext.mkForall S.hypotheses S.motiveApp =
      S.sourceFullContext.lctx.mkForall
        (B.fvars.map Expr.fvar).toArray S.motiveApp := by
    calc
      _ = S.sourceFullContext.lctx.mkForall S.hypotheses S.motiveApp :=
        congrArg (fun lctx => lctx.mkForall S.hypotheses S.motiveApp)
          S.sourceContext_eq.symm
      _ = _ := congrArg
        (fun fields => S.sourceFullContext.lctx.mkForall fields S.motiveApp)
        B.expressions
  rw [houter]
  simpa only [B, ← hsize] using Htelescope

/-- The retained constructor fields likewise form the exact outer telescope
of the minor source type around any chosen body. -/
theorem RecInfoMinorTypeShape.fieldTelescope
    (S : RecInfoMinorTypeShape) (body : Expr) :
    Expr.ForallTelescope
      (S.sourceContext.mkForall S.fields body)
      S.fields.size (body.abstractList S.fields_bound.fvars) := by
  have Htelescope := S.fields_bound.mkForall_forallTelescope
    S.sourceFullWF body
  have houter : S.sourceContext.mkForall S.fields body =
      S.sourceFullContext.lctx.mkForall S.fields body :=
    congrArg (fun lctx => lctx.mkForall S.fields body)
      S.sourceContext_eq.symm
  rw [houter]
  exact Htelescope

/-- Combining the two retained arrays exposes the complete field/hypothesis
telescope of the unconsumed minor source type, including the precise
abstraction cutoff beneath the inner hypothesis binders. -/
theorem RecInfoMinorTypeShape.sourceTelescope
    (S : RecInfoMinorTypeShape) :
    Expr.ForallTelescope S.sourceType
      (S.fields.size + S.hypotheses.size)
      ((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size) := by
  rw [S.sourceType_eq]
  have Hfields := S.fieldTelescope
    (S.sourceContext.mkForall S.hypotheses S.motiveApp)
  have Hhypotheses :=
    S.hypothesisTelescope.abstractList S.fields_bound.fvars
  simpa only [Nat.zero_add] using Hfields.trans Hhypotheses

/-- The annotation-consumed origin installed as the minor declaration keeps
the complete field/hypothesis arity of its unconsumed production source. -/
theorem RecInfoMinorTypeShape.originTelescope
    (S : RecInfoMinorTypeShape) :
    ∃ residual, Expr.ForallTelescope S.origin
      (S.fields.size + S.hypotheses.size) residual := by
  rcases S.sourceTelescope.consumeTypeAnnotations_arity with
    ⟨residual, Htelescope⟩
  rw [S.consumed_eq] at Htelescope
  exact ⟨residual, Htelescope⟩

/-- Exact `withLocalDecl` origin types retained in the same row structure as
production `RecInfo`s.  Per-owner rows avoid losing the insertion position of
minor premises during the second mutual pass. -/
structure RecInfoTypeOrigins (c : AddInductive.Context)
    (recInfos : Array AddInductive.RecInfo) where
  motiveTypes : Array Expr
  majorTypes : Array Expr
  indexTypes : Array (Array Expr)
  minorTypes : Array (Array Expr)
  indexTypes_size : indexTypes.size = recInfos.size
  minorTypes_size : minorTypes.size = recInfos.size
  motives : BoundFVarTypeOrigins c (recInfos.map (·.motive)) motiveTypes
  majors : BoundFVarTypeOrigins c (recInfos.map (·.major)) majorTypes
  indices : ∀ i (hi : i < recInfos.size),
    BoundFVarTypeOrigins c recInfos[i]!.indices indexTypes[i]!
  minors : ∀ i (hi : i < recInfos.size),
    BoundFVarTypeOrigins c recInfos[i]!.minors minorTypes[i]!
  minorShapes : ∀ i (hi : i < recInfos.size) j
    (hj : j < minorTypes[i]!.size),
    RecInfoMinorTypeShape

/-- Exact production shape of every generated major-premise declaration.
This positional certificate is independent of translation: it records that
the stored origin is the selected family applied to the retained common
parameters and this record's indices. -/
structure RecInfoMajorTypeShapes (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) (majorTypes : Array Expr) : Prop where
  size_eq : majorTypes.size = recInfos.size
  shape : ∀ i (hi : i < recInfos.size),
    majorTypes[i]! =
      (mkAppN (mkAppN stats.indConsts[i]! stats.params)
        recInfos[i]!.indices).consumeTypeAnnotations

def RecInfoMajorTypeShapes.empty (stats : AddInductive.InductiveStats) :
    RecInfoMajorTypeShapes stats #[] #[] where
  size_eq := rfl
  shape i hi := by simp at hi

/-- Append one family frame to the positional major-domain certificate. -/
def RecInfoMajorTypeShapes.push
    (H : RecInfoMajorTypeShapes stats recInfos majorTypes)
    (info : AddInductive.RecInfo) (majorType : Expr)
    (hnew : majorType =
      (mkAppN (mkAppN stats.indConsts[recInfos.size]! stats.params)
        info.indices).consumeTypeAnnotations) :
    RecInfoMajorTypeShapes stats (recInfos.push info)
      (majorTypes.push majorType) where
  size_eq := by simpa using H.size_eq
  shape i hi := by
    by_cases hold : i < recInfos.size
    · have hmajor : i < majorTypes.size := by
        rw [H.size_eq]
        exact hold
      have hmajorPush : (majorTypes.push majorType)[i]! = majorTypes[i]! := by
        have hpush : i < (majorTypes.push majorType).size := by
          simp only [Array.size_push]
          omega
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hpush, dif_pos hmajor]
        exact Array.getElem_push_lt hmajor
      have hinfoPush : (recInfos.push info)[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hmajorPush, hinfoPush]
      exact H.shape i hold
    · have hieq : i = recInfos.size := by
        simp only [Array.size_push] at hi
        omega
      subst i
      have hmajorPush :
          (majorTypes.push majorType)[recInfos.size]! = majorType := by
        rw [show recInfos.size = majorTypes.size from H.size_eq.symm]
        simp
      have hinfoPush : (recInfos.push info)[recInfos.size]! = info := by
        simp
      rw [hmajorPush, hinfoPush]
      exact hnew

def RecInfoTypeOrigins.empty (c : AddInductive.Context) :
    RecInfoTypeOrigins c #[] where
  motiveTypes := #[]
  majorTypes := #[]
  indexTypes := #[]
  minorTypes := #[]
  indexTypes_size := rfl
  minorTypes_size := rfl
  motives := by simpa using BoundFVarTypeOrigins.empty c
  majors := by simpa using BoundFVarTypeOrigins.empty c
  indices i hi := by simp at hi
  minors i hi := by simp at hi
  minorShapes i hi := by simp at hi

def RecInfoTypeOrigins.mono
    (H : RecInfoTypeOrigins c recInfos) (hle : BindingContextLE c c') :
    RecInfoTypeOrigins c' recInfos where
  motiveTypes := H.motiveTypes
  majorTypes := H.majorTypes
  indexTypes := H.indexTypes
  minorTypes := H.minorTypes
  indexTypes_size := H.indexTypes_size
  minorTypes_size := H.minorTypes_size
  motives := H.motives.mono hle
  majors := H.majors.mono hle
  indices i hi := (H.indices i hi).mono hle
  minors i hi := (H.minors i hi).mono hle
  minorShapes i hi j hj := H.minorShapes i hi j hj

/-- Exact production shape of every motive declaration domain.  This is
kept separately from `RecursorTranslatedOriginTypes`: the latter certifies
that the stored domain translates to a type, while this certificate states
which dependent forall telescope that domain is supposed to be. -/
structure RecInfoMotiveTypeShapes (c : AddInductive.Context)
    (recInfos : Array AddInductive.RecInfo) (motiveTypes : Array Expr)
    (elimLevel : Level) : Prop where
  size_eq : motiveTypes.size = recInfos.size
  shape : ∀ i (hi : i < recInfos.size),
    motiveTypes[i]! =
      c.lctx.mkForall recInfos[i]!.indices
        (c.lctx.mkForall #[recInfos[i]!.major] (.sort elimLevel))

/-- Semantic lookup package for one generated motive.  It connects the
retained executable free variable to the exact independently recorded
index/major telescope used when the motive was introduced. -/
structure RecursorMotiveBindingAt
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (recInfos : Array AddInductive.RecInfo) (target : Nat)
    (elimLevel : Level) : Type where
  target_lt : target < recInfos.size
  motiveTarget : VExpr
  motiveTypeTarget : VExpr
  motive : TrExprS R.venv recLparams R.mlctx.vlctx
    recInfos[target]!.motive motiveTarget
  motiveType : TrExprS R.venv recLparams R.mlctx.vlctx
    (c.lctx.mkForall recInfos[target]!.indices
      (c.lctx.mkForall #[recInfos[target]!.major] (.sort elimLevel)))
    motiveTypeTarget
  typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    motiveTarget motiveTypeTarget
  typeIsType : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
    motiveTypeTarget

/-- Context-local semantic package for a generated motive, stated directly
against one `RecInfo`.  The indexed lookup package below is converted to this
form before invoking the context-independent motive application invariant. -/
structure RecursorMotiveBinding
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (info : AddInductive.RecInfo) (elimLevel : Level) : Type where
  motiveTarget : VExpr
  motiveTypeTarget : VExpr
  motive : TrExprS R.venv recLparams R.mlctx.vlctx
    info.motive motiveTarget
  motiveType : TrExprS R.venv recLparams R.mlctx.vlctx
    (c.lctx.mkForall info.indices
      (c.lctx.mkForall #[info.major] (.sort elimLevel)))
    motiveTypeTarget
  typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    motiveTarget motiveTypeTarget
  typeIsType : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
    motiveTypeTarget

def RecursorMotiveBindingAt.toBinding
    (H : RecursorMotiveBindingAt R recInfos target elimLevel) :
    RecursorMotiveBinding R recInfos[target]! elimLevel where
  motiveTarget := H.motiveTarget
  motiveTypeTarget := H.motiveTypeTarget
  motive := H.motive
  motiveType := H.motiveType
  typing := H.typing
  typeIsType := H.typeIsType

/-- Independent semantic contract for applying one generated motive.  It is
deliberately quantified over the eventual reader context: the first
`mkRecInfos` pass records this property once for each `RecInfo`, while the
second pass may use it after opening any number of constructor or
higher-order recursive binders.

The validated application supplies the exact source/abstract index payload.
The other two typing premises say that the exposed family application is a
type and that the proposed major premise inhabits it.  Thus this contract is
precisely the declarative fact needed to justify production's motive
application, rather than an assertion about the executable classifier. -/
def RecursorMotiveApplicationAt
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : Nat) (info : AddInductive.RecInfo)
    (elimLevel : Level) : Prop :=
  ∀ {current : AddInductive.Context}
    (R : RecursorContextWF current recLparams)
    (_Hext : RecursorContextExtension Rroot R)
    {depth : Nat}
    {exposedType major : Expr} {syntaxTarget majorTarget : VExpr},
    RecursorMotiveBinding R info elimLevel →
    TrExprS R.venv recLparams R.mlctx.vlctx exposedType syntaxTarget →
    R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx syntaxTarget →
    TrExprS R.venv recLparams R.mlctx.vlctx major majorTarget →
    R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      majorTarget syntaxTarget →
    RecursorValidatedIndAppAt R.venv recLparams R.mlctx.vlctx stats decl
      depth exposedType syntaxTarget target →
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app (mkAppN info.motive itIndices) major
    ∃ motiveTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx motiveApp motiveTarget ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx motiveTarget

/-- The smaller semantic payload from which a motive application follows.
It states that the validated terminal family application and the retained
motive type consume the same abstract index telescope.  Keeping this
separate makes the first-pass obligation reviewable: it need not mention a
particular recursive field or induction-hypothesis major. -/
structure RecursorMotiveTelescopeEvidence
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats) (info : AddInductive.RecInfo)
    (binding : RecursorMotiveBinding R info elimLevel)
    (exposedType : Expr) (syntaxTarget : VExpr) : Type where
  indices : List VExpr
  family : VExpr
  familyActualType : VExpr
  familyType : VExpr
  motiveType : VExpr
  resultLevel : VLevel
  syntax_eq : syntaxTarget = VExpr.mkApps family indices
  indices_translation : List.Forall₂
    (TrExprS R.venv recLparams R.mlctx.vlctx)
    (exposedType.getAppArgs[stats.params.size:]).toList indices
  family_typing : R.venv.HasType recLparams.length
    R.mlctx.vlctx.toCtx family familyActualType
  family_type_defeq : R.venv.IsDefEqU recLparams.length
    R.mlctx.vlctx.toCtx familyActualType familyType
  motive_type_defeq : R.venv.IsDefEqU recLparams.length
    R.mlctx.vlctx.toCtx binding.motiveTypeTarget motiveType
  telescope : RecursorMotiveTelescope resultLevel indices.length family
    familyType motiveType

/-- The family prefix of a validated, well-formed terminal application is
itself well typed.  This is obtained by retaining the prefix of the complete
abstract application spine, without choosing or normalizing its type. -/
theorem RecursorValidatedIndAppAt.familyPrefixTyping
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorValidatedIndAppAt R.venv recLparams R.mlctx.vlctx
      stats decl depth exposedType syntaxTarget target)
    (HsyntaxType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx syntaxTarget)
    {levels : List VLevel} {params indices : List VExpr}
    (hspine : syntaxTarget.getAppFnArgs =
      (.const (decl.types[target]'H.target_lt).name levels,
        params ++ indices)) :
    ∃ familyType,
      R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
        (VExpr.mkApps
          (.const (decl.types[target]'H.target_lt).name levels) params)
        familyType := by
  let family := VExpr.mkApps
    (.const (decl.types[target]'H.target_lt).name levels) params
  have hrebuild := VExpr.mkApps_getAppFnArgs syntaxTarget
  rw [hspine] at hrebuild
  have hsyntax : syntaxTarget = VExpr.mkApps family indices := by
    rw [← hrebuild]
    simp [family, VExpr.mkApps, List.foldl_append]
  have HsyntaxWF : VExpr.WF R.venv recLparams.length
      R.mlctx.vlctx.toCtx syntaxTarget := by
    rcases HsyntaxType with ⟨level, Htyped⟩
    exact ⟨.sort level, Htyped⟩
  have HfullWF : VExpr.WF R.venv recLparams.length
      R.mlctx.vlctx.toCtx (VExpr.mkApps family indices) := by
    rwa [← hsyntax]
  exact VExpr.WF.mkApps_fn R.checking.tr.wf.ordered
    R.mlctx_wf.tr.wf.toCtx HfullWF

/-- Fill the syntactic half of shared-telescope evidence directly from the
validated terminal payload.  The only remaining inputs are the semantic
typing of the family prefix and its parallel relation to the retained motive
type. -/
theorem RecursorValidatedIndAppAt.motiveTelescopeEvidence
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (H : RecursorValidatedIndAppAt R.venv recLparams R.mlctx.vlctx
      stats decl depth exposedType syntaxTarget target)
    (binding : RecursorMotiveBinding R info elimLevel)
    (familyActualType familyType motiveType : VExpr)
    (resultLevel : VLevel)
    {levels : List VLevel} {params indices : List VExpr}
    (hspine : syntaxTarget.getAppFnArgs =
      (.const (decl.types[target]'H.target_lt).name levels,
        params ++ indices))
    (Hindices : List.Forall₂
      (TrExprS R.venv recLparams R.mlctx.vlctx)
      (exposedType.getAppArgs[stats.params.size:]).toList indices)
    (Hfamily :
      R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
        (VExpr.mkApps
          (.const (decl.types[target]'H.target_lt).name levels) params)
        familyActualType)
    (HfamilyType : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx familyActualType familyType)
    (HmotiveType : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx binding.motiveTypeTarget motiveType)
    (Htelescope :
      RecursorMotiveTelescope resultLevel indices.length
        (VExpr.mkApps
          (.const (decl.types[target]'H.target_lt).name levels) params)
        familyType motiveType) :
    Nonempty (RecursorMotiveTelescopeEvidence R stats info binding
      exposedType syntaxTarget) := by
  let family := VExpr.mkApps
    (.const (decl.types[target]'H.target_lt).name levels) params
  have hrebuild := VExpr.mkApps_getAppFnArgs syntaxTarget
  rw [hspine] at hrebuild
  have hsyntax : syntaxTarget = VExpr.mkApps family indices := by
    rw [← hrebuild]
    simp [family, VExpr.mkApps, List.foldl_append]
  exact ⟨{
    indices := indices
    family := family
    familyActualType := familyActualType
    familyType := familyType
    motiveType := motiveType
    resultLevel := resultLevel
    syntax_eq := hsyntax
    indices_translation := Hindices
    family_typing := Hfamily
    family_type_defeq := HfamilyType
    motive_type_defeq := HmotiveType
    telescope := Htelescope }⟩

/-- Exact-target form of motive application.  Besides typing the result, it
records that the strict translation target is literally the retained motive
local applied to the evidence's index spine and the checked major premise. -/
theorem RecursorMotiveTelescopeEvidence.applyMajorTypedExact
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {elimLevel : Level}
    {info : AddInductive.RecInfo}
    {binding : RecursorMotiveBinding R info elimLevel}
    (H : RecursorMotiveTelescopeEvidence R stats info binding
      exposedType syntaxTarget)
    {major : Expr} {majorTarget : VExpr}
    (Hmajor : TrExprS R.venv recLparams R.mlctx.vlctx major majorTarget)
    (HmajorType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      majorTarget syntaxTarget) :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app (mkAppN info.motive itIndices) major
    let motiveTarget :=
      VExpr.app (VExpr.mkApps binding.motiveTarget H.indices) majorTarget
    TrExprS R.venv recLparams R.mlctx.vlctx motiveApp motiveTarget ∧
      R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
        motiveTarget (.sort H.resultLevel) := by
  have HmajorType' : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx majorTarget (VExpr.mkApps H.family H.indices) := by
    rwa [← H.syntax_eq]
  have Hfamily : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      H.family H.familyType :=
    H.family_typing.defeqU_r R.checking.tr.wf R.mlctx_wf.tr.wf.toCtx
      H.family_type_defeq
  have Hmotive : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      binding.motiveTarget H.motiveType :=
    binding.typing.defeqU_r R.checking.tr.wf R.mlctx_wf.tr.wf.toCtx
      H.motive_type_defeq
  have Hresult := H.telescope.applyMajorTyped R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx Hfamily Hmotive HmajorType'
  let motiveTarget :=
    VExpr.app (VExpr.mkApps binding.motiveTarget H.indices) majorTarget
  have Hresult' : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      motiveTarget (.sort H.resultLevel) := by
    simpa [motiveTarget, VExpr.mkApps, List.foldl_append] using Hresult
  have HtargetWF : VExpr.WF R.venv recLparams.length
      R.mlctx.vlctx.toCtx motiveTarget := ⟨.sort H.resultLevel, Hresult'⟩
  have Hargs := List.Forall₂.append' H.indices_translation
    (.cons Hmajor .nil)
  have Htranslated := checkPositivityStep.TrExprS.mkAppList
    R.checking.tr.wf.ordered
    R.mlctx_wf.tr.wf.toCtx binding.motive Hargs (by
      simpa [motiveTarget, VExpr.mkApps, List.foldl_append] using HtargetWF)
  exact ⟨by
    simpa [motiveTarget, Expr.mkAppN_eq_mkAppList,
      Expr.mkAppList_append, VExpr.mkApps, List.foldl_append] using Htranslated,
    Hresult'⟩

/-- A shared family/motive telescope supplies the complete independently
typed motive application.  The exact result sort is retained for equation
typing; the abstract spine is assembled without invoking executable
inference. -/
theorem RecursorMotiveTelescopeEvidence.applyMajorTyped
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {elimLevel : Level}
    {info : AddInductive.RecInfo}
    {binding : RecursorMotiveBinding R info elimLevel}
    (H : RecursorMotiveTelescopeEvidence R stats info binding
      exposedType syntaxTarget)
    {major : Expr} {majorTarget : VExpr}
    (Hmajor : TrExprS R.venv recLparams R.mlctx.vlctx major majorTarget)
    (HmajorType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      majorTarget syntaxTarget) :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app (mkAppN info.motive itIndices) major
    ∃ motiveTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx motiveApp motiveTarget ∧
      R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx motiveTarget
        (.sort H.resultLevel) := by
  rcases H.applyMajorTypedExact Hmajor HmajorType with ⟨Htr, Htyped⟩
  exact ⟨_, Htr, Htyped⟩

/-- Typehood wrapper around `applyMajorTyped`. -/
theorem RecursorMotiveTelescopeEvidence.applyMajor
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {elimLevel : Level}
    {info : AddInductive.RecInfo}
    {binding : RecursorMotiveBinding R info elimLevel}
    (H : RecursorMotiveTelescopeEvidence R stats info binding
      exposedType syntaxTarget)
    {major : Expr} {majorTarget : VExpr}
    (Hmajor : TrExprS R.venv recLparams R.mlctx.vlctx major majorTarget)
    (HmajorType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      majorTarget syntaxTarget) :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app (mkAppN info.motive itIndices) major
    ∃ motiveTarget,
      TrExprS R.venv recLparams R.mlctx.vlctx motiveApp motiveTarget ∧
      R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx motiveTarget := by
  rcases H.applyMajorTyped Hmajor HmajorType with ⟨target, Htr, Htyped⟩
  exact ⟨target, Htr, H.resultLevel, Htyped⟩

/-- Rooted, context-polymorphic form of the shared telescope evidence.  This
is the invariant established by the first `mkRecInfos` pass; later recursive
field traversals supply only the validated terminal application. -/
def RecursorMotiveTelescopeAt
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : Nat) (info : AddInductive.RecInfo)
    (elimLevel : Level) : Prop :=
  ∀ {current : AddInductive.Context}
    (R : RecursorContextWF current recLparams)
    (_Hext : RecursorContextExtension Rroot R)
    {depth : Nat} {exposedType : Expr} {syntaxTarget : VExpr}
    (binding : RecursorMotiveBinding R info elimLevel),
    TrExprS R.venv recLparams R.mlctx.vlctx exposedType syntaxTarget →
    R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx syntaxTarget →
    RecursorValidatedIndAppAt R.venv recLparams R.mlctx.vlctx stats decl
      depth exposedType syntaxTarget target →
    Nonempty (RecursorMotiveTelescopeEvidence R stats info binding
      exposedType syntaxTarget)

theorem RecursorMotiveTelescopeAt.toApplication
    (H : RecursorMotiveTelescopeAt Rroot stats decl target info elimLevel) :
    RecursorMotiveApplicationAt Rroot stats decl target info elimLevel := by
  intro current R Hext depth exposedType major syntaxTarget
    majorTarget binding Hexposed HsyntaxType Hmajor HmajorType Hvalidated
  rcases H R Hext binding Hexposed HsyntaxType Hvalidated with ⟨Hevidence⟩
  exact Hevidence.applyMajor Hmajor HmajorType

/-- Canonical, permutation-free motive telescope produced while replaying a
family header.  Unlike the executable seed below, this package lives only
under the common parameter domains: later first-pass index/major frames have
not yet been interleaved with sibling motives.  It is therefore the stable
form that can be compared with the grouped generated-recursor telescope. -/
structure RecursorCanonicalMotiveTelescope
    (env : VEnv) (levelParams : List Name)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : Nat) (info : AddInductive.RecInfo)
    (elimLevel : Level) : Type where
  target_lt : target < decl.types.length
  params : List VExpr
  indices : List VExpr
  levels : List VLevel
  family : VExpr
  familyResult : VExpr
  motiveType : VExpr
  resultLevel : VLevel
  params_length : params.length = stats.params.size
  indices_length : indices.length = info.indices.size
  levels_length : levels.length = (decl.types[target]'target_lt).uvars
  levels_wf : ∀ level ∈ levels, level.WF levelParams.length
  levels_translation : stats.levels.mapM (VLevel.ofLevel levelParams) =
    some levels
  family_eq : family = VExpr.mkApps
    ((VExpr.const (decl.types[target]'target_lt).name
      levels).liftN params.length 0)
    (recursorCanonicalVars params.length)
  motiveType_eq : motiveType = VExpr.wrapForalls indices
    (.forallE
      (VExpr.mkApps (family.liftN indices.length 0)
        (recursorCanonicalVars indices.length))
      (.sort resultLevel))
  family_typing : env.HasType levelParams.length params.reverse family
    (VExpr.wrapForalls indices familyResult)
  telescope : RecursorMotiveTelescope resultLevel indices.length family
    (VExpr.wrapForalls indices familyResult) motiveType

def RecursorCanonicalMotiveTelescope.mono
    (H : RecursorCanonicalMotiveTelescope env levelParams stats decl target info
      elimLevel)
    (henv : env ≤ env') :
    RecursorCanonicalMotiveTelescope env' levelParams stats decl target info
      elimLevel where
  target_lt := H.target_lt
  params := H.params
  indices := H.indices
  levels := H.levels
  family := H.family
  familyResult := H.familyResult
  motiveType := H.motiveType
  resultLevel := H.resultLevel
  params_length := H.params_length
  indices_length := H.indices_length
  levels_length := H.levels_length
  levels_wf := H.levels_wf
  levels_translation := H.levels_translation
  family_eq := H.family_eq
  motiveType_eq := H.motiveType_eq
  family_typing := H.family_typing.mono henv
  telescope := H.telescope

/-- A canonical motive telescope remains directly applicable after adding an
arbitrary well-formed inner context.  The family prefix and the parallel
motive type are weakened by the same amount, so a major premise at any
concrete translated index spine yields the exact motive application type. -/
theorem RecursorCanonicalMotiveTelescope.applyMajorTypedAfter
    (C : RecursorCanonicalMotiveTelescope env levelParams stats decl target info
      elimLevel)
    (henv : env.WF) (added : List VExpr)
    (hctx : OnCtx (added.reverse ++ C.params.reverse)
      (env.IsType levelParams.length))
    (indexTargets : List VExpr)
    (hindices : indexTargets.length = C.indices.length)
    (motive major : VExpr)
    (Hmotive : env.HasType levelParams.length
      (added.reverse ++ C.params.reverse) motive
      (C.motiveType.liftN added.length 0))
    (Hmajor : env.HasType levelParams.length
      (added.reverse ++ C.params.reverse) major
      (VExpr.mkApps (C.family.liftN added.length 0) indexTargets)) :
    env.HasType levelParams.length (added.reverse ++ C.params.reverse)
      (.app (VExpr.mkApps motive indexTargets) major)
      (.sort C.resultLevel) := by
  have W : Ctx.LiftN added.length 0 C.params.reverse
      (added.reverse ++ C.params.reverse) := by
    exact .zero added.reverse (by simp)
  have Hfamily := C.family_typing.weakN henv.ordered W
  have Htelescope := C.telescope.liftN added.length 0
  rw [← hindices] at Htelescope
  exact Htelescope.applyMajorTyped henv hctx Hfamily Hmotive Hmajor

/-- Context-converted form of `applyMajorTypedAfter`.  This is the equation
typing interface: the canonical first-pass parameter scope may be replaced
by the cached or generated parameter scope before the common inner binder
block is introduced. -/
theorem RecursorCanonicalMotiveTelescope.applyMajorTypedAfterDefEq
    (C : RecursorCanonicalMotiveTelescope env levelParams stats decl target info
      elimLevel)
    (henv : env.WF) (base added : List VExpr)
    (Hbase : VEnv.IsDefEqCtx env levelParams.length [] C.params.reverse base)
    (hctx : OnCtx (added.reverse ++ base)
      (env.IsType levelParams.length))
    (indexTargets : List VExpr)
    (hindices : indexTargets.length = C.indices.length)
    (motive major : VExpr)
    (Hmotive : env.HasType levelParams.length (added.reverse ++ base) motive
      (C.motiveType.liftN added.length 0))
    (Hmajor : env.HasType levelParams.length (added.reverse ++ base) major
      (VExpr.mkApps (C.family.liftN added.length 0) indexTargets)) :
    env.HasType levelParams.length (added.reverse ++ base)
      (.app (VExpr.mkApps motive indexTargets) major)
      (.sort C.resultLevel) := by
  have HfamilyBase := C.family_typing.defeqDFC henv.ordered Hbase
  have W : Ctx.LiftN added.length 0 base (added.reverse ++ base) := by
    exact .zero added.reverse (by simp)
  have Hfamily := HfamilyBase.weakN henv.ordered W
  have Htelescope := C.telescope.liftN added.length 0
  rw [← hindices] at Htelescope
  exact Htelescope.applyMajorTyped henv hctx Hfamily Hmotive Hmajor

/-- Context-rooted semantic seed for one generated motive.  The first
`mkRecInfos` pass establishes this package at the point where the motive is
introduced.  Its family prefix has unique concrete translation, while the
stored motive type is compared definitionally after later context extension. -/
structure RecursorMotiveTelescopeSeed
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (target : Nat) (info : AddInductive.RecInfo)
    (elimLevel : Level) : Type where
  canonical : RecursorCanonicalMotiveTelescope Rroot.venv recLparams stats
    decl target info elimLevel
  target_lt : target < decl.types.length
  indexCount : info.indices.size =
    (decl.types[target]'target_lt).numIndices
  family : VExpr
  familyActualType : VExpr
  familyType : VExpr
  motiveActualType : VExpr
  motiveType : VExpr
  resultLevel : VLevel
  /-- The exact production motive telescope before it is weakened through
  this family's opened indices, major, and motive declarations.  Keeping
  the closed scope explicit is what permits later inverse weakening to
  discard the interleaved executable frames and return to the cached
  parameter context. -/
  motiveClosedScope : VLCtx
  motiveClosedAmbient : VLCtx
  motiveParameterScope : VLCtx
  motiveClosedContext : motiveClosedScope =
    motiveClosedAmbient ++ motiveParameterScope
  motiveParameterAlignment : VEnv.IsDefEqCtx Rroot.venv
    recLparams.length [] canonical.params.reverse motiveParameterScope.toCtx
  motiveParameterDecls : List.Forall₂
    checkInductiveTypes.loopType.CachedParameterDecl
    stats.params.toList.reverse motiveParameterScope
  /-- The genuine-index front also exposes the narrow scope below those
  indices, together with its literal weakening into the closed executable
  context.  This is the context in which the canonical motive is originally
  synthesized. -/
  motiveSourceScope : VLCtx
  motiveSourceExpanded : VLCtx
  motiveSourceShift : Lift
  motiveSourceAlignment : VEnv.IsDefEqCtx Rroot.venv recLparams.length []
    canonical.params.reverse motiveSourceScope.toCtx
  motiveSourceParameterScope : motiveSourceScope = motiveParameterScope
  motiveSourceLift : VLCtx.FVLift' motiveSourceScope motiveSourceExpanded
    0 motiveSourceShift 0
  motiveSourceContext : VLCtx.IsDefEq Rroot.venv recLparams.length
    motiveSourceExpanded motiveClosedScope
  motiveSourceNoBV : VLCtx.NoBV motiveSourceScope
  motiveSourceFVars : FVarsIn (· ∈ motiveSourceScope.fvars)
    (root.lctx.mkForall info.indices
      (root.lctx.mkForall #[info.major] (.sort elimLevel)))
  motiveClosedTarget : VExpr
  motiveClosedTr : TrExprS Rroot.venv recLparams motiveClosedScope
    (root.lctx.mkForall info.indices
      (root.lctx.mkForall #[info.major] (.sort elimLevel)))
    motiveClosedTarget
  motiveClosedType : Rroot.venv.IsType recLparams.length
    motiveClosedScope.toCtx motiveClosedTarget
  motiveClosedCanonicalTarget : VExpr
  motiveClosedCanonicalEq :
    canonical.motiveType.lift' motiveSourceShift =
      motiveClosedCanonicalTarget
  motiveClosedCanonicalDefEq : Rroot.venv.IsDefEqU recLparams.length
    motiveClosedScope.toCtx motiveClosedTarget motiveClosedCanonicalTarget
  motiveReopenedCanonicalTarget : VExpr
  motiveTypeCanonicalEq : motiveType = motiveReopenedCanonicalTarget
  familyUnique : TrExprS.IsUnique
    (mkAppN stats.indConsts[target]! stats.params)
  familyTr : TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx
    (mkAppN stats.indConsts[target]! stats.params) family
  familyTyping : Rroot.venv.HasType recLparams.length
    Rroot.mlctx.vlctx.toCtx family familyActualType
  familyTypeDefEq : Rroot.venv.IsDefEqU recLparams.length
    Rroot.mlctx.vlctx.toCtx familyActualType familyType
  indicesBound : BoundFVarArray root info.indices
  majorBound : BoundFVarArray root #[info.major]
  motiveTypeTr : TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx
    (root.lctx.mkForall info.indices
      (root.lctx.mkForall #[info.major] (.sort elimLevel))) motiveActualType
  motiveTypeDefEq : Rroot.venv.IsDefEqU recLparams.length
    Rroot.mlctx.vlctx.toCtx motiveActualType motiveType
  telescope : RecursorMotiveTelescope resultLevel info.indices.size
    family familyType motiveType

/-- A motive seed remains valid after later executable frames extend its
root context.  The paired canonical telescope is unchanged, while every
runtime target is weakened by the exact retained recursor-context lift. -/
def RecursorMotiveTelescopeSeed.mono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    (H : RecursorMotiveTelescopeSeed Rroot stats decl target info elimLevel)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    RecursorMotiveTelescopeSeed Rcurrent stats decl target info elimLevel := by
  have hmajorSource :
      current.lctx.mkForall #[info.major] (.sort elimLevel) =
        root.lctx.mkForall #[info.major] (.sort elimLevel) :=
    H.majorBound.mkForall_mono Hext.contextLE _
  have hmotiveSource :
      current.lctx.mkForall info.indices
          (current.lctx.mkForall #[info.major] (.sort elimLevel)) =
        root.lctx.mkForall info.indices
          (root.lctx.mkForall #[info.major] (.sort elimLevel)) := by
    calc
      current.lctx.mkForall info.indices
          (current.lctx.mkForall #[info.major] (.sort elimLevel)) =
          current.lctx.mkForall info.indices
            (root.lctx.mkForall #[info.major] (.sort elimLevel)) :=
        congrArg (fun body => current.lctx.mkForall info.indices body)
          hmajorSource
      _ = root.lctx.mkForall info.indices
            (root.lctx.mkForall #[info.major] (.sort elimLevel)) :=
        H.indicesBound.mkForall_mono Hext.contextLE _
  have HmotiveTypeTr := Hext.weakTrExprS H.motiveTypeTr
  rw [← hmotiveSource] at HmotiveTypeTr
  have HmotiveClosedTr := H.motiveClosedTr
  rw [← hmotiveSource] at HmotiveClosedTr
  exact {
    canonical := H.canonical.mono (by
      rw [Hext.venv_eq]
      exact VEnv.LE.rfl)
    target_lt := H.target_lt
    indexCount := H.indexCount
    family := H.family.lift' (Hext.shift.consN 0)
    familyActualType := H.familyActualType.lift' (Hext.shift.consN 0)
    familyType := H.familyType.lift' (Hext.shift.consN 0)
    motiveActualType := H.motiveActualType.lift' (Hext.shift.consN 0)
    motiveType := H.motiveType.lift' (Hext.shift.consN 0)
    resultLevel := H.resultLevel
    motiveClosedScope := H.motiveClosedScope
    motiveClosedAmbient := H.motiveClosedAmbient
    motiveParameterScope := H.motiveParameterScope
    motiveClosedContext := H.motiveClosedContext
    motiveParameterAlignment := by
      change Rcurrent.venv.IsDefEqCtx recLparams.length []
        H.canonical.params.reverse H.motiveParameterScope.toCtx
      simpa only [Hext.venv_eq] using H.motiveParameterAlignment
    motiveParameterDecls := H.motiveParameterDecls
    motiveSourceScope := H.motiveSourceScope
    motiveSourceExpanded := H.motiveSourceExpanded
    motiveSourceShift := H.motiveSourceShift
    motiveSourceAlignment := by
      change Rcurrent.venv.IsDefEqCtx recLparams.length []
        H.canonical.params.reverse H.motiveSourceScope.toCtx
      simpa only [Hext.venv_eq] using H.motiveSourceAlignment
    motiveSourceParameterScope := H.motiveSourceParameterScope
    motiveSourceLift := H.motiveSourceLift
    motiveSourceContext := by
      simpa only [Hext.venv_eq] using H.motiveSourceContext
    motiveSourceNoBV := H.motiveSourceNoBV
    motiveSourceFVars := by
      rw [hmotiveSource]
      exact H.motiveSourceFVars
    motiveClosedTarget := H.motiveClosedTarget
    motiveClosedTr := by
      simpa only [Hext.venv_eq] using HmotiveClosedTr
    motiveClosedType := by
      simpa only [Hext.venv_eq] using H.motiveClosedType
    motiveClosedCanonicalTarget := H.motiveClosedCanonicalTarget
    motiveClosedCanonicalEq := H.motiveClosedCanonicalEq
    motiveClosedCanonicalDefEq := by
      simpa only [Hext.venv_eq] using H.motiveClosedCanonicalDefEq
    motiveReopenedCanonicalTarget := H.motiveReopenedCanonicalTarget.lift'
      (Hext.shift.consN 0)
    motiveTypeCanonicalEq := congrArg
      (fun target => target.lift' (Hext.shift.consN 0))
      H.motiveTypeCanonicalEq
    familyUnique := H.familyUnique
    familyTr := Hext.weakTrExprS H.familyTr
    familyTyping := Hext.weakHasType H.familyTyping
    familyTypeDefEq := Hext.weakDefEqU H.familyTypeDefEq
    indicesBound := H.indicesBound.mono Hext.contextLE
    majorBound := H.majorBound.mono Hext.contextLE
    motiveTypeTr := HmotiveTypeTr
    motiveTypeDefEq := Hext.weakDefEqU H.motiveTypeDefEq
    telescope := H.telescope.lift' (Hext.shift.consN 0) }

/-- Changing only irrelevant `RecInfo` fields, such as the accumulated minor
array, preserves the paired first-pass seed. -/
def RecursorMotiveTelescopeSeed.congrInfo
    (H : RecursorMotiveTelescopeSeed Rroot stats decl target info elimLevel)
    (hindices : info'.indices = info.indices)
    (hmajor : info'.major = info.major) :
    RecursorMotiveTelescopeSeed Rroot stats decl target info' elimLevel where
  canonical := {
    H.canonical with
    indices_length := by simpa [hindices] using H.canonical.indices_length }
  target_lt := H.target_lt
  indexCount := by simpa [hindices] using H.indexCount
  family := H.family
  familyActualType := H.familyActualType
  familyType := H.familyType
  motiveActualType := H.motiveActualType
  motiveType := H.motiveType
  resultLevel := H.resultLevel
  motiveClosedScope := H.motiveClosedScope
  motiveClosedAmbient := H.motiveClosedAmbient
  motiveParameterScope := H.motiveParameterScope
  motiveClosedContext := H.motiveClosedContext
  motiveParameterAlignment := H.motiveParameterAlignment
  motiveParameterDecls := H.motiveParameterDecls
  motiveSourceScope := H.motiveSourceScope
  motiveSourceExpanded := H.motiveSourceExpanded
  motiveSourceShift := H.motiveSourceShift
  motiveSourceAlignment := H.motiveSourceAlignment
  motiveSourceParameterScope := H.motiveSourceParameterScope
  motiveSourceLift := H.motiveSourceLift
  motiveSourceContext := H.motiveSourceContext
  motiveSourceNoBV := H.motiveSourceNoBV
  motiveSourceFVars := by
    simpa [hindices, hmajor] using H.motiveSourceFVars
  motiveClosedTarget := H.motiveClosedTarget
  motiveClosedTr := by simpa [hindices, hmajor] using H.motiveClosedTr
  motiveClosedType := H.motiveClosedType
  motiveClosedCanonicalTarget := H.motiveClosedCanonicalTarget
  motiveClosedCanonicalEq := H.motiveClosedCanonicalEq
  motiveClosedCanonicalDefEq := H.motiveClosedCanonicalDefEq
  motiveReopenedCanonicalTarget := H.motiveReopenedCanonicalTarget
  motiveTypeCanonicalEq := H.motiveTypeCanonicalEq
  familyUnique := H.familyUnique
  familyTr := H.familyTr
  familyTyping := H.familyTyping
  familyTypeDefEq := H.familyTypeDefEq
  indicesBound := by simpa [hindices] using H.indicesBound
  majorBound := by simpa [hmajor] using H.majorBound
  motiveTypeTr := by simpa [hindices, hmajor] using H.motiveTypeTr
  motiveTypeDefEq := H.motiveTypeDefEq
  telescope := by simpa [hindices] using H.telescope

/-- A first-pass telescope seed supplies the context-polymorphic contract
used by recursive constructor traversal.  Exact context extensions preserve
the seed; unique translation identifies the validated family prefix, and
translation uniqueness relates the later motive binding to the stored
canonical motive telescope. -/
theorem RecursorMotiveTelescopeSeed.toTelescopeAt
    {root : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    (H : RecursorMotiveTelescopeSeed Rroot stats decl target info
      elimLevel) :
    RecursorMotiveTelescopeAt Rroot stats decl target info elimLevel := by
  intro current R Hext depth exposedType syntaxTarget binding Hexposed
    HsyntaxType Hvalidated
  rcases Hvalidated.indices_payload with
    ⟨levels, params, indices, hspine, _hparams, hindicesLength,
      Hindices, HfamilyPayload⟩
  have HfamilyWeak := Hext.weakTrExprS H.familyTr
  have hfamilyEq :
      VExpr.mkApps
          (.const (decl.types[target]'Hvalidated.target_lt).name levels)
          params =
        H.family.lift' (Hext.shift.consN 0) :=
    TrExprS.unique H.familyUnique HfamilyPayload HfamilyWeak
  have HfamilyTyping := Hext.weakHasType H.familyTyping
  have HfamilyTyping' : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx
      (VExpr.mkApps
        (.const (decl.types[target]'Hvalidated.target_lt).name levels)
        params)
      (H.familyActualType.lift' (Hext.shift.consN 0)) := by
    rwa [hfamilyEq]
  have HfamilyTypeDefEq := Hext.weakDefEqU H.familyTypeDefEq
  have Htelescope := H.telescope.lift' (Hext.shift.consN 0)
  have hmajorSource :
      current.lctx.mkForall #[info.major] (.sort elimLevel) =
        root.lctx.mkForall #[info.major] (.sort elimLevel) :=
    H.majorBound.mkForall_mono Hext.contextLE _
  have hmotiveSource :
      current.lctx.mkForall info.indices
          (current.lctx.mkForall #[info.major] (.sort elimLevel)) =
        root.lctx.mkForall info.indices
          (root.lctx.mkForall #[info.major] (.sort elimLevel)) := by
    calc
      current.lctx.mkForall info.indices
          (current.lctx.mkForall #[info.major] (.sort elimLevel)) =
          current.lctx.mkForall info.indices
            (root.lctx.mkForall #[info.major] (.sort elimLevel)) :=
        congrArg (fun body => current.lctx.mkForall info.indices body)
          hmajorSource
      _ = root.lctx.mkForall info.indices
            (root.lctx.mkForall #[info.major] (.sort elimLevel)) :=
        H.indicesBound.mkForall_mono Hext.contextLE _
  have HmotiveWeak := Hext.weakTrExprS H.motiveTypeTr
  rw [← hmotiveSource] at HmotiveWeak
  have HbindingActual : R.venv.IsDefEqU recLparams.length
      R.mlctx.vlctx.toCtx binding.motiveTypeTarget
      (H.motiveActualType.lift' (Hext.shift.consN 0)) :=
    (HmotiveWeak.uniq R.checking.tr.wf
      (.refl R.checking.tr.wf R.mlctx_wf.tr.wf)
      binding.motiveType).symm
  have HmotiveDefEq := HbindingActual.trans R.checking.tr.wf
    R.mlctx_wf.tr.wf.toCtx (Hext.weakDefEqU H.motiveTypeDefEq)
  have Htelescope' : RecursorMotiveTelescope H.resultLevel indices.length
      (VExpr.mkApps
        (.const (decl.types[target]'Hvalidated.target_lt).name levels)
        params)
      (H.familyType.lift' (Hext.shift.consN 0))
      (H.motiveType.lift' (Hext.shift.consN 0)) := by
    rw [hfamilyEq, hindicesLength, ← H.indexCount]
    simpa using Htelescope
  exact Hvalidated.motiveTelescopeEvidence binding
    (H.familyActualType.lift' (Hext.shift.consN 0))
    (H.familyType.lift' (Hext.shift.consN 0))
    (H.motiveType.lift' (Hext.shift.consN 0)) H.resultLevel hspine Hindices
    HfamilyTyping' HfamilyTypeDefEq HmotiveDefEq Htelescope'

/-- The motive-telescope contract is insensitive to the minor array stored
beside the motive, indices, and major.  This extensional form is useful for
the in-place record updates performed by the second `mkRecInfos` pass. -/
theorem RecursorMotiveTelescopeAt.congrInfo
    (H : RecursorMotiveTelescopeAt Rroot stats decl target info elimLevel)
    (hmotive : info'.motive = info.motive)
    (hindices : info'.indices = info.indices)
    (hmajor : info'.major = info.major) :
    RecursorMotiveTelescopeAt Rroot stats decl target info' elimLevel := by
  intro current R Hext depth exposedType syntaxTarget binding' Hexposed
    HsyntaxType Hvalidated
  let binding : RecursorMotiveBinding R info elimLevel := {
    motiveTarget := binding'.motiveTarget
    motiveTypeTarget := binding'.motiveTypeTarget
    motive := by simpa [hmotive] using binding'.motive
    motiveType := by simpa [hindices, hmajor] using binding'.motiveType
    typing := binding'.typing
    typeIsType := binding'.typeIsType }
  rcases H R Hext binding Hexposed HsyntaxType Hvalidated with ⟨Hevidence⟩
  exact ⟨{
    indices := Hevidence.indices
    family := Hevidence.family
    familyActualType := Hevidence.familyActualType
    familyType := Hevidence.familyType
    motiveType := Hevidence.motiveType
    resultLevel := Hevidence.resultLevel
    syntax_eq := Hevidence.syntax_eq
    indices_translation := Hevidence.indices_translation
    family_typing := Hevidence.family_typing
    family_type_defeq := Hevidence.family_type_defeq
    motive_type_defeq := Hevidence.motive_type_defeq
    telescope := Hevidence.telescope }⟩

/-- Pointwise shared family/motive telescopes for a completed mutual record
array.  This is stronger and easier to establish than storing applications
for arbitrary majors directly. -/
structure RecInfoMotiveTelescopes
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (parameterCtx : List VExpr)
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level) : Prop where
  telescope : ∀ target (htarget : target < recInfos.size),
    RecursorMotiveTelescopeAt Rroot stats decl target recInfos[target]!
      elimLevel
  seed : ∀ target (htarget : target < recInfos.size),
    ∃ S : RecursorMotiveTelescopeSeed Rroot stats decl target
        recInfos[target]! elimLevel,
      VEnv.IsDefEqCtx Rroot.venv recLparams.length []
        S.canonical.params.reverse parameterCtx
  canonical : ∀ target (htarget : target < recInfos.size),
    ∃ C : RecursorCanonicalMotiveTelescope Rroot.venv recLparams stats
        decl target recInfos[target]! elimLevel,
      VEnv.IsDefEqCtx Rroot.venv recLparams.length []
        C.params.reverse parameterCtx

def RecInfoMotiveTelescopes.empty
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (parameterCtx : List VExpr)
    (elimLevel : Level) :
    RecInfoMotiveTelescopes Rroot stats decl parameterCtx #[] elimLevel where
  telescope target htarget := by simp at htarget
  seed target htarget := by simp at htarget
  canonical target htarget := by simp at htarget

def RecInfoMotiveTelescopes.mono
    (H : RecInfoMotiveTelescopes Rroot stats decl parameterCtx recInfos
      elimLevel)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    RecInfoMotiveTelescopes Rcurrent stats decl parameterCtx recInfos
      elimLevel where
  telescope target htarget := fun R Hlater =>
    H.telescope target htarget R (Hext.trans Hlater)
  seed target htarget := by
    rcases H.seed target htarget with ⟨S, hparams⟩
    refine ⟨S.mono Hext, ?_⟩
    simpa [RecursorMotiveTelescopeSeed.mono,
      RecursorCanonicalMotiveTelescope.mono, Hext.venv_eq] using hparams
  canonical target htarget := by
    rw [Hext.venv_eq]
    exact H.canonical target htarget

def RecInfoMotiveTelescopes.push
    {root : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    (H : RecInfoMotiveTelescopes Rroot stats decl parameterCtx recInfos
      elimLevel)
    (next : AddInductive.RecInfo)
    (Hnext : RecursorMotiveTelescopeAt Rroot stats decl recInfos.size next
      elimLevel)
    (Hseed : RecursorMotiveTelescopeSeed Rroot stats decl recInfos.size next
      elimLevel)
    (Hparams :
      VEnv.IsDefEqCtx Rroot.venv recLparams.length []
        Hseed.canonical.params.reverse parameterCtx) :
    RecInfoMotiveTelescopes Rroot stats decl parameterCtx (recInfos.push next)
      elimLevel where
  telescope target htarget := by
    by_cases hlast : target = recInfos.size
    · subst target
      have hget : (recInfos.push next)[recInfos.size]! = next := by simp
      rw [hget]
      exact Hnext
    · have hold : target < recInfos.size := by
        simp only [Array.size_push] at htarget
        omega
      have hget : (recInfos.push next)[target]! = recInfos[target]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos htarget, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hget]
      exact H.telescope target hold
  seed target htarget := by
    by_cases hlast : target = recInfos.size
    · subst target
      have hget : (recInfos.push next)[recInfos.size]! = next := by simp
      rw [hget]
      exact ⟨Hseed, Hparams⟩
    · have hold : target < recInfos.size := by
        simp only [Array.size_push] at htarget
        omega
      have hget : (recInfos.push next)[target]! = recInfos[target]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos htarget, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hget]
      exact H.seed target hold
  canonical target htarget := by
    by_cases hlast : target = recInfos.size
    · subst target
      have hget : (recInfos.push next)[recInfos.size]! = next := by simp
      rw [hget]
      exact ⟨Hseed.canonical, Hparams⟩
    · have hold : target < recInfos.size := by
        simp only [Array.size_push] at htarget
        omega
      have hget : (recInfos.push next)[target]! = recInfos[target]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos htarget, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hget]
      exact H.canonical target hold

/-- Adding a minor premise does not change any family's motive telescope.
The executable second pass updates `RecInfo.minors` in place; making this
transport explicit keeps the first-pass semantic contract available after
every constructor. -/
def RecInfoMotiveTelescopes.modifyMinors
    (H : RecInfoMotiveTelescopes Rroot stats decl parameterCtx recInfos
      elimLevel)
    (owner : Nat) (f : Array Expr → Array Expr) :
    RecInfoMotiveTelescopes Rroot stats decl parameterCtx
      (recInfos.modify owner fun info =>
        { info with minors := f info.minors }) elimLevel where
  telescope target htarget := by
    have hold : target < recInfos.size := by simpa using htarget
    apply RecursorMotiveTelescopeAt.congrInfo (H.telescope target hold)
    all_goals
      by_cases howner : owner = target
      · subst target
        rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos owner _ hold]
      · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos owner target _
            hold howner]
  seed target htarget := by
    have hold : target < recInfos.size := by simpa using htarget
    rcases H.seed target hold with ⟨S, hparams⟩
    by_cases howner : owner = target
    · subst target
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos owner _ hold]
      refine ⟨S.congrInfo rfl rfl, ?_⟩
      simpa [RecursorMotiveTelescopeSeed.congrInfo] using hparams
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos owner target _
            hold howner]
      exact ⟨S, hparams⟩
  canonical target htarget := by
    have hold : target < recInfos.size := by simpa using htarget
    rcases H.canonical target hold with ⟨C, hparams⟩
    by_cases howner : owner = target
    · subst target
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos owner _ hold]
      exact ⟨{ C with indices_length := by simpa using C.indices_length },
        hparams⟩
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos owner target _
          hold howner]
      exact ⟨C, hparams⟩

/-- Pointwise motive-application contracts for the complete mutual `RecInfo`
array.  Array indexing, rather than family names, is intentional: production
selects motives with the target returned by `isValidIndApp?`, and the
validated application certificate proves that the same target denotes the
independent source family. -/
structure RecInfoMotiveApplications
    {root : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (recInfos : Array AddInductive.RecInfo) (elimLevel : Level) : Prop where
  application : ∀ target (htarget : target < recInfos.size),
    RecursorMotiveApplicationAt Rroot stats decl target recInfos[target]!
      elimLevel

def RecInfoMotiveApplications.empty
    (Rroot : RecursorContextWF root recLparams)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (elimLevel : Level) :
    RecInfoMotiveApplications Rroot stats decl #[] elimLevel where
  application target htarget := by simp at htarget

/-- Re-root every existing contract at a later production context.  A use
still has to provide an extension of the new root; composing inclusions shows
that it is also a legitimate use of the original contract. -/
def RecInfoMotiveApplications.mono
    (H : RecInfoMotiveApplications Rroot stats decl recInfos elimLevel)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    RecInfoMotiveApplications Rcurrent stats decl recInfos elimLevel where
  application target htarget := fun R Hlater =>
    H.application target htarget R (Hext.trans Hlater)

/-- Extend the pointwise motive contract in lockstep with the first mutual
pass.  Earlier contracts are definitionally unchanged by `Array.push`; only
the newly generated frame needs a fresh semantic application proof. -/
def RecInfoMotiveApplications.push
    (H : RecInfoMotiveApplications Rroot stats decl recInfos elimLevel)
    (next : AddInductive.RecInfo)
    (Hnext : RecursorMotiveApplicationAt Rroot stats decl recInfos.size next
      elimLevel) :
    RecInfoMotiveApplications Rroot stats decl (recInfos.push next)
      elimLevel where
  application target htarget := by
    by_cases hlast : target = recInfos.size
    · subst target
      have hget : (recInfos.push next)[recInfos.size]! = next := by simp
      rw [hget]
      exact Hnext
    · have hold : target < recInfos.size := by
        simp only [Array.size_push] at htarget
        omega
      have hget : (recInfos.push next)[target]! = recInfos[target]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos htarget, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hget]
      exact H.application target hold

def RecInfoMotiveTelescopes.applications
    (H : RecInfoMotiveTelescopes Rroot stats decl parameterCtx recInfos
      elimLevel) :
    RecInfoMotiveApplications Rroot stats decl recInfos elimLevel where
  application target htarget :=
    RecursorMotiveTelescopeAt.toApplication (H.telescope target htarget)

/-- Semantic lookup package for one generated major premise and its exact
family-application declaration type. -/
structure RecursorMajorBindingAt
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) (target : Nat) : Type where
  target_lt : target < recInfos.size
  majorTarget : VExpr
  majorTypeTarget : VExpr
  major : TrExprS R.venv recLparams R.mlctx.vlctx
    recInfos[target]!.major majorTarget
  majorType : TrExprS R.venv recLparams R.mlctx.vlctx
    ((mkAppN (mkAppN stats.indConsts[target]! stats.params)
      recInfos[target]!.indices).consumeTypeAnnotations) majorTypeTarget
  typing : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
    majorTarget majorTypeTarget
  typeIsType : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx
    majorTypeTarget

/-- Recover a generated major premise from its retained binding and exact
positional family-application origin. -/
theorem RecInfoMajorTypeShapes.majorBindingAt
    (R : RecursorContextWF c recLparams)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hshape : RecInfoMajorTypeShapes stats recInfos Horigins.majorTypes)
    (target : Nat) (htarget : target < recInfos.size) :
    Nonempty (RecursorMajorBindingAt R stats recInfos target) := by
  have htargetMap : target < (recInfos.map (·.major)).size := by
    simpa using htarget
  rcases Hbindings.majors.declarationAt R.toBindingContextWF target
      htargetMap with ⟨D⟩
  have hmajor : recInfos[target]!.major = .fvar D.fvar := by
    have h := D.expression
    simpa [Array.getElem!_eq_getD, Array.getD, htarget] using h
  have htype : D.type =
      (mkAppN (mkAppN stats.indConsts[target]! stats.params)
        recInfos[target]!.indices).consumeTypeAnnotations :=
    (Horigins.majors.type_eq D).trans (Hshape.shape target htarget)
  have hfind := D.declaration
  rw [R.toBindingContextWF.wf.find?_eq_find?_toList] at hfind
  have hmember : (.cdecl D.index D.fvar D.userName D.type
      D.binderInfo D.kind) ∈ c.lctx.toList :=
    List.mem_of_find?_eq_some hfind
  have hmember' : (.cdecl D.index D.fvar D.userName D.type
      D.binderInfo D.kind) ∈ R.mlctx.lctx.toList := by
    rw [R.lctx_eq]
    exact hmember
  rcases R.mlctx_wf.tr.find?_of_mem R.checking.tr.wf hmember' with
    ⟨majorTarget, majorTypeTarget, hlookup, _hvalueBelow,
      _htypeBelow, hmajorTr, hmajorTypeTr⟩
  have hmajorTyping := R.mlctx_wf.tr.wf.find?_wf
    R.checking.tr.wf.ordered hlookup
  refine ⟨{
    target_lt := htarget
    majorTarget := majorTarget
    majorTypeTarget := majorTypeTarget
    major := ?_
    majorType := ?_
    typing := hmajorTyping
    typeIsType := hmajorTyping.isType R.checking.tr.wf
      R.mlctx_wf.tr.wf.toCtx }⟩
  · simpa [Lean.LocalDecl.value', hmajor] using hmajorTr
  · rw [← htype]
    simpa only [Lean.LocalDecl.type] using hmajorTypeTr

/-- Recover one motive's complete semantic lookup package from the binding,
origin, and telescope-shape invariants retained by the first mutual pass. -/
theorem RecInfoMotiveTypeShapes.motiveBindingAt
    (R : RecursorContextWF c recLparams)
    (Hbindings : RecInfoBindings c recInfos)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (Hshape : RecInfoMotiveTypeShapes c recInfos
      Horigins.motiveTypes elimLevel)
    (target : Nat) (htarget : target < recInfos.size) :
    Nonempty (RecursorMotiveBindingAt R recInfos target elimLevel) := by
  have htargetMap : target < (recInfos.map (·.motive)).size := by
    simpa using htarget
  rcases Hbindings.motives.declarationAt R.toBindingContextWF target
      htargetMap with ⟨D⟩
  have hmotive : recInfos[target]!.motive = .fvar D.fvar := by
    have h := D.expression
    simpa [Array.getElem!_eq_getD, Array.getD, htarget] using h
  have htype : D.type =
      c.lctx.mkForall recInfos[target]!.indices
        (c.lctx.mkForall #[recInfos[target]!.major] (.sort elimLevel)) :=
    (Horigins.motives.type_eq D).trans (Hshape.shape target htarget)
  have hfind := D.declaration
  rw [R.toBindingContextWF.wf.find?_eq_find?_toList] at hfind
  have hmember : (.cdecl D.index D.fvar D.userName D.type
      D.binderInfo D.kind) ∈ c.lctx.toList :=
    List.mem_of_find?_eq_some hfind
  have hmember' : (.cdecl D.index D.fvar D.userName D.type
      D.binderInfo D.kind) ∈ R.mlctx.lctx.toList := by
    rw [R.lctx_eq]
    exact hmember
  rcases R.mlctx_wf.tr.find?_of_mem R.checking.tr.wf hmember' with
    ⟨motiveTarget, motiveTypeTarget, hlookup, _hvalueBelow,
      _htypeBelow, hmotiveTr, hmotiveTypeTr⟩
  have hmotiveTyping := R.mlctx_wf.tr.wf.find?_wf
    R.checking.tr.wf.ordered hlookup
  refine ⟨{
    target_lt := htarget
    motiveTarget := motiveTarget
    motiveTypeTarget := motiveTypeTarget
    motive := ?_
    motiveType := ?_
    typing := hmotiveTyping
    typeIsType := hmotiveTyping.isType R.checking.tr.wf
      R.mlctx_wf.tr.wf.toCtx }⟩
  · simpa [Lean.LocalDecl.value', hmotive] using hmotiveTr
  · simpa [Lean.LocalDecl.type, htype] using hmotiveTypeTr

def RecInfoMotiveTypeShapes.empty (c : AddInductive.Context)
    (elimLevel : Level) :
    RecInfoMotiveTypeShapes c #[] #[] elimLevel where
  size_eq := rfl
  shape i hi := by simp at hi

/-- Row-wise inverse image of one declaration in production's flattened
minor array.  It records the mutual-family owner, the constructor-local
position, and the exact type used when that minor premise was introduced. -/
structure RecInfoTypeOrigins.FlatMinorOrigin
    (H : RecInfoTypeOrigins c recInfos)
    (D : BoundFVarDeclarationAt c (recInfos.flatMap (·.minors)) i) where
  owner : Nat
  owner_lt : owner < recInfos.size
  localIndex : Nat
  local_lt : localIndex < recInfos[owner].minors.size
  declaration : BoundFVarDeclarationAt c recInfos[owner].minors localIndex
  expression_eq : recInfos[owner].minors[localIndex]'local_lt =
    (recInfos.flatMap (·.minors))[i]'D.inBounds
  originType_eq : D.type = H.minorTypes[owner]![localIndex]!

/-- Every flattened minor declaration comes from an actual owner row.  The
proof follows the executable `Array.flatMap` membership, then uses local
declaration uniqueness to connect the row certificate to the flattened
witness. -/
theorem RecInfoTypeOrigins.flatMinorOrigin
    (H : RecInfoTypeOrigins c recInfos)
    (D : BoundFVarDeclarationAt c (recInfos.flatMap (·.minors)) i) :
    Nonempty (H.FlatMinorOrigin D) := by
  have hmember : Expr.fvar D.fvar ∈ recInfos.flatMap (·.minors) := by
    rw [← D.expression]
    exact Array.getElem_mem D.inBounds
  rcases Array.mem_flatMap.mp hmember with ⟨info, hinfo, hminor⟩
  rcases Array.mem_iff_getElem.mp hinfo with ⟨owner, howner, hinfoEq⟩
  rcases Array.mem_iff_getElem.mp hminor with
    ⟨localIndex, hlocal, hlocalEq⟩
  subst info
  have hinfoBang : recInfos[owner]! = recInfos[owner] := by
    simp [Array.getElem!_eq_getD, Array.getD, howner]
  have Hrow : BoundFVarTypeOrigins c recInfos[owner].minors
      H.minorTypes[owner]! := by
    simpa only [hinfoBang] using H.minors owner howner
  rcases Hrow.declaration localIndex hlocal with
    ⟨E, htype⟩
  have hexpression : recInfos[owner].minors[localIndex]'hlocal =
      (recInfos.flatMap (·.minors))[i]'D.inBounds :=
    hlocalEq.trans D.expression.symm
  exact ⟨{
    owner := owner
    owner_lt := howner
    localIndex := localIndex
    local_lt := hlocal
    declaration := E
    expression_eq := hexpression
    originType_eq := (D.type_eq_of_expression E hexpression.symm).trans htype }⟩

def RecInfoBindings.flatMinors
    (H : RecInfoBindings c recInfos) :
    BoundFVarArray c (recInfos.flatMap (·.minors)) where
  fvars := (List.ofFn fun i : Fin recInfos.size =>
    (H.minors i i.isLt).fvars).flatten
  expressions := by
    rw [← Array.toList_inj]
    simp only [Array.toList_flatMap, List.map_flatten]
    rw [← List.ofFn_getElem (xs := recInfos.toList)]
    apply congrArg List.flatten
    simp only [List.map_ofFn]
    apply List.ext_get
    · simp
    · intro n hleft hright
      have hn : n < recInfos.size := by simpa using hleft
      simpa [Array.getElem!_eq_getD, Array.getD, hn] using
        congrArg Array.toList (H.minors n hn).expressions
  members := by
    intro fv hfv
    simp only [List.mem_flatten, List.mem_ofFn] at hfv
    rcases hfv with ⟨fvs, ⟨i, rfl⟩, hfv⟩
    exact (H.minors i i.isLt).members fv hfv

def RecInfoBindings.flatIndices
    (H : RecInfoBindings c recInfos) :
    BoundFVarArray c (recInfos.flatMap (·.indices)) where
  fvars := (List.ofFn fun i : Fin recInfos.size =>
    (H.indices i i.isLt).fvars).flatten
  expressions := by
    rw [← Array.toList_inj]
    simp only [Array.toList_flatMap, List.map_flatten]
    rw [← List.ofFn_getElem (xs := recInfos.toList)]
    apply congrArg List.flatten
    simp only [List.map_ofFn]
    apply List.ext_get
    · simp
    · intro n hleft hright
      have hn : n < recInfos.size := by simpa using hleft
      simpa [Array.getElem!_eq_getD, Array.getD, hn] using
        congrArg Array.toList (H.indices n hn).expressions
  members := by
    intro fv hfv
    simp only [List.mem_flatten, List.mem_ofFn] at hfv
    rcases hfv with ⟨fvs, ⟨i, rfl⟩, hfv⟩
    exact (H.indices i i.isLt).members fv hfv

/-- All binder identities retained for recursor generation, in the category
order used by the generated telescope. Keeping this global list distinct is
stronger than the per-owner fact needed by any one recursor. -/
def RecInfoBindings.allFvars
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params) : List FVarId :=
  ExprArrayFVarIds stats.params ++
    (ExprArrayFVarIds (recInfos.map (·.motive)) ++
      (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++
        (ExprArrayFVarIds (recInfos.flatMap (·.indices)) ++
          ExprArrayFVarIds (recInfos.map (·.major)))))

theorem RecInfoBindings.allFvars_eq
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params) :
    H.allFvars Hparams =
      Hparams.fvars ++
        (H.motives.fvars ++
          (H.flatMinors.fvars ++ (H.flatIndices.fvars ++ H.majors.fvars))) := by
  unfold RecInfoBindings.allFvars
  rw [Hparams.exprArrayFVarIds, H.motives.exprArrayFVarIds,
    H.flatMinors.exprArrayFVarIds, H.flatIndices.exprArrayFVarIds,
    H.majors.exprArrayFVarIds]

def RecInfoBindings.NoAlias
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params) : Prop :=
  (H.allFvars Hparams).Nodup

theorem RecInfoBindings.allFvars_members
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params) :
    ∀ fv ∈ H.allFvars Hparams, fv ∈ c.lctx.fvars := by
  intro fv hfv
  rw [H.allFvars_eq Hparams] at hfv
  simp only [List.mem_append] at hfv
  rcases hfv with hp | hm | hmi | hi | hma
  · exact Hparams.members fv hp
  · exact H.motives.members fv hm
  · exact H.flatMinors.members fv hmi
  · exact H.flatIndices.members fv hi
  · exact H.majors.members fv hma

theorem RecInfoBindings.outerNodup
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : H.NoAlias Hparams) :
    ((Hparams.fvars ++ H.motives.fvars) ++
      H.flatMinors.fvars).Nodup := by
  have hsub : ((Hparams.fvars ++ H.motives.fvars) ++
      H.flatMinors.fvars) <+ H.allFvars Hparams := by
    rw [H.allFvars_eq Hparams]
    simpa [List.append_assoc] using
      ((List.Sublist.refl Hparams.fvars).append
        ((List.Sublist.refl H.motives.fvars).append
          ((List.Sublist.refl H.flatMinors.fvars).append
            (List.nil_sublist _))))
  exact hnoalias.sublist hsub

/-- The outer binders selected by the generated recursor telescope occur in
their category order inside the executable local context.  Local contexts
store newest declarations first, hence the reversal.  This operational fact
is deliberately separate from `NoAlias`: membership and distinctness alone
do not determine binder order when indices and majors are interleaved. -/
def RecInfoOuterOrder
    {stats : AddInductive.InductiveStats}
    (R : RecursorContextWF c recLparams)
    (Hparams : BoundFVarArray c stats.params)
    (Hbindings : RecInfoBindings c recInfos) : Prop :=
  (Hparams.fvars ++ Hbindings.motives.fvars ++
    Hbindings.flatMinors.fvars).reverse <+ R.mlctx.vlctx.fvars

def RecInfoBindings.major
    (H : RecInfoBindings c recInfos) (i : Nat) (hi : i < recInfos.size) :
    BoundFVarArray c #[recInfos[i]!.major] := by
  have hsize : H.majors.fvars.length = recInfos.size := by
    have h := congrArg Array.size H.majors.expressions
    simpa using h.symm
  let fv := H.majors.fvars[i]'(by simpa [hsize] using hi)
  refine {
    fvars := [fv]
    expressions := ?_
    members := ?_
  }
  · apply congrArg (fun e => #[e])
    have hget := congrArg (fun xs => xs[i]!) H.majors.expressions
    simpa [fv, Array.getElem!_eq_getD, Array.getD, hi, hsize] using hget
  · intro fv' hfv'
    simp only [List.mem_singleton] at hfv'
    subst fv'
    exact H.majors.members fv (List.getElem_mem (by simpa [hsize] using hi))

/-- Motive telescope shapes are stable under verified local-context
extension because all selected index and major declarations retain their
original declaration data. -/
def RecInfoMotiveTypeShapes.mono
    (H : RecInfoMotiveTypeShapes c recInfos motiveTypes elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (hle : BindingContextLE c c') :
    RecInfoMotiveTypeShapes c' recInfos motiveTypes elimLevel where
  size_eq := H.size_eq
  shape i hi := by
    let Hindices := Hbindings.indices i hi
    let Hmajor := Hbindings.major i hi
    calc
      motiveTypes[i]! =
          c.lctx.mkForall recInfos[i]!.indices
            (c.lctx.mkForall #[recInfos[i]!.major] (.sort elimLevel)) :=
        H.shape i hi
      _ = c'.lctx.mkForall recInfos[i]!.indices
            (c.lctx.mkForall #[recInfos[i]!.major] (.sort elimLevel)) :=
        (Hindices.mkForall_mono hle _).symm
      _ = c'.lctx.mkForall recInfos[i]!.indices
            (c'.lctx.mkForall #[recInfos[i]!.major] (.sort elimLevel)) := by
        rw [Hmajor.mkForall_mono hle]

/-- Append one newly constructed motive telescope while weakening every
earlier family shape into the final frame context. -/
def RecInfoMotiveTypeShapes.push
    (H : RecInfoMotiveTypeShapes c recInfos motiveTypes elimLevel)
    (Hbindings : RecInfoBindings c recInfos)
    (hle : BindingContextLE c c')
    (info : AddInductive.RecInfo) (motiveType : Expr)
    (hnew : motiveType =
      c'.lctx.mkForall info.indices
        (c'.lctx.mkForall #[info.major] (.sort elimLevel))) :
    RecInfoMotiveTypeShapes c' (recInfos.push info)
      (motiveTypes.push motiveType) elimLevel where
  size_eq := by simpa using H.size_eq
  shape i hi := by
    by_cases hold : i < recInfos.size
    · have hmotives : i < motiveTypes.size := by
        rw [H.size_eq]
        exact hold
      have hmotivesPush : (motiveTypes.push motiveType)[i]! =
          motiveTypes[i]! := by
        have hmotivesPushBounds : i < (motiveTypes.push motiveType).size := by
          simp only [Array.size_push]
          omega
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hmotivesPushBounds, dif_pos hmotives]
        exact Array.getElem_push_lt hmotives
      have hinfoPush : (recInfos.push info)[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hold]
        exact Array.getElem_push_lt hold
      rw [hmotivesPush, hinfoPush]
      exact (H.mono Hbindings hle).shape i hold
    · have hieq : i = recInfos.size := by
        simp only [Array.size_push] at hi
        omega
      subst i
      have hmotivesPush :
          (motiveTypes.push motiveType)[recInfos.size]! = motiveType := by
        rw [show recInfos.size = motiveTypes.size from H.size_eq.symm]
        simp
      have hinfoPush : (recInfos.push info)[recInfos.size]! = info := by
        simp
      rw [hmotivesPush, hinfoPush]
      exact hnew

/-- The five executable binder groups used to build one production recursor
type, all selected from the same retained local context. -/
structure RecursorLocalSelections (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) (ownerIdx : Nat) where
  params : LocalForallSelection c.lctx stats.params
  motives : LocalForallSelection c.lctx (recInfos.map (·.motive))
  minors : LocalForallSelection c.lctx (recInfos.flatMap (·.minors))
  indices : LocalForallSelection c.lctx recInfos[ownerIdx]!.indices
  major : LocalForallSelection c.lctx #[recInfos[ownerIdx]!.major]

def RecursorLocalSelections.allFvars
    (H : RecursorLocalSelections c stats recInfos ownerIdx) : List FVarId :=
  H.params.fvars ++
    (H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)))

def RecursorLocalSelections.NoAlias
    (H : RecursorLocalSelections c stats recInfos ownerIdx) : Prop :=
  H.allFvars.Nodup

structure RecursorLocalSelections.NoAliasParts
    (H : RecursorLocalSelections c stats recInfos ownerIdx) : Prop where
  params : H.params.fvars.Nodup
  motives : H.motives.fvars.Nodup
  minors : H.minors.fvars.Nodup
  indices : H.indices.fvars.Nodup
  major : H.major.fvars.Nodup
  params_later : ∀ fv ∈ H.params.fvars,
    ∀ fv' ∈ H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)), fv ≠ fv'
  motives_later : ∀ fv ∈ H.motives.fvars,
    ∀ fv' ∈ H.minors.fvars ++
      (H.indices.fvars ++ H.major.fvars), fv ≠ fv'
  minors_later : ∀ fv ∈ H.minors.fvars,
    ∀ fv' ∈ H.indices.fvars ++ H.major.fvars, fv ≠ fv'
  indices_major : ∀ fv ∈ H.indices.fvars,
    ∀ fv' ∈ H.major.fvars, fv ≠ fv'

theorem RecursorLocalSelections.NoAlias.parts
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (h : H.NoAlias) : H.NoAliasParts := by
  unfold RecursorLocalSelections.NoAlias
    RecursorLocalSelections.allFvars at h
  rcases List.nodup_append.mp h with ⟨hp, hrest, hpLater⟩
  rcases List.nodup_append.mp hrest with ⟨hm, hrest, hmLater⟩
  rcases List.nodup_append.mp hrest with ⟨hmi, hrest, hmiLater⟩
  rcases List.nodup_append.mp hrest with ⟨hi, hma, hiMajor⟩
  exact ⟨hp, hm, hmi, hi, hma, hpLater, hmLater, hmiLater, hiMajor⟩

def RecInfoBindings.toRecursorLocalSelections
    (H : RecInfoBindings c recInfos) (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (ownerIdx : Nat) (howner : ownerIdx < recInfos.size) :
    RecursorLocalSelections c stats recInfos ownerIdx where
  params := Hparams.toLocalForallSelection Hc
  motives := H.motives.toLocalForallSelection Hc
  minors := H.flatMinors.toLocalForallSelection Hc
  indices := (H.indices ownerIdx howner).toLocalForallSelection Hc
  major := (H.major ownerIdx howner).toLocalForallSelection Hc

theorem RecInfoBindings.selectionNoAlias
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos) (Hc : BindingContextWF c)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : H.NoAlias Hparams)
    (ownerIdx : Nat) (howner : ownerIdx < recInfos.size) :
    (H.toRecursorLocalSelections Hc Hparams ownerIdx howner).NoAlias := by
  let rows := List.ofFn fun i : Fin recInfos.size =>
    (H.indices i i.isLt).fvars
  have hrowMem : (H.indices ownerIdx howner).fvars ∈ rows := by
    simp only [rows, List.mem_ofFn]
    exact ⟨⟨ownerIdx, howner⟩, rfl⟩
  have hindices : (H.indices ownerIdx howner).fvars <+
      H.flatIndices.fvars := by
    exact List.sublist_flatten_of_mem hrowMem
  have hmajor : (H.major ownerIdx howner).fvars <+ H.majors.fvars := by
    have himap : ownerIdx < (recInfos.map (·.major)).size := by
      simpa using howner
    let Hget := H.majors.get ownerIdx himap
    have heq : #[recInfos[ownerIdx]!.major] =
        #[(recInfos.map (·.major))[ownerIdx]] := by
      simp [Array.getElem!_eq_getD, Array.getD, howner]
    rw [BoundFVarArray.fvars_eq (H.major ownerIdx howner) Hget heq]
    exact BoundFVarArray.get_fvars_sublist _ _ _
  have hsub :
      Hparams.fvars ++
        (H.motives.fvars ++
          (H.flatMinors.fvars ++
            ((H.indices ownerIdx howner).fvars ++
              (H.major ownerIdx howner).fvars))) <+
      H.allFvars Hparams :=
    H.allFvars_eq Hparams ▸
      ((List.Sublist.refl Hparams.fvars).append <|
        (List.Sublist.refl H.motives.fvars).append <|
          (List.Sublist.refl H.flatMinors.fvars).append <|
            hindices.append hmajor)
  apply hnoalias.sublist hsub

/-- The replayed index telescope of every accumulated recursor frame has the
arity recorded by the checked inductive header. -/
def RecInfoArities (stats : AddInductive.InductiveStats)
    (recInfos : Array AddInductive.RecInfo) : Prop :=
  ∀ i, i < recInfos.size →
    recInfos[i]!.indices.size = stats.nindices[i]!

theorem RecInfoArities.empty (stats : AddInductive.InductiveStats) :
    RecInfoArities stats #[] := by
  intro i hi
  simp at hi

theorem RecInfoArities.push
    (H : RecInfoArities stats recInfos)
    (hnew : indices.size = stats.nindices[recInfos.size]!) :
    RecInfoArities stats (recInfos.push {
      motive, minors := #[], indices, major }) := by
  intro i hi
  by_cases hilast : i = recInfos.size
  · subst i
    simpa using hnew
  · have hiOld : i < recInfos.size := by
      have : i < recInfos.size + 1 := by simpa using hi
      omega
    have hget : (recInfos.push {
        motive, minors := #[], indices, major })[i]! = recInfos[i]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos hi, dif_pos hiOld]
      exact Array.getElem_push_lt hiOld
    rw [hget]
    exact H i hiOld

def RecInfoMinorsEmpty (recInfos : Array AddInductive.RecInfo) : Prop :=
  ∀ i, i < recInfos.size → recInfos[i]!.minors.size = 0

theorem RecInfoMinorsEmpty.empty : RecInfoMinorsEmpty #[] := by
  intro i hi
  simp at hi

theorem RecInfoMinorsEmpty.push
    (H : RecInfoMinorsEmpty recInfos) :
    RecInfoMinorsEmpty (recInfos.push {
      motive, minors := #[], indices, major }) := by
  intro i hi
  by_cases hilast : i = recInfos.size
  · subst i
    simp
  · have hiOld : i < recInfos.size := by
      have : i < recInfos.size + 1 := by simpa using hi
      omega
    have hget : (recInfos.push {
        motive, minors := #[], indices, major })[i]! = recInfos[i]! := by
      simp only [Array.getElem!_eq_getD]
      unfold Array.getD
      rw [dif_pos hi, dif_pos hiOld]
      exact Array.getElem_push_lt hiOld
    rw [hget]
    exact H i hiOld

/-- If every recursor-info minor row is empty, the retained flattened minor
selection contains no identifiers either. -/
theorem RecInfoMinorsEmpty.flatMinors_fvars
    (Hempty : RecInfoMinorsEmpty recInfos)
    (Hbindings : RecInfoBindings c recInfos) :
    Hbindings.flatMinors.fvars = [] := by
  change (List.ofFn fun i : Fin recInfos.size =>
    (Hbindings.minors i i.isLt).fvars).flatten = []
  have hrows : (List.ofFn fun i : Fin recInfos.size =>
      (Hbindings.minors i i.isLt).fvars) =
      List.replicate recInfos.size [] := by
    apply List.ext_get
    · simp
    · intro n hleft hright
      have hn : n < recInfos.size := by simpa using hleft
      have hrow : (Hbindings.minors n hn).fvars = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [(Hbindings.minors n hn).length_fvars]
        exact Hempty n hn
      simpa using hrow
  rw [hrows]
  simp

theorem RecInfoArities.modifyMinors
    (H : RecInfoArities stats recInfos) (dIdx : Nat)
    (f : Array Expr → Array Expr) :
    RecInfoArities stats (recInfos.modify dIdx fun info =>
      { info with minors := f info.minors }) := by
  intro i hi
  have hiOld : i < recInfos.size := by simpa using hi
  by_cases hdi : dIdx = i
  · subst i
    rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hiOld]
    exact H dIdx hiOld
  · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
      hiOld hdi]
    exact H i hiOld

/-- Major-domain shapes ignore the minor array updated by the constructor
pass. -/
theorem RecInfoMajorTypeShapes.modifyMinors
    (H : RecInfoMajorTypeShapes stats recInfos majorTypes)
    (dIdx : Nat) (f : Array Expr → Array Expr) :
    RecInfoMajorTypeShapes stats
      (recInfos.modify dIdx fun info =>
        { info with minors := f info.minors }) majorTypes where
  size_eq := by simpa using H.size_eq
  shape i hi := by
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases hdi : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hiOld]
      exact H.shape dIdx hiOld
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
          hiOld hdi]
      exact H.shape i hiOld

/-- Motive declaration shapes likewise depend only on the retained indices
and major, not on the accumulating minor row. -/
theorem RecInfoMotiveTypeShapes.modifyMinors
    (H : RecInfoMotiveTypeShapes c recInfos motiveTypes elimLevel)
    (dIdx : Nat) (f : Array Expr → Array Expr) :
    RecInfoMotiveTypeShapes c
      (recInfos.modify dIdx fun info =>
        { info with minors := f info.minors }) motiveTypes elimLevel where
  size_eq := by simpa using H.size_eq
  shape i hi := by
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases hdi : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hiOld]
      exact H.shape dIdx hiOld
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
          hiOld hdi]
      exact H.shape i hiOld

def RecInfoBindings.empty (c : AddInductive.Context) :
    RecInfoBindings c #[] where
  motives := by simpa using BoundFVarArray.empty c
  majors := by simpa using BoundFVarArray.empty c
  indices i hi := by simp at hi
  minors i hi := by simp at hi

theorem RecInfoOuterOrder.empty
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    (Hsuffix : RecursorParameterContextSuffix R stats depth)
    (Hparams : BoundFVarArray c stats.params) :
    RecInfoOuterOrder R Hparams (RecInfoBindings.empty c) := by
  have hmotives : (RecInfoBindings.empty c).motives.fvars = [] :=
    BoundFVarArray.fvars_eq (RecInfoBindings.empty c).motives
      (BoundFVarArray.empty c) (by simp)
  have hminors : (RecInfoBindings.empty c).flatMinors.fvars = [] :=
    BoundFVarArray.fvars_eq (RecInfoBindings.empty c).flatMinors
      (BoundFVarArray.empty c) (by simp)
  have hcontext := congrArg VLCtx.fvars Hsuffix.context
  rw [VLCtx.fvars_append, Hsuffix.parameterDecls_fvars,
    Hparams.exprArrayFVarIds] at hcontext
  unfold RecInfoOuterOrder
  rw [hmotives, hminors]
  simp only [List.append_nil, List.reverse_append, List.reverse_nil,
    List.nil_append]
  rw [hcontext]
  exact (List.nil_sublist Hsuffix.ambientDecls.fvars).append
    (List.Sublist.refl Hparams.fvars.reverse)

/-- Adding one first-pass motive preserves the selected outer-binder order.
The declarations opened for its indices and major may be interleaved in the
runtime context, but they are deliberately not part of the outer recursor
prefix. -/
theorem RecInfoOuterOrder.pushMotive
    {stats : AddInductive.InductiveStats}
    {Rold : RecursorContextWF old recLparams}
    {Rnew : RecursorContextWF new recLparams}
    {oldInfos newInfos : Array AddInductive.RecInfo}
    {oldParams : BoundFVarArray old stats.params}
    {newParams : BoundFVarArray new stats.params}
    {oldBindings : RecInfoBindings old oldInfos}
    {newBindings : RecInfoBindings new newInfos}
    {motive : FVarId} {interleaved : List FVarId}
    (Horder : RecInfoOuterOrder Rold oldParams oldBindings)
    (holdMinors : oldBindings.flatMinors.fvars = [])
    (hparams : newParams.fvars = oldParams.fvars)
    (hmotives : newBindings.motives.fvars =
      oldBindings.motives.fvars ++ [motive])
    (hnewMinors : newBindings.flatMinors.fvars = [])
    (hcontext : Rnew.mlctx.vlctx.fvars =
      motive :: interleaved ++ Rold.mlctx.vlctx.fvars) :
    RecInfoOuterOrder Rnew newParams newBindings := by
  unfold RecInfoOuterOrder at Horder ⊢
  rw [holdMinors] at Horder
  simp only [List.append_nil] at Horder
  have Horder' : oldBindings.motives.fvars.reverse ++
      oldParams.fvars.reverse <+ Rold.mlctx.vlctx.fvars := by
    simpa only [List.reverse_append] using Horder
  rw [hparams, hmotives, hnewMinors, hcontext]
  simp only [List.append_nil, List.reverse_append, List.reverse_singleton,
    List.singleton_append]
  exact ((List.nil_sublist interleaved).append Horder').cons_cons motive

/-- A newly installed minor becomes the newest selected outer binder when
its flattened row order appends it after the previous minors. -/
theorem RecInfoOuterOrder.addMinor
    {stats : AddInductive.InductiveStats}
    {Rold : RecursorContextWF old recLparams}
    {Rnew : RecursorContextWF new recLparams}
    {oldInfos newInfos : Array AddInductive.RecInfo}
    {oldParams : BoundFVarArray old stats.params}
    {newParams : BoundFVarArray new stats.params}
    {oldBindings : RecInfoBindings old oldInfos}
    {newBindings : RecInfoBindings new newInfos}
    {minor : FVarId}
    (Horder : RecInfoOuterOrder Rold oldParams oldBindings)
    (hparams : newParams.fvars = oldParams.fvars)
    (hmotives : newBindings.motives.fvars = oldBindings.motives.fvars)
    (hminors : newBindings.flatMinors.fvars =
      oldBindings.flatMinors.fvars ++ [minor])
    (hcontext : Rnew.mlctx.vlctx.fvars =
      minor :: Rold.mlctx.vlctx.fvars) :
    RecInfoOuterOrder Rnew newParams newBindings := by
  unfold RecInfoOuterOrder at Horder ⊢
  have Horder' : oldBindings.flatMinors.fvars.reverse ++
      oldBindings.motives.fvars.reverse ++ oldParams.fvars.reverse <+
      Rold.mlctx.vlctx.fvars := by
    simpa only [List.reverse_append, List.append_assoc] using Horder
  rw [hparams, hmotives, hminors, hcontext]
  simp only [List.reverse_append, List.reverse_singleton,
    List.singleton_append]
  simpa only [List.cons_append, List.append_assoc] using
    Horder'.cons_cons minor

def RecInfoBindings.mono
    (H : RecInfoBindings c recInfos) (hle : BindingContextLE c c') :
    RecInfoBindings c' recInfos where
  motives := H.motives.mono hle
  majors := H.majors.mono hle
  indices i hi := (H.indices i hi).mono hle
  minors i hi := (H.minors i hi).mono hle

/-- Exact recent local extensions only add a newest-first prefix, so any
previous outer selection remains ordered after weakening. -/
theorem RecInfoOuterOrder.monoRecent
    {stats : AddInductive.InductiveStats}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {recInfos : Array AddInductive.RecInfo} {args : Array Expr}
    {Hparams : BoundFVarArray root stats.params}
    {Hbindings : RecInfoBindings root recInfos}
    (Horder : RecInfoOuterOrder Rroot Hparams Hbindings)
    (Hrecent : RecursorRecentBoundFVarArray Rroot Rcurrent args) :
    RecInfoOuterOrder Rcurrent (Hparams.mono Hrecent.contextLE)
      (Hbindings.mono Hrecent.contextLE) := by
  unfold RecInfoOuterOrder at Horder ⊢
  change (Hparams.fvars ++ Hbindings.motives.fvars ++
    Hbindings.flatMinors.fvars).reverse <+ Rcurrent.mlctx.vlctx.fvars
  rw [Hrecent.contextFVars]
  exact (List.nil_sublist Hrecent.fvars.reverse).append Horder

/-- Select a motive in any later executable binding context.  All declaration
origins and the exact telescope shape are monotone; the semantic lookup is
then reconstructed from the later context's own `RecursorContextWF`. -/
theorem RecInfoMotiveTypeShapes.motiveBindingAtMono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rcurrent : RecursorContextWF current recLparams}
    (Hbindings : RecInfoBindings root recInfos)
    (Horigins : RecInfoTypeOrigins root recInfos)
    (Hshape : RecInfoMotiveTypeShapes root recInfos
      Horigins.motiveTypes elimLevel)
    (Hle : BindingContextLE root current)
    (target : Nat) (htarget : target < recInfos.size) :
    Nonempty (RecursorMotiveBindingAt Rcurrent recInfos target elimLevel) := by
  let HbindingsCurrent := Hbindings.mono Hle
  let HoriginsCurrent := Horigins.mono Hle
  let HshapeCurrent := Hshape.mono Hbindings Hle
  exact HshapeCurrent.motiveBindingAt Rcurrent HbindingsCurrent
    HoriginsCurrent target htarget

/-- Consecutive higher-order suffix specialization of
`motiveBindingAtMono`. -/
theorem RecInfoMotiveTypeShapes.motiveBindingAtRecent
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams} {args : Array Expr}
    (Hbindings : RecInfoBindings root recInfos)
    (Horigins : RecInfoTypeOrigins root recInfos)
    (Hshape : RecInfoMotiveTypeShapes root recInfos
      Horigins.motiveTypes elimLevel)
    (Hrecent : RecursorRecentBoundFVarArray Rroot Rcurrent args)
    (target : Nat) (htarget : target < recInfos.size) :
    Nonempty (RecursorMotiveBindingAt Rcurrent recInfos target elimLevel) :=
  Hshape.motiveBindingAtMono Hbindings Horigins Hrecent.contextLE target
    htarget

/-- Use a retained target-indexed motive contract after a higher-order local
suffix has been opened.  The executable traversal exposes a terminal type
only up to definitional equality; this bridge transports both typehood and
the major's typing back to the validated syntax target before invoking the
independent motive property. -/
theorem RecInfoMotiveApplications.applyAtMono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    (Happlications : RecInfoMotiveApplications Rroot stats decl recInfos
      elimLevel)
    (Hbindings : RecInfoBindings root recInfos)
    (Horigins : RecInfoTypeOrigins root recInfos)
    (Hshape : RecInfoMotiveTypeShapes root recInfos
      Horigins.motiveTypes elimLevel)
    (Hext : RecursorContextExtension Rroot Rcurrent)
    (target : Nat) (htarget : target < recInfos.size)
    {depth : Nat} {exposedType major : Expr}
    {syntaxTarget terminalTarget majorTarget : VExpr}
    (Hexposed : TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
      exposedType syntaxTarget)
    (Hdefeq : Rcurrent.venv.IsDefEqU recLparams.length
      Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget)
    (Hterminal : Rcurrent.venv.IsType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx terminalTarget)
    (Hmajor : TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
      major majorTarget)
    (HmajorType : Rcurrent.venv.HasType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx majorTarget terminalTarget)
    (Hvalidated : RecursorValidatedIndAppAt Rcurrent.venv recLparams
      Rcurrent.mlctx.vlctx stats decl depth exposedType syntaxTarget target) :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[target]!.motive itIndices) major
    ∃ motiveTarget,
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        motiveApp motiveTarget ∧
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx motiveTarget := by
  rcases Hshape.motiveBindingAtMono Hbindings Horigins Hext.contextLE target
      htarget with ⟨Hbinding⟩
  have HsyntaxType : Rcurrent.venv.IsType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx syntaxTarget :=
    Hterminal.defeqU_l Rcurrent.checking.tr.wf
      Rcurrent.mlctx_wf.tr.wf.toCtx Hdefeq.symm
  have HmajorType' : Rcurrent.venv.HasType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx majorTarget syntaxTarget :=
    HmajorType.defeqU_r Rcurrent.checking.tr.wf
      Rcurrent.mlctx_wf.tr.wf.toCtx Hdefeq.symm
  exact Happlications.application target htarget Rcurrent Hext
    Hbinding.toBinding Hexposed HsyntaxType Hmajor HmajorType' Hvalidated

/-- Exact-suffix specialization of `applyAtMono`. -/
theorem RecInfoMotiveApplications.applyAtRecent
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams} {args : Array Expr}
    (Happlications : RecInfoMotiveApplications Rroot stats decl recInfos
      elimLevel)
    (Hbindings : RecInfoBindings root recInfos)
    (Horigins : RecInfoTypeOrigins root recInfos)
    (Hshape : RecInfoMotiveTypeShapes root recInfos
      Horigins.motiveTypes elimLevel)
    (Hrecent : RecursorRecentBoundFVarArray Rroot Rcurrent args)
    (target : Nat) (htarget : target < recInfos.size)
    {depth : Nat} {exposedType major : Expr}
    {syntaxTarget terminalTarget majorTarget : VExpr}
    (Hexposed : TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
      exposedType syntaxTarget)
    (Hdefeq : Rcurrent.venv.IsDefEqU recLparams.length
      Rcurrent.mlctx.vlctx.toCtx syntaxTarget terminalTarget)
    (Hterminal : Rcurrent.venv.IsType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx terminalTarget)
    (Hmajor : TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
      major majorTarget)
    (HmajorType : Rcurrent.venv.HasType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx majorTarget terminalTarget)
    (Hvalidated : RecursorValidatedIndAppAt Rcurrent.venv recLparams
      Rcurrent.mlctx.vlctx stats decl depth exposedType syntaxTarget target) :
    let itIndices := exposedType.getAppArgs[stats.params.size:]
    let motiveApp := Expr.app
      (mkAppN recInfos[target]!.motive itIndices) major
    ∃ motiveTarget,
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        motiveApp motiveTarget ∧
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx motiveTarget :=
  Happlications.applyAtMono Hbindings Horigins Hshape Hrecent.contextExtension
    target htarget Hexposed Hdefeq Hterminal Hmajor HmajorType Hvalidated

/-- Select the matching major premise after a higher-order recursive suffix
has extended the local context. -/
theorem RecInfoMajorTypeShapes.majorBindingAtRecent
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams} {args : Array Expr}
    (Hbindings : RecInfoBindings root recInfos)
    (Horigins : RecInfoTypeOrigins root recInfos)
    (Hshape : RecInfoMajorTypeShapes stats recInfos Horigins.majorTypes)
    (Hrecent : RecursorRecentBoundFVarArray Rroot Rcurrent args)
    (target : Nat) (htarget : target < recInfos.size) :
    Nonempty (RecursorMajorBindingAt Rcurrent stats recInfos target) := by
  exact Hshape.majorBindingAt Rcurrent
    (Hbindings.mono Hrecent.contextLE) (Horigins.mono Hrecent.contextLE)
    target htarget

theorem RecInfoBindings.empty_noAlias
    {stats : AddInductive.InductiveStats}
    (c : AddInductive.Context) (Hparams : BoundFVarArray c stats.params)
    (hparams : Hparams.fvars.Nodup) :
    (RecInfoBindings.empty c).NoAlias Hparams := by
  have hm : (RecInfoBindings.empty c).motives.fvars = [] := by
    exact BoundFVarArray.fvars_eq (RecInfoBindings.empty c).motives
      (BoundFVarArray.empty c) (by simp)
  have hma : (RecInfoBindings.empty c).majors.fvars = [] := by
    exact BoundFVarArray.fvars_eq (RecInfoBindings.empty c).majors
      (BoundFVarArray.empty c) (by simp)
  unfold RecInfoBindings.NoAlias RecInfoBindings.allFvars
  rw [Hparams.exprArrayFVarIds]
  simpa [ExprArrayFVarIds] using hparams

theorem RecInfoBindings.mono_noAlias
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos) (Hparams : BoundFVarArray c stats.params)
    (hle : BindingContextLE c c') (hnoalias : H.NoAlias Hparams) :
    (H.mono hle).NoAlias (Hparams.mono hle) := by
  simpa [RecInfoBindings.NoAlias, RecInfoBindings.allFvars,
    RecInfoBindings.mono, BoundFVarArray.mono,
    RecInfoBindings.flatMinors, RecInfoBindings.flatIndices] using hnoalias

def RecInfoBindings.pushFrame
    {indices : Array Expr}
    (H : RecInfoBindings c recInfos)
    (hle : BindingContextLE c cIndices)
    (HcIndices : BindingContextWF cIndices)
    (Hindices : BoundFVarArray cIndices indices)
    (majorName : Name) (majorTy : Expr) (majorBi : BinderInfo)
    (motiveName : Name) (motiveTy : Expr) (motiveBi : BinderInfo) :
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
        majorName majorTy majorBi }
    let cMotive : AddInductive.Context := { cMajor with
      ngen := cMajor.ngen.next
      lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
        motiveName motiveTy motiveBi }
    RecInfoBindings cMotive (recInfos.push {
      motive := .fvar ⟨cMajor.ngen.curr⟩
      minors := #[]
      indices
      major := .fvar ⟨cIndices.ngen.curr⟩ }) := by
  dsimp only
  let cMajor : AddInductive.Context := { cIndices with
    ngen := cIndices.ngen.next
    lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
      majorName majorTy majorBi }
  let cMotive : AddInductive.Context := { cMajor with
    ngen := cMajor.ngen.next
    lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
      motiveName motiveTy motiveBi }
  let hMajor := BindingContextLE.withLocalDecl cIndices HcIndices
    majorName majorTy majorBi
  let hMotive := BindingContextLE.withLocalDecl cMajor
    (HcIndices.withLocalDecl majorName majorTy majorBi)
    motiveName motiveTy motiveBi
  let hall : BindingContextLE c cMotive := hle.trans (hMajor.trans hMotive)
  refine {
    motives := ?_
    majors := ?_
    indices := ?_
    minors := ?_
  }
  · simpa [cMajor, cMotive] using
      ((H.motives.mono (hle.trans hMajor)).pushCurrent
        motiveName motiveTy motiveBi)
  · simpa [cMajor, cMotive] using
      (((H.majors.mono hle).pushCurrent majorName majorTy majorBi).weaken
        motiveName motiveTy motiveBi)
  · intro i hi
    by_cases hilast : i = recInfos.size
    · subst i
      simpa [cMajor, cMotive] using Hindices.mono (hMajor.trans hMotive)
    · have hiSize : i < recInfos.size + 1 := by simpa using hi
      have hiOld : i < recInfos.size := by omega
      have hget : (recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hget]
      exact (H.indices i hiOld).mono hall
  · intro i hi
    by_cases hilast : i = recInfos.size
    · subst i
      simpa using BoundFVarArray.empty cMotive
    · have hiSize : i < recInfos.size + 1 := by simpa using hi
      have hiOld : i < recInfos.size := by omega
      have hget : (recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hget]
      exact (H.minors i hiOld).mono hall

def RecInfoTypeOrigins.pushFrame
    {indices indexOrigins : Array Expr}
    (H : RecInfoTypeOrigins c recInfos)
    (hle : BindingContextLE c cIndices)
    (HcIndices : BindingContextWF cIndices)
    (Hindices : BoundFVarTypeOrigins cIndices indices indexOrigins)
    (majorName : Name) (majorTy : Expr) (majorBi : BinderInfo)
    (motiveName : Name) (motiveTy : Expr) (motiveBi : BinderInfo) :
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
        majorName majorTy majorBi }
    let cMotive : AddInductive.Context := { cMajor with
      ngen := cMajor.ngen.next
      lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
        motiveName motiveTy motiveBi }
    RecInfoTypeOrigins cMotive (recInfos.push {
      motive := .fvar ⟨cMajor.ngen.curr⟩
      minors := #[]
      indices
      major := .fvar ⟨cIndices.ngen.curr⟩ }) := by
  dsimp only
  let cMajor : AddInductive.Context := { cIndices with
    ngen := cIndices.ngen.next
    lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
      majorName majorTy majorBi }
  let cMotive : AddInductive.Context := { cMajor with
    ngen := cMajor.ngen.next
    lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
      motiveName motiveTy motiveBi }
  let HcMajor := HcIndices.withLocalDecl majorName majorTy majorBi
  let hMajor := BindingContextLE.withLocalDecl cIndices HcIndices
    majorName majorTy majorBi
  let hMotive := BindingContextLE.withLocalDecl cMajor HcMajor
    motiveName motiveTy motiveBi
  let hall : BindingContextLE c cMotive := hle.trans (hMajor.trans hMotive)
  refine {
    motiveTypes := H.motiveTypes.push motiveTy
    majorTypes := H.majorTypes.push majorTy
    indexTypes := H.indexTypes.push indexOrigins
    minorTypes := H.minorTypes.push #[]
    indexTypes_size := by simpa using H.indexTypes_size
    minorTypes_size := by simpa using H.minorTypes_size
    motives := ?_
    majors := ?_
    indices := ?_
    minors := ?_
    minorShapes := ?_ }
  · simpa [cMajor, cMotive] using
      (H.motives.mono (hle.trans hMajor)).pushCurrent HcMajor
        motiveName motiveTy motiveBi
  · simpa [cMajor, cMotive] using
      ((H.majors.mono hle).pushCurrent HcIndices
        majorName majorTy majorBi).mono hMotive
  · intro i hi
    by_cases hilast : i = recInfos.size
    · subst i
      have hindexOrigins :
          (H.indexTypes.push indexOrigins)[recInfos.size]! = indexOrigins := by
        rw [show recInfos.size = H.indexTypes.size from
          H.indexTypes_size.symm]
        simp
      rw [hindexOrigins]
      simpa [cMajor, cMotive] using Hindices.mono (hMajor.trans hMotive)
    · have hiOld : i < recInfos.size := by
        have : i < recInfos.size + 1 := by simpa using hi
        omega
      have hrec : (recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hrec]
      have hiTypes : i < H.indexTypes.size := by
        rw [H.indexTypes_size]
        exact hiOld
      have horigin : (H.indexTypes.push indexOrigins)[i]! =
          H.indexTypes[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        have hiPush : i < (H.indexTypes.push indexOrigins).size := by
          simp only [Array.size_push]
          omega
        rw [dif_pos hiPush, dif_pos hiTypes]
        exact Array.getElem_push_lt hiTypes
      rw [horigin]
      exact (H.indices i hiOld).mono hall
  · intro i hi
    by_cases hilast : i = recInfos.size
    · subst i
      have horigin : (H.minorTypes.push #[])[recInfos.size]! = #[] := by
        rw [show recInfos.size = H.minorTypes.size from
          H.minorTypes_size.symm]
        simp
      rw [horigin]
      simpa using BoundFVarTypeOrigins.empty cMotive
    · have hiOld : i < recInfos.size := by
        have : i < recInfos.size + 1 := by simpa using hi
        omega
      have hrec : (recInfos.push {
          motive := .fvar ⟨cMajor.ngen.curr⟩
          minors := #[]
          indices
          major := .fvar ⟨cIndices.ngen.curr⟩ })[i]! = recInfos[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        rw [dif_pos hi, dif_pos hiOld]
        exact Array.getElem_push_lt hiOld
      rw [hrec]
      have hiTypes : i < H.minorTypes.size := by
        rw [H.minorTypes_size]
        exact hiOld
      have horigin : (H.minorTypes.push #[])[i]! = H.minorTypes[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        have hiPush : i < (H.minorTypes.push #[]).size := by
          simp only [Array.size_push]
          omega
        rw [dif_pos hiPush, dif_pos hiTypes]
        exact Array.getElem_push_lt hiTypes
      rw [horigin]
      exact (H.minors i hiOld).mono hall
  · intro i hi j hj
    by_cases hilast : i = recInfos.size
    · subst i
      have horigin : (H.minorTypes.push #[])[recInfos.size]! = #[] := by
        rw [show recInfos.size = H.minorTypes.size from
          H.minorTypes_size.symm]
        simp
      rw [horigin] at hj
      simp at hj
    · have hiOld : i < recInfos.size := by
        have : i < recInfos.size + 1 := by simpa using hi
        omega
      have hiTypes : i < H.minorTypes.size := by
        rw [H.minorTypes_size]
        exact hiOld
      have horigin : (H.minorTypes.push #[])[i]! = H.minorTypes[i]! := by
        simp only [Array.getElem!_eq_getD]
        unfold Array.getD
        have hiPush : i < (H.minorTypes.push #[]).size := by
          simp only [Array.size_push]
          omega
        rw [dif_pos hiPush, dif_pos hiTypes]
        exact Array.getElem_push_lt hiTypes
      rw [horigin] at hj
      exact H.minorShapes i hiOld j hj
theorem RecInfoBindings.pushFrame_allFvars_perm
    {stats : AddInductive.InductiveStats} {indices : Array Expr}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hle : BindingContextLE c cIndices)
    (HcIndices : BindingContextWF cIndices)
    (Hindices : BoundFVarArray cIndices indices)
    (majorName : Name) (majorTy : Expr) (majorBi : BinderInfo)
    (motiveName : Name) (motiveTy : Expr) (motiveBi : BinderInfo) :
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
        majorName majorTy majorBi }
    let cMotive : AddInductive.Context := { cMajor with
      ngen := cMajor.ngen.next
      lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
        motiveName motiveTy motiveBi }
    let hall : BindingContextLE c cMotive := hle.trans <|
      (BindingContextLE.withLocalDecl cIndices HcIndices
        majorName majorTy majorBi).trans <|
        BindingContextLE.withLocalDecl cMajor
          (HcIndices.withLocalDecl majorName majorTy majorBi)
          motiveName motiveTy motiveBi
    ((H.pushFrame hle HcIndices Hindices majorName majorTy majorBi
      motiveName motiveTy motiveBi).allFvars (Hparams.mono hall)).Perm
      (H.allFvars Hparams ++ Hindices.fvars ++
        [(⟨cIndices.ngen.curr⟩ : FVarId),
          (⟨cMajor.ngen.curr⟩ : FVarId)]) := by
  dsimp only
  rw [← Hindices.exprArrayFVarIds]
  simp only [RecInfoBindings.allFvars, Array.map_push, Array.flatMap_push,
    Array.flatMap_append, ExprArrayFVarIds, Array.toList_push,
    Array.toList_append, List.map_append, List.map_cons, List.map_nil,
    recursorFVarId]
  simp only [List.nil_append, List.append_assoc]
  apply List.Perm.append (List.Perm.refl _) <|
    List.Perm.append (List.Perm.refl _) ?_
  have reorder (minors oldIndices newIndices majors : List FVarId)
      (major motive : FVarId) :
      ([motive] ++ minors ++ oldIndices ++ newIndices ++ majors ++ [major]) ~
        (minors ++ oldIndices ++ majors ++ newIndices ++ [major, motive]) := by
    have hswap : newIndices ++ majors ~ majors ++ newIndices :=
      List.perm_append_comm
    have hmiddle :
        minors ++ oldIndices ++ newIndices ++ majors ++ [major] ~
        minors ++ oldIndices ++ majors ++ newIndices ++ [major] := by
      simpa only [List.append_assoc] using
        (List.Perm.refl (minors ++ oldIndices)).append
          (hswap.append_right [major])
    have hmove :
        [motive] ++ (minors ++ oldIndices ++ newIndices ++ majors ++ [major]) ~
        (minors ++ oldIndices ++ newIndices ++ majors ++ [major]) ++
          [motive] := List.perm_append_comm
    exact hmove.trans <| by
      simpa [List.append_assoc] using hmiddle.append_right [motive]
  simpa only [List.append_assoc] using reorder
    ((Array.flatMap (fun x => x.minors) recInfos).toList.map recursorFVarId)
    ((Array.flatMap (fun x => x.indices) recInfos).toList.map recursorFVarId)
    (indices.toList.map recursorFVarId)
    ((Array.map (fun x => x.major) recInfos).toList.map recursorFVarId)
    ⟨cIndices.ngen.curr⟩ ⟨cIndices.ngen.next.curr⟩

theorem RecInfoBindings.pushFrame_noAlias
    {stats : AddInductive.InductiveStats} {indices : Array Expr}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : H.NoAlias Hparams)
    (hle : BindingContextLE c cIndices)
    (HcIndices : BindingContextWF cIndices)
    (Hindices : FreshBoundFVarArray c cIndices indices)
    (majorName : Name) (majorTy : Expr) (majorBi : BinderInfo)
    (motiveName : Name) (motiveTy : Expr) (motiveBi : BinderInfo) :
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
        majorName majorTy majorBi }
    let cMotive : AddInductive.Context := { cMajor with
      ngen := cMajor.ngen.next
      lctx := cMajor.lctx.mkLocalDecl ⟨cMajor.ngen.curr⟩
        motiveName motiveTy motiveBi }
    let hall : BindingContextLE c cMotive := hle.trans <|
      (BindingContextLE.withLocalDecl cIndices HcIndices
        majorName majorTy majorBi).trans <|
        BindingContextLE.withLocalDecl cMajor
          (HcIndices.withLocalDecl majorName majorTy majorBi)
          motiveName motiveTy motiveBi
    (H.pushFrame hle HcIndices Hindices.toBoundFVarArray
      majorName majorTy majorBi
      motiveName motiveTy motiveBi).NoAlias (Hparams.mono hall) := by
  dsimp only
  let old := H.allFvars Hparams
  let indexFVars := Hindices.toBoundFVarArray.fvars
  let major : FVarId := ⟨cIndices.ngen.curr⟩
  let motive : FVarId := ⟨cIndices.ngen.next.curr⟩
  have hOldIndices : (old ++ indexFVars).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hnoalias, Hindices.nodup, ?_⟩
    intro fv hfv fv' hfv'
    exact fun heq => Hindices.fresh fv' hfv' <| heq ▸
      H.allFvars_members Hparams fv hfv
  have hMajorFresh : major ∉ old ++ indexFVars := by
    intro hmem
    simp only [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact HcIndices.current_not_mem <| hle <|
        H.allFvars_members Hparams major hmem
    · exact HcIndices.current_not_mem <|
        Hindices.toBoundFVarArray.members major hmem
  have hWithMajor : (old ++ indexFVars ++ [major]).Nodup := by
    apply List.nodup_append.mpr
    exact ⟨hOldIndices, by simp, by
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hMajorFresh (heq ▸ hfv)⟩
  let cMajor : AddInductive.Context := { cIndices with
    ngen := cIndices.ngen.next
    lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩
      majorName majorTy majorBi }
  have hMotiveFresh : motive ∉ old ++ indexFVars ++ [major] := by
    intro hmem
    apply (HcIndices.withLocalDecl majorName majorTy majorBi).current_not_mem
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with (hOld | hIndex) | hMajor
    · exact Or.inr <| hle <| H.allFvars_members Hparams motive hOld
    · exact Or.inr <| Hindices.toBoundFVarArray.members motive hIndex
    · exact Or.inl hMajor
  have hCombined : (old ++ indexFVars ++ [major, motive]).Nodup := by
    rw [show [major, motive] = [major] ++ [motive] by rfl,
      ← List.append_assoc]
    apply List.nodup_append.mpr
    exact ⟨hWithMajor, by simp, by
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hMotiveFresh (heq ▸ hfv)⟩
  apply (H.pushFrame_allFvars_perm Hparams hle HcIndices
    Hindices.toBoundFVarArray majorName majorTy majorBi
    motiveName motiveTy motiveBi).symm.nodup
  simpa [old, indexFVars, major, motive, List.append_assoc] using hCombined

def RecInfoBindings.addMinor
    (H : RecInfoBindings c recInfos) (dIdx : Nat)
    (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    RecInfoBindings cMinor (recInfos.modify dIdx fun info =>
      { info with minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }) := by
  dsimp only
  let cMinor : AddInductive.Context := { cMinorTy with
    ngen := cMinorTy.ngen.next
    lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
      minorName minorTy minorBi }
  let hstep := BindingContextLE.withLocalDecl cMinorTy HcMinorTy
    minorName minorTy minorBi
  let hall := hle.trans hstep
  refine {
    motives := ?_
    majors := ?_
    indices := ?_
    minors := ?_
  }
  · have heq : (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }).map (·.motive) =
        recInfos.map (·.motive) := by
      apply Array.ext
      · simp
      · intro i hiLeft hiRight
        by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]
    rw [heq]
    exact H.motives.mono hall
  · have heq : (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }).map (·.major) =
        recInfos.map (·.major) := by
      apply Array.ext
      · simp
      · intro i hiLeft hiRight
        by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]
    rw [heq]
    exact H.majors.mono hall
  · intro i hi
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases heq : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      exact (H.indices dIdx hidx).mono hall
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hiOld heq]
      exact (H.indices i hiOld).mono hall
  · intro i hi
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases heq : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      simpa [cMinor] using
        ((H.minors dIdx hidx).mono hle).pushCurrent
          minorName minorTy minorBi
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _ hiOld heq]
      exact (H.minors i hiOld).mono hall

def RecInfoTypeOrigins.addMinor
    (H : RecInfoTypeOrigins c recInfos) (dIdx : Nat)
    (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo)
    (Hshape : RecInfoMinorTypeShape)
    (HshapePosition :
      Hshape.localIndex = H.minorTypes[dIdx]!.size ∧
      Hshape.origin = minorTy) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    RecInfoTypeOrigins cMinor (recInfos.modify dIdx fun info =>
      { info with minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }) := by
  dsimp only
  let cMinor : AddInductive.Context := { cMinorTy with
    ngen := cMinorTy.ngen.next
    lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
      minorName minorTy minorBi }
  let hstep := BindingContextLE.withLocalDecl cMinorTy HcMinorTy
    minorName minorTy minorBi
  let hall := hle.trans hstep
  let nextMinorTypes := H.minorTypes.modify dIdx fun types =>
    types.push minorTy
  refine {
    motiveTypes := H.motiveTypes
    majorTypes := H.majorTypes
    indexTypes := H.indexTypes
    minorTypes := nextMinorTypes
    indexTypes_size := by simpa using H.indexTypes_size
    minorTypes_size := by simpa [nextMinorTypes] using H.minorTypes_size
    motives := ?_
    majors := ?_
    indices := ?_
    minors := ?_
    minorShapes := ?_ }
  · have heq : (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }).map
          (·.motive) = recInfos.map (·.motive) := by
      apply Array.ext
      · simp
      · intro i hiLeft hiRight
        by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]
    rw [heq]
    exact H.motives.mono hall
  · have heq : (recInfos.modify dIdx fun info =>
        { info with
          minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }).map
          (·.major) = recInfos.map (·.major) := by
      apply Array.ext
      · simp
      · intro i hiLeft hiRight
        by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]
    rw [heq]
    exact H.majors.mono hall
  · intro i hi
    have hiOld : i < recInfos.size := by simpa using hi
    by_cases hdi : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      exact (H.indices dIdx hidx).mono hall
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
        hiOld hdi]
      exact (H.indices i hiOld).mono hall
  · intro i hi
    have hiOld : i < recInfos.size := by simpa using hi
    have hiTypes : i < H.minorTypes.size := by
      rw [H.minorTypes_size]
      exact hiOld
    by_cases hdi : dIdx = i
    · subst i
      rw [mkRecInfos.loopCtors.getElemBang_modify_self recInfos dIdx _ hidx]
      have horigin : nextMinorTypes[dIdx]! =
          (H.minorTypes[dIdx]!).push minorTy := by
        dsimp [nextMinorTypes]
        rw [mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx _
          hiTypes]
      rw [horigin]
      simpa [cMinor] using
        ((H.minors dIdx hidx).mono hle).pushCurrent HcMinorTy
          minorName minorTy minorBi
    · rw [mkRecInfos.loopCtors.getElemBang_modify_ne recInfos dIdx i _
        hiOld hdi]
      have horigin : nextMinorTypes[i]! = H.minorTypes[i]! := by
        dsimp [nextMinorTypes]
        rw [mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx i _
          hiTypes hdi]
      rw [horigin]
      exact (H.minors i hiOld).mono hall
  · intro i hi j hj
    have hiOld : i < recInfos.size := by simpa using hi
    have hiTypes : i < H.minorTypes.size := by
      rw [H.minorTypes_size]
      exact hiOld
    by_cases hdi : dIdx = i
    · subst i
      have horigin : nextMinorTypes[dIdx]! =
          (H.minorTypes[dIdx]!).push minorTy := by
        dsimp [nextMinorTypes]
        rw [mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx _
          hiTypes]
      rw [horigin] at hj
      by_cases hjlast : j = H.minorTypes[dIdx]!.size
      · subst j
        have hlast : ((H.minorTypes[dIdx]!).push minorTy)[
            H.minorTypes[dIdx]!.size]! = minorTy := by
          have hpush : H.minorTypes[dIdx]!.size <
              (H.minorTypes[dIdx]!.push minorTy).size := by simp
          rw [getElem!_pos (H.minorTypes[dIdx]!.push minorTy)
            H.minorTypes[dIdx]!.size hpush]
          exact Array.getElem_push_eq
        exact Hshape
      · have hjOld : j < H.minorTypes[dIdx]!.size := by
          simp only [Array.size_push] at hj
          omega
        have hget : ((H.minorTypes[dIdx]!).push minorTy)[j]! =
            H.minorTypes[dIdx]![j]! := by
          have hjPush : j < (H.minorTypes[dIdx]!.push minorTy).size := by
            simp only [Array.size_push]
            omega
          rw [getElem!_pos (H.minorTypes[dIdx]!.push minorTy) j hjPush,
            getElem!_pos H.minorTypes[dIdx]! j hjOld]
          exact Array.getElem_push_lt hjOld
        exact H.minorShapes dIdx hidx j hjOld
    · have horigin : nextMinorTypes[i]! = H.minorTypes[i]! := by
        dsimp [nextMinorTypes]
        rw [mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx i _
          hiTypes hdi]
      rw [horigin] at hj
      exact H.minorShapes i hiOld j hj
/-- Every retained minor shape names the concrete constructor list of its
owning source family.  This is the final cross-pass provenance invariant:
the second `mkRecInfos` traversal and rule generation may allocate different
locals, but they replay the same owner-indexed constructor arrays. -/
def RecInfoMinorSourceAlignment
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType)
    (H : RecInfoTypeOrigins c recInfos) : Prop :=
  ∀ owner (howner : owner < recInfos.size)
    (hsourceOwner : owner < indTypes.size)
    localIndex (hlocal : localIndex < H.minorTypes[owner]!.size),
    let S := H.minorShapes owner howner localIndex hlocal;
      S.origin = H.minorTypes[owner]![localIndex]! ∧
      S.localIndex = localIndex ∧
      S.sourceConstructors = indTypes[owner]!.ctors ∧
      S.HasHypothesisTypeOrigins stats recInfos ∧
        ∃ traversal, S.traversal = some traversal ∧
          traversal.constructor = S.constructor ∧
          traversal.fields = S.fields ∧
          traversal.recursiveFields = S.recursiveFields ∧
          traversal.stats = stats ∧
          AddInductive.isValidIndApp? stats traversal.terminal = some
            (AddInductive.getIIndices stats traversal.terminal).1 ∧
          S.motiveApp = (
            let (motiveOwner, indices) :=
              AddInductive.getIIndices stats traversal.terminal
            Expr.app
              (mkAppN recInfos[motiveOwner]!.motive indices)
              (mkAppN
                (mkAppN (.const S.constructor.name stats.levels)
                  stats.params)
                S.fields)) ∧
          BindingContextLE traversal.rootContext c ∧
          BindingContextLE traversal.terminalContext c ∧
          BindingContextLE S.sourceFullContext c

/-- Semantic counterpart of `RecInfoMinorSourceAlignment` for one retained
minor.  The structural alignment remembers that the source context embeds in
the final local context; this certificate additionally remembers the exact
translation-side lift produced by that executable extension.  Keeping the
source `RecursorContextWF` existential avoids baking a particular sequence of
intermediate field and hypothesis binders into the stable minor shape. -/
structure RecInfoMinorSemanticSource
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (S : RecInfoMinorTypeShape) where
  sourceWF : RecursorContextWF S.sourceFullContext recLparams
  extension : RecursorContextExtension sourceWF R
  traversal : RecInfoMinorTraversalShape
  traversal_eq : S.traversal = some traversal
  traversal_fields : traversal.fields = S.fields
  rootWF : RecursorContextWF traversal.rootContext recLparams
  terminalWF : RecursorContextWF traversal.terminalContext recLparams
  parameterDepth : Nat
  parameterSuffix : RecursorParameterContextSuffix rootWF traversal.stats
    parameterDepth
  parameterScope : traversal.parameterTail.FVarsIn
    (fun fv => fv ∈ parameterSuffix.parameterDecls.fvars)
  parameterTarget : VExpr
  parameterTranslation : TrExprS rootWF.venv recLparams
    rootWF.mlctx.vlctx traversal.parameterTail parameterTarget
  parameterType : rootWF.venv.IsType recLparams.length
    rootWF.mlctx.vlctx.toCtx parameterTarget
  fieldsRecent : RecursorRecentBoundFVarArray rootWF terminalWF S.fields
  hypothesesRecent : RecursorRecentBoundFVarArray terminalWF sourceWF
    S.hypotheses
  terminalTarget : VExpr
  terminalTranslation : TrExprS terminalWF.venv recLparams
    terminalWF.mlctx.vlctx traversal.terminal terminalTarget
  terminalType : terminalWF.venv.IsType recLparams.length
    terminalWF.mlctx.vlctx.toCtx terminalTarget
  fieldTargetDefEq : rootWF.venv.IsDefEqU recLparams.length
    rootWF.mlctx.vlctx.toCtx parameterTarget
      (terminalWF.mlctx.mkForall' S.fields.size fieldsRecent.size_le
        terminalTarget)
  /-- The source motive application is assembled before recursive-hypothesis
  locals are opened.  Retaining this pre-weakening derivation makes the later
  hypothesis closure visibly alpha-invariant. -/
  motivePreTarget : VExpr
  motivePreTranslation : TrExprS terminalWF.venv recLparams
    terminalWF.mlctx.vlctx S.motiveApp motivePreTarget
  motivePreType : terminalWF.venv.IsType recLparams.length
    terminalWF.mlctx.vlctx.toCtx motivePreTarget
  /-- The application head is an outer motive binder, introduced before the
  fresh constructor fields. -/
  motiveHeadRoot : ∃ fv,
    S.motiveApp.getAppFn = .fvar fv ∧
      fv ∈ rootWF.mlctx.vlctx.fvars
  motiveTarget : VExpr
  motiveTranslation : TrExprS sourceWF.venv recLparams
    sourceWF.mlctx.vlctx S.motiveApp motiveTarget
  motiveType : sourceWF.venv.IsType recLparams.length
    sourceWF.mlctx.vlctx.toCtx motiveTarget
  sourceTarget : VExpr
  consumedTarget : VExpr
  consumption : sourceWF.ConsumedDomain S.sourceType sourceTarget
    consumedTarget

def RecInfoMinorSemanticSource.mono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {S : RecInfoMinorTypeShape}
    (HS : RecInfoMinorSemanticSource Rroot S)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    RecInfoMinorSemanticSource Rcurrent S where
  sourceWF := HS.sourceWF
  extension := HS.extension.trans Hext
  traversal := HS.traversal
  traversal_eq := HS.traversal_eq
  traversal_fields := HS.traversal_fields
  rootWF := HS.rootWF
  terminalWF := HS.terminalWF
  parameterDepth := HS.parameterDepth
  parameterSuffix := HS.parameterSuffix
  parameterScope := HS.parameterScope
  parameterTarget := HS.parameterTarget
  parameterTranslation := HS.parameterTranslation
  parameterType := HS.parameterType
  fieldsRecent := HS.fieldsRecent
  hypothesesRecent := HS.hypothesesRecent
  terminalTarget := HS.terminalTarget
  terminalTranslation := HS.terminalTranslation
  terminalType := HS.terminalType
  fieldTargetDefEq := HS.fieldTargetDefEq
  motivePreTarget := HS.motivePreTarget
  motivePreTranslation := HS.motivePreTranslation
  motivePreType := HS.motivePreType
  motiveHeadRoot := HS.motiveHeadRoot
  motiveTarget := HS.motiveTarget
  motiveTranslation := HS.motiveTranslation
  motiveType := HS.motiveType
  sourceTarget := HS.sourceTarget
  consumedTarget := HS.consumedTarget
  consumption := HS.consumption

/-- Recursive hypotheses are introduced only after the selected-motive
application has been assembled.  Closing their fresh identifiers therefore
leaves that source application unchanged. -/
theorem RecInfoMinorSemanticSource.abstractHypotheses_motiveApp
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : RecInfoMinorTypeShape}
    (HS : RecInfoMinorSemanticSource R S) :
    S.motiveApp.abstractList S.hypotheses_bound.fvars = S.motiveApp := by
  have hclosed : Closed S.motiveApp 0 := by
    have h := HS.motivePreTranslation.closed
    rw [HS.terminalWF.mlctx.noBV] at h
    simpa using h
  have hscope := HS.motivePreTranslation.fvarsIn
  have havoids : S.motiveApp.FVarsIn
      (fun fv => fv ∉ S.hypotheses_bound.fvars) := by
    apply hscope.mono
    intro fv hterminal hhypothesis
    have hhypothesisFVars : HS.hypothesesRecent.fvars =
        S.hypotheses_bound.fvars :=
      BoundFVarArray.fvars_eq_of_array_eq
        HS.hypothesesRecent.toFreshBoundFVarArray.toBoundFVarArray
        S.hypotheses_bound rfl
    rw [← hhypothesisFVars] at hhypothesis
    apply HS.hypothesesRecent.fresh fv hhypothesis
    rw [← HS.terminalWF.lctx_eq,
      HS.terminalWF.mlctx_wf.tr.fvars_eq]
    exact hterminal
  exact havoids.abstractList_eq_self hclosed

/-- Consuming binder annotations cannot change a generated minor type.  A
nonempty field/hypothesis telescope starts with a genuine forall binder.  In
the degenerate empty-telescope case the residual is an application headed by
the freshly bound motive variable, so it cannot be any of Lean's four
top-level parameter-annotation encodings either. -/
theorem RecInfoMinorSemanticSource.sourceType_consumeTypeAnnotations_eq_self
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : RecInfoMinorTypeShape}
    (HS : RecInfoMinorSemanticSource R S) :
    S.sourceType.consumeTypeAnnotations = S.sourceType := by
  by_cases hpositive : 0 < S.fields.size + S.hypotheses.size
  · exact S.sourceTelescope.consumeTypeAnnotations_eq_self_of_pos hpositive
  · have hfields : S.fields.size = 0 := by omega
    have hhypotheses : S.hypotheses.size = 0 := by omega
    have hfieldsEmpty : S.fields = #[] :=
      Array.eq_empty_of_size_eq_zero hfields
    have hhypothesesEmpty : S.hypotheses = #[] :=
      Array.eq_empty_of_size_eq_zero hhypotheses
    have hsource : S.sourceType = S.motiveApp := by
      rw [S.sourceType_eq, hfieldsEmpty, hhypothesesEmpty,
        LocalContext.mkForall_empty, LocalContext.mkForall_empty]
    rw [hsource]
    rcases HS.motiveHeadRoot with ⟨motiveFVar, hhead, _hmotiveRoot⟩
    apply Expr.consumeTypeAnnotations_eq_self
    · change S.motiveApp.isAppOfArity `optParam 2 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change S.motiveApp.isAppOfArity `autoParam 2 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change S.motiveApp.isAppOfArity `outParam 1 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _
    · change S.motiveApp.isAppOfArity `semiOutParam 1 = false
      exact Expr.isAppOfArity_eq_false_of_getAppFn_fvar hhead _ _

def RecInfoMinorSemanticSource.fieldDomains
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : RecInfoMinorTypeShape}
    (HS : RecInfoMinorSemanticSource R S) : List VExpr :=
  MLCtxForallDomains HS.terminalWF.mlctx S.fields.size
    HS.fieldsRecent.size_le

def RecInfoMinorSemanticSource.hypothesisDomains
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : RecInfoMinorTypeShape}
    (HS : RecInfoMinorSemanticSource R S) : List VExpr :=
  MLCtxForallDomains HS.sourceWF.mlctx S.hypotheses.size
    HS.hypothesesRecent.size_le

/-- The domains replayed from consumed field declarations are not expected
to be syntactically identical to the domains obtained by translating the
original constructor telescope.  The retained whole-target equality implies
the correct invariant: their completed dependent contexts are definitionally
equal over the common root context. -/
theorem RecInfoMinorSemanticSource.fieldContextDefEq
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : RecInfoMinorTypeShape}
    (HS : RecInfoMinorSemanticSource R S) :
    ∃ sourceDomains sourceResidual,
      sourceDomains.length = S.fields.size ∧
      HS.parameterTarget =
        VExpr.wrapForalls sourceDomains sourceResidual ∧
      VEnv.IsDefEqCtx HS.rootWF.venv recLparams.length []
        (sourceDomains.reverse ++ HS.rootWF.mlctx.vlctx.toCtx)
        (HS.fieldDomains.reverse ++ HS.rootWF.mlctx.vlctx.toCtx) := by
  rcases TrExprS.forallTelescope_shape HS.traversal.fieldTelescope
      HS.parameterTranslation with
    ⟨sourceDomains, sourceResidual, hsourceLength, hparameterTarget⟩
  have hsourceLength' : sourceDomains.length = S.fields.size :=
    hsourceLength.trans (congrArg Array.size HS.traversal_fields)
  have hfieldLength : HS.fieldDomains.length = S.fields.size := by
    exact HS.terminalWF.onlyLams.forallDomains_length S.fields.size
      HS.fieldsRecent.size_le
  have Htarget : HS.rootWF.venv.IsDefEqU recLparams.length
      HS.rootWF.mlctx.vlctx.toCtx
      (VExpr.wrapForalls sourceDomains sourceResidual)
      (VExpr.wrapForalls HS.fieldDomains HS.terminalTarget) := by
    rw [← hparameterTarget]
    simpa [RecInfoMinorSemanticSource.fieldDomains,
      TypeChecker.MLCtx.mkForall'_eq_wrapForalls] using
        HS.fieldTargetDefEq
  have Hbase : VEnv.IsDefEqCtx HS.rootWF.venv recLparams.length []
      HS.rootWF.mlctx.vlctx.toCtx HS.rootWF.mlctx.vlctx.toCtx :=
    .refl HS.rootWF.mlctx_wf.tr.wf.toCtx
  exact ⟨sourceDomains, sourceResidual, hsourceLength', hparameterTarget,
    VEnv.IsDefEqU.wrapForalls_context HS.rootWF.checking.tr.wf Hbase
      (hsourceLength'.trans hfieldLength.symm) Htarget⟩

/-- Transport the field-context conversion to any later recursor context.
The consumed domains are exposed after the exact free-variable lift carried
by the executable context extension; this is the form needed when the minor
is finally installed among motives and preceding minors. -/
theorem RecInfoMinorSemanticSource.fieldContextDefEqMono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {S : RecInfoMinorTypeShape}
    (HS : RecInfoMinorSemanticSource Rroot S)
    (Hext : RecursorContextExtension HS.rootWF Rcurrent) :
    ∃ sourceDomains sourceResidual consumedDomains consumedResidual,
      sourceDomains.length = S.fields.size ∧
      consumedDomains.length = S.fields.size ∧
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        HS.traversal.parameterTail
        (VExpr.wrapForalls sourceDomains sourceResidual) ∧
      (VExpr.wrapForalls HS.fieldDomains HS.terminalTarget).lift'
          (Hext.shift.consN 0) =
        VExpr.wrapForalls consumedDomains consumedResidual ∧
      VEnv.IsDefEqCtx Rcurrent.venv recLparams.length []
        (sourceDomains.reverse ++ Rcurrent.mlctx.vlctx.toCtx)
        (consumedDomains.reverse ++ Rcurrent.mlctx.vlctx.toCtx) := by
  have Hparameter := Hext.weakTrExprS HS.parameterTranslation
  rcases TrExprS.forallTelescope_shape HS.traversal.fieldTelescope
      Hparameter with
    ⟨sourceDomains, sourceResidual, hsourceLength, hsourceTarget⟩
  have hsourceLength' : sourceDomains.length = S.fields.size :=
    hsourceLength.trans (congrArg Array.size HS.traversal_fields)
  rcases VExpr.lift'_wrapForalls_shape HS.fieldDomains HS.terminalTarget
      (Hext.shift.consN 0) with
    ⟨consumedDomains, consumedResidual, hconsumedLength, hconsumedTarget⟩
  have hfieldLength : HS.fieldDomains.length = S.fields.size := by
    exact HS.terminalWF.onlyLams.forallDomains_length S.fields.size
      HS.fieldsRecent.size_le
  have hconsumedLength' : consumedDomains.length = S.fields.size :=
    hconsumedLength.trans hfieldLength
  have HfieldTarget : HS.rootWF.venv.IsDefEqU recLparams.length
      HS.rootWF.mlctx.vlctx.toCtx HS.parameterTarget
      (VExpr.wrapForalls HS.fieldDomains HS.terminalTarget) := by
    simpa [RecInfoMinorSemanticSource.fieldDomains,
      TypeChecker.MLCtx.mkForall'_eq_wrapForalls] using
        HS.fieldTargetDefEq
  have Htarget := Hext.weakDefEqU HfieldTarget
  rw [hsourceTarget, hconsumedTarget] at Htarget
  have Hbase : VEnv.IsDefEqCtx Rcurrent.venv recLparams.length []
      Rcurrent.mlctx.vlctx.toCtx Rcurrent.mlctx.vlctx.toCtx :=
    .refl Rcurrent.mlctx_wf.tr.wf.toCtx
  exact ⟨sourceDomains, sourceResidual, consumedDomains, consumedResidual,
    hsourceLength', hconsumedLength', by
      rw [← hsourceTarget]
      exact Hparameter,
    hconsumedTarget,
    VEnv.IsDefEqU.wrapForalls_context Rcurrent.checking.tr.wf Hbase
      (hsourceLength'.trans hconsumedLength'.symm) Htarget⟩

/-- Replay the exact two-stage `mkForall` closure used to construct a minor,
without passing through its later installed declaration.  The field and
hypothesis domain lists are therefore the literal targets introduced by the
first executable pass. -/
theorem RecInfoMinorSemanticSource.sourceTypeTranslation
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : RecInfoMinorTypeShape}
    (HS : RecInfoMinorSemanticSource R S) :
    TrExprS HS.rootWF.venv recLparams HS.rootWF.mlctx.vlctx S.sourceType
        (VExpr.wrapForalls HS.fieldDomains
          (VExpr.wrapForalls HS.hypothesisDomains HS.motiveTarget)) ∧
      HS.rootWF.venv.IsType recLparams.length HS.rootWF.mlctx.vlctx.toCtx
        (VExpr.wrapForalls HS.fieldDomains
          (VExpr.wrapForalls HS.hypothesisDomains HS.motiveTarget)) := by
  have Hhypotheses := HS.hypothesesRecent.mkForallExact
    HS.motiveTranslation HS.motiveType
  have Hfields := HS.fieldsRecent.mkForallExact
    Hhypotheses.1 Hhypotheses.2
  have hfields := HS.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
    |>.mkForall_mono HS.hypothesesRecent.contextLE
      (S.sourceFullContext.lctx.mkForall S.hypotheses S.motiveApp)
  rw [S.sourceType_eq, ← S.sourceContext_eq, hfields]
  simpa [RecInfoMinorSemanticSource.fieldDomains,
    RecInfoMinorSemanticSource.hypothesisDomains] using Hfields

/-- Restrict the shared constructor-tail translation to the cached parameter
suffix.  The ambient motives and previously generated minors cannot occur in
that source by the retained field-traversal scope invariant. -/
theorem RecInfoMinorSemanticSource.parameterTranslationAtSuffix
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : RecInfoMinorTypeShape}
    (HS : RecInfoMinorSemanticSource R S) :
    ∃ target, TrExprS HS.rootWF.venv recLparams
      HS.parameterSuffix.parameterDecls HS.traversal.parameterTail target := by
  have Htr := HS.parameterTranslation
  rw [HS.parameterSuffix.context] at Htr
  have Hwf : (HS.parameterSuffix.ambientDecls ++
      HS.parameterSuffix.parameterDecls).WF HS.rootWF.venv
        recLparams.length := by
    rw [← HS.parameterSuffix.context]
    exact HS.rootWF.mlctx_wf.tr.wf
  have HnoBV : (HS.parameterSuffix.ambientDecls ++
      HS.parameterSuffix.parameterDecls).NoBV := by
    rw [← HS.parameterSuffix.context]
    exact HS.rootWF.mlctx.noBV
  exact TrExprS.dropFVarPrefix HS.rootWF.checking.tr.wf
    Hwf HnoBV Htr HS.parameterScope

/-- Compare the replayed unconsumed telescope with the exact consumed target
installed by production, in the original full source context. -/
theorem RecInfoMinorSemanticSource.replayedSourceDefEqConsumed
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams} {S : RecInfoMinorTypeShape}
    (HS : RecInfoMinorSemanticSource R S) :
    let replayed :=
      (VExpr.wrapForalls HS.fieldDomains
        (VExpr.wrapForalls HS.hypothesisDomains HS.motiveTarget)).lift'
          ((HS.fieldsRecent.contextExtension.trans
            HS.hypothesesRecent.contextExtension).shift.consN 0)
    HS.sourceWF.venv.IsDefEqU recLparams.length
      HS.sourceWF.mlctx.vlctx.toCtx replayed HS.consumedTarget := by
  dsimp only
  have Hreplayed :=
    (HS.fieldsRecent.contextExtension.trans
      HS.hypothesesRecent.contextExtension).weakTrExprS
        HS.sourceTypeTranslation.1
  have Hsource := Hreplayed.uniq HS.sourceWF.checking.tr.wf
    (.refl HS.sourceWF.checking.tr.wf HS.sourceWF.mlctx_wf.tr.wf)
    HS.consumption.source
  rcases HS.consumption.source_defeq with ⟨level, Hconsumed⟩
  exact Hsource.trans HS.sourceWF.checking.tr.wf
    HS.sourceWF.mlctx_wf.tr.wf.toCtx ⟨.sort level, Hconsumed⟩

structure RecInfoMinorSemanticSourceAt
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams) (S : RecInfoMinorTypeShape)
    (parameterDecls : VLCtx) where
  semantic : RecInfoMinorSemanticSource R S
  parameterDecls_eq : semantic.parameterSuffix.parameterDecls =
    parameterDecls

def RecInfoMinorSemanticSourceAt.mono
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {S : RecInfoMinorTypeShape} {parameterDecls : VLCtx}
    (HS : RecInfoMinorSemanticSourceAt Rroot S parameterDecls)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    RecInfoMinorSemanticSourceAt Rcurrent S parameterDecls where
  semantic := HS.semantic.mono Hext
  parameterDecls_eq := HS.parameterDecls_eq

/-- Every retained minor source carries its exact semantic extension into the
current recursor context.  Unlike `BindingContextLE`, this invariant is strong
enough to transport or restrict translated declaration types without guessing
how later named locals shift their de Bruijn targets. -/
def RecInfoMinorSemanticAlignment
    {c : AddInductive.Context} {recInfos : Array AddInductive.RecInfo}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (H : RecInfoTypeOrigins c recInfos) (parameterDecls : VLCtx) : Prop :=
  ∀ owner (howner : owner < recInfos.size)
    localIndex (hlocal : localIndex < H.minorTypes[owner]!.size),
    Nonempty (RecInfoMinorSemanticSourceAt R
      (H.minorShapes owner howner localIndex hlocal) parameterDecls)

theorem RecInfoMinorSemanticAlignment.ofEmpty
    (R : RecursorContextWF c recLparams)
    (H : RecInfoTypeOrigins c recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos) :
    RecInfoMinorSemanticAlignment R H parameterDecls := by
  intro owner howner localIndex hlocal
  have hsize := (H.minors owner howner).size_eq
  rw [Hempty owner howner] at hsize
  omega

theorem RecInfoMinorSemanticAlignment.mono
    {root current : AddInductive.Context} {recLparams : List Name}
    {recInfos : Array AddInductive.RecInfo}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {H : RecInfoTypeOrigins root recInfos}
    (A : RecInfoMinorSemanticAlignment Rroot H parameterDecls)
    (Hext : RecursorContextExtension Rroot Rcurrent) :
    RecInfoMinorSemanticAlignment Rcurrent (H.mono Hext.contextLE)
      parameterDecls := by
  intro owner howner localIndex hlocal
  rcases A owner howner localIndex hlocal with ⟨HS⟩
  exact ⟨HS.mono Hext⟩

theorem RecInfoMinorSemanticAlignment.addMinor
    {root current : AddInductive.Context} {recLparams : List Name}
    {recInfos : Array AddInductive.RecInfo}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    {H : RecInfoTypeOrigins root recInfos}
    (A : RecInfoMinorSemanticAlignment Rroot H parameterDecls)
    (Hext : RecursorContextExtension Rroot Rcurrent)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo)
    {minorTarget : VExpr}
    (Hminor : TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
      minorTy minorTarget)
    (HminorType : Rcurrent.venv.IsType recLparams.length
      Rcurrent.mlctx.vlctx.toCtx minorTarget)
    (Hshape : RecInfoMinorTypeShape)
    (HshapePosition :
      Hshape.localIndex = H.minorTypes[dIdx]!.size ∧
      Hshape.origin = minorTy)
    (HshapeSemantic : Nonempty
      (RecInfoMinorSemanticSourceAt Rcurrent Hshape parameterDecls)) :
    RecInfoMinorSemanticAlignment
      (Rcurrent.withLocalDecl (name := minorName) (bi := minorBi)
        Hminor HminorType)
      (H.addMinor dIdx hidx Hext.contextLE Rcurrent.toBindingContextWF
        minorName minorTy minorBi Hshape HshapePosition) parameterDecls := by
  let Rnext := Rcurrent.withLocalDecl (name := minorName) (bi := minorBi)
    Hminor HminorType
  let Hstep := RecursorContextExtension.withLocalDecl
    (name := minorName) (bi := minorBi) Rcurrent Hminor HminorType
  let nextMinorTypes := H.minorTypes.modify dIdx fun types =>
    types.push minorTy
  intro owner howner localIndex hlocal
  have hownerOld : owner < recInfos.size := by simpa using howner
  have hownerTypes : owner < H.minorTypes.size := by
    rw [H.minorTypes_size]
    exact hownerOld
  by_cases hdi : dIdx = owner
  · subst owner
    have horigin : nextMinorTypes[dIdx]! =
        H.minorTypes[dIdx]!.push minorTy := by
      dsimp [nextMinorTypes]
      rw [mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx _
        hownerTypes]
    change localIndex < nextMinorTypes[dIdx]!.size at hlocal
    rw [horigin] at hlocal
    by_cases hlast : localIndex = H.minorTypes[dIdx]!.size
    · subst localIndex
      rcases HshapeSemantic with ⟨HS⟩
      simpa [RecInfoTypeOrigins.addMinor, nextMinorTypes,
        mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx
          (fun types => types.push minorTy) hownerTypes] using
        (show Nonempty
            (RecInfoMinorSemanticSourceAt Rnext Hshape parameterDecls) from
          ⟨HS.mono Hstep⟩)
    · have hold : localIndex < H.minorTypes[dIdx]!.size := by
        simp only [Array.size_push] at hlocal
        omega
      rcases A dIdx hidx localIndex hold with ⟨HS⟩
      have hget : (H.minorTypes[dIdx]!.push minorTy)[localIndex]! =
          H.minorTypes[dIdx]![localIndex]! := by
        have hpush : localIndex <
            (H.minorTypes[dIdx]!.push minorTy).size := by simp; omega
        rw [getElem!_pos (H.minorTypes[dIdx]!.push minorTy) localIndex hpush,
          getElem!_pos H.minorTypes[dIdx]! localIndex hold]
        exact Array.getElem_push_lt hold
      simpa [RecInfoTypeOrigins.addMinor, hlast,
        mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx
          (fun types => types.push minorTy) hownerTypes, hget] using
        (show Nonempty (RecInfoMinorSemanticSourceAt Rnext
            (H.minorShapes dIdx hidx localIndex hold) parameterDecls) from
          ⟨HS.mono (Hext.trans Hstep)⟩)
  · have horigin : nextMinorTypes[owner]! = H.minorTypes[owner]! := by
      dsimp [nextMinorTypes]
      rw [mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx owner _
        hownerTypes hdi]
    change localIndex < nextMinorTypes[owner]!.size at hlocal
    rw [horigin] at hlocal
    rcases A owner hownerOld localIndex hlocal with ⟨HS⟩
    simpa [RecInfoTypeOrigins.addMinor, hdi,
      mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx owner
        (fun types => types.push minorTy) hownerTypes hdi] using
      (show Nonempty (RecInfoMinorSemanticSourceAt Rnext
          (H.minorShapes owner hownerOld localIndex hlocal)
            parameterDecls) from
        ⟨HS.mono (Hext.trans Hstep)⟩)

theorem RecInfoMinorSourceAlignment.ofEmpty
    (H : RecInfoTypeOrigins c recInfos)
    (Hempty : RecInfoMinorsEmpty recInfos) :
    RecInfoMinorSourceAlignment stats indTypes H := by
  intro owner howner _ localIndex hlocal
  have hsize := (H.minors owner howner).size_eq
  rw [Hempty owner howner] at hsize
  omega

theorem RecInfoMinorSourceAlignment.mono
    {c c' : AddInductive.Context}
    {recInfos : Array AddInductive.RecInfo}
    {H : RecInfoTypeOrigins c recInfos}
    (A : RecInfoMinorSourceAlignment stats indTypes H)
    (hle : BindingContextLE c c') :
    RecInfoMinorSourceAlignment stats indTypes (H.mono hle) := by
  intro owner howner hsourceOwner localIndex hlocal
  rcases A owner howner hsourceOwner localIndex hlocal with
    ⟨horigin, hindex, hsource, hhypothesisOrigins,
      traversal, htraversal, hconstructor,
      hfields, hrecursive, hstats, hvalid, hmotiveApp,
      hroot, hterminal,
      hsourceContext⟩
  exact ⟨horigin, hindex, hsource, hhypothesisOrigins,
    traversal, htraversal, hconstructor,
    hfields, hrecursive, hstats, hvalid, hmotiveApp,
    hroot.trans hle,
    hterminal.trans hle, hsourceContext.trans hle⟩

theorem RecInfoMinorSourceAlignment.addMinor
    {c cMinorTy : AddInductive.Context}
    {recInfos : Array AddInductive.RecInfo}
    {H : RecInfoTypeOrigins c recInfos}
    (A : RecInfoMinorSourceAlignment stats indTypes H)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hsourceIdx : dIdx < indTypes.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo)
    (Hshape : RecInfoMinorTypeShape)
    (HshapePosition :
      Hshape.localIndex = H.minorTypes[dIdx]!.size ∧
      Hshape.origin = minorTy)
    (hsource : Hshape.sourceConstructors = indTypes[dIdx]!.ctors)
    (hhypothesisOrigins : Hshape.HasHypothesisTypeOrigins stats recInfos)
    (htraversal : ∃ traversal,
      Hshape.traversal = some traversal ∧
      traversal.constructor = Hshape.constructor ∧
      traversal.fields = Hshape.fields ∧
      traversal.recursiveFields = Hshape.recursiveFields ∧
      traversal.stats = stats ∧
      AddInductive.isValidIndApp? stats traversal.terminal = some
        (AddInductive.getIIndices stats traversal.terminal).1 ∧
      Hshape.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN recInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const Hshape.constructor.name stats.levels)
              stats.params)
            Hshape.fields)) ∧
      BindingContextLE traversal.rootContext cMinorTy ∧
      BindingContextLE traversal.terminalContext cMinorTy ∧
      BindingContextLE Hshape.sourceFullContext cMinorTy) :
    RecInfoMinorSourceAlignment stats indTypes
      (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy minorBi
        Hshape HshapePosition) := by
  let cMinor : AddInductive.Context := { cMinorTy with
    ngen := cMinorTy.ngen.next
    lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
      minorName minorTy minorBi }
  let hstep := BindingContextLE.withLocalDecl cMinorTy HcMinorTy
    minorName minorTy minorBi
  let hfinal := hle.trans hstep
  let nextRecInfos := recInfos.modify dIdx fun info =>
    { info with minors := info.minors.push (.fvar ⟨cMinorTy.ngen.curr⟩) }
  have hmotives : nextRecInfos.map (·.motive) =
      recInfos.map (·.motive) := by
    apply Array.ext
    · simp [nextRecInfos]
    · intro owner hleft hright
      by_cases howner : dIdx = owner <;>
        simp [nextRecInfos, Array.getElem_modify, howner]
  have motiveAppNext (S : RecInfoMinorTypeShape)
      (traversal : RecInfoMinorTraversalShape)
      (Happ : S.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN recInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const S.constructor.name stats.levels) stats.params)
            S.fields))) :
      S.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN nextRecInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const S.constructor.name stats.levels) stats.params)
            S.fields)) := by
    rw [Happ]
    have hmotiveGet : ∀ motiveOwner : Nat,
        AddInductive.RecInfo.motive nextRecInfos[motiveOwner]! =
          AddInductive.RecInfo.motive recInfos[motiveOwner]! := by
      intro motiveOwner
      by_cases hi : motiveOwner < recInfos.size
      · by_cases hdi : dIdx = motiveOwner <;>
          simp [nextRecInfos, Array.getElem!_eq_getD, Array.getD, hi,
            Array.getElem_modify, hdi]
      · simp [nextRecInfos, Array.getElem!_eq_getD, Array.getD, hi]
    rcases AddInductive.getIIndices stats traversal.terminal with
      ⟨motiveOwner, indices⟩
    simp only
    rw [hmotiveGet]
  have hypothesisOriginsNext (S : RecInfoMinorTypeShape)
      (HS : S.HasHypothesisTypeOrigins stats recInfos) :
      S.HasHypothesisTypeOrigins stats nextRecInfos := by
    unfold RecInfoMinorTypeShape.HasHypothesisTypeOrigins at HS ⊢
    cases horigins : S.hypothesis_type_origins with
    | none => simp [horigins] at HS
    | some origins =>
      simp only [horigins] at HS ⊢
      exact ⟨HS.1, HS.2.trans hmotives.symm⟩
  have htraversalFinal : ∃ traversal,
      Hshape.traversal = some traversal ∧
      traversal.constructor = Hshape.constructor ∧
      traversal.fields = Hshape.fields ∧
      traversal.recursiveFields = Hshape.recursiveFields ∧
      traversal.stats = stats ∧
      AddInductive.isValidIndApp? stats traversal.terminal = some
        (AddInductive.getIIndices stats traversal.terminal).1 ∧
      Hshape.motiveApp = (
        let (motiveOwner, indices) :=
          AddInductive.getIIndices stats traversal.terminal
        Expr.app
          (mkAppN nextRecInfos[motiveOwner]!.motive indices)
          (mkAppN
            (mkAppN (.const Hshape.constructor.name stats.levels)
              stats.params)
            Hshape.fields)) ∧
      BindingContextLE traversal.rootContext cMinor ∧
      BindingContextLE traversal.terminalContext cMinor ∧
      BindingContextLE Hshape.sourceFullContext cMinor := by
    rcases htraversal with
      ⟨traversal, hsome, hconstructor, hfields, hrecursive, hstats,
        hvalid, hmotiveApp, hroot, hterminal, hsourceContext⟩
    exact ⟨traversal, hsome, hconstructor, hfields, hrecursive, hstats,
      hvalid, motiveAppNext Hshape traversal hmotiveApp,
      hroot.trans hstep,
      hterminal.trans hstep,
      hsourceContext.trans hstep⟩
  have Aextended : ∀ owner (howner : owner < recInfos.size)
      (hsourceOwner : owner < indTypes.size)
      localIndex (hlocal : localIndex < H.minorTypes[owner]!.size),
      let S := H.minorShapes owner howner localIndex hlocal;
        S.origin = H.minorTypes[owner]![localIndex]! ∧
        S.localIndex = localIndex ∧
        S.sourceConstructors = indTypes[owner]!.ctors ∧
        S.HasHypothesisTypeOrigins stats nextRecInfos ∧
          ∃ traversal, S.traversal = some traversal ∧
            traversal.constructor = S.constructor ∧
            traversal.fields = S.fields ∧
            traversal.recursiveFields = S.recursiveFields ∧
            traversal.stats = stats ∧
            AddInductive.isValidIndApp? stats traversal.terminal = some
              (AddInductive.getIIndices stats traversal.terminal).1 ∧
            S.motiveApp = (
              let (motiveOwner, indices) :=
                AddInductive.getIIndices stats traversal.terminal
              Expr.app
                (mkAppN nextRecInfos[motiveOwner]!.motive indices)
                (mkAppN
                  (mkAppN (.const S.constructor.name stats.levels)
                    stats.params)
                  S.fields)) ∧
            BindingContextLE traversal.rootContext cMinor ∧
            BindingContextLE traversal.terminalContext cMinor ∧
            BindingContextLE S.sourceFullContext cMinor := by
    intro owner howner hsourceOwner localIndex hlocal
    rcases A owner howner hsourceOwner localIndex hlocal with
      ⟨horigin, hindex, hsource, hhypothesisOrigins,
        traversal, hsome, hconstructor,
        hfields, hrecursive, hstats, hvalid, hmotiveApp,
        hroot, hterminal,
        hsourceContext⟩
    exact ⟨horigin, hindex, hsource,
      hypothesisOriginsNext _ hhypothesisOrigins,
      traversal, hsome, hconstructor,
      hfields, hrecursive, hstats, hvalid,
      motiveAppNext _ traversal hmotiveApp,
      hroot.trans hfinal,
      hterminal.trans hfinal, hsourceContext.trans hfinal⟩
  intro owner howner hsourceOwner localIndex hlocal
  by_cases hdi : dIdx = owner
  · subst owner
    have hiTypes : dIdx < H.minorTypes.size := by
      rw [H.minorTypes_size]
      exact hidx
    have horigin : (H.minorTypes.modify dIdx fun types =>
        types.push minorTy)[dIdx]! = H.minorTypes[dIdx]!.push minorTy := by
      rw [mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx _
        hiTypes]
    change localIndex < (H.minorTypes.modify dIdx fun types =>
      types.push minorTy)[dIdx]!.size at hlocal
    rw [horigin] at hlocal
    by_cases hlast : localIndex = H.minorTypes[dIdx]!.size
    · subst localIndex
      simpa [RecInfoTypeOrigins.addMinor,
        mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx
          (fun types => types.push minorTy) hiTypes,
        getElem!_pos (H.minorTypes[dIdx]!.push minorTy)
          H.minorTypes[dIdx]!.size (by simp)] using
        ⟨HshapePosition.2, HshapePosition.1, hsource,
          hypothesisOriginsNext _ hhypothesisOrigins, htraversalFinal⟩
    · have hold : localIndex < H.minorTypes[dIdx]!.size := by
        simp only [Array.size_push] at hlocal
        omega
      have hget : (H.minorTypes[dIdx]!.push minorTy)[localIndex]! =
          H.minorTypes[dIdx]![localIndex]! := by
        have hpush : localIndex <
            (H.minorTypes[dIdx]!.push minorTy).size := by simp; omega
        rw [getElem!_pos (H.minorTypes[dIdx]!.push minorTy) localIndex hpush,
          getElem!_pos H.minorTypes[dIdx]! localIndex hold]
        exact Array.getElem_push_lt hold
      simpa [RecInfoTypeOrigins.addMinor, hlast,
        mkRecInfos.loopCtors.getElemBang_modify_self H.minorTypes dIdx
          (fun types => types.push minorTy) hiTypes, hget] using
        Aextended dIdx hidx hsourceIdx localIndex hold
  · have hownerOld : owner < recInfos.size := by simpa using howner
    have hownerTypes : owner < H.minorTypes.size := by
      rw [H.minorTypes_size]
      exact hownerOld
    have horigin : (H.minorTypes.modify dIdx fun types =>
        types.push minorTy)[owner]! = H.minorTypes[owner]! := by
      rw [mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx owner _
        hownerTypes hdi]
    change localIndex < (H.minorTypes.modify dIdx fun types =>
      types.push minorTy)[owner]!.size at hlocal
    rw [horigin] at hlocal
    have hlocalOld : localIndex < H.minorTypes[owner]!.size := by
      exact hlocal
    simpa [RecInfoTypeOrigins.addMinor, hdi,
      mkRecInfos.loopCtors.getElemBang_modify_ne H.minorTypes dIdx owner
        (fun types => types.push minorTy) hownerTypes hdi] using
      Aextended owner hownerOld hsourceOwner localIndex hlocalOld

private def recInfoMinorIds (info : AddInductive.RecInfo) : List FVarId :=
  ExprArrayFVarIds info.minors

private theorem recInfoMinorIds_flatMap_eq_nil
    (infos : List AddInductive.RecInfo)
    (hempty : ∀ info ∈ infos, info.minors.size = 0) :
    infos.flatMap recInfoMinorIds = [] := by
  induction infos with
  | nil => rfl
  | cons info infos ih =>
    have hhead : info.minors = #[] :=
      Array.eq_empty_of_size_eq_zero (hempty info (by simp))
    have htail : ∀ tailInfo ∈ infos, tailInfo.minors.size = 0 := by
      intro tailInfo htailInfo
      exact hempty tailInfo (by simp [htailInfo])
    rw [List.flatMap_cons, ih htail]
    simp [recInfoMinorIds, hhead, ExprArrayFVarIds]

/-- Appending a minor in row `i` appends it to the flattened minor order when
all later rows are still empty. -/
private theorem recInfoMinorIds_modify_eq
    (infos : List AddInductive.RecInfo) (i : Nat) (hi : i < infos.length)
    (minor : Expr)
    (hlater : ∀ j, i < j → j < infos.length →
      infos[j]!.minors.size = 0) :
    (infos.modify i fun info =>
      { info with minors := info.minors.push minor }).flatMap
        recInfoMinorIds =
      infos.flatMap recInfoMinorIds ++ [recursorFVarId minor] := by
  induction infos generalizing i with
  | nil => simp at hi
  | cons info infos ih =>
    cases i with
    | zero =>
      have htailRows : ∀ tailInfo ∈ infos,
          tailInfo.minors.size = 0 := by
        intro tailInfo htailInfo
        rcases List.mem_iff_getElem.mp htailInfo with ⟨j, hj, rfl⟩
        have h := hlater (j + 1) (by omega) (by simpa using hj)
        rw [getElem!_pos (info :: infos) (j + 1) (by simpa using hj)] at h
        simpa using h
      have htail := recInfoMinorIds_flatMap_eq_nil infos htailRows
      simp [List.modify, recInfoMinorIds, ExprArrayFVarIds, htail,
        List.append_assoc]
    | succ i =>
      have hi' : i < infos.length := by simpa using hi
      have hlater' : ∀ j, i < j → j < infos.length →
          infos[j]!.minors.size = 0 := by
        intro j hij hj
        have h := hlater (j + 1) (by omega) (by simpa using hj)
        simpa using h
      rw [List.modify, List.modifyTailIdx_succ_cons]
      change (recInfoMinorIds info ++
        (infos.modify i fun info =>
          { info with minors := info.minors.push minor }).flatMap
            recInfoMinorIds) = _
      rw [ih i hi' hlater']
      simp [List.append_assoc]

theorem RecInfoBindings.addMinor_flatMinors_fvars
    (H : RecInfoBindings c recInfos)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo)
    (hlater : ∀ i, dIdx < i → i < recInfos.size →
      recInfos[i]!.minors.size = 0) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy minorBi
      ).flatMinors.fvars = H.flatMinors.fvars ++
        [(⟨cMinorTy.ngen.curr⟩ : FVarId)] := by
  dsimp only
  let minor := Expr.fvar ⟨cMinorTy.ngen.curr⟩
  let next := recInfos.modify dIdx fun info =>
    { info with minors := info.minors.push minor }
  have hlaterList : ∀ j, dIdx < j → j < recInfos.toList.length →
      recInfos.toList[j]!.minors.size = 0 := by
    intro j hdj hj
    have hj' : j < recInfos.size := by simpa using hj
    rw [getElem!_pos recInfos.toList j (by simpa using hj)]
    have h := hlater j hdj hj'
    rw [getElem!_pos recInfos j hj'] at h
    simpa using h
  have hflat := recInfoMinorIds_modify_eq recInfos.toList dIdx
    (by simpa using hidx) minor hlaterList
  rw [← (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy
      minorBi).flatMinors.exprArrayFVarIds,
    ← H.flatMinors.exprArrayFVarIds]
  change ((recInfos.toList.modify dIdx fun info =>
      { info with minors := info.minors.push minor }).flatMap
        (fun info => info.minors.toList.map recursorFVarId)) =
    recInfos.toList.flatMap
      (fun info => info.minors.toList.map recursorFVarId) ++
        [recursorFVarId minor] at hflat
  simpa [next, minor, recInfoMinorIds, ExprArrayFVarIds,
    Array.toList_flatMap, List.map_flatMap, recursorFVarId] using hflat

theorem RecInfoBindings.addMinor_motives_fvars
    (H : RecInfoBindings c recInfos)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy minorBi
      ).motives.fvars = H.motives.fvars := by
  dsimp only
  rw [← (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy
      minorBi).motives.exprArrayFVarIds,
    ← H.motives.exprArrayFVarIds]
  apply congrArg ExprArrayFVarIds
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    by_cases hdi : dIdx = i <;> simp [Array.getElem_modify, hdi]

private theorem recInfoMinorIds_modify_perm
    (infos : List AddInductive.RecInfo) (i : Nat) (hi : i < infos.length)
    (minor : Expr) :
    ((infos.modify i fun info =>
      { info with minors := info.minors.push minor }).flatMap
        recInfoMinorIds).Perm
      (infos.flatMap recInfoMinorIds ++ [recursorFVarId minor]) := by
  induction infos generalizing i with
  | nil => simp at hi
  | cons info infos ih =>
    cases i with
    | zero =>
      rw [List.modify, List.modifyTailIdx_zero, List.modifyHead_cons]
      simp only [List.flatMap_cons, recInfoMinorIds,
        ExprArrayFVarIds, Array.toList_push, List.map_append,
        List.map_cons, List.map_nil]
      simpa [List.append_assoc] using
        (List.Perm.refl
          (info.minors.toList.map recursorFVarId)).append
            (List.perm_append_comm :
              [recursorFVarId minor] ++ infos.flatMap recInfoMinorIds ~
                infos.flatMap recInfoMinorIds ++ [recursorFVarId minor])
    | succ i =>
      have hi' : i < infos.length := by simpa using hi
      rw [List.modify, List.modifyTailIdx_succ_cons]
      change (recInfoMinorIds info ++
        (infos.modify i fun info =>
          { info with minors := info.minors.push minor }).flatMap
            recInfoMinorIds).Perm _
      simpa only [List.flatMap_cons, List.append_assoc] using
        (List.Perm.refl (recInfoMinorIds info)).append
          (ih i hi')

theorem RecInfoBindings.addMinor_allFvars_perm
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    let hall : BindingContextLE c cMinor := hle.trans <|
      BindingContextLE.withLocalDecl cMinorTy HcMinorTy
        minorName minorTy minorBi
    ((H.addMinor dIdx hidx hle HcMinorTy minorName minorTy minorBi).allFvars
      (Hparams.mono hall)).Perm
      (H.allFvars Hparams ++ [(⟨cMinorTy.ngen.curr⟩ : FVarId)]) := by
  dsimp only
  let minor := Expr.fvar ⟨cMinorTy.ngen.curr⟩
  let next := recInfos.modify dIdx fun info =>
    { info with minors := info.minors.push minor }
  have hMotives : next.map (·.motive) = recInfos.map (·.motive) := by
    apply Array.ext
    · simp [next]
    · intro i hiLeft hiRight
      by_cases hdi : dIdx = i <;> simp [next, Array.getElem_modify, hdi]
  have hMajors : next.map (·.major) = recInfos.map (·.major) := by
    apply Array.ext
    · simp [next]
    · intro i hiLeft hiRight
      by_cases hdi : dIdx = i <;> simp [next, Array.getElem_modify, hdi]
  have hIndexRows : next.map (·.indices) = recInfos.map (·.indices) := by
    apply Array.ext
    · simp [next]
    · intro i hiLeft hiRight
      by_cases hdi : dIdx = i <;> simp [next, Array.getElem_modify, hdi]
  have hIndices : next.flatMap (·.indices) =
      recInfos.flatMap (·.indices) := by
    rw [Array.flatMap_def, Array.flatMap_def, hIndexRows]
  have hMinors :
      (ExprArrayFVarIds (next.flatMap (·.minors))).Perm
        (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++
          [(⟨cMinorTy.ngen.curr⟩ : FVarId)]) := by
    have h := recInfoMinorIds_modify_perm recInfos.toList dIdx
      (by simpa using hidx) minor
    change ((recInfos.toList.modify dIdx fun info =>
        { info with minors := info.minors.push minor }).flatMap
          (fun info => info.minors.toList.map recursorFVarId)).Perm
      (recInfos.toList.flatMap
        (fun info => info.minors.toList.map recursorFVarId) ++
          [recursorFVarId minor]) at h
    dsimp [minor, recursorFVarId] at h
    simpa [next, minor, ExprArrayFVarIds, Array.toList_flatMap,
      List.map_flatMap] using h
  unfold RecInfoBindings.allFvars
  change (ExprArrayFVarIds stats.params ++
    (ExprArrayFVarIds (next.map (·.motive)) ++
      (ExprArrayFVarIds (next.flatMap (·.minors)) ++
        (ExprArrayFVarIds (next.flatMap (·.indices)) ++
          ExprArrayFVarIds (next.map (·.major)))))).Perm _
  rw [hMotives, hIndices, hMajors]
  let pre := ExprArrayFVarIds stats.params ++
    ExprArrayFVarIds (recInfos.map (·.motive))
  let suffix := ExprArrayFVarIds (recInfos.flatMap (·.indices)) ++
    ExprArrayFVarIds (recInfos.map (·.major))
  have hMove :
      (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++
        [(⟨cMinorTy.ngen.curr⟩ : FVarId)]) ++ suffix ~
      (ExprArrayFVarIds (recInfos.flatMap (·.minors)) ++ suffix) ++
        [(⟨cMinorTy.ngen.curr⟩ : FVarId)] := by
    simpa [List.append_assoc] using
      (List.Perm.refl
        (ExprArrayFVarIds (recInfos.flatMap (·.minors)))).append
          (List.perm_append_comm :
            [(⟨cMinorTy.ngen.curr⟩ : FVarId)] ++ suffix ~
              suffix ++ [(⟨cMinorTy.ngen.curr⟩ : FVarId)])
  have hTail := (hMinors.append (List.Perm.refl suffix)).trans hMove
  simpa [pre, suffix, List.append_assoc] using
    (List.Perm.refl pre).append hTail

theorem RecInfoBindings.addMinor_noAlias
    {stats : AddInductive.InductiveStats}
    (H : RecInfoBindings c recInfos)
    (Hparams : BoundFVarArray c stats.params)
    (hnoalias : H.NoAlias Hparams)
    (dIdx : Nat) (hidx : dIdx < recInfos.size)
    (hle : BindingContextLE c cMinorTy)
    (HcMinorTy : BindingContextWF cMinorTy)
    (minorName : Name) (minorTy : Expr) (minorBi : BinderInfo) :
    let cMinor : AddInductive.Context := { cMinorTy with
      ngen := cMinorTy.ngen.next
      lctx := cMinorTy.lctx.mkLocalDecl ⟨cMinorTy.ngen.curr⟩
        minorName minorTy minorBi }
    let hall : BindingContextLE c cMinor := hle.trans <|
      BindingContextLE.withLocalDecl cMinorTy HcMinorTy
        minorName minorTy minorBi
    (H.addMinor dIdx hidx hle HcMinorTy minorName minorTy minorBi).NoAlias
      (Hparams.mono hall) := by
  dsimp only
  let minor : FVarId := ⟨cMinorTy.ngen.curr⟩
  have hfresh : minor ∉ H.allFvars Hparams := by
    intro hmem
    exact HcMinorTy.current_not_mem <| hle <|
      H.allFvars_members Hparams minor hmem
  have hcombined : (H.allFvars Hparams ++ [minor]).Nodup := by
    apply List.nodup_append.mpr
    exact ⟨hnoalias, by simp, by
      intro fv hfv fv' hfv'
      simp only [List.mem_singleton] at hfv'
      subst fv'
      exact fun heq => hfresh (heq ▸ hfv)⟩
  apply (H.addMinor_allFvars_perm Hparams dIdx hidx hle HcMinorTy
    minorName minorTy minorBi).symm.nodup
  simpa [minor] using hcombined


end VerifyInductive
end Lean4Lean
