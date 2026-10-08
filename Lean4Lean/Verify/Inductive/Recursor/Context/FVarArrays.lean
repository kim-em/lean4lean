import Lean4Lean.Verify.Inductive.Recursor.Context.ForallTelescope

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

theorem BindingContextLE.withLocalDecl
    (c : AddInductive.Context) (Hc : BindingContextWF c)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    BindingContextLE c { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } where
  fvars := by
    intro fv hfv
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    exact Or.inr hfv
  declarations := by
    intro fv hfv
    simp only [LocalContext.mkLocalDecl, LocalContext.find?,
      Hc.wf.map_wf.find?_insert]
    rw [if_neg]
    intro heq
    have : fv = ⟨c.ngen.curr⟩ := (LawfulBEq.eq_of_beq heq).symm
    subst fv
    exact Hc.current_not_mem hfv
  env_eq := rfl
  lparams_eq := rfl
  safety_eq := rfl
  allowPrimitive_eq := rfl
  fuel_eq := rfl

/-- Variant of `BindingContextLE.withLocalDecl` for a binder opened in both contexts. -/
theorem BindingContextLE.withCheckedLocalDecl
    {base : LocalContext}
    (c : AddInductive.Context) (Hc : BindingContextWF c)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    BindingContextLE c { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
      checkLCtx := base.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } where
  fvars := by
    intro fv hfv
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    exact Or.inr hfv
  declarations := by
    intro fv hfv
    simp only [LocalContext.mkLocalDecl, LocalContext.find?,
      Hc.wf.map_wf.find?_insert]
    rw [if_neg]
    intro heq
    have : fv = ⟨c.ngen.curr⟩ := (LawfulBEq.eq_of_beq heq).symm
    subst fv
    exact Hc.current_not_mem hfv
  env_eq := rfl
  lparams_eq := rfl
  safety_eq := rfl
  allowPrimitive_eq := rfl
  fuel_eq := rfl

/-- An executable recursor-context extension together with its exact semantic
free-variable weakening.  `BindingContextLE` is enough for looking up raw
local declarations, but it does not determine how translated de Bruijn
targets move.  The explicit `FVLift'` is the missing transport datum for
first-pass motive certificates consumed under later constructor binders. -/
structure RecursorContextExtension
    {root current : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (Rcurrent : RecursorContextWF current recLparams) where
  contextLE : BindingContextLE root current
  venv_eq : Rcurrent.venv = Rroot.venv
  shift : Lift
  lift : VLCtx.FVLift' Rroot.mlctx.vlctx Rcurrent.mlctx.vlctx
    0 shift 0

def RecursorContextExtension.refl
    (R : RecursorContextWF c recLparams) :
    RecursorContextExtension R R where
  contextLE := BindingContextLE.refl c
  venv_eq := rfl
  shift := .refl
  lift := .refl

def RecursorContextExtension.trans
    (H₁ : RecursorContextExtension R₁ R₂)
    (H₂ : RecursorContextExtension R₂ R₃) :
    RecursorContextExtension R₁ R₃ where
  contextLE := H₁.contextLE.trans H₂.contextLE
  venv_eq := H₂.venv_eq.trans H₁.venv_eq
  shift := H₁.shift.comp H₂.shift
  lift := H₁.lift.comp H₂.lift

/-- The exact one-local extension corresponding to
`RecursorContextWF.withLocalDecl`. -/
def RecursorContextExtension.withLocalDecl
    (R : RecursorContextWF c recLparams)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty') :
    RecursorContextExtension R
      (R.withLocalDecl (name := name) (bi := bi) htr hty) where
  contextLE := BindingContextLE.withLocalDecl c R.toBindingContextWF
    name ty bi
  venv_eq := rfl
  shift := (.refl : Lift).skipN 1
  lift := .skip_fvar _ _ .refl

/-- Transport a syntax translation along an exact recursor-context
extension.  The concrete expression is unchanged; its abstract target is
shifted by precisely the retained `Lift`. -/
theorem RecursorContextExtension.weakTrExprS
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    (H : RecursorContextExtension Rroot Rcurrent)
    (htr : TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx source target) :
    TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx source
      (target.lift' (H.shift.consN 0)) := by
  have hcurrentWF : VLCtx.WF Rroot.venv recLparams.length
      Rcurrent.mlctx.vlctx := by
    simpa only [H.venv_eq] using Rcurrent.mlctx_wf.tr.wf
  have hweak := htr.weakFV' Rroot.checking.tr.wf.ordered H.lift
    hcurrentWF
  simpa only [H.venv_eq] using hweak

/-- Transport a typing derivation along the context lift carried by an exact
recursor extension. -/
theorem RecursorContextExtension.weakHasType
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    (H : RecursorContextExtension Rroot Rcurrent)
    (htype : Rroot.venv.HasType recLparams.length Rroot.mlctx.vlctx.toCtx
      term type) :
    Rcurrent.venv.HasType recLparams.length Rcurrent.mlctx.vlctx.toCtx
      (term.lift' (H.shift.consN 0))
      (type.lift' (H.shift.consN 0)) := by
  have hweak := htype.weak' Rroot.checking.tr.wf.ordered H.lift.toCtx
  simpa only [H.venv_eq] using hweak

/-- Transport typehood along an exact recursor extension. -/
theorem RecursorContextExtension.weakIsType
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    (H : RecursorContextExtension Rroot Rcurrent)
    (htype : Rroot.venv.IsType recLparams.length Rroot.mlctx.vlctx.toCtx
      type) :
    Rcurrent.venv.IsType recLparams.length Rcurrent.mlctx.vlctx.toCtx
      (type.lift' (H.shift.consN 0)) := by
  have hweak := htype.weak' Rroot.checking.tr.wf.ordered H.lift.toCtx
  simpa only [H.venv_eq] using hweak

/-- Transport definitional equality along an exact recursor extension. -/
theorem RecursorContextExtension.weakDefEqU
    {root current : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {Rcurrent : RecursorContextWF current recLparams}
    (H : RecursorContextExtension Rroot Rcurrent)
    (hdefeq : Rroot.venv.IsDefEqU recLparams.length
      Rroot.mlctx.vlctx.toCtx left right) :
    Rcurrent.venv.IsDefEqU recLparams.length Rcurrent.mlctx.vlctx.toCtx
      (left.lift' (H.shift.consN 0))
      (right.lift' (H.shift.consN 0)) := by
  have hweak := hdefeq.weak' Rroot.checking.tr.wf.ordered H.lift.toCtx
  simpa only [H.venv_eq] using hweak

def BoundFVarArray.empty (c : AddInductive.Context) :
    BoundFVarArray c #[] where
  fvars := []
  expressions := rfl
  members _ h := by simp at h

def BoundFVarArray.weaken
    (H : BoundFVarArray c xs) (name : Name) (ty : Expr) (bi : BinderInfo) :
    BoundFVarArray { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } xs where
  fvars := H.fvars
  expressions := H.expressions
  members := by
    intro fv hfv
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    exact Or.inr (H.members fv hfv)

def BoundFVarArray.mono
    (H : BoundFVarArray c xs) (hle : BindingContextLE c c') :
    BoundFVarArray c' xs where
  fvars := H.fvars
  expressions := H.expressions
  members fv hfv := hle (H.members fv hfv)

def BoundFVarArray.monoFVars
    (H : BoundFVarArray c xs)
    (hle : c.lctx.fvars ⊆ c'.lctx.fvars) :
    BoundFVarArray c' xs where
  fvars := H.fvars
  expressions := H.expressions
  members fv hfv := hle (H.members fv hfv)

def BoundFVarArray.pushCurrent
    (H : BoundFVarArray c xs) (name : Name) (ty : Expr) (bi : BinderInfo) :
    BoundFVarArray { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      (xs.push (.fvar ⟨c.ngen.curr⟩)) where
  fvars := H.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)]
  expressions := calc
    xs.push (.fvar ⟨c.ngen.curr⟩) =
        ((H.fvars.map Expr.fvar).toArray).push (.fvar ⟨c.ngen.curr⟩) :=
      congrArg (fun ys => ys.push (.fvar ⟨c.ngen.curr⟩)) H.expressions
    _ = ((H.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)]).map Expr.fvar).toArray := by
      simp
  members := by
    intro fv hfv
    simp only [List.mem_append, List.mem_singleton] at hfv
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    rcases hfv with hfv | rfl
    · exact Or.inr (H.members fv hfv)
    · exact Or.inl rfl

/-- Variant of `BoundFVarArray.pushCurrent` for a binder opened in both contexts. -/
def BoundFVarArray.pushCurrentChecked
    {base : LocalContext}
    (H : BoundFVarArray c xs) (name : Name) (ty : Expr) (bi : BinderInfo) :
    BoundFVarArray { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
      checkLCtx := base.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      (xs.push (.fvar ⟨c.ngen.curr⟩)) where
  fvars := H.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)]
  expressions := calc
    xs.push (.fvar ⟨c.ngen.curr⟩) =
        ((H.fvars.map Expr.fvar).toArray).push (.fvar ⟨c.ngen.curr⟩) :=
      congrArg (fun ys => ys.push (.fvar ⟨c.ngen.curr⟩)) H.expressions
    _ = ((H.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)]).map Expr.fvar).toArray := by
      simp
  members := by
    intro fv hfv
    simp only [List.mem_append, List.mem_singleton] at hfv
    simp only [LocalContext.fvars, LocalContext.mkLocalDecl_toList,
      List.map_cons, LocalDecl.fvarId, List.mem_cons]
    rcases hfv with hfv | rfl
    · exact Or.inr (H.members fv hfv)
    · exact Or.inl rfl

def BoundFVarArray.toLocalForallSelection
    (H : BoundFVarArray c xs) (Hc : BindingContextWF c) :
    LocalForallSelection c.lctx xs where
  fvars := H.fvars
  expressions := H.expressions
  declarations fv hfv := Hc.findCDecl fv (H.members fv hfv)

def BoundFVarArray.append
    (H₁ : BoundFVarArray c xs) (H₂ : BoundFVarArray c ys) :
    BoundFVarArray c (xs ++ ys) where
  fvars := H₁.fvars ++ H₂.fvars
  expressions := by
    simp [H₁.expressions, H₂.expressions]
  members := by
    intro fv hfv
    simp only [List.mem_append] at hfv
    rcases hfv with hfv | hfv
    · exact H₁.members fv hfv
    · exact H₂.members fv hfv

theorem BoundFVarArray.mkForall_mono
    (H : BoundFVarArray c xs) (hle : BindingContextLE c c')
    (body : Expr) :
    c'.lctx.mkForall xs body = c.lctx.mkForall xs body := by
  rcases H with ⟨fvars, rfl, members⟩
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN,
    LocalContext.mkForall, LocalContext.mkBinding_eqN]
  apply LocalContext.mkBindingListN_congr
  intro fv hfv
  exact hle.declarations fv (members fv hfv)

theorem BoundFVarArray.mkLambda_mono
    (H : BoundFVarArray c xs) (hle : BindingContextLE c c')
    (body : Expr) :
    c'.lctx.mkLambda xs body = c.lctx.mkLambda xs body := by
  rcases H with ⟨fvars, rfl, members⟩
  rw [LocalContext.mkLambda, LocalContext.mkBinding_eqN,
    LocalContext.mkLambda, LocalContext.mkBinding_eqN]
  apply LocalContext.mkBindingListN_congr
  intro fv hfv
  exact hle.declarations fv (members fv hfv)

/-- Closing a bound free-variable array with `LocalContext.mkForall` exposes
exactly that array as a concrete forall telescope. -/
theorem BoundFVarArray.mkForall_forallTelescope
    (H : BoundFVarArray c xs) (Hc : BindingContextWF c) (body : Expr) :
    Expr.ForallTelescope (c.lctx.mkForall xs body) xs.size
      (body.abstractN H.fvars) := by
  have hsize : H.fvars.length = xs.size := by
    have h := congrArg Array.size H.expressions
    simpa using h.symm
  have Htelescope := LocalContext.mkForall_fvars_forallTelescope
    (lctx := c.lctx) (body := body) (fvs := H.fvars) (by
      intro fv hfv
      exact Hc.findCDecl fv (H.members fv hfv))
  have houter : c.lctx.mkForall xs body =
      c.lctx.mkForall (H.fvars.map Expr.fvar).toArray body :=
    congrArg (fun fields => c.lctx.mkForall fields body) H.expressions
  rw [houter]
  simpa only [← hsize] using Htelescope

/-- Sequential-model form of `mkForall_forallTelescope` for locally closed bodies. -/
theorem BoundFVarArray.mkForall_forallTelescopeList
    (H : BoundFVarArray c xs) (Hc : BindingContextWF c) (body : Expr)
    (hnodup : H.fvars.Nodup) (hb : Closed body) :
    Expr.ForallTelescope (c.lctx.mkForall xs body) xs.size
      (body.abstractList H.fvars) := by
  rw [← Expr.abstractN_eq_abstractList_of_closed hnodup hb]
  exact H.mkForall_forallTelescope Hc body

/-- Closing a locally closed body over selected declarations of a locally closed context
yields a locally closed expression. -/
theorem BoundFVarArray.mkForall_closed
    (H : BoundFVarArray c xs) (Hc : BindingContextWF c) (hnodup : H.fvars.Nodup)
    (hl : LocalContext.LctxClosed c.lctx) (hb : Closed body) :
    Closed (c.lctx.mkForall xs body) := by
  rw [H.expressions, LocalContext.mkForall]
  exact LocalContext.mkBinding_closed
    (fun fv hfv => by
      rcases Hc.findCDecl fv (H.members fv hfv) with ⟨i, n, t, bi, k, h⟩
      exact ⟨_, h⟩)
    hnodup hb hl.declsClosed

/-- A retained array introduced strictly after `root`. Besides recording that
its entries remain selectable, this packages the two facts needed to combine
it with selections already present at `root`: its entries are distinct and
none of them occurred in the root context. -/
structure FreshBoundFVarArray (root c : AddInductive.Context)
    (xs : Array Expr) extends BoundFVarArray c xs where
  nodup : toBoundFVarArray.fvars.Nodup
  fresh : ∀ fv ∈ toBoundFVarArray.fvars, fv ∉ root.lctx.fvars

def FreshBoundFVarArray.empty (c : AddInductive.Context) :
    FreshBoundFVarArray c c #[] where
  toBoundFVarArray := BoundFVarArray.empty c
  nodup := List.nodup_nil
  fresh _ h := nomatch h

def FreshBoundFVarArray.pushCurrent
    (H : FreshBoundFVarArray root c xs)
    (Hc : BindingContextWF c) (Hroot : BindingContextLE root c)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    FreshBoundFVarArray root { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      (xs.push (.fvar ⟨c.ngen.curr⟩)) where
  toBoundFVarArray := H.toBoundFVarArray.pushCurrent name ty bi
  nodup := by
    rw [show (H.toBoundFVarArray.pushCurrent name ty bi).fvars =
      H.toBoundFVarArray.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)] from rfl]
    apply List.nodup_append.mpr
    refine ⟨H.nodup, by simp, ?_⟩
    intro fv hfv fv' hfv'
    simp only [List.mem_singleton] at hfv'
    subst fv'
    exact fun heq => Hc.current_not_mem <| heq ▸
      H.toBoundFVarArray.members fv hfv
  fresh := by
    intro fv hfv
    change fv ∈ H.toBoundFVarArray.fvars ++
      [(⟨c.ngen.curr⟩ : FVarId)] at hfv
    simp only [List.mem_append, List.mem_singleton] at hfv
    rcases hfv with hfv | rfl
    · exact H.fresh fv hfv
    · intro hroot
      exact Hc.current_not_mem (Hroot hroot)

/-- Variant of `FreshBoundFVarArray.pushCurrent` for a binder opened in both contexts. -/
def FreshBoundFVarArray.pushCurrentChecked
    {base : LocalContext}
    (H : FreshBoundFVarArray root c xs)
    (Hc : BindingContextWF c) (Hroot : BindingContextLE root c)
    (name : Name) (ty : Expr) (bi : BinderInfo) :
    FreshBoundFVarArray root { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
      checkLCtx := base.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }
      (xs.push (.fvar ⟨c.ngen.curr⟩)) where
  toBoundFVarArray := H.toBoundFVarArray.pushCurrentChecked (base := base) name ty bi
  nodup := by
    rw [show (H.toBoundFVarArray.pushCurrentChecked (base := base) name ty bi).fvars =
      H.toBoundFVarArray.fvars ++ [(⟨c.ngen.curr⟩ : FVarId)] from rfl]
    apply List.nodup_append.mpr
    refine ⟨H.nodup, by simp, ?_⟩
    intro fv hfv fv' hfv'
    simp only [List.mem_singleton] at hfv'
    subst fv'
    exact fun heq => Hc.current_not_mem <| heq ▸
      H.toBoundFVarArray.members fv hfv
  fresh := by
    intro fv hfv
    change fv ∈ H.toBoundFVarArray.fvars ++
      [(⟨c.ngen.curr⟩ : FVarId)] at hfv
    simp only [List.mem_append, List.mem_singleton] at hfv
    rcases hfv with hfv | rfl
    · exact H.fresh fv hfv
    · intro hroot
      exact Hc.current_not_mem (Hroot hroot)

def FreshBoundFVarArray.rebaseRoot
    (H : FreshBoundFVarArray root c xs)
    (hle : BindingContextLE root' root) :
    FreshBoundFVarArray root' c xs where
  toBoundFVarArray := H.toBoundFVarArray
  nodup := H.nodup
  fresh := by
    intro fv hfv hroot'
    exact H.fresh fv hfv (hle hroot')

/-- The exact ordered suffix of ordinary locals introduced after `root`.
Unlike `FreshBoundFVarArray`, this remembers both that no unrelated local was
interleaved and that `xs` lists the suffix in introduction order.  These are
the equations required by `RecursorContextWF.mkForallRecent`. -/
structure RecentBoundFVarArray {root c : AddInductive.Context}
    (Hroot : ContextWF root) (Hc : ContextWF c) (xs : Array Expr)
    extends FreshBoundFVarArray root c xs where
  contextLE : BindingContextLE root c
  size_le : xs.size ≤ Hc.mlctx.length
  reverse_eq : xs.toList.reverse =
    (Hc.mlctx.fvarRevList xs.size size_le).map Expr.fvar
  drop_eq : Hc.mlctx.dropN xs.size size_le = Hroot.mlctx

def RecentBoundFVarArray.empty (Hc : ContextWF c) :
    RecentBoundFVarArray Hc Hc #[] where
  toFreshBoundFVarArray := FreshBoundFVarArray.empty c
  contextLE := BindingContextLE.refl c
  size_le := by simp
  reverse_eq := by simp
  drop_eq := rfl

/-- Variant of `RecentBoundFVarArray.pushCurrent` for a binder opened in both contexts. -/
def RecentBoundFVarArray.pushCurrentChecked {root c : AddInductive.Context}
    {Hroot : ContextWF root} {Hc : ContextWF c} {xs : Array Expr}
    (H : RecentBoundFVarArray Hroot Hc xs)
    (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    {ty₀ : VExpr}
    (htr₀ : TrExprS Hc.venv c.lparams Hc.chk.vlctx ty ty₀)
    (hty₀ : Hc.venv.IsType c.lparams.length Hc.chk.vlctx.toCtx ty₀) :
    RecentBoundFVarArray Hroot
      (ContextWF.withCheckedLocalDecl (c := c) (name := name) (ty := ty)
        (ty' := ty') (bi := bi) (H := Hc) htr hty htr₀ hty₀)
      (xs.push (.fvar ⟨c.ngen.curr⟩)) where
  toFreshBoundFVarArray := H.toFreshBoundFVarArray.pushCurrentChecked
    Hc.toBindingContextWF H.contextLE name ty bi
  contextLE := H.contextLE.trans <|
    BindingContextLE.withCheckedLocalDecl c Hc.toBindingContextWF name ty bi
  size_le := by
    simpa only [Array.size_push, ContextWF.withCheckedLocalDecl, ContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.length] using Nat.succ_le_succ H.size_le
  reverse_eq := by
    simpa only [Array.toList_push, List.reverse_append, List.reverse_singleton,
      List.singleton_append, Array.size_push, ContextWF.withCheckedLocalDecl, ContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.fvarRevList, List.map_cons] using
        congrArg (List.cons (.fvar ⟨c.ngen.curr⟩)) H.reverse_eq
  drop_eq := by
    simpa only [Array.size_push, ContextWF.withCheckedLocalDecl, ContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.dropN] using H.drop_eq

/-- Exact consecutive index-local suffix tracked wholly inside one recursor
universe interpretation. -/
structure RecursorRecentBoundFVarArray
    {root c : AddInductive.Context} {recLparams : List Name}
    (Rroot : RecursorContextWF root recLparams)
    (R : RecursorContextWF c recLparams) (xs : Array Expr)
    extends FreshBoundFVarArray root c xs where
  contextLE : BindingContextLE root c
  venv_eq : R.venv = Rroot.venv
  size_le : xs.size ≤ R.mlctx.length
  reverse_eq : xs.toList.reverse =
    (R.mlctx.fvarRevList xs.size size_le).map Expr.fvar
  drop_eq : R.mlctx.dropN xs.size size_le = Rroot.mlctx

/-- A recent suffix rooted at a checker-context variant of `Rroot` is rooted
at `Rroot` itself: the root's checker context plays no role. -/
def RecursorRecentBoundFVarArray.ofCheckRoot
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    {l : LocalContext} {B : Rroot.Base l}
    (H : RecursorRecentBoundFVarArray (Rroot.withCheckLCtx l B) R xs) :
    RecursorRecentBoundFVarArray Rroot R xs where
  toBoundFVarArray := H.toBoundFVarArray
  nodup := H.nodup
  fresh := H.fresh
  contextLE := ⟨H.contextLE.fvars, H.contextLE.declarations, H.contextLE.env_eq,
    H.contextLE.lparams_eq, H.contextLE.safety_eq, H.contextLE.allowPrimitive_eq,
    H.contextLE.fuel_eq⟩
  venv_eq := H.venv_eq
  size_le := H.size_le
  reverse_eq := H.reverse_eq
  drop_eq := H.drop_eq

def RecursorRecentBoundFVarArray.empty
    (R : RecursorContextWF c recLparams) :
    RecursorRecentBoundFVarArray R R #[] where
  toFreshBoundFVarArray := FreshBoundFVarArray.empty c
  contextLE := BindingContextLE.refl c
  venv_eq := rfl
  size_le := by simp
  reverse_eq := by simp
  drop_eq := rfl

def RecursorRecentBoundFVarArray.pushCurrent
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs)
    (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty') :
    RecursorRecentBoundFVarArray Rroot
      (R.withLocalDecl (name := name) (bi := bi) htr hty)
      (xs.push (.fvar ⟨c.ngen.curr⟩)) where
  toFreshBoundFVarArray := H.toFreshBoundFVarArray.pushCurrent
    R.toBindingContextWF H.contextLE name ty bi
  contextLE := H.contextLE.trans <|
    BindingContextLE.withLocalDecl c R.toBindingContextWF name ty bi
  venv_eq := H.venv_eq
  size_le := by
    simpa only [Array.size_push, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.length] using Nat.succ_le_succ H.size_le
  reverse_eq := by
    simpa only [Array.toList_push, List.reverse_append, List.reverse_singleton,
      List.singleton_append, Array.size_push, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.fvarRevList, List.map_cons] using
        congrArg (List.cons (.fvar ⟨c.ngen.curr⟩)) H.reverse_eq
  drop_eq := by
    simpa only [Array.size_push, RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.dropN] using H.drop_eq

/-- Variant of `RecursorRecentBoundFVarArray.pushCurrent` for a binder opened in both contexts. -/
def RecursorRecentBoundFVarArray.pushCurrentChecked
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs)
    (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty')
    {ty₀ : VExpr}
    (htr₀ : TrExprS R.venv recLparams R.chk.vlctx ty ty₀)
    (hty₀ : R.venv.IsType recLparams.length R.chk.vlctx.toCtx ty₀) :
    RecursorRecentBoundFVarArray Rroot
      (R.withCheckedLocalDecl (name := name) (bi := bi) htr hty htr₀ hty₀)
      (xs.push (.fvar ⟨c.ngen.curr⟩)) where
  toFreshBoundFVarArray := H.toFreshBoundFVarArray.pushCurrentChecked
    R.toBindingContextWF H.contextLE name ty bi
  contextLE := H.contextLE.trans <|
    BindingContextLE.withCheckedLocalDecl c R.toBindingContextWF name ty bi
  venv_eq := H.venv_eq
  size_le := by
    simpa only [Array.size_push, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.length] using Nat.succ_le_succ H.size_le
  reverse_eq := by
    simpa only [Array.toList_push, List.reverse_append, List.reverse_singleton,
      List.singleton_append, Array.size_push, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.fvarRevList, List.map_cons] using
        congrArg (List.cons (.fvar ⟨c.ngen.curr⟩)) H.reverse_eq
  drop_eq := by
    simpa only [Array.size_push, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.dropN] using H.drop_eq

/-- Variant of `RecursorRecentBoundFVarArray.pushCurrent` for a binder opened
on an explicit checker base. -/
def RecursorRecentBoundFVarArray.pushCurrentOn
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs)
    (name : Name) (ty : Expr) (ty' : VExpr) (bi : BinderInfo)
    (base : LocalContext) (B : R.Base base)
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty')
    {ty₀ : VExpr}
    (htr₀ : TrExprS R.venv recLparams B.m.vlctx ty ty₀)
    (hty₀ : R.venv.IsType recLparams.length B.m.vlctx.toCtx ty₀) :
    RecursorRecentBoundFVarArray Rroot
      (R.withCheckedLocalDeclOn (name := name) (bi := bi) base B htr hty htr₀ hty₀)
      (xs.push (.fvar ⟨c.ngen.curr⟩)) where
  toFreshBoundFVarArray := H.toFreshBoundFVarArray.pushCurrentChecked
    R.toBindingContextWF H.contextLE name ty bi
  contextLE := H.contextLE.trans <|
    BindingContextLE.withCheckedLocalDecl c R.toBindingContextWF name ty bi
  venv_eq := H.venv_eq
  size_le := by
    simpa only [Array.size_push, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.length] using Nat.succ_le_succ H.size_le
  reverse_eq := by
    simpa only [Array.toList_push, List.reverse_append, List.reverse_singleton,
      List.singleton_append, Array.size_push, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.fvarRevList, List.map_cons] using
        congrArg (List.cons (.fvar ⟨c.ngen.curr⟩)) H.reverse_eq
  drop_eq := by
    simpa only [Array.size_push, RecursorContextWF.withCheckedLocalDeclOn,
      TypeChecker.MLCtx.dropN] using H.drop_eq

/-- An exact consecutive recursor suffix induces the semantic context
extension needed to weaken certificates rooted before that suffix. -/
def RecursorRecentBoundFVarArray.contextExtension
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs) :
    RecursorContextExtension Rroot R where
  contextLE := H.contextLE
  venv_eq := H.venv_eq
  shift := .skipN .refl xs.size
  lift := by
    have W := (R.onlyLams.dropN_fvlift xs.size H.size_le).toFVLift'
    simpa only [H.drop_eq] using W

/-- The newest-first free-variable prefix of the semantic metacontext is
exactly the retained recent array, reversed. -/
theorem RecursorRecentBoundFVarArray.fvarRevList_eq
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs) :
    R.mlctx.fvarRevList xs.size H.size_le = H.fvars.reverse := by
  have hexpressions := congrArg Array.toList H.expressions
  have hmapped : xs.toList = H.fvars.map Expr.fvar := by
    simpa using hexpressions
  apply (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp
  calc
    (R.mlctx.fvarRevList xs.size H.size_le).map Expr.fvar =
        xs.toList.reverse := H.reverse_eq.symm
    _ = (H.fvars.map Expr.fvar).reverse := by rw [hmapped]
    _ = H.fvars.reverse.map Expr.fvar := by simp

/-- The current recursor context is the exact recent binder prefix followed
by its retained root.  This is the identifier-level counterpart of
`abstractRecent_toCtx`; unlike `BindingContextLE`, it preserves order. -/
theorem RecursorRecentBoundFVarArray.contextFVars
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs) :
    R.mlctx.vlctx.fvars = H.fvars.reverse ++ Rroot.mlctx.vlctx.fvars := by
  have hsplit := TypeChecker.MLCtx.vlctx_eq_take_append_dropN
    R.mlctx xs.size H.size_le
  rw [H.drop_eq] at hsplit
  have hprefix : VLCtx.fvars (R.mlctx.vlctx.take xs.size) =
      H.fvars.reverse := by
    rw [TypeChecker.MLCtx.vlctx_take_fvars]
    exact H.fvarRevList_eq
  rw [hsplit, VLCtx.fvars_append, hprefix]

/-- A source up-set on the retained root remains an up-set after an exact
recent suffix, provided the source predicate denotes only root variables.
The freshly allocated suffix binders are outside the predicate, while their
dependencies may still lie inside it. -/
theorem RecursorRecentBoundFVarArray.upsetRoot
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs)
    {P : FVarId → Prop}
    (hscope : ∀ fv, P fv → fv ∈ Rroot.mlctx.vlctx.fvars)
    (hup : IsFVarUpSet P Rroot.mlctx.vlctx) :
    IsFVarUpSet P R.mlctx.vlctx := by
  have hsplit := TypeChecker.MLCtx.vlctx_eq_take_append_dropN
    R.mlctx xs.size H.size_le
  rw [H.drop_eq] at hsplit
  rw [hsplit]
  apply IsFVarUpSet.prependFresh P Rroot.mlctx.vlctx
  · exact hup
  · intro fv hfv hp
    have hprefix : VLCtx.fvars (R.mlctx.vlctx.take xs.size) =
        H.fvars.reverse := by
      rw [TypeChecker.MLCtx.vlctx_take_fvars]
      exact H.fvarRevList_eq
    rw [hprefix] at hfv
    apply H.fresh fv (by simpa using hfv)
    rw [← Rroot.lctx_eq, Rroot.mlctx_wf.tr.fvars_eq]
    exact hscope fv hp

/-- Opening an exact consecutive suffix preserves the independently checked
parameter context.  The fresh locals become additional ambient declarations;
the cached parameter declarations and their source translations are unchanged. -/
def RecursorParameterContextSuffix.weakenRecent
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorParameterContextSuffix Rroot stats depth)
    (Hrecent : RecursorRecentBoundFVarArray Rroot R xs) :
    RecursorParameterContextSuffix R stats (depth + xs.size) := by
  let added := R.mlctx.vlctx.take xs.size
  have hadded : added.length = xs.size := by
    change (R.mlctx.vlctx.take xs.size).length = xs.size
    rw [List.length_take, Nat.min_eq_left]
    simpa only [TypeChecker.MLCtx.vlctx_length] using Hrecent.size_le
  exact {
    ambientDecls := added ++ H.ambientDecls
    parameterDecls := H.parameterDecls
    context := by
      calc
        R.mlctx.vlctx =
            added ++ (R.mlctx.dropN xs.size Hrecent.size_le).vlctx :=
          TypeChecker.MLCtx.vlctx_eq_take_append_dropN
            R.mlctx xs.size Hrecent.size_le
        _ = added ++ Rroot.mlctx.vlctx := by rw [Hrecent.drop_eq]
        _ = added ++ (H.ambientDecls ++ H.parameterDecls) := by rw [H.context]
        _ = (added ++ H.ambientDecls) ++ H.parameterDecls := by
          simp only [List.append_assoc]
    prefixLength := by
      simp only [List.length_append, hadded, H.prefixLength]
      omega
    cached := H.cached
    narrowParams := by
      simpa only [Hrecent.venv_eq] using H.narrowParams
    sources := by
      simpa only [Hrecent.venv_eq] using H.sources }

/-- Cached inductive parameters remain aligned after `loopUArgs` opens an
exact suffix of higher-order arguments.  The semantic parameter variables
shift by the suffix length, matching the executable context extension. -/
def RecursorValidAppStatsWF.weakenRecent
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorValidAppStatsWF Rroot.venv recLparams
      Rroot.mlctx.vlctx stats decl depth)
    (Hrecent : RecursorRecentBoundFVarArray Rroot R xs) :
    RecursorValidAppStatsWF R.venv recLparams R.mlctx.vlctx
      stats decl (depth + xs.size) := by
  let W := R.onlyLams.dropN_fvlift xs.size Hrecent.size_le
  have hparams : List.Forall₂
      (TrExprS R.venv recLparams R.mlctx.vlctx)
      stats.params.toList
      ((decl.paramVars depth).map fun target =>
        target.liftN xs.size 0) := by
    apply checkPositivityStep.forall₂_map_right H.params
    intro source target Hsource
    have Hsource' : TrExprS R.venv recLparams
        (R.mlctx.dropN xs.size Hrecent.size_le).vlctx source target := by
      simpa only [Hrecent.venv_eq, Hrecent.drop_eq] using Hsource
    exact Hsource'.weakFV R.checking.tr.wf.ordered W R.mlctx_wf.tr.wf
  exact {
    levels := H.levels
    consts := H.consts
    indices := H.indices
    params := by simpa using hparams
    paramFVars := H.paramFVars }

/-- Lookup values in the exact higher-order suffix are fresh bound variables,
so a no-inductive-constants context invariant extends across that suffix. -/
theorem RecursorRecentBoundFVarArray.noIndConsts
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs)
    (hroot : VLCtx.NoIndConsts names Rroot.mlctx.vlctx) :
    VLCtx.NoIndConsts names R.mlctx.vlctx := by
  apply checkInductiveTypes.loopType.MLCtxOnlyLams.noIndConsts_of_dropN
    R.onlyLams xs.size H.size_le
  rw [H.drop_eq]
  exact hroot

/-- Every recursively selected constructor argument is one of the exact
fresh field variables opened by `loopCtorArgs`, with its pointwise semantic
translation recovered at the same array position. -/
theorem RecursorFieldSelectionsAt.selectedFVars
    (H : RecursorFieldSelectionsAt env decl uvars bu u fields)
    (Hbu : BoundFVarArray c bu)
    (Hargs : List.Forall₂ (TrExprS env Us Delta) u.toList args) :
    ∀ j (hj : j < u.size),
      ∃ fv target,
        u[j] = .fvar fv ∧ TrExprS env Us Delta (.fvar fv) target := by
  intro j hj
  have hjFields : j < fields.length := by
    rw [H.fields_length]
    exact hj
  have Hposition := List.forall₂_getElem
    H.arguments_at_positions j hjFields (by simpa using hj)
  rcases Hposition with ⟨hposition, hselected⟩
  have hboundSize : bu.size = Hbu.fvars.length := by
    have h := congrArg Array.size Hbu.expressions
    simpa using h
  have hpositionFVars : fields[j].fieldIndex < Hbu.fvars.length := by
    rw [← hboundSize]
    exact hposition
  let fv := Hbu.fvars[fields[j].fieldIndex]
  have hfield : bu[fields[j].fieldIndex]'hposition = .fvar fv := by
    have h := congrArg
      (fun xs : Array Expr => xs[fields[j].fieldIndex]!) Hbu.expressions
    simpa [fv, Array.getElem!_eq_getD, Array.getD, hposition,
      hpositionFVars] using h
  have hu : u[j] = .fvar fv := hselected.trans hfield
  have hargsLength : u.toList.length = args.length :=
    List.Forall₂.length_eq Hargs
  have hjArgs : j < args.length := by simpa using hargsLength ▸ (by
    simpa using hj : j < u.toList.length)
  let target := args[j]
  have hargTr := List.forall₂_getElem
    Hargs j (by simpa using hj) hjArgs
  refine ⟨fv, target, hu, ?_⟩
  simpa [target, hu] using hargTr

theorem ConstructorFieldOpening.fvars_eq_bound
    (H : ConstructorFieldOpening source current fields)
    (B : BoundFVarArray c fields) :
    H.fvars = B.fvars := by
  have harrays : (H.fvars.map Expr.fvar).toArray =
      (B.fvars.map Expr.fvar).toArray :=
    H.expressions.symm.trans B.expressions
  have hlists : H.fvars.map Expr.fvar = B.fvars.map Expr.fvar := by
    simpa using congrArg Array.toList harrays
  exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlists

/-- Reopening a constructor telescope adds only the explicitly selected
field identifiers to the free-variable scope of the original source. -/
theorem ConstructorFieldOpening.currentFVarsIn
    (H : ConstructorFieldOpening source current fields)
    (hsource : source.FVarsIn P) :
    current.FVarsIn (fun fv => fv ∈ H.fvars ∨ P fv) := by
  have resultScope : ∀ {outer arity result},
      Expr.ForallTelescope outer arity result →
      outer.FVarsIn P → result.FVarsIn P := by
    intro outer arity result Htel houter
    induction Htel with
    | nil => exact houter
    | cons _ ih => exact ih houter.2
  have hresidual : H.residual.FVarsIn P := by
    exact resultScope H.telescope hsource
  rw [← H.closed] at hresidual
  exact FVarsIn.of_abstractList hresidual

/-- Alpha-independent result of the checker constructor traversal.  The
terminal application itself contains checker-chosen free variables, so the
certificate retains only its maximal closed telescope residual. -/
structure CheckedConstructorOwnerNormalForm
    (stats : AddInductive.InductiveStats) (targetIdx : Nat)
    (source : Expr) : Type where
  arity : Nat
  residual : Expr
  telescope : Expr.ForallTelescope source arity residual
  maximal : residual.isForall = false
  valid : AddInductive.isValidIndAppIdx stats residual targetIdx = true

/-- Close a successful checker traversal to its canonical owner normal form.
The parameter array belongs to the root context, while every field belongs to
the fresh suffix, which is exactly the disjointness needed by validation. -/
def CheckedConstructorOwnerNormalForm.ofOpening
    {root current : AddInductive.Context}
    (Hopening : ConstructorFieldOpening source terminal fields)
    (Hparams : BoundFVarArray root stats.params)
    (Hfields : FreshBoundFVarArray root current fields)
    (hconst : stats.indConsts[targetIdx]? = some (.const name levels))
    (hterminal : terminal.isForall = false)
    (hvalid : AddInductive.isValidIndAppIdx stats terminal targetIdx = true) :
    CheckedConstructorOwnerNormalForm stats targetIdx source := by
  have hopenFvars : Hopening.fvars = Hfields.toBoundFVarArray.fvars :=
    Hopening.fvars_eq_bound Hfields.toBoundFVarArray
  have hdisjoint : ∀ fv, fv ∈ Hparams.fvars → fv ∉ Hopening.fvars := by
    intro fv hparam hfield
    rw [hopenFvars] at hfield
    exact Hfields.fresh fv hfield (Hparams.members fv hparam)
  refine {
    arity := fields.size
    residual := Hopening.residual
    telescope := Hopening.telescope
    maximal := ?_
    valid := ?_ }
  · rw [← Hopening.closed, Expr.abstractList_isForall, hterminal]
  · rw [← Hopening.closed]
    exact checkPositivityStep.isValidIndAppIdx.abstractList
      hvalid hconst Hparams.fvars Hopening.fvars Hparams.expressions
      hdisjoint

/-- Reopening a checked constructor telescope with a different fresh suffix
recovers the same validated family application. -/
theorem CheckedConstructorOwnerNormalForm.validOfOpening
    {root current : AddInductive.Context}
    (H : CheckedConstructorOwnerNormalForm stats targetIdx source)
    (Hopening : ConstructorFieldOpening source terminal fields)
    (Hparams : BoundFVarArray root stats.params)
    (Hfields : FreshBoundFVarArray root current fields)
    (hconst : stats.indConsts[targetIdx]? = some (.const name levels))
    (hterminal : terminal.isForall = false) :
    AddInductive.isValidIndAppIdx stats terminal targetIdx = true := by
  have hopenFvars : Hopening.fvars = Hfields.toBoundFVarArray.fvars :=
    Hopening.fvars_eq_bound Hfields.toBoundFVarArray
  have hdisjoint : ∀ fv, fv ∈ Hparams.fvars → fv ∉ Hopening.fvars := by
    intro fv hparam hfield
    rw [hopenFvars] at hfield
    exact Hfields.fresh fv hfield (Hparams.members fv hparam)
  have hopenTerminal : Hopening.residual.isForall = false := by
    rw [← Hopening.closed, Expr.abstractList_isForall, hterminal]
  have hresidual : H.residual = Hopening.residual :=
    (H.telescope.eq_of_residual_not_forall Hopening.telescope
      H.maximal hopenTerminal).2
  have hclosedValid : AddInductive.isValidIndAppIdx stats
      (terminal.abstractList Hopening.fvars) targetIdx = true := by
    rw [Hopening.closed, ← hresidual]
    exact H.valid
  exact checkPositivityStep.isValidIndAppIdx.of_abstractList
    Hparams.fvars Hopening.fvars 0 hclosedValid hconst
    Hparams.expressions hdisjoint

/-- The production constructor checker emits a canonical owner certificate
at its terminal success.  This traversal is intentionally separate from the
semantic `CtorTailWF` projection: both inspect the same executable run, while
this one retains the concrete alpha-normalized evidence needed later by
`mkRecInfos`. -/
theorem checkConstructors.loopCtor.ownerNormalFormWF
    {decl : VInductDecl} {scope : VLCtx} {depth : Nat}
    {narrowType fullType : VExpr}
    {root c : AddInductive.Context} {Hroot : ContextWF root}
    {fields : Array Expr} {source : Expr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length scope Hc.chk.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hi : targetIdx < decl.types.length)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (Hparams : BoundFVarArray root stats.params)
    (Hfields : RecentBoundFVarArray Hroot Hc fields)
    (Hopening : ConstructorFieldOpening source type fields)
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => Nonempty
        (CheckedConstructorOwnerNormalForm stats targetIdx source)) := by
  induction fuel generalizing c type scope narrowType fullType depth i fields with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      rcases htrFull with ⟨fullForall, hfullForall, _hfullTarget⟩
      cases htrNarrow with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType _hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hfullForall with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          rcases halign.forallE_align Hc.checking.tr.wf hdomNarrow
              hdomNarrowType hbodyNarrow with
            ⟨dom₀, _, hdom₀, hdom₀Type, _, hbody₀, _⟩
          rcases hconsume _ Hc.narrow hdom₀ hdom₀Type with
            ⟨consumedDom₀, Hdom₀⟩
          have hparamNext : stats.params[i + 1]? = none := by
            rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
            omega
          have hdeps : (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomNarrow.fvarsIn)).1
          rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
            ⟨_domainLevel, hdomain⟩
          cases isUnsafe with
          | false =>
            have Hpos := checkPositivity.refinesNarrow
              (ctor := ctor) (idx := i) Hc Hruntime halign Hstats
              hconsume hlit hdomNarrow
              (hdomFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
            refine checkConstructors.loopCtor.safeField.sourceWF
              (Q := fun _ => Nonempty
                (CheckedConstructorOwnerNormalForm stats targetIdx source))
              Hc hparamAt Hdom hbodyFull Hdom₀ hbody₀ Hpos ?_
            intro _fieldType _fieldLevel _fieldLevel' _hfield _hlevel
              _htyped _ _ _ _hfieldBound _hpositive bodyFull' _hbodyFullEq
              _ _ hopenedFull _
            let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType Hdom₀.consumed Hdom₀.isType
            let Hruntime' :
                checkInductiveTypes.loopType.NarrowRuntimeScope
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
                hdomNarrow hdomain hdomNarrowType
            have halign' := Hc.alignedBinder (name := name) (bi := bi) halign
              Hdom Hdom₀ hdomNarrow hdomNarrowType hdeps
            have hscopeWF := halign'.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            let Hfields' := Hfields.pushCurrentChecked name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) consumedDom bi
              Hdom.consumed Hdom.isType Hdom₀.consumed Hdom₀.isType
            have hopenFvars : Hopening.fvars =
                Hfields.toBoundFVarArray.fvars :=
              Hopening.fvars_eq_bound Hfields.toBoundFVarArray
            have hcurrentFresh :
                (⟨c.ngen.curr⟩ : FVarId) ∉ Hopening.fvars := by
              rw [hopenFvars]
              intro hmem
              exact Hc.toBindingContextWF.current_not_mem
                (Hfields.toBoundFVarArray.members _ hmem)
            have hbodyFresh : body.FVarsIn
                (fun other => other ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
              apply hbodyFull.fvarsIn.mono
              intro other hother heq
              subst other
              have hbase : (⟨c.ngen.curr⟩ : FVarId) ∈
                  Hc.mlctx.vlctx.fvars := by simpa using hother
              exact Hc.current_not_mem hbase
            let Hopening' := Hopening.push hcurrentFresh hbodyFresh
            exact ih Hc' Hruntime' halign' Hstats' hparamNext hlit Hfields'
              Hopening' hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
          | true =>
            refine checkConstructors.loopCtor.unsafeField.sourceWF
              (Q := fun _ => Nonempty
                (CheckedConstructorOwnerNormalForm stats targetIdx source))
              Hc hparamAt Hdom hbodyFull Hdom₀ hbody₀ ?_
            intro _fieldType _fieldLevel _fieldLevel' _hfield _hlevel
              _htyped _ _ _ _hfieldBound bodyFull' _hbodyFullEq _ _
              hopenedFull _
            let Hc' := Hc.withCheckedLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType Hdom₀.consumed Hdom₀.isType
            let Hruntime' :
                checkInductiveTypes.loopType.NarrowRuntimeScope
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps name bi dom
                hdomNarrow hdomain hdomNarrowType
            have halign' := Hc.alignedBinder (name := name) (bi := bi) halign
              Hdom Hdom₀ hdomNarrow hdomNarrowType hdeps
            have hscopeWF := halign'.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            let Hfields' := Hfields.pushCurrentChecked name
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) consumedDom bi
              Hdom.consumed Hdom.isType Hdom₀.consumed Hdom₀.isType
            have hopenFvars : Hopening.fvars =
                Hfields.toBoundFVarArray.fvars :=
              Hopening.fvars_eq_bound Hfields.toBoundFVarArray
            have hcurrentFresh :
                (⟨c.ngen.curr⟩ : FVarId) ∉ Hopening.fvars := by
              rw [hopenFvars]
              intro hmem
              exact Hc.toBindingContextWF.current_not_mem
                (Hfields.toBoundFVarArray.members _ hmem)
            have hbodyFresh : body.FVarsIn
                (fun other => other ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
              apply hbodyFull.fvarsIn.mono
              intro other hother heq
              subst other
              have hbase : (⟨c.ngen.curr⟩ : FVarId) ∈
                  Hc.mlctx.vlctx.fvars := by simpa using hother
              exact Hc.current_not_mem hbase
            let Hopening' := Hopening.push hcurrentFresh hbodyFresh
            exact ih Hc' Hruntime' halign' Hstats' hparamNext hlit Hfields'
              Hopening' hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
    · cases hvalid :
          AddInductive.isValidIndAppIdx stats type targetIdx
      · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
      · exact checkConstructors.loopCtor.result.WF hforall hvalid
          ⟨CheckedConstructorOwnerNormalForm.ofOpening Hopening Hparams
            Hfields.toFreshBoundFVarArray (Hstats.indConstAt hi)
            (by cases type <;> simp_all [Expr.isForall]) hvalid⟩

/-- Public owner-normal-form projection from the beginning of a constructor
telescope.  Cached parameters are replayed exactly as in
`refinesCtorShape`; only genuine constructor fields enter the alpha-closed
normal form. -/
theorem checkConstructors.loopCtor.ownerNormalFormFromStartWF
    {decl : VInductDecl} {ctorVal : VConstVal}
    (Hc : ContextWF c)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hsuffix.parameterDecls stats decl 0)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length
      Hsuffix.parameterDecls Hc.chk.vlctx)
    (Hctor : TrSourceConstRaw Hc.venv c.lparams ctor source ctorVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source checkedType fullType checkedType')
    (hi : targetIdx < decl.types.length)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source 0 fuel c).WF
      (fun _ => ∃ tail,
        RecursorParamPrefix stats 0 source tail ∧
        Nonempty
          (CheckedConstructorOwnerNormalForm stats targetIdx tail)) := by
  have hnoFVars : FVarsIn (fun _ => False) source := by
    simpa [VLCtx.fvars] using Hctor.type.fvarsIn
  by_cases hzero : decl.nparams = 0
  · have hscopeLength : Hsuffix.parameterDecls.length = 0 := by
      simpa [Hstats.params_size, hzero] using
        Hsuffix.parameterDecls_length
    have hscope : Hsuffix.parameterDecls = [] :=
      List.eq_nil_of_length_eq_zero hscopeLength
    cases fuel with
    | zero => exact checkConstructors.loopCtor.zero.WF
    | succ fuel =>
      have hparamAt : stats.params[0]? = none := by
        rw [Array.getElem?_eq_none_iff, Hstats.params_size, hzero]
        omega
      have Hnormal := checkConstructors.loopCtor.ownerNormalFormWF
        (type := source) (source := source) (fields := #[])
        (i := 0) (ctor := ctor) (fuel := fuel + 1)
        (isUnsafe := isUnsafe)
        (Hroot := Hc) Hc
        (checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
          Hc Hsuffix) halign
        Hstats hi hparamAt hconsume hlit Hsuffix.paramsBound
        (RecentBoundFVarArray.empty Hc)
        (ConstructorFieldOpening.empty source)
        (by simpa [hscope] using Hctor.type)
        (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      exact Hnormal.mono fun _ Hnormal =>
        ⟨source, .done (by rw [Hstats.params_size, hzero]), Hnormal⟩
  by_cases hforall : ∃ name dom body bi,
      source = .forallE name dom body bi
  · rcases hforall with ⟨name, dom, body, bi, rfl⟩
    have htype : Hc.venv.IsType c.lparams.length [] ctorVal.type := by
      rcases TrExpr.forallE_source
          (Hctor.type.trExpr Hc.checking.tr.wf (by trivial)) with
        ⟨dom', body', _hdom, _hbody, hdomType, hbodyType, heq⟩
      exact (VEnv.IsType.forallE hdomType hbodyType).defeqU_l
        Hc.checking.tr.wf (by trivial) heq
    let Hinitial := ConstructorSynthesisState.initial Hctor htype
    apply checkConstructors.loopCtor.parameterSynthesisWF
      (decl := decl) (ctorVal := ctorVal) Hc
      (Q := fun _ => ∃ tail,
        RecursorParamPrefix stats 0 (.forallE name dom body bi) tail ∧
        Nonempty
          (CheckedConstructorOwnerNormalForm stats targetIdx tail))
      (Hresult := by
        intro source' current' fullCurrent' fuel' sourceDomains
          _Hsynthesis htrNarrow htrFull Hsegment _Hcomparisons
        have hparamAt : stats.params[decl.nparams]? = none := by
          rw [Array.getElem?_eq_none_iff]
          exact Nat.le_of_eq Hstats.params_size
        have Hnormal := checkConstructors.loopCtor.ownerNormalFormWF
          (type := source') (source := source') (fields := #[])
          (i := decl.nparams) (ctor := ctor) (fuel := fuel' + 1)
          (isUnsafe := isUnsafe)
          (Hroot := Hc) Hc
          (checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
            Hc Hsuffix) halign
          Hstats hi hparamAt hconsume hlit Hsuffix.paramsBound
          (RecentBoundFVarArray.empty Hc)
          (ConstructorFieldOpening.empty source') htrNarrow htrFull
        exact Hnormal.mono fun _ Hnormal =>
          ⟨source', by
            have Hcomplete : RecursorParamSegment stats 0 stats.params.size
                (.forallE name dom body bi) source' := by
              simpa only [Hstats.params_size] using Hsegment
            exact Hcomplete.complete rfl,
            Hnormal⟩)
      (Hearly := by
        intro source' scope' current' fullCurrent' i' fuel' sourceDomains hi'
          hforall Hscope' _Hsynthesis _htrNarrow _htrFull _Hcomparisons
        exact checkConstructors.loopCtor.earlyParameterResult.WF
          (fuel := fuel') Hc Hscope'
          (by simpa [Hstats.params_size] using hi') hforall)
      Hstats.params_size (by omega) (.done)
      (fun h =>
        checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars h hnoFVars)
      (fun h =>
        (checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars
          h hnoFVars).older_eq_nil h |>.symm)
      (by
        intro hdone
        have hlength := Hsuffix.parameterDecls_length
        have hempty : Hsuffix.parameterDecls = [] :=
          List.eq_nil_of_length_eq_zero (by
            rw [hlength, Hstats.params_size, hdone])
        exact hempty.symm)
      Hinitial Hctor.type
      (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      CheckedConstructorParameterPrefix.zero
  · cases fuel with
    | zero => exact checkConstructors.loopCtor.zero.WF
    | succ fuel =>
      have hiStats : 0 < stats.params.size := by
        rw [Hstats.params_size]
        omega
      exact checkConstructors.loopCtor.earlyParameterResult.WF
        (Hsuffix := Hsuffix) (fuel := fuel) Hc
        (checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars
          (Hsuffix := Hsuffix) hiStats hnoFVars)
        (by omega) hforall

/-- Checked owner normal form selected by a concrete constructor position. -/
def CheckedConstructorOwnerNormalFormAt
    (stats : AddInductive.InductiveStats) (targetIdx : Nat)
    (ctor : Constructor) : Prop :=
  ∃ tail,
    RecursorParamPrefix stats 0 ctor.type tail ∧
    Nonempty (CheckedConstructorOwnerNormalForm stats targetIdx tail)

structure ConstructorOwnerNormalFormRow
    (stats : AddInductive.InductiveStats) (targetIdx : Nat)
    (ctors : List Constructor) (done : Nat) : Prop where
  covered : done ≤ ctors.length
  entries : ∀ i, i < done → (hi : i < ctors.length) →
    CheckedConstructorOwnerNormalFormAt stats targetIdx ctors[i]

def ConstructorOwnerNormalFormRow.empty
    (stats : AddInductive.InductiveStats) (targetIdx : Nat)
    (ctors : List Constructor) :
    ConstructorOwnerNormalFormRow stats targetIdx ctors 0 where
  covered := Nat.zero_le _
  entries _ hi := by omega

def ConstructorOwnerNormalFormRow.push
    (H : ConstructorOwnerNormalFormRow stats targetIdx ctors done)
    (hi : done < ctors.length)
    (Hentry : CheckedConstructorOwnerNormalFormAt stats targetIdx ctors[done]) :
    ConstructorOwnerNormalFormRow stats targetIdx ctors (done + 1) where
  covered := by omega
  entries i hidone hi' := by
    by_cases hlast : i = done
    · subst i
      exact Hentry
    · exact H.entries i (by omega) hi'

structure ConstructorOwnerNormalFormRows
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (done : Nat) : Prop where
  covered : done ≤ indTypes.size
  rows : ∀ i, i < done → (hi : i < indTypes.size) →
    ConstructorOwnerNormalFormRow stats i indTypes[i].ctors
      indTypes[i].ctors.length

def ConstructorOwnerNormalFormRows.empty
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) :
    ConstructorOwnerNormalFormRows stats indTypes 0 where
  covered := Nat.zero_le _
  rows _ hi := by omega

def ConstructorOwnerNormalFormRows.push
    (H : ConstructorOwnerNormalFormRows stats indTypes done)
    (hi : done < indTypes.size)
    (Hrow : ConstructorOwnerNormalFormRow stats done
      indTypes[done].ctors indTypes[done].ctors.length) :
    ConstructorOwnerNormalFormRows stats indTypes (done + 1) where
  covered := by omega
  rows i hidone hi' := by
    by_cases hlast : i = done
    · subst i
      exact Hrow
    · exact H.rows i (by omega) hi'

/-- Public matrix of checker-produced owner normal forms, indexed in the
same family/constructor coordinates later traversed by `mkRecInfos`. -/
structure CheckedConstructorOwnerNormalForms
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) : Prop where
  replay : ∀ familyIdx (hfamily : familyIdx < indTypes.size)
      ctorIdx (hctor : ctorIdx < indTypes[familyIdx].ctors.length),
    CheckedConstructorOwnerNormalFormAt stats familyIdx
      indTypes[familyIdx].ctors[ctorIdx]

def ConstructorOwnerNormalFormRows.complete
    (H : ConstructorOwnerNormalFormRows stats indTypes indTypes.size) :
    CheckedConstructorOwnerNormalForms stats indTypes where
  replay familyIdx hfamily ctorIdx hctor :=
    (H.rows familyIdx hfamily hfamily).entries ctorIdx hctor hctor

namespace checkConstructors.loopCtors

/-- Accumulate owner normal forms across the executable constructor loop. -/
theorem ownerNormalFormsWF
    {decl : VInductDecl} {sourceEnv : VEnv}
    {source : InductiveType} {target : VInductiveType}
    (Hc : ContextWF c)
    (Htarget : TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams
      source target)
    (Hrow : ConstructorOwnerNormalFormRow stats targetIdx
      source.ctors ctorIdx)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hsuffix.parameterDecls stats decl 0)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length
      Hsuffix.parameterDecls Hc.chk.vlctx)
    (htargetIdx : targetIdx < decl.types.length)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (Hfinish : ConstructorOwnerNormalFormRow stats targetIdx source.ctors
        source.ctors.length → Q ()) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      source.ctors ctorIdx foundCtors c).WF Q := by
  by_cases hidx : ctorIdx < source.ctors.length
  · have htarget : ctorIdx < target.ctors.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctors_length
        Htarget]
      exact hidx
    have Hctor := Lean4Lean.VerifyInductive.TrInductiveTypeHeaders.ctorAt
      Htarget ctorIdx hidx htarget
    apply stepPrefix.checkedWF (stats := stats) (isUnsafe := isUnsafe)
      (targetIdx := targetIdx) (Q := Q) Hc hidx
    intro checkedType type' checkedType' hchecked
    have Hnormal :=
      checkConstructors.loopCtor.ownerNormalFormFromStartWF
        (fuel := c.fuel.inductiveFuel) (isUnsafe := isUnsafe)
        Hc Hsuffix Hstats halign Hctor hchecked
        htargetIdx hconsume hlit
    exact Hnormal.mono fun _ Hentry =>
      ownerNormalFormsWF Hc Htarget
        (Hrow.push hidx Hentry) Hsuffix Hstats halign htargetIdx
        hconsume hlit Hfinish
  · have heq : ctorIdx = source.ctors.length := by
      have := Hrow.covered
      omega
    apply result.WF (Q := Q) hidx
    exact Hfinish (by simpa [heq] using Hrow)
termination_by source.ctors.length - ctorIdx

end checkConstructors.loopCtors

namespace checkConstructors.loopTypes

/-- Accumulate the owner-normal-form rows across every mutual family. -/
theorem ownerNormalFormsWF
    {decl : VInductDecl} {sourceEnv : VEnv}
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams)
      indTypes.toList decl.types)
    (Hrows : ConstructorOwnerNormalFormRows stats indTypes targetIdx)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hsuffix.parameterDecls stats decl 0)
    (halign : VLCtx.IsDefEq Hc.venv c.lparams.length
      Hsuffix.parameterDecls Hc.chk.vlctx)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint Hc.venv stats.indConsts)
    (Hfinish : ConstructorOwnerNormalFormRows stats indTypes indTypes.size →
      Q ()) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  by_cases hidx : targetIdx < indTypes.size
  · have htarget : targetIdx < decl.types.length := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using List.Forall₂.length_eq Htypes
      omega
    have Htarget : TrInductiveTypeHeaders sourceEnv Hc.venv c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := List.forall₂_getElem Htypes
        targetIdx (by simpa using hidx) htarget
      rw [Array.getElem_toList] at Htarget'
      exact Htarget'
    apply step.WF (Q := Q) hidx
    apply checkConstructors.loopCtors.ownerNormalFormsWF
      (Q := fun _ =>
        (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
          (targetIdx + 1) c).WF Q)
      Hc Htarget
      (ConstructorOwnerNormalFormRow.empty stats targetIdx
        indTypes[targetIdx].ctors)
      Hsuffix Hstats halign htarget hconsume hlit
    intro Hrow
    exact ownerNormalFormsWF Hc Htypes (Hrows.push hidx Hrow)
      Hsuffix Hstats halign hconsume hlit Hfinish
  · have heq : targetIdx = indTypes.size := by
      have := Hrows.covered
      omega
    apply result.WF (Q := Q) hidx
    exact Hfinish (by simpa [heq] using Hrows)
termination_by indTypes.size - targetIdx

end checkConstructors.loopTypes

theorem RecursorParameterContextSuffix.fieldFVars
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    (R.mlctx.dropN depth H.depth_le).fvarList =
      (stats.params ++ (#[] : Array Expr)).toList.map (·.fvarId!) := by
  rw [TypeChecker.MLCtx.fvarList_eq, H.dropAmbient_vlctx,
    checkInductiveTypes.loopType.CachedParameterDecl.forall₂_fvars H.cached]
  simp [List.map_reverse]

/-- The checker context of the first constructor field: the parameters, at
the bottom of the recursor context. -/
def RecursorParameterContextSuffix.fieldBase
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    R.Base (ctorFieldCheck c stats #[]) :=
  (R.baseMain depth H.depth_le).cast
    (((R.baseMain depth H.depth_le).restrictTo_eq R.lctxWF).symm.trans
      (congrArg c.lctx.restrictTo H.fieldFVars))

theorem RecursorParameterContextSuffix.fieldBase_fvarList
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    H.fieldBase.m.fvarList =
      (stats.params ++ (#[] : Array Expr)).toList.map (·.fvarId!) :=
  H.fieldFVars

theorem RecursorParameterContextSuffix.fieldBase_vlctx
    {c : AddInductive.Context} {recLparams : List Name}
    {R : RecursorContextWF c recLparams}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    (H : RecursorParameterContextSuffix R stats depth) :
    H.fieldBase.m.vlctx = H.parameterDecls :=
  H.dropAmbient_vlctx

/-- The checker context of the next constructor field: the parameters and
every field opened so far. -/
def RecursorContextWF.fieldBaseNext
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {stats : AddInductive.InductiveStats} {bu : Array Expr}
    (B : R.Base (ctorFieldCheck c stats bu))
    (hB : B.m.fvarList = (stats.params ++ bu).toList.map (·.fvarId!))
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS R.venv recLparams B.m.vlctx ty ty₀)
    (hty₀ : R.venv.IsType recLparams.length B.m.vlctx.toCtx ty₀) :
    (R.withCheckedLocalDeclOn (name := name) (bi := bi) _ B
        htr hty htr₀ hty₀).Base
      (ctorFieldCheck { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
        checkLCtx := (ctorFieldCheck c stats bu).mkLocalDecl ⟨c.ngen.curr⟩
          name ty bi } stats (bu.push (.fvar ⟨c.ngen.curr⟩))) :=
  let R' := R.withCheckedLocalDeclOn (name := name) (bi := bi) _ B
    htr hty htr₀ hty₀
  R'.check.cast ((R'.check.restrictTo_eq R'.lctxWF).symm.trans
    (congrArg (c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi).restrictTo (by
      change B.m.fvarList ++ [⟨c.ngen.curr⟩] = _
      rw [hB]
      simp [Expr.fvarId!])))

theorem RecursorContextWF.fieldBaseNext_fvarList
    {c : AddInductive.Context} {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    {stats : AddInductive.InductiveStats} {bu : Array Expr}
    (B : R.Base (ctorFieldCheck c stats bu))
    (hB : B.m.fvarList = (stats.params ++ bu).toList.map (·.fvarId!))
    (htr : TrExprS R.venv recLparams R.mlctx.vlctx ty ty')
    (hty : R.venv.IsType recLparams.length R.mlctx.vlctx.toCtx ty')
    (htr₀ : TrExprS R.venv recLparams B.m.vlctx ty ty₀)
    (hty₀ : R.venv.IsType recLparams.length B.m.vlctx.toCtx ty₀) :
    (R.fieldBaseNext (name := name) (bi := bi) B hB htr hty htr₀ hty₀).m.fvarList =
      (stats.params ++ bu.push (.fvar ⟨c.ngen.curr⟩)).toList.map (·.fvarId!) := by
  change B.m.fvarList ++ [⟨c.ngen.curr⟩] = _
  rw [hB]
  simp [Expr.fvarId!]

namespace mkRecInfos.loopCtorArgs.loop

/-- Strengthening of `recursiveDomainsRecursor` which also records that the
complete constructor-field array is the exact consecutive suffix opened by
the production traversal.  This trace is required when the second pass closes
all field binders around the generated minor premise. -/
theorem recursiveDomainsRecursorRecent {alpha : Type}
    (stats : AddInductive.InductiveStats)
    (head : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M alpha)
    {decl : VInductDecl} {depth : Nat} {typeTarget rootTypeTarget : VExpr}
    {recLparams : List Name}
    {source t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {root c : AddInductive.Context} {Q : alpha → Prop}
    (Rroot : RecursorContextWF root recLparams)
    (R : RecursorContextWF c recLparams)
    {fields : List (RecursorRecursiveDomainAt
      R.venv decl recLparams.length)}
    {positions : List Nat}
    {args : List VExpr}
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hparams : stats.params.size ≤ i)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts
      (decl.types.map (·.name)) R.mlctx.vlctx)
    (htype : TrExprS R.venv recLparams R.mlctx.vlctx t typeTarget)
    (B : R.Base (ctorFieldCheck c stats bu))
    (hB : B.m.fvarList = (stats.params ++ bu).toList.map (·.fvarId!))
    {typeTarget₀ : VExpr}
    (htype₀ : TrExprS R.venv recLparams B.m.vlctx t typeTarget₀)
    (hchkFields : 0 < bu.size →
      R.chk.fvarList = (stats.params ++ bu).toList.map (·.fvarId!))
    {baseV : VLCtx} {root₀ : VExpr}
    (hagreeB : ∃ hn : bu.size ≤ B.m.length,
      MLCtxTopAgree R.mlctx B.m bu.size ∧ (B.m.dropN bu.size hn).vlctx = baseV ∧
        R.venv.IsDefEqU recLparams.length baseV.toCtx root₀
          (B.m.mkForall' bu.size hn typeTarget₀))
    (hchkB : 0 < bu.size → R.chk = B.m)
    (htypeType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx typeTarget)
    (hfields : RecursorFieldSelectionsAt R.venv decl recLparams.length
      bu u fields)
    (hdecisions : RecursorFieldDecisions stats root source c t bu u positions)
    (hargs : List.Forall₂
      (TrExprS R.venv recLparams R.mlctx.vlctx) u.toList args)
    (Hrecent : RecursorRecentBoundFVarArray Rroot R bu)
    (Hopening : ConstructorFieldOpening source t bu)
    (hrootType : Rroot.venv.IsDefEqU recLparams.length
      Rroot.mlctx.vlctx.toCtx rootTypeTarget
        (R.mlctx.mkForall' bu.size Hrecent.size_le typeTarget))
    {P : FVarId → Prop}
    (hsourceScope : source.FVarsIn P)
    (hcurrentUp : IsFVarUpSet
      (fun fv => fv ∈ Hopening.fvars ∨ P fv) R.mlctx.vlctx)
    {appliedTarget : VExpr}
    (happlied : TrExprS R.venv recLparams R.mlctx.vlctx
      (mkAppN head bu) appliedTarget)
    (happliedType : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx appliedTarget typeTarget)
    (Hk : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {t' : Expr} {typeTarget' appliedTarget' : VExpr}
      {bu' u' : Array Expr}
      {fields' : List (RecursorRecursiveDomainAt
        Rcurrent.venv decl recLparams.length)} {positions' : List Nat}
      {args' : List VExpr},
      t'.isForall = false →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        t' typeTarget' →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx typeTarget' →
      RecursorFieldSelectionsAt Rcurrent.venv decl recLparams.length
        bu' u' fields' →
      RecursorFieldDecisions stats root source current t'
        bu' u' positions' →
      List.Forall₂
        (TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx)
        u'.toList args' →
      (Hrecent' : RecursorRecentBoundFVarArray Rroot Rcurrent bu') →
      (Hopening' : ConstructorFieldOpening source t' bu') →
      Rroot.venv.IsDefEqU recLparams.length Rroot.mlctx.vlctx.toCtx
        rootTypeTarget
          (Rcurrent.mlctx.mkForall' bu'.size
            Hrecent'.size_le typeTarget') →
      t'.FVarsIn (fun fv => fv ∈ Hopening'.fvars ∨ P fv) →
      IsFVarUpSet (fun fv => fv ∈ Hopening'.fvars ∨ P fv)
        Rcurrent.mlctx.vlctx →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN head bu') appliedTarget' →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget' typeTarget' →
      (0 < bu'.size →
        Rcurrent.chk.fvarList = (stats.params ++ bu').toList.map (·.fvarId!)) →
      (∃ M : TypeChecker.MLCtx, M.WF Rcurrent.venv recLparams ∧
        (0 < bu'.size → Rcurrent.chk = M) ∧
        ∃ hn : bu'.size ≤ M.length,
          MLCtxTopAgree Rcurrent.mlctx M bu'.size ∧
            (M.dropN bu'.size hn).vlctx = baseV ∧
            ∃ t₀', TrExprS Rcurrent.venv recLparams M.vlctx t' t₀' ∧
              Rcurrent.venv.IsDefEqU recLparams.length baseV.toCtx root₀
                (M.mkForall' bu'.size hn t₀')) →
      (k t' bu' u' current).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k
      t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u depth typeTarget typeTarget₀ fields
      positions args appliedTarget B with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      have hparam : stats.params[i]? = none := by
        apply Array.getElem?_eq_none
        omega
      rw [hparam]
      have htypeTr := htype.trExpr R.checking.tr.wf R.mlctx_wf.tr.wf
      rcases TrExpr.forallE_source htypeTr with
        ⟨sourceDom, sourceBody, hdom, hbody, hdomType,
          hbodyType, hforallEq⟩
      rcases hconsume c recLparams R hdom hdomType with
        ⟨consumedDom, Hdom⟩
      rcases Hdom.body R hbody with
        ⟨consumedBody, hbodyConsumed, _hbodyEq⟩
      let RB := R.withCheckLCtx _ B
      rcases TrExpr.forallE_source (htype₀.trExpr R.checking.tr.wf B.wf.tr.wf) with
        ⟨dom₀, bodyN₀, hdom₀, hbodyN₀, hdom₀Type, hbodyN₀Type, hforallEq₀⟩
      rcases hconsume _ recLparams RB.narrow hdom₀ hdom₀Type with
        ⟨consumedDom₀, Hdom₀⟩
      rcases Hdom₀.body RB.narrow hbodyN₀ with ⟨body₀'', hbody₀'', hbody₀Eq⟩
      have hcons₀ : TrExprS R.venv recLparams B.m.vlctx
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) consumedDom₀ := Hdom₀.consumed
      have hconsT₀ : R.venv.IsType recLparams.length B.m.vlctx.toCtx
          consumedDom₀ := Hdom₀.isType
      refine AddInductive.M.WF_bind AddInductive.getLCtx.WF fun _ hlctx => ?_
      subst hlctx
      refine withCheckedLocalDeclOn.WF (name := name) (bi := bi) (Q := Q) ?_
      let c' : AddInductive.Context := { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi
        checkLCtx := (ctorFieldCheck c stats bu).mkLocalDecl ⟨c.ngen.curr⟩ name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) bi }
      let R' : RecursorContextWF c' recLparams :=
        R.withCheckedLocalDeclOn (name := name) (bi := bi)
          (ctorFieldCheck c stats bu) B
          Hdom.consumed Hdom.isType hcons₀ hconsT₀
      have Hstats' := Hstats.withFVar R'.checking.tr.wf
        R'.mlctx_wf.tr.wf
      have hctx' : VLCtx.NoIndConsts
          (decl.types.map (·.name)) R'.mlctx.vlctx := by
        apply VLCtx.NoIndConsts.cons hctx
        rfl
      let W : VLCtx.FVLift R.mlctx.vlctx R'.mlctx.vlctx 0 1 0 :=
        .skip_fvar _ _ .refl
      have happliedFn := happlied.weakFV R.checking.tr.wf.ordered W
        R'.mlctx_wf.tr.wf
      have happliedFnType : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx (appliedTarget.liftN 1 0)
          ((VExpr.forallE sourceDom sourceBody).liftN 1 0) := by
        exact (happliedType.defeqU_r R.checking.tr.wf
          R.mlctx_wf.tr.wf.toCtx hforallEq.symm).weakN
            R.checking.tr.wf.ordered W.toCtx
      have hdomWeak : TrExprS R'.venv recLparams R'.mlctx.vlctx dom
          (sourceDom.liftN 1 0) := by
        exact Hdom.source.weakFV R.checking.tr.wf.ordered W
          R'.mlctx_wf.tr.wf
      have hargsWeak : List.Forall₂
          (TrExprS R'.venv recLparams R'.mlctx.vlctx) u.toList
          (args.map fun arg => arg.liftN 1 0) := by
        apply checkPositivityStep.forall₂_map_right hargs
        intro source arg harg
        exact harg.weakFV R.checking.tr.wf.ordered W R'.mlctx_wf.tr.wf
      have harg : TrExprS R'.venv recLparams R'.mlctx.vlctx
          (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
        exact TrExprS.fvar (A := consumedDom.lift) (by
          change VLCtx.find? ((some (⟨c.ngen.curr⟩,
            (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList), .vlam consumedDom) ::
              R.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
          simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
            VLocalDecl.value, VLocalDecl.type])
      have hargType : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx (.bvar 0) (sourceDom.liftN 1 0) := by
        have hlookup : R'.mlctx.vlctx.find? (.inr ⟨c.ngen.curr⟩) =
            some ((.bvar 0), consumedDom.liftN 1 0) := by
          change VLCtx.find?
            ((some (⟨c.ngen.curr⟩,
                (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList), .vlam consumedDom) ::
              R.mlctx.vlctx)
            (.inr ⟨c.ngen.curr⟩) =
              some ((.bvar 0), consumedDom.liftN 1 0)
          simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
            VLocalDecl.value, VLocalDecl.type, VExpr.lift]
        have hconsumed := R'.mlctx_wf.tr.wf.find?_wf
          R'.checking.tr.wf.ordered hlookup
        have hdomainEq := Hdom.source_defeq.choose_spec.weakN
          R.checking.tr.wf.ordered W.toCtx
        exact hconsumed.defeqU_r R'.checking.tr.wf
          R'.mlctx_wf.tr.wf.toCtx hdomainEq.symm.toU
      have happlied' : TrExprS R'.venv recLparams R'.mlctx.vlctx
          (mkAppN head (bu.push (.fvar ⟨c.ngen.curr⟩)))
          (.app (appliedTarget.liftN 1 0) (.bvar 0)) := by
        simpa [mkAppN] using
          TrExprS.app happliedFnType hargType happliedFn harg
      have happliedType' : R'.venv.HasType recLparams.length
          R'.mlctx.vlctx.toCtx
          (.app (appliedTarget.liftN 1 0) (.bvar 0)) consumedBody := by
        have happ := VEnv.HasType.app happliedFnType hargType
        have hbodyEq' := Hdom.bodyDefEqConsumed R _hbodyEq
        apply happ.defeqU_r R'.checking.tr.wf R'.mlctx_wf.tr.wf.toCtx
        simpa only [R', RecursorContextWF.withLocalDecl_venv, RecursorContextWF.withCheckedLocalDecl_venv, RecursorContextWF.withCheckedLocalDeclOn_venv,
          RecursorContextWF.withLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDeclOn_toCtx, VExpr.inst_liftN_bvar] using
            hbodyEq'
      have hopened := R.instantiateFresh (name := name) (bi := bi)
        Hdom.consumed Hdom.isType hbodyConsumed
      have hsourceBodyType : R'.venv.IsType recLparams.length
          R'.mlctx.vlctx.toCtx sourceBody := by
        let hctxEq : VLCtx.IsDefEq R.venv recLparams.length
            ((none, .vlam sourceDom) :: R.mlctx.vlctx)
            ((none, .vlam consumedDom) :: R.mlctx.vlctx) :=
          VLCtx.IsDefEq.cons
            (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) nofun
            (.vlam Hdom.source_defeq.choose_spec)
        simpa only [R', RecursorContextWF.withLocalDecl_venv, RecursorContextWF.withCheckedLocalDecl_venv, RecursorContextWF.withCheckedLocalDeclOn_venv,
          RecursorContextWF.withLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDeclOn_toCtx, VLCtx.toCtx] using
          hbodyType.defeqDFC R.checking.tr.wf.ordered hctxEq.defeqCtx
      have hbodyEq' := Hdom.bodyDefEqConsumed R _hbodyEq
      have hconsumedBodyType : R'.venv.IsType recLparams.length
          R'.mlctx.vlctx.toCtx consumedBody := by
        apply hsourceBodyType.defeqU_l R'.checking.tr.wf
          R'.mlctx_wf.tr.wf.toCtx
        simpa only [R', RecursorContextWF.withLocalDecl_venv, RecursorContextWF.withCheckedLocalDecl_venv, RecursorContextWF.withCheckedLocalDeclOn_venv,
          RecursorContextWF.withLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDecl_toCtx, RecursorContextWF.withCheckedLocalDeclOn_toCtx, VLCtx.toCtx] using hbodyEq'
      let HdomainCtx : VLCtx.IsDefEq R.venv recLparams.length
          ((none, .vlam sourceDom) :: R.mlctx.vlctx)
          ((none, .vlam consumedDom) :: R.mlctx.vlctx) :=
        .cons (.refl R.checking.tr.wf R.mlctx_wf.tr.wf) nofun
          (.vlam Hdom.source_defeq.choose_spec)
      have HbodyAtSourceU : R.venv.IsDefEqU recLparams.length
          (sourceDom :: R.mlctx.vlctx.toCtx) sourceBody consumedBody := by
        exact hbodyEq'.defeqDFC R.checking.tr.wf
          ((HdomainCtx.symm R.checking.tr.wf.ordered).defeqCtx)
      rcases hbodyType with ⟨bodyLevel, HbodyType⟩
      have HbodyAtSource : R.venv.IsDefEq recLparams.length
          (sourceDom :: R.mlctx.vlctx.toCtx) sourceBody consumedBody
          (.sort bodyLevel) :=
        HbodyAtSourceU.of_l R.checking.tr.wf
          ⟨R.mlctx_wf.tr.wf.toCtx, hdomType⟩ HbodyType
      have HforallConsumed : R.venv.IsDefEqU recLparams.length
          R.mlctx.vlctx.toCtx
          (.forallE sourceDom sourceBody)
          (.forallE consumedDom consumedBody) := by
        exact ⟨_, VEnv.IsDefEq.forallEDF
          Hdom.source_defeq.choose_spec HbodyAtSource⟩
      have HtypeConsumed : R.venv.IsDefEqU recLparams.length
          R.mlctx.vlctx.toCtx typeTarget
          (.forallE consumedDom consumedBody) :=
        hforallEq.symm.trans R.checking.tr.wf
          R.mlctx_wf.tr.wf.toCtx HforallConsumed
      rcases htypeType with ⟨typeLevel, HtypeType⟩
      have HtypeConsumedAtSort : R.venv.IsDefEq recLparams.length
          R.mlctx.vlctx.toCtx typeTarget
          (.forallE consumedDom consumedBody) (.sort typeLevel) :=
        HtypeConsumed.of_l R.checking.tr.wf
          R.mlctx_wf.tr.wf.toCtx HtypeType
      rcases R.mlctx_wf.mkForall'_congr HtypeConsumedAtSort bu.size
          Hrecent.size_le with
        ⟨closedLevel, HclosedConsumed⟩
      have HclosedConsumedU : R.venv.IsDefEqU recLparams.length
          (R.mlctx.dropN bu.size Hrecent.size_le).vlctx.toCtx
          (R.mlctx.mkForall' bu.size Hrecent.size_le typeTarget)
          (R.mlctx.mkForall' bu.size Hrecent.size_le
            (.forallE consumedDom consumedBody)) :=
        ⟨.sort closedLevel, HclosedConsumed⟩
      let Hrecent' := Hrecent.pushCurrentOn name (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper)
        consumedDom bi (ctorFieldCheck c stats bu) B
        Hdom.consumed Hdom.isType hcons₀ hconsT₀
      have HclosedConsumedRoot : Rroot.venv.IsDefEqU recLparams.length
          Rroot.mlctx.vlctx.toCtx
          (R.mlctx.mkForall' bu.size Hrecent.size_le typeTarget)
          (R'.mlctx.mkForall' (bu.push (.fvar ⟨c.ngen.curr⟩)).size
            Hrecent'.size_le consumedBody) := by
        simpa only [Hrecent.venv_eq, Hrecent.drop_eq, R',
          RecursorContextWF.withLocalDecl, RecursorContextWF.withCheckedLocalDecl, RecursorContextWF.withCheckedLocalDeclOn, Array.size_push,
          TypeChecker.MLCtx.mkForall'] using HclosedConsumedU
      have hrootType' : Rroot.venv.IsDefEqU recLparams.length
          Rroot.mlctx.vlctx.toCtx rootTypeTarget
          (R'.mlctx.mkForall' (bu.push (.fvar ⟨c.ngen.curr⟩)).size
            Hrecent'.size_le consumedBody) :=
        hrootType.trans Rroot.checking.tr.wf
          Rroot.mlctx_wf.tr.wf.toCtx HclosedConsumedRoot
      -- `isRecArg` runs in the checker context saved before the field binder.
      have Hclass := isRecArg.refinesRecursor
        ((R.withLocalDecl (name := name) (bi := bi) Hdom.consumed Hdom.isType).withCheckLCtx
          (ctorFieldCheck c stats bu)
          (B.skip R.checking.tr.wf.ordered R.mlctx_wf R.lctx_eq
            (R.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType).mlctx_wf))
        Hstats' hconsume
        hlit hctx'
        (hdomWeak.trExpr R'.checking.tr.wf R'.mlctx_wf.tr.wf) hdom₀
      let B' := R.fieldBaseNext (name := name) (bi := bi) B hB
        Hdom.consumed Hdom.isType hcons₀ hconsT₀
      have hB' := R.fieldBaseNext_fvarList (name := name) (bi := bi) B hB
        Hdom.consumed Hdom.isType hcons₀ hconsT₀
      have hagreeB₁ : ∃ hn : bu.size ≤ B.m.length,
          MLCtxTopAgree R.mlctx B.m bu.size ∧
            (B.m.dropN bu.size hn).vlctx = baseV ∧
            R.venv.IsDefEqU recLparams.length baseV.toCtx root₀
              (B.m.mkForall' bu.size hn (.forallE consumedDom₀ body₀'')) := by
        obtain ⟨hnB, hagB, hdropB, hrootB⟩ := hagreeB
        refine ⟨hnB, hagB, hdropB, ?_⟩
        have hbodyEq₀ := Hdom₀.bodyDefEqConsumed RB.narrow hbody₀Eq
        let HdomainCtx₀ : VLCtx.IsDefEq R.venv recLparams.length
            ((none, .vlam dom₀) :: B.m.vlctx)
            ((none, .vlam consumedDom₀) :: B.m.vlctx) :=
          .cons (.refl R.checking.tr.wf B.wf.tr.wf) nofun
            (.vlam Hdom₀.source_defeq.choose_spec)
        have HbodyAtSourceU₀ : R.venv.IsDefEqU recLparams.length
            (dom₀ :: B.m.vlctx.toCtx) bodyN₀ body₀'' := by
          have h := hbodyEq₀.defeqDFC R.checking.tr.wf
            ((HdomainCtx₀.symm R.checking.tr.wf.ordered).defeqCtx)
          simpa [VLCtx.toCtx] using h
        rcases hbodyN₀Type with ⟨bodyLevel₀, HbodyType₀⟩
        have HbodyAtSource₀ : R.venv.IsDefEq recLparams.length
            (dom₀ :: B.m.vlctx.toCtx) bodyN₀ body₀'' (.sort bodyLevel₀) :=
          HbodyAtSourceU₀.of_l R.checking.tr.wf
            ⟨B.wf.tr.wf.toCtx, hdom₀Type⟩ HbodyType₀
        have HforallDF := VEnv.IsDefEq.forallEDF
          Hdom₀.source_defeq.choose_spec HbodyAtSource₀
        have HtypeConsumed₀ : R.venv.IsDefEqU recLparams.length
            B.m.vlctx.toCtx typeTarget₀ (.forallE consumedDom₀ body₀'') :=
          hforallEq₀.symm.trans R.checking.tr.wf B.wf.tr.wf.toCtx ⟨_, HforallDF⟩
        have HtypeConsumedAtSort₀ :=
          HtypeConsumed₀.of_r R.checking.tr.wf B.wf.tr.wf.toCtx
            HforallDF.hasType.2
        rcases B.wf.mkForall'_congr HtypeConsumedAtSort₀ bu.size hnB with
          ⟨closedLevel₀, Hclosed₀⟩
        rw [hdropB] at Hclosed₀
        exact hrootB.trans R.checking.tr.wf
          (by rw [← hdropB]; exact (B.wf.dropN bu.size hnB).tr.wf.toCtx)
          ⟨_, Hclosed₀⟩
      have hagreeB' : ∃ hn : (bu.push (.fvar ⟨c.ngen.curr⟩)).size ≤ B'.m.length,
          MLCtxTopAgree R'.mlctx B'.m (bu.push (.fvar ⟨c.ngen.curr⟩)).size ∧
            (B'.m.dropN (bu.push (.fvar ⟨c.ngen.curr⟩)).size hn).vlctx = baseV ∧
            R'.venv.IsDefEqU recLparams.length baseV.toCtx root₀
              (B'.m.mkForall' (bu.push (.fvar ⟨c.ngen.curr⟩)).size hn body₀'') := by
        have h := MLCtxTopAgree.stepDropForall ⟨c.ngen.curr⟩ name
          (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper) consumedDom consumedDom₀ bi hagreeB₁
        simp only [Array.size_push]
        exact h
      have hopened₀ : TrExprS R.venv recLparams B'.m.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body₀'' :=
        RB.narrow.instantiateFresh (name := name) (bi := bi)
          Hdom₀.consumed Hdom₀.isType hbody₀''
      have hopenFvars : Hopening.fvars =
          Hrecent.toBoundFVarArray.fvars :=
        Hopening.fvars_eq_bound Hrecent.toBoundFVarArray
      have hcurrentFresh : (⟨c.ngen.curr⟩ : FVarId) ∉ Hopening.fvars := by
        rw [hopenFvars]
        intro hmem
        exact R.toBindingContextWF.current_not_mem
          (Hrecent.toBoundFVarArray.members _ hmem)
      have hbodyFresh : body.FVarsIn
          (fun other => other ≠ (⟨c.ngen.curr⟩ : FVarId)) := by
        apply hbody.fvarsIn.mono
        intro other hother heq
        subst other
        have hbase : (⟨c.ngen.curr⟩ : FVarId) ∈
            R.mlctx.vlctx.fvars := by
          simpa using hother
        rw [← R.mlctx_wf.tr.fvars_eq, R.lctx_eq] at hbase
        exact R.toBindingContextWF.current_not_mem hbase
      let Hopening' := Hopening.push hcurrentFresh hbodyFresh
      have hcurrentScope := Hopening.currentFVarsIn hsourceScope
      have hdomScope : dom.FVarsIn
          (fun fv => fv ∈ Hopening.fvars ∨ P fv) := hcurrentScope.1
      have hnewNotCurrent : (⟨c.ngen.curr⟩ : FVarId) ∉
          R.mlctx.vlctx.fvars := by
        intro hmem
        rw [← R.mlctx_wf.tr.fvars_eq, R.lctx_eq] at hmem
        exact R.toBindingContextWF.current_not_mem hmem
      have hcurrentUp' : IsFVarUpSet
          (fun fv => fv ∈ Hopening'.fvars ∨ P fv)
          R.mlctx.vlctx := by
        apply (IsFVarUpSet.congr (R.mlctx_wf.tr.wf).fvwf ?_).mp hcurrentUp
        intro fv hfv
        constructor
        · intro h
          rcases h with h | h
          · exact Or.inl (by
              change fv ∈ Hopening.fvars ++ [⟨c.ngen.curr⟩]
              exact List.mem_append_left _ h)
          · exact Or.inr h
        · intro h
          rcases h with h | h
          · change fv ∈ Hopening.fvars ++ [⟨c.ngen.curr⟩] at h
            rcases List.mem_append.mp h with h | h
            · exact Or.inl h
            · simp only [List.mem_singleton] at h
              subst fv
              exact False.elim (hnewNotCurrent hfv)
          · exact Or.inr h
      have hnextUp : IsFVarUpSet
          (fun fv => fv ∈ Hopening'.fvars ∨ P fv)
          R'.mlctx.vlctx := by
        change IsFVarUpSet _
          ((some (⟨c.ngen.curr⟩,
              (dom.consumeTypeAnnotationsVerified c.env.isTypeAnnotationWrapper).fvarsList), .vlam consumedDom) ::
            R.mlctx.vlctx)
        refine ⟨hcurrentUp', fun _ dep hdep => ?_⟩
        have hselected : dep ∈ Hopening.fvars ∨ P dep :=
          (fvarsIn_iff.mp
            (Expr.consumeTypeAnnotationsVerified_fvarsIn hdomScope)).1 dep hdep
        rcases hselected with hfield | hparam
        · exact Or.inl (by
            change dep ∈ Hopening.fvars ++ [⟨c.ngen.curr⟩]
            exact List.mem_append_left _ hfield)
        · exact Or.inr hparam
      have HclassExact : (AddInductive.isRecArg stats dom { c' with checkLCtx := ctorFieldCheck c stats bu }).WF
          (fun selected =>
            AddInductive.isRecArg stats dom { c' with checkLCtx := ctorFieldCheck c stats bu } = .ok selected ∧
              ∀ target, selected = some target →
                ∃ htarget : target < decl.types.length,
                decl.RecursiveArgAtTarget R'.venv recLparams.length
                  (decl.types[target]'htarget).name
                  R'.mlctx.vlctx.toCtx (depth + 1)
                  (sourceDom.liftN 1 0)) := by
        intro selected hrun
        exact ⟨hrun, Hclass selected hrun⟩
      refine HclassExact.bind fun selected hselected => ?_
      cases selected with
      | none =>
        exact ih R' Hstats' (by omega) hlit hctx' hopened B' hB' hopened₀
          (fun _ => hB') hagreeB' (fun _ => rfl)
          hconsumedBodyType (.nonrecursive hfields)
          (.nonrecursive hdecisions hselected.1) hargsWeak Hrecent'
          Hopening' hrootType' hnextUp happlied' happliedType'
      | some target =>
        rcases hselected.2 target rfl with ⟨howner, hrecursive⟩
        let cert : RecursorRecursiveDomainAt
            R'.venv decl recLparams.length := {
          fieldIndex := bu.size
          ownerIdx := target
          owner_lt := howner
          ctx := R'.mlctx.vlctx.toCtx
          depth := depth + 1
          domain := sourceDom.liftN 1 0
          recursive := hrecursive }
        have hargs' : List.Forall₂
            (TrExprS R'.venv recLparams R'.mlctx.vlctx)
            (u.push (.fvar ⟨c.ngen.curr⟩)).toList
            ((args.map fun arg => arg.liftN 1 0) ++ [.bvar 0]) := by
          simpa using List.Forall₂.append'
            hargsWeak (.cons harg .nil)
        exact ih R' Hstats' (by omega) hlit hctx' hopened B' hB' hopened₀
          (fun _ => hB') hagreeB' (fun _ => rfl)
          hconsumedBodyType
          (.recursive hfields (cert := cert) rfl)
          (.recursive hdecisions hselected.1) hargs' Hrecent'
          Hopening' hrootType' hnextUp happlied' happliedType'
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
      exact Hk R rfl htype htypeType hfields hdecisions hargs Hrecent
        Hopening hrootType (Hopening.currentFVarsIn hsourceScope) hcurrentUp
        happlied happliedType hchkFields ⟨B.m, B.wf, hchkB, by
          obtain ⟨hnB, hagB, hdropB, hrootB⟩ := hagreeB
          exact ⟨hnB, hagB, hdropB, typeTarget₀, htype₀, hrootB⟩⟩

end mkRecInfos.loopCtorArgs.loop

/-- Public constructor-field traversal retaining both the semantic recursive
selection and the exact consecutive all-field suffix. -/
theorem mkRecInfos.loopCtorArgs.recursiveDomainsRecursorRecent {alpha : Type}
    (stats : AddInductive.InductiveStats) (t tail : Expr)
    (head : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M alpha)
    (c : AddInductive.Context) {Q : alpha → Prop}
    {decl : VInductDecl} {depth : Nat} {tailTarget : VExpr}
    {recLparams : List Name}
    (R : RecursorContextWF c recLparams)
    (Hstats : RecursorValidAppStatsWF R.venv recLparams
      R.mlctx.vlctx stats decl depth)
    (hprefix : RecursorParamPrefix stats 0 t tail)
    (hconsume : RecursorConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.AvailableLiteralDisjoint R.venv stats.indConsts)
    (hctx : VLCtx.NoIndConsts
      (decl.types.map (·.name)) R.mlctx.vlctx)
    (htail : TrExprS R.venv recLparams R.mlctx.vlctx tail tailTarget)
    {sdepth : Nat} (Hsuffix : RecursorParameterContextSuffix R stats sdepth)
    {tailTarget₀ : VExpr}
    (htail₀ : TrExprS R.venv recLparams Hsuffix.parameterDecls tail tailTarget₀)
    (htail₀Type : R.venv.IsType recLparams.length
      Hsuffix.parameterDecls.toCtx tailTarget₀)
    (htailType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx tailTarget)
    {P : FVarId → Prop}
    (htailScope : tail.FVarsIn P)
    (hrootUp : IsFVarUpSet P R.mlctx.vlctx)
    {appliedTarget : VExpr}
    (happlied : TrExprS R.venv recLparams R.mlctx.vlctx
      head appliedTarget)
    (happliedType : R.venv.HasType recLparams.length
      R.mlctx.vlctx.toCtx appliedTarget tailTarget)
    (Hk : ∀ {current : AddInductive.Context}
      (Rcurrent : RecursorContextWF current recLparams)
      {t' : Expr} {typeTarget' appliedTarget' : VExpr}
      {bu' u' : Array Expr}
      {fields' : List (RecursorRecursiveDomainAt
        Rcurrent.venv decl recLparams.length)} {positions' : List Nat}
      {args' : List VExpr},
      t'.isForall = false →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        t' typeTarget' →
      Rcurrent.venv.IsType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx typeTarget' →
      RecursorFieldSelectionsAt Rcurrent.venv decl recLparams.length
        bu' u' fields' →
      RecursorFieldDecisions stats c tail current t' bu' u' positions' →
      List.Forall₂
        (TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx)
        u'.toList args' →
      (Hrecent : RecursorRecentBoundFVarArray R Rcurrent bu') →
      (Hopening : ConstructorFieldOpening tail t' bu') →
      R.venv.IsDefEqU recLparams.length R.mlctx.vlctx.toCtx tailTarget
        (Rcurrent.mlctx.mkForall' bu'.size Hrecent.size_le typeTarget') →
      t'.FVarsIn (fun fv => fv ∈ Hopening.fvars ∨ P fv) →
      IsFVarUpSet (fun fv => fv ∈ Hopening.fvars ∨ P fv)
        Rcurrent.mlctx.vlctx →
      TrExprS Rcurrent.venv recLparams Rcurrent.mlctx.vlctx
        (mkAppN head bu') appliedTarget' →
      Rcurrent.venv.HasType recLparams.length
        Rcurrent.mlctx.vlctx.toCtx appliedTarget' typeTarget' →
      (0 < bu'.size →
        Rcurrent.chk.fvarList = (stats.params ++ bu').toList.map (·.fvarId!)) →
      (∃ M : TypeChecker.MLCtx, M.WF Rcurrent.venv recLparams ∧
        (0 < bu'.size → Rcurrent.chk = M) ∧
        ∃ hn : bu'.size ≤ M.length,
          MLCtxTopAgree Rcurrent.mlctx M bu'.size ∧
            (M.dropN bu'.size hn).vlctx = Hsuffix.parameterDecls ∧
            ∃ t₀', TrExprS Rcurrent.venv recLparams M.vlctx t' t₀' ∧
              Rcurrent.venv.IsDefEqU recLparams.length
                Hsuffix.parameterDecls.toCtx tailTarget₀
                (M.mkForall' bu'.size hn t₀')) →
      (k t' bu' u' current).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  let inputContext := c
  unfold AddInductive.mkRecInfos.loopCtorArgs
  have hread : ((read : AddInductive.M AddInductive.Context)
      inputContext).WF (fun c' => c' = inputContext) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  have Htail : ∀ fuel,
      (AddInductive.mkRecInfos.loopCtorArgs.loop stats k tail
        stats.params.size #[] #[] fuel inputContext).WF Q := by
    intro fuel
    have hrootType : R.venv.IsDefEqU recLparams.length
        R.mlctx.vlctx.toCtx tailTarget
          (R.mlctx.mkForall' (#[] : Array Expr).size
            (by simp) tailTarget) := by
      rcases htailType with ⟨level, Htype⟩
      change R.venv.IsDefEqU recLparams.length R.mlctx.vlctx.toCtx
        tailTarget tailTarget
      exact ⟨.sort level, Htype⟩
    exact mkRecInfos.loopCtorArgs.loop.recursiveDomainsRecursorRecent
      stats head k R R Hstats (Nat.le_refl _) hconsume hlit hctx
      htail Hsuffix.fieldBase Hsuffix.fieldBase_fvarList
      (by rw [Hsuffix.fieldBase_vlctx]; exact htail₀) (fun h => by simp at h)
      ⟨Nat.zero_le _, .zero _ _, Hsuffix.fieldBase_vlctx, by
        rcases htail₀Type with ⟨level₀, Htype₀⟩
        exact ⟨.sort level₀, Htype₀⟩⟩
      (fun h => by simp at h)
      htailType .nil .nil .nil (RecursorRecentBoundFVarArray.empty R)
      (ConstructorFieldOpening.empty tail)
      hrootType
      htailScope (by
        apply (IsFVarUpSet.congr (R.mlctx_wf.tr.wf).fvwf ?_).mp hrootUp
        intro fv _
        simp [ConstructorFieldOpening.empty])
      (by simpa [mkAppN] using happlied) happliedType Hk
  exact mkRecInfos.loopCtorArgs.loop.followsParamPrefix stats k hprefix Htail
    inputContext.fuel.inductiveFuel

/-- Close the exact higher-order suffix retained by `loopUArgs` around a
well-typed body.  The result is interpreted back in the root recursor
context, exactly matching the executable `LocalContext.mkForall`. -/
theorem RecursorRecentBoundFVarArray.mkForall
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs)
    {body : Expr} {bodyTarget : VExpr}
    (hbody : TrExprS R.venv recLparams R.mlctx.vlctx body bodyTarget)
    (hbodyType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx bodyTarget) :
    ∃ resultTarget,
      TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx
        (c.lctx.mkForall xs body) resultTarget ∧
      Rroot.venv.IsType recLparams.length
        Rroot.mlctx.vlctx.toCtx resultTarget := by
  rcases R.mkForallRecent hbody hbodyType xs.size H.size_le xs
      H.reverse_eq with ⟨htr, htype⟩
  refine ⟨R.mlctx.mkForall' xs.size H.size_le bodyTarget, ?_, ?_⟩
  · simpa only [H.venv_eq, H.drop_eq] using htr
  · simpa only [H.venv_eq, H.drop_eq] using htype

/-- Exact-target form of `mkForall`, exposing the semantic domain list
instead of hiding it behind an existential. -/
theorem RecursorRecentBoundFVarArray.mkForallExact
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs)
    {body : Expr} {bodyTarget : VExpr}
    (hbody : TrExprS R.venv recLparams R.mlctx.vlctx body bodyTarget)
    (hbodyType : R.venv.IsType recLparams.length
      R.mlctx.vlctx.toCtx bodyTarget) :
    let domains := MLCtxForallDomains R.mlctx xs.size H.size_le
    TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx
        (c.lctx.mkForall xs body) (VExpr.wrapForalls domains bodyTarget) ∧
      Rroot.venv.IsType recLparams.length Rroot.mlctx.vlctx.toCtx
        (VExpr.wrapForalls domains bodyTarget) := by
  rcases R.mkForallRecent hbody hbodyType xs.size H.size_le xs
      H.reverse_eq with ⟨htr, htype⟩
  simpa only [H.venv_eq, H.drop_eq,
    TypeChecker.MLCtx.mkForall'_eq_wrapForalls] using And.intro htr htype

/-- Close the exact higher-order suffix retained by `loopCtorArgs` around a
well-typed term.  This is the term-level counterpart of `mkForall`: the
abstract lambda and its forall type use the very same semantic domain list,
so later equation typing cannot accidentally choose a different constructor
field telescope. -/
theorem RecursorRecentBoundFVarArray.mkLambda
    {root c : AddInductive.Context} {recLparams : List Name}
    {Rroot : RecursorContextWF root recLparams}
    {R : RecursorContextWF c recLparams} {xs : Array Expr}
    (H : RecursorRecentBoundFVarArray Rroot R xs)
    {body : Expr} {bodyTarget typeTarget : VExpr}
    (hbody : TrExprS R.venv recLparams R.mlctx.vlctx body bodyTarget)
    (hbodyType : R.venv.HasType recLparams.length R.mlctx.vlctx.toCtx
      bodyTarget typeTarget) :
    let domains := MLCtxForallDomains R.mlctx xs.size H.size_le
    TrExprS Rroot.venv recLparams Rroot.mlctx.vlctx
        (c.lctx.mkLambda xs body) (VExpr.wrapLams domains bodyTarget) ∧
      Rroot.venv.HasType recLparams.length Rroot.mlctx.vlctx.toCtx
        (VExpr.wrapLams domains bodyTarget)
        (VExpr.wrapForalls domains typeTarget) := by
  have Hclosed := R.mlctx_wf.mkLambda_trS R.checking.tr.wf hbody
    hbodyType xs.size H.size_le
  have hsource : c.lctx.mkLambda xs body =
      R.mlctx.mkLambda xs.size H.size_le body := by
    rw [← R.lctx_eq]
    exact R.mlctx_wf.mkLambda_eq xs.size H.size_le H.reverse_eq
      (by simpa [TypeChecker.MLCtx.noBV] using hbody.closed)
  rw [hsource]
  simpa only [H.venv_eq, H.drop_eq,
    TypeChecker.MLCtx.mkForall'_eq_wrapForalls,
    TypeChecker.MLCtx.mkLambda'_eq_wrapLams] using Hclosed

end VerifyInductive
end Lean4Lean
