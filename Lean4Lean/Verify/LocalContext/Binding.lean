import Lean4Lean.Verify.Expr.Abstraction
import Lean4Lean.Verify.ExprUniverses

/-! # Binders closed over a local context

Lemmas about `LocalContext.mkForall`, `mkLambda` and `mkBindingList`: the telescopes they
produce, their binder positions and their level parameters.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive
attribute [local simp] Lean.Expr.abstractList_const Lean.Expr.abstractList_app Lean.Expr.abstractList_lam
  Lean.Expr.abstractList_forallE Lean.Expr.abstractList_letE Lean.Expr.abstractList_mdata
  Lean.Expr.abstractList_proj

/-- Binding a list of ordinary local declarations creates one concrete forall
per selected declaration and leaves precisely the simultaneous abstraction of
the selected free variables as its residual body. -/
theorem LocalContext.mkBindingListN_forallTelescope
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.ForallTelescope
      (LocalContext.mkBindingListN false lctx fvs body)
      fvs.length (body.abstractN fvs) := by
  have go : ∀ (xs : List FVarId) (current : Expr),
      (∀ fv ∈ xs, ∃ index name type bi kind,
        lctx.find? fv = some (.cdecl index fv name type bi kind)) →
      Expr.ForallTelescope
        (LocalContext.mkBindingListN.go false lctx xs current)
        xs.length current := by
    intro xs
    induction xs with
    | nil =>
      intro current _
      exact .nil _
    | cons fv xs ih =>
      intro current hxs
      rw [LocalContext.mkBindingListN.go]
      have htail := ih
        (LocalContext.mkBindingList1N false lctx xs.reverse fv current)
        (fun x hx => hxs x (by simp [hx]))
      rcases hxs fv (by simp) with
        ⟨index, name, type, bi, kind, hfind⟩
      have hhead : Expr.ForallTelescope
          (LocalContext.mkBindingList1N false lctx xs.reverse fv current)
          1 current := by
        simp only [LocalContext.mkBindingList1N, hfind]
        exact Expr.ForallTelescope.cons (.nil _)
      simpa using htail.trans hhead
  simpa only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core,
    List.length_reverse] using
    go fvs.reverse (body.abstractN fvs) (fun fv hfv =>
      hdecl fv (by simpa using hfv))

/-- `LocalContext.mkForall` over a list of free variables denoting ordinary declarations
gives a forall telescope with the simultaneous abstraction as residual. -/
theorem LocalContext.mkForall_fvars_forallTelescope
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.ForallTelescope
      (lctx.mkForall (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractN fvs) := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN]
  exact LocalContext.mkBindingListN_forallTelescope hdecl

/-- Closing two bodies over the same list of ordinary local declarations
creates the same concrete lambda prefix. -/
theorem LocalContext.sameLambdaPrefixN_fold
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (left right : Expr) :
    Expr.SameLambdaPrefix fvars.length
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N true lctx [] fv
            (result.abstractN [fv])) left)
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N true lctx [] fv
            (result.abstractN [fv])) right) := by
  induction fvars with
  | nil => exact .nil
  | cons fv fvars ih =>
    rcases hdecl fv (by simp) with ⟨index, name, type, bi, kind, hfind⟩
    simp only [List.foldr_cons, List.length_cons]
    simp only [LocalContext.mkBindingList1N, hfind]
    exact Expr.SameLambdaPrefix.cons
      ((ih (fun other hother => hdecl other (by simp [hother]))).abstractN [fv])

/-- Closing one residual with foralls and another with lambdas over the same
ordinary declarations creates one literal cross-kind binder prefix. -/
theorem LocalContext.sameForallLambdaPrefixN_fold
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (forallBody lambdaBody : Expr) :
    Expr.SameForallLambdaPrefix fvars.length
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N false lctx [] fv
            (result.abstractN [fv])) forallBody)
      (fvars.foldr
        (fun fv result =>
          LocalContext.mkBindingList1N true lctx [] fv
            (result.abstractN [fv])) lambdaBody) := by
  induction fvars with
  | nil => exact .nil
  | cons fv fvars ih =>
    rcases hdecl fv (by simp) with ⟨index, name, type, bi, kind, hfind⟩
    simp only [List.foldr_cons, List.length_cons]
    simp only [LocalContext.mkBindingList1N, hfind]
    exact Expr.SameForallLambdaPrefix.cons
      ((ih (fun other hother => hdecl other (by simp [hother]))).abstractN [fv])

/-- `LocalContext.mkLambda` over a list of free variables denoting ordinary declarations
gives a lambda telescope with the simultaneous abstraction as residual. -/
theorem LocalContext.mkBindingListN_lambdaTelescope
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.LambdaTelescope
      (LocalContext.mkBindingListN true lctx fvs body)
      fvs.length (body.abstractN fvs) := by
  have go : ∀ (xs : List FVarId) (current : Expr),
      (∀ fv ∈ xs, ∃ index name type bi kind,
        lctx.find? fv = some (.cdecl index fv name type bi kind)) →
      Expr.LambdaTelescope
        (LocalContext.mkBindingListN.go true lctx xs current)
        xs.length current := by
    intro xs
    induction xs with
    | nil =>
      intro current _
      exact .nil _
    | cons fv xs ih =>
      intro current hxs
      rw [LocalContext.mkBindingListN.go]
      have htail := ih
        (LocalContext.mkBindingList1N true lctx xs.reverse fv current)
        (fun x hx => hxs x (by simp [hx]))
      rcases hxs fv (by simp) with
        ⟨index, name, type, bi, kind, hfind⟩
      have hhead : Expr.LambdaTelescope
          (LocalContext.mkBindingList1N true lctx xs.reverse fv current)
          1 current := by
        simp only [LocalContext.mkBindingList1N, hfind]
        exact Expr.LambdaTelescope.cons (.nil _)
      simpa using htail.trans hhead
  simpa only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core,
    List.length_reverse] using
    go fvs.reverse (body.abstractN fvs) (fun fv hfv =>
      hdecl fv (by simpa using hfv))

theorem LocalContext.mkLambda_fvars_lambdaTelescopeN
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind)) :
    Expr.LambdaTelescope
      (lctx.mkLambda (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractN fvs) := by
  rw [LocalContext.mkLambda, LocalContext.mkBinding_eqN]
  exact LocalContext.mkBindingListN_lambdaTelescope hdecl

/-- Sequential-model form of `mkLambda_fvars_lambdaTelescopeN`, valid for locally closed
bodies and duplicate-free variable lists. -/
theorem LocalContext.mkLambda_fvars_lambdaTelescopeList
    {lctx : LocalContext} {fvs : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvs, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (hnodup : fvs.Nodup) (hb : Closed body) :
    Expr.LambdaTelescope
      (lctx.mkLambda (fvs.map Expr.fvar).toArray body)
      fvs.length (body.abstractList fvs) := by
  rw [← Expr.abstractN_eq_abstractList_of_closed hnodup hb]
  exact LocalContext.mkLambda_fvars_lambdaTelescopeN hdecl

theorem LocalContext.mkBindingListN_append_four
    (hdecl : ∀ fv ∈ ((as ++ bs) ++ cs) ++ ds,
      ∃ decl, lctx.find? fv = some decl)
    (hnodup : (((as ++ bs) ++ cs) ++ ds).Nodup) :
    LocalContext.mkBindingListN isLambda lctx
        (((as ++ bs) ++ cs) ++ ds) body =
      LocalContext.mkBindingListN isLambda lctx as
        (LocalContext.mkBindingListN isLambda lctx bs
          (LocalContext.mkBindingListN isLambda lctx cs
            (LocalContext.mkBindingListN isLambda lctx ds body))) := by
  have habcd := List.nodup_append.mp hnodup
  have habc := List.nodup_append.mp habcd.1
  have hab := List.nodup_append.mp habc.1
  have hasDecl : ∀ fv ∈ as, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hbsDecl : ∀ fv ∈ bs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hcsDecl : ∀ fv ∈ cs, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  have hdsDecl : ∀ fv ∈ ds, ∃ decl, lctx.find? fv = some decl := by
    intro fv hfv; exact hdecl fv (by simp [hfv])
  rw [LocalContext.mkBindingListN_eq_fold hdecl hnodup,
    LocalContext.mkBindingListN_eq_fold hasDecl hab.1,
    LocalContext.mkBindingListN_eq_fold hbsDecl hab.2.1,
    LocalContext.mkBindingListN_eq_fold hcsDecl habc.2.1,
    LocalContext.mkBindingListN_eq_fold hdsDecl habcd.2.1]
  simp only [List.foldr_append]

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

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

/-- Conversely, a telescope over ordinary declarations mentioning only `Us`
has its declared binder types in `Us`. -/
theorem LocalContext.levelParamsIn_mkForall_foldN_types
    {lctx : LocalContext} {fvars : List FVarId} {Us : List Name}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    {body : Expr}
    (h : (fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
      (result.abstractN [fv])) body).levelParamsIn Us = true) :
    ∀ fv ∈ fvars, ∀ decl, lctx.find? fv = some decl →
      decl.type.levelParamsIn Us = true := by
  induction fvars with
  | nil => simp
  | cons fv fvars ih =>
    obtain ⟨index, name, type, bi, kind, hfind⟩ := hdecl fv (by simp)
    simp only [List.foldr_cons, LocalContext.mkBindingList1N, hfind,
      Bool.false_eq_true, ↓reduceIte, Expr.levelParamsIn, Bool.and_eq_true,
      Expr.levelParamsIn_abstractN] at h
    intro other hother decl hdecl'
    simp only [List.mem_cons] at hother
    rcases hother with rfl | hother
    · rw [hfind] at hdecl'
      cases hdecl'
      simpa [LocalDecl.type] using h.1
    · exact ih (fun o ho => hdecl o (by simp [ho])) h.2 other hother decl hdecl'

open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

/-- The binder domain selected by `LocalContext.mkForall` is the exact local
declaration type, simultaneously closed over the strictly earlier selected
free variables. This is what compares a domain of a generated recursor type with the
binder type recorded for it (`RecInfoBinderTypes`). -/
theorem LocalContext.mkBindingListN_forallBinderAt
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length)
    (index : Nat) (name : Name) (type : Expr) (bi : BinderInfo)
    (kind : LocalDeclKind)
    (hselected : lctx.find? fvars[i] =
      some (.cdecl index fvars[i] name type bi kind)) :
    Expr.ForallBinderAt
      (LocalContext.mkBindingListN false lctx fvars body) i
      (type.abstractN (fvars.take i)) := by
  induction fvars generalizing i body with
  | nil => simp at hi
  | cons fv fvars ih =>
    have htailDecl : ∀ other ∈ fvars, ∃ index name type bi kind,
        lctx.find? other = some (.cdecl index other name type bi kind) := by
      intro other hother
      exact hdecl other (by simp [hother])
    have hnodupParts := List.nodup_cons.mp hnodup
    rw [LocalContext.mkBindingListN_cons
      (fun other hother => by
        rcases htailDecl other hother with
          ⟨index, name, type, bi, kind, hlookup⟩
        exact ⟨.cdecl index other name type bi kind, hlookup⟩)
      hnodup]
    cases i with
    | zero =>
      have hhead := hselected
      simp only [List.getElem_cons_zero] at hhead
      simp only [LocalContext.mkBindingList1N, hhead,
        List.take_zero, Expr.abstractN_nil]
      exact .here
    | succ i =>
      have hiTail : i < fvars.length := by simp at hi; omega
      rcases hdecl fv (by simp) with
        ⟨headIndex, headName, headType, headBi, headKind, hheadDecl⟩
      have htailSelected : lctx.find? fvars[i] =
          some (.cdecl index fvars[i] name type bi kind) := by
        simpa using hselected
      have Htail := ih htailDecl hnodupParts.2 i hiTail htailSelected
        (body := body)
      have Habstract := Htail.abstractN [fv] 0
      have hprefixNodup : (fv :: fvars.take i).Nodup := by
        apply List.nodup_cons.mpr
        exact ⟨fun hmem => hnodupParts.1
          (List.mem_of_mem_take hmem),
          hnodupParts.2.take⟩
      have hdomain :
          (type.abstractN (fvars.take i)).abstractN [fv] i =
            type.abstractN (fv :: fvars.take i) := by
        have Hclose := Expr.abstractN_cons (List.nodup_cons.1 hprefixNodup).1 type 0
        simpa [List.length_take, Nat.min_eq_left (Nat.le_of_lt hiTail)] using Hclose.symm
      simp only [Nat.zero_add] at Habstract
      rw [hdomain] at Habstract
      simpa [LocalContext.mkBindingList1N, hheadDecl] using
        Expr.ForallBinderAt.there Habstract

/-- `mkForall` specialization of the positional declaration theorem for an
explicit list of selected free variables. -/
theorem LocalContext.mkForall_fvars_forallBinderAt
    {lctx : LocalContext} {fvars : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length)
    (index : Nat) (name : Name) (type : Expr) (bi : BinderInfo)
    (kind : LocalDeclKind)
    (hselected : lctx.find? fvars[i] =
      some (.cdecl index fvars[i] name type bi kind)) :
    Expr.ForallBinderAt
      (lctx.mkForall (fvars.map Expr.fvar).toArray body) i
      (type.abstractN (fvars.take i)) := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eqN]
  exact LocalContext.mkBindingListN_forallBinderAt hdecl hnodup i hi
    index name type bi kind hselected

/-- Sequential-model form of `mkForall_fvars_forallBinderAt` for closed binder
types. -/
theorem LocalContext.mkForall_fvars_forallBinderAtList
    {lctx : LocalContext} {fvars : List FVarId} {body : Expr}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (hnodup : fvars.Nodup)
    (i : Nat) (hi : i < fvars.length)
    (index : Nat) (name : Name) (type : Expr) (bi : BinderInfo)
    (kind : LocalDeclKind)
    (hselected : lctx.find? fvars[i] =
      some (.cdecl index fvars[i] name type bi kind))
    (hclosed : Closed type) :
    Expr.ForallBinderAt
      (lctx.mkForall (fvars.map Expr.fvar).toArray body) i
      (type.abstractList (fvars.take i)) := by
  rw [← Expr.abstractN_eq_abstractList_of_closed
    (List.Nodup.sublist (List.take_sublist _ _) hnodup) hclosed]
  exact LocalContext.mkForall_fvars_forallBinderAt hdecl hnodup i hi index name
    type bi kind hselected

theorem LocalContext.forallDomainsOnly_foldN
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (body : Expr) :
    Expr.forallDomainsOnly fvars.length
      (fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
        (result.abstractN [fv])) body) =
      fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
        (result.abstractN [fv])) (.sort .zero) := by
  induction fvars with
  | nil => rfl
  | cons fv fvars ih =>
    obtain ⟨index, name, type, bi, kind, hfind⟩ := hdecl fv (by simp)
    simp only [List.foldr_cons, List.length_cons, LocalContext.mkBindingList1N, hfind,
      Bool.false_eq_true, ↓reduceIte, Expr.forallDomainsOnly, Expr.forallDomainsOnly_abstractN]
    simpa only [LocalContext.mkBindingList1N, Bool.false_eq_true, ↓reduceIte] using
      congrArg (fun e => Expr.forallE name (type.abstractN []) (e.abstractN [fv]) bi)
        (ih (fun other hother => hdecl other (by simp [hother])))

theorem LocalContext.forallDomainsOnly_foldN_add
    {lctx : LocalContext} {fvars : List FVarId}
    (hdecl : ∀ fv ∈ fvars, ∃ index name type bi kind,
      lctx.find? fv = some (.cdecl index fv name type bi kind))
    (k : Nat) (body : Expr) :
    Expr.forallDomainsOnly (fvars.length + k)
      (fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
        (result.abstractN [fv])) body) =
      fvars.foldr (fun fv result => LocalContext.mkBindingList1N false lctx [] fv
        (result.abstractN [fv])) (Expr.forallDomainsOnly k body) := by
  induction fvars with
  | nil => simp
  | cons fv fvars ih =>
    obtain ⟨index, name, type, bi, kind, hfind⟩ := hdecl fv (by simp)
    rw [List.length_cons, Nat.add_right_comm]
    simp only [List.foldr_cons, LocalContext.mkBindingList1N, hfind,
      Bool.false_eq_true, ↓reduceIte, Expr.forallDomainsOnly, Expr.forallDomainsOnly_abstractN]
    simpa only [LocalContext.mkBindingList1N, Bool.false_eq_true, ↓reduceIte] using
      congrArg (fun e => Expr.forallE name (type.abstractN []) (e.abstractN [fv]) bi)
        (ih (fun other hother => hdecl other (by simp [hother])))

/-- Peel the outermost binder of a local-context forall. -/
theorem LocalContext.mkForall_cons_cdecl {lctx : LocalContext}
    {x : FVarId} {xs : List FVarId} {b : Expr}
    {idx : Nat} {n : Name} {ty : Expr} {bi : BinderInfo} {kind : LocalDeclKind}
    (hx : lctx.find? x = some (.cdecl idx x n ty bi kind))
    (hxs : ∀ y ∈ xs, ∃ d, lctx.find? y = some d)
    (nd : (x :: xs).Nodup) (hb : Closed b) (hclosed : LocalContext.LctxClosed lctx) :
    lctx.mkForall ((x :: xs).map Expr.fvar).toArray b =
      .forallE n ty ((lctx.mkForall (xs.map Expr.fvar).toArray b).abstract1 x) bi := by
  have hex : ∀ y ∈ x :: xs, ∃ d, lctx.find? y = some d := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, hx⟩
    · exact hxs y hy
  rw [LocalContext.mkForall, LocalContext.mkBinding_eq' hex nd hb hclosed.declsClosed,
    LocalContext.mkBindingList_cons hxs nd, LocalContext.mkForall,
    LocalContext.mkBinding_eq' hxs (List.nodup_cons.mp nd).2 hb hclosed.declsClosed]
  simp [LocalContext.mkBindingList1, hx]

/-- Nested local-context foralls over disjoint lists combine. -/
theorem LocalContext.mkForall_mkForall {lctx : LocalContext}
    {xs ys : List FVarId} {b : Expr}
    (hex : ∀ y ∈ xs ++ ys, ∃ d, lctx.find? y = some d)
    (nd : (xs ++ ys).Nodup) (hb : Closed b) (hclosed : LocalContext.LctxClosed lctx) :
    lctx.mkForall (xs.map Expr.fvar).toArray
        (lctx.mkForall (ys.map Expr.fvar).toArray b) =
      lctx.mkForall ((xs ++ ys).map Expr.fvar).toArray b := by
  have hexY : ∀ y ∈ ys, ∃ d, lctx.find? y = some d :=
    fun y hy => hex y (List.mem_append_right _ hy)
  have hexX : ∀ y ∈ xs, ∃ d, lctx.find? y = some d :=
    fun y hy => hex y (List.mem_append_left _ hy)
  have ndY := (List.nodup_append.mp nd).2.1
  have ndX := (List.nodup_append.mp nd).1
  obtain ⟨hinner, hinnerClosed⟩ := LocalContext.mkBindingListN_eq_mkBindingList
    (isLambda := false) hexY ndY hb hclosed.declsClosed
  have hinner' : lctx.mkForall (ys.map Expr.fvar).toArray b =
      LocalContext.mkBindingList false lctx ys b := by
    rw [LocalContext.mkForall, LocalContext.mkBinding_eqN]
    exact hinner
  rw [hinner', LocalContext.mkForall,
    LocalContext.mkBinding_eq' hexX ndX hinnerClosed hclosed.declsClosed,
    LocalContext.mkForall, LocalContext.mkBinding_eq' hex nd hb hclosed.declsClosed,
    LocalContext.mkBindingList_append hex nd]

end VerifyInductive

end Lean4Lean
