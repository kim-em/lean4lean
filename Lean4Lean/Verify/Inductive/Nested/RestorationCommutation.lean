import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRhs
import Lean4Lean.Verify.Inductive.Recursor.RestoredRealization
import Lean4Lean.Verify.TypeChecker.AlphaLocality

/-! Commutation of executable nested restoration with `Restoration.expr`.

`ElimNestedInductive.Result.restoreNested` opens the common parameters as
free variables and runs `Expr.replace` with `restoreNestedNode`. A matched
auxiliary node `auxI As args` is replaced by the container specialization
applied to `args`; the matched node's parameter arguments are discarded (the
executable assumes they are literally the opened parameters) and its other
arguments are not traversed. `Restoration.expr` instead restores every
argument and substitutes the actual parameter arguments into the head
specialization.

The two agree exactly under the syntactic side condition `RestoreReady`:
every matched auxiliary node is applied to the opened parameters followed by
arguments free of restorable names, at the agreed universe levels, and every
unmatched spine has no auxiliary head. The correspondence between the
executable tables and the abstract restoration is the hypothesis structure
`RestorationMapAgreement`.

The main theorem `ExprReplacement.restorationCommutes` is stated for the
opened body against arbitrary binder-only contexts; the translation of the
restored output is a hypothesis, because `TrExprS` contains typing and the
typing of restored syntax is a separate obligation. Translation of the
restorable fragment is syntactic (`RestoreFragment.translation_eq`), so the
statement fixes the abstract restoration of any translation of the input.
-/

namespace Lean4Lean.InductiveSignature

/-- Names on which `Restoration.expr` acts nontrivially. -/
def Restoration.restorableNames (r : Restoration) : List Name :=
  r.heads.map (·.auxiliary) ++ r.recursors.map Prod.fst

theorem Restoration.expr.go_mkApps (r : Restoration) {xs ys : List VExpr}
    (H : List.Forall₂ (fun x y => Restoration.expr.go r x [] = some y) xs ys)
    (f : VExpr) (args : List VExpr) :
    Restoration.expr.go r (VExpr.mkApps f xs) args =
      Restoration.expr.go r f (ys ++ args) := by
  induction H generalizing f with
  | nil => rfl
  | @cons x y xs ys hxy _ ih =>
    show Restoration.expr.go r (VExpr.mkApps (.app f x) xs) args = _
    rw [ih]
    simp [Restoration.expr.go, hxy]

theorem Restoration.heads_find?_eq_none {r : Restoration} {name : Name}
    (h : name ∉ r.heads.map (·.auxiliary)) :
    r.heads.find? (fun h => h.auxiliary == name) = none := by
  apply List.find?_eq_none.mpr
  intro head hmem heq
  exact h (List.mem_map.mpr ⟨head, hmem, by simpa using heq⟩)

theorem Restoration.recursorName_of_not_mem {r : Restoration} {name : Name}
    (h : name ∉ r.recursors.map Prod.fst) : r.recursorName name = name := by
  have hnone : r.recursors.find? (fun pair => pair.1 == name) = none := by
    apply List.find?_eq_none.mpr
    intro pair hmem heq
    exact h (List.mem_map.mpr ⟨pair, hmem, by simpa using heq⟩)
  simp [Restoration.recursorName, hnone]

/-- Restoration is the identity on syntax mentioning none of its names. -/
theorem Restoration.expr.go_of_not_contains (r : Restoration) {e : VExpr}
    (H : e.containsAnyConst r.restorableNames = false) (args : List VExpr) :
    Restoration.expr.go r e args = some (VExpr.mkApps e args) := by
  induction e generalizing args with
  | bvar | sort | elim => rfl
  | const name levels =>
    have hname : name ∉ r.restorableNames := by
      simpa [VExpr.containsAnyConst] using H
    simp only [Restoration.restorableNames, List.mem_append, not_or] at hname
    simp [Restoration.expr.go, Restoration.heads_find?_eq_none hname.1,
      Restoration.recursorName_of_not_mem hname.2]
  | app fn arg ihfn iharg =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at H
    simp [Restoration.expr.go, iharg H.2, ihfn H.1, VExpr.mkApps]
  | lam domain body ihd ihb =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at H
    simp [Restoration.expr.go, ihd H.1, ihb H.2, VExpr.mkApps]
  | forallE domain body ihd ihb =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at H
    simp [Restoration.expr.go, ihd H.1, ihb H.2, VExpr.mkApps]
  | proj name i major ih =>
    simp only [VExpr.containsAnyConst, Bool.or_eq_false_iff] at H
    simp [Restoration.expr.go, ih H.2, VExpr.mkApps]

theorem Restoration.expr_of_not_contains (r : Restoration) {e : VExpr}
    (H : e.containsAnyConst r.restorableNames = false) : r.expr e = some e :=
  Restoration.expr.go_of_not_contains r H []

theorem Restoration.expr_wrapForalls (r : Restoration) {domains : List VExpr}
    (hdomains : ∀ d ∈ domains, d.containsAnyConst r.restorableNames = false)
    {body body' : VExpr} (hbody : r.expr body = some body') :
    r.expr (VExpr.wrapForalls domains body) = some (VExpr.wrapForalls domains body') := by
  induction domains with
  | nil => simpa [VExpr.wrapForalls] using hbody
  | cons d ds ih =>
    have hd := Restoration.expr_of_not_contains r (hdomains d (by simp))
    have ht := ih (fun d' hd' => hdomains d' (by simp [hd']))
    simp only [Restoration.expr, VExpr.wrapForalls, List.foldr_cons] at hd ht ⊢
    simp [Restoration.expr.go, hd, ht, VExpr.mkApps]

theorem Restoration.expr_wrapLams (r : Restoration) {domains : List VExpr}
    (hdomains : ∀ d ∈ domains, d.containsAnyConst r.restorableNames = false)
    {body body' : VExpr} (hbody : r.expr body = some body') :
    r.expr (VExpr.wrapLams domains body) = some (VExpr.wrapLams domains body') := by
  induction domains with
  | nil => simpa [VExpr.wrapLams] using hbody
  | cons d ds ih =>
    have hd := Restoration.expr_of_not_contains r (hdomains d (by simp))
    have ht := ih (fun d' hd' => hdomains d' (by simp [hd']))
    simp only [Restoration.expr, VExpr.wrapLams, List.foldr_cons] at hd ht ⊢
    simp [Restoration.expr.go, hd, ht, VExpr.mkApps]

end Lean4Lean.InductiveSignature

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open InductiveSignature (Restoration HeadSpecialization instantiateParams)

namespace VerifyInductive

/-- The executable replacement head for one restorable auxiliary name: the
expression `restoreNestedNode` applies to the non-parameter arguments of a
matched node. -/
def restoreHead (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (c : Name) : Option Expr :=
  match result.aux2nested.find? c with
  | some nested => some ((nested.abstract result.params).instantiateRev As)
  | none =>
    match result.getNestedIfAuxCtor env c with
    | some (nested, auxI) =>
      let nested' := (nested.abstract result.params).instantiateRev As
      match nested'.getAppFn with
      | .const I_c I_ls =>
        some (mkAppN (.const (c.replacePrefix auxI I_c) I_ls) nested'.getAppArgs)
      | _ => none
    | none => none

theorem restoreNestedNode_eq_of_notRecursor
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (As : Array Expr) (auxRec : NameMap Name) (t : Expr)
    (hnotrec : ∀ c ls, t = .const c ls → auxRec.find? c = none) :
    result.restoreNestedNode env As auxRec t =
      match t.getAppFn with
      | .const c _ => (restoreHead result env As c).bind fun H =>
          if result.nparams ≤ t.getAppArgs.size then
            some (mkAppRange H result.nparams t.getAppArgs.size t.getAppArgs)
          else none
      | _ => none := by
  unfold Lean4Lean.ElimNestedInductive.Result.restoreNestedNode
  simp only []
  split
  · rename_i c ls
    simp only [hnotrec c ls rfl]
    generalize (Expr.const c ls).getAppArgs = args
    generalize (Expr.const c ls).getAppFn = fn
    cases fn with
    | const c us =>
      simp only [restoreHead]
      cases hn : result.aux2nested.find? c with
      | some nested => simp [panicWithPosWithDecl, panic, panicCore]; rfl
      | none =>
        cases hc : result.getNestedIfAuxCtor env c with
        | none => simp
        | some pair =>
          rcases pair with ⟨nested, auxI⟩
          simp only [Expr.withApp_eq]
          split <;> split <;> simp_all [panicWithPosWithDecl, panic, panicCore] <;> rfl
    | _ => rfl
  · generalize t.getAppArgs = args
    generalize t.getAppFn = fn
    cases fn with
    | const c us =>
      simp only [restoreHead]
      cases hn : result.aux2nested.find? c with
      | some nested => simp [panicWithPosWithDecl, panic, panicCore]; rfl
      | none =>
        cases hc : result.getNestedIfAuxCtor env c with
        | none => simp
        | some pair =>
          rcases pair with ⟨nested, auxI⟩
          simp only [Expr.withApp_eq]
          split <;> split <;> simp_all [panicWithPosWithDecl, panic, panicCore] <;> rfl
    | _ => rfl

/-- Every entry is an ordinary (non-`let`) binder. -/
def VLCtx.AllVLam (Δ : VLCtx) : Prop := ∀ entry ∈ Δ, ∃ type, entry.2 = .vlam type

/-- Two binder-only contexts with the same variable naming. -/
inductive VLCtx.VLamShape : VLCtx → VLCtx → Prop
  | nil : VLCtx.VLamShape [] []
  | cons {left right : VLCtx} {ofv : Option (FVarId × List FVarId)} {x y : VExpr} :
      VLCtx.VLamShape left right →
      VLCtx.VLamShape ((ofv, .vlam x) :: left) ((ofv, .vlam y) :: right)

theorem VLCtx.VLamShape.left {left right : VLCtx} (H : VLCtx.VLamShape left right) :
    VLCtx.AllVLam left := by
  induction H with
  | nil => intro _ h; cases h
  | cons _ ih =>
    intro entry hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨_, rfl⟩
    · exact ih entry hmem

theorem VLCtx.VLamShape.right {left right : VLCtx} (H : VLCtx.VLamShape left right) :
    VLCtx.AllVLam right := by
  induction H with
  | nil => intro _ h; cases h
  | cons _ ih =>
    intro entry hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨_, rfl⟩
    · exact ih entry hmem

theorem VLCtx.VLamShape.refl {Δ : VLCtx} (H : VLCtx.AllVLam Δ) : VLCtx.VLamShape Δ Δ := by
  induction Δ with
  | nil => exact .nil
  | cons entry Δ ih =>
    rcases entry with ⟨ofv, d⟩
    rcases H (ofv, d) List.mem_cons_self with ⟨x, hx⟩
    simp only at hx
    subst hx
    exact .cons (ih fun e he => H e (by simp [he]))

theorem VLCtx.VLamShape.append {a b c d : VLCtx} (H₁ : VLCtx.VLamShape a b)
    (H₂ : VLCtx.VLamShape c d) : VLCtx.VLamShape (a ++ c) (b ++ d) := by
  induction H₁ with
  | nil => simpa using H₂
  | cons _ ih => exact .cons ih

theorem VLCtx.VLamShape.find? {left right : VLCtx} (H : VLCtx.VLamShape left right)
    (v : Nat ⊕ FVarId) :
    (left.find? v).map Prod.fst = (right.find? v).map Prod.fst := by
  induction H generalizing v with
  | nil => rfl
  | @cons left right ofv x y _ ih =>
    simp only [VLCtx.find?]
    cases VLCtx.next ofv v with
    | none => simp [VLocalDecl.value]
    | some v' =>
      have := ih v'
      cases hl : left.find? v' <;> cases hr : right.find? v' <;>
        simp_all [VLocalDecl.depth]

theorem VLCtx.AllVLam.cons {Δ : VLCtx} (H : VLCtx.AllVLam Δ)
    (ofv : Option (FVarId × List FVarId)) (x : VExpr) :
    VLCtx.AllVLam ((ofv, .vlam x) :: Δ) := by
  intro entry hmem
  rcases List.mem_cons.mp hmem with rfl | hmem
  · exact ⟨_, rfl⟩
  · exact H entry hmem

theorem VLCtx.AllVLam.find?_bvar {Δ : VLCtx} {v : Nat ⊕ FVarId} {e A : VExpr}
    (H : VLCtx.AllVLam Δ) (h : Δ.find? v = some (e, A)) :
    ∃ i, e = .bvar i := by
  induction Δ generalizing v e A with
  | nil => cases h
  | cons entry Δ ih =>
    rcases entry with ⟨ofv, d⟩
    rcases H (ofv, d) List.mem_cons_self with ⟨x, hx⟩
    simp only at hx
    subst hx
    simp only [VLCtx.find?] at h
    cases hn : VLCtx.next ofv v with
    | none =>
      simp [hn, VLocalDecl.value] at h
      exact ⟨0, h.1.symm⟩
    | some v' =>
      simp [hn] at h
      rcases h with ⟨a, b, hf, rfl, rfl⟩
      rcases ih (fun e he => H e (by simp [he])) hf with ⟨i, rfl⟩
      exact ⟨_, rfl⟩

/-- The syntactic fragment of generated recursor types and rule right-hand
sides: no `let`, literals, projections, metadata, or metavariables. -/
inductive RestoreFragment : Expr → Prop
  | bvar (i : Nat) : RestoreFragment (.bvar i)
  | fvar (fv : FVarId) : RestoreFragment (.fvar fv)
  | sort (u : Level) : RestoreFragment (.sort u)
  | const (c : Name) (ls : List Level) : RestoreFragment (.const c ls)
  | app : RestoreFragment fn → RestoreFragment arg → RestoreFragment (.app fn arg)
  | lam : RestoreFragment dom → RestoreFragment body →
      RestoreFragment (.lam name dom body bi)
  | forallE : RestoreFragment dom → RestoreFragment body →
      RestoreFragment (.forallE name dom body bi)

/-- In the fragment, translation is syntactic: it depends on neither the
environment nor the binder types, only on the variable naming. -/
theorem RestoreFragment.translation_eq (Hf : RestoreFragment e)
    (Hshape : VLCtx.VLamShape Δ₁ Δ₂)
    (H₁ : TrExprS env₁ Us Δ₁ e v₁) (H₂ : TrExprS env₂ Us Δ₂ e v₂) : v₁ = v₂ := by
  induction Hf generalizing Δ₁ Δ₂ v₁ v₂ with
  | bvar i =>
    cases H₁ with | bvar h₁ => cases H₂ with | bvar h₂ =>
    have := Hshape.find? (.inl i)
    rw [h₁, h₂] at this
    simpa using this
  | fvar fv =>
    cases H₁ with | fvar h₁ => cases H₂ with | fvar h₂ =>
    have := Hshape.find? (.inr fv)
    rw [h₁, h₂] at this
    simpa using this
  | sort u =>
    cases H₁ with | sort h₁ => cases H₂ with | sort h₂ =>
    cases h₁.symm.trans h₂; rfl
  | const c ls =>
    cases H₁ with | const _ h₁ _ => cases H₂ with | const _ h₂ _ =>
    cases h₁.symm.trans h₂; rfl
  | app _ _ ihf iha =>
    cases H₁ with | app _ _ hf₁ ha₁ => cases H₂ with | app _ _ hf₂ ha₂ =>
    rw [ihf Hshape hf₁ hf₂, iha Hshape ha₁ ha₂]
  | lam _ _ ihd ihb =>
    cases H₁ with | lam _ hd₁ hb₁ => cases H₂ with | lam _ hd₂ hb₂ =>
    cases ihd Hshape hd₁ hd₂
    rw [ihb (.cons Hshape) hb₁ hb₂]
  | forallE _ _ ihd ihb =>
    cases H₁ with | forallE _ _ hd₁ hb₁ => cases H₂ with | forallE _ _ hd₂ hb₂ =>
    cases ihd Hshape hd₁ hd₂
    rw [ihb (.cons Hshape) hb₁ hb₂]

theorem RestoreFragment.translations_eq {es : List Expr}
    (Hf : ∀ e ∈ es, RestoreFragment e) (Hshape : VLCtx.VLamShape Δ₁ Δ₂)
    (H₁ : List.Forall₂ (TrExprS env₁ Us Δ₁) es vs₁)
    (H₂ : List.Forall₂ (TrExprS env₂ Us Δ₂) es vs₂) : vs₁ = vs₂ := by
  induction H₁ generalizing vs₂ with
  | nil => cases H₂; rfl
  | cons h₁ _ ih =>
    cases H₂ with
    | cons h₂ t₂ =>
      rw [(Hf _ (by simp)).translation_eq Hshape h₁ h₂,
        ih (fun e he => Hf e (by simp [he])) t₂]

/-- Constant support of a fragment translation is the source constant support. -/
theorem RestoreFragment.translation_containsAnyConst (Hf : RestoreFragment e)
    (hΔ : VLCtx.AllVLam Δ) (Havoid : e.AvoidsConsts names)
    (H : TrExprS env Us Δ e v) : v.containsAnyConst names = false := by
  induction Hf generalizing Δ v with
  | bvar i =>
    cases H with | bvar h =>
    rcases hΔ.find?_bvar h with ⟨j, rfl⟩; rfl
  | fvar fv =>
    cases H with | fvar h =>
    rcases hΔ.find?_bvar h with ⟨j, rfl⟩; rfl
  | sort u => cases H; rfl
  | const c ls =>
    cases H with | const =>
    cases Havoid with | const _ _ hfresh =>
    simpa [VExpr.containsAnyConst] using hfresh
  | app _ _ ihf iha =>
    cases H with | app _ _ hf ha =>
    cases Havoid with | app _ _ Hf' Ha' =>
    simp [VExpr.containsAnyConst, ihf hΔ Hf' hf, iha hΔ Ha' ha]
  | lam _ _ ihd ihb =>
    cases H with | lam _ hd hb =>
    cases Havoid with | lam _ _ _ _ Hd Hb =>
    simp [VExpr.containsAnyConst, ihd hΔ Hd hd, ihb (hΔ.cons _ _) Hb hb]
  | forallE _ _ ihd ihb =>
    cases H with | forallE _ _ hd hb =>
    cases Havoid with | forallE _ _ _ _ Hd Hb =>
    simp [VExpr.containsAnyConst, ihd hΔ Hd hd, ihb (hΔ.cons _ _) Hb hb]


theorem restoreNestedNode_eq_none_of_restoreHead
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (As : Array Expr) (auxRec : NameMap Name) (t : Expr)
    (hnotrec : ∀ c ls, t = .const c ls → auxRec.find? c = none)
    (hhead : ∀ c ls, t.getAppFn = .const c ls → restoreHead result env As c = none) :
    result.restoreNestedNode env As auxRec t = none := by
  rw [restoreNestedNode_eq_of_notRecursor result env As auxRec t hnotrec]
  cases hfn : t.getAppFn with
  | const c ls => simp [hhead c ls hfn]
  | _ => rfl

theorem restoreNestedNode_eq_of_restoreHead
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (As : Array Expr) (auxRec : NameMap Name) (t : Expr)
    (hnotrec : ∀ c ls, t = .const c ls → auxRec.find? c = none)
    (hfn : t.getAppFn = .const c ls) (hhead : restoreHead result env As c = some H)
    (hsize : result.nparams ≤ t.getAppArgsList.length) :
    result.restoreNestedNode env As auxRec t =
      some (Expr.mkAppList H (t.getAppArgsList.drop result.nparams)) := by
  rw [restoreNestedNode_eq_of_notRecursor result env As auxRec t hnotrec, hfn]
  have hsize' : result.nparams ≤ t.getAppArgs.size := by
    rw [← Array.length_toList, Expr.getAppArgs_toList]; exact hsize
  simp only [hhead, Option.bind_some, if_pos hsize']
  congr 1
  apply Expr.mkAppRange_eq (l₁ := t.getAppArgsList.take result.nparams) (l₃ := [])
  · simp [Expr.getAppArgs_toList]
  · simp; omega
  · simp [← Array.length_toList, Expr.getAppArgs_toList]

private theorem forall₂_take {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (n : Nat), List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.take n) (l₂.take n)
  | _, _, 0, _ => by simp
  | _, _, _ + 1, .nil => by simp
  | _, _, n + 1, .cons h t => by simpa using List.Forall₂.cons h (forall₂_take n t)

private theorem forall₂_drop {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} (n : Nat), List.Forall₂ R l₁ l₂ →
      List.Forall₂ R (l₁.drop n) (l₂.drop n)
  | _, _, 0, h => by simpa using h
  | _, _, _ + 1, .nil => by simp
  | _, _, n + 1, .cons _ t => by simpa using forall₂_drop n t

private theorem forall₂_length {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → l₁.length = l₂.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [forall₂_length t]

private theorem forall₂_self {R : α → α → Prop} :
    ∀ {l : List α}, (∀ x ∈ l, R x x) → List.Forall₂ R l l
  | [], _ => .nil
  | x :: l, h => .cons (h x (by simp)) (forall₂_self fun y hy => h y (by simp [hy]))

private theorem forall₂_mem_right {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ y ∈ l₂, ∃ x ∈ l₁, R x y
  | _, _, .nil, _, hy => by cases hy
  | _, _, .cons h t, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, by simp, h⟩
    · rcases forall₂_mem_right t y hy with ⟨x, hx, hr⟩
      exact ⟨x, by simp [hx], hr⟩

/-- A successful callback at the root fixes the output of `Expr.replace`. -/
theorem ExprReplacement.output_of_hit
    (H : ExprReplacement replaceNode input output)
    (h : replaceNode input = some out) : output = out := by
  rw [H.eq_replace]
  simp [Expr.replace_eq, Lean.Expr.replaceNoCache.eq_def, h]

/-- A free variable translates to the same expression in any context of the
same variable shape. -/
theorem VLCtx.VLamShape.transfer_fvar {Δs Δt : VLCtx}
    (Hshape : VLCtx.VLamShape Δs Δt)
    (h : TrExprS envS Us Δs (.fvar fv) p) : TrExprS envT Us Δt (.fvar fv) p := by
  cases h with
  | fvar hf =>
    have := Hshape.find? (.inr fv)
    rw [hf] at this
    cases hg : Δt.find? (.inr fv) with
    | none => simp [hg] at this
    | some pair =>
      rcases pair with ⟨p', A'⟩
      simp [hg] at this
      subst this
      exact .fvar hg

theorem VLCtx.VLamShape.transfer_fvars {Δs Δt : VLCtx}
    (Hshape : VLCtx.VLamShape Δs Δt) :
    ∀ {l : List Expr} {l' : List VExpr}, (∀ a ∈ l, ∃ fv, a = .fvar fv) →
      List.Forall₂ (TrExprS envS Us Δs) l l' →
      List.Forall₂ (TrExprS envT Us Δt) l l'
  | _, _, _, .nil => .nil
  | _, _, hl, .cons h t => by
    rcases hl _ List.mem_cons_self with ⟨fv, rfl⟩
    exact .cons (Hshape.transfer_fvar h)
      (Hshape.transfer_fvars (fun a ha => hl a (by simp [ha])) t)

/-- Correspondence between the executable restoration tables and an abstract
restoration `r` (intended: `compilationRestoration source auxiliaries`).

* `recursorName`: `auxRec` (from `mkAuxRecNameMap`) is `r.recursorName`.
* `recursorNotHead`: renamed recursors are not specialization heads.
* `headNone`/`head`: a name has an executable replacement head
  (`restoreHead`: an `aux2nested` family, or a constructor of one) exactly
  when it is an abstract head. For a head, the specialization has the
  executable's parameter count, the auxiliary constant's universe arity, and
  the executable replacement head translates to the specialization applied
  to the translated parameters, at the levels `auxLevels` (on the lowered
  side, `lparams.map .param`). -/
structure RestorationMapAgreement (r : Restoration)
    (result : Lean4Lean.ElimNestedInductive.Result) (env : Environment)
    (auxRec : NameMap Name) (targetEnv : VEnv) (Us : List Name)
    (auxLevels : List Level) : Prop where
  recursorName : ∀ c, r.recursorName c = (auxRec.find? c).getD c
  recursorNotHead : ∀ c new, auxRec.find? c = some new →
    c ∉ r.heads.map (·.auxiliary)
  headNone : ∀ As c, restoreHead result env As c = none →
    c ∉ r.heads.map (·.auxiliary)
  head : ∀ As c H, restoreHead result env As c = some H →
    ∃ h : HeadSpecialization, r.heads.find? (fun h => h.auxiliary == c) = some h ∧
      h.nparams = result.nparams ∧
      ∀ levels, auxLevels.mapM (VLevel.ofLevel Us) = some levels →
        h.uvars = levels.length ∧
        ∀ (Δ : VLCtx) (params : List VExpr) (v : VExpr),
          VLCtx.AllVLam Δ →
          List.Forall₂ (TrExprS targetEnv Us Δ) As.toList params →
          TrExprS targetEnv Us Δ H v →
          v = VExpr.mkApps (.const h.target (h.levels.map (·.inst levels)))
            (h.arguments.map fun arg => instantiateParams (arg.instL levels) params)
  /-- The executable constructor renaming (`restoreCtorName`, a prefix
  replacement by the container family's name) is the abstract head target. -/
  ctorTarget : ∀ c nested auxI, result.aux2nested.find? c = none →
    result.getNestedIfAuxCtor env c = some (nested, auxI) →
    ∃ I ls, nested.getAppFn = .const I ls ∧
      r.restoredHeadName c = c.replacePrefix auxI I

/-- The syntactic side condition under which the executable `Expr.replace`
traversal agrees with `Restoration.expr`. It mirrors the traversal: a node
whose head has an executable replacement is a hit, and must be applied to the
opened parameters `As` followed by restorable-name-free fragment arguments,
at the agreed levels; every other node has no replaceable head and is
traversed structurally. -/
inductive RestoreReady (result : Lean4Lean.ElimNestedInductive.Result)
    (env : Environment) (As : Array Expr) (names : List Name)
    (auxLevels : List Level) : Expr → Prop
  | hit {t : Expr} {c : Name}
      (hfn : t.getAppFn = .const c auxLevels)
      (hhead : restoreHead result env As c ≠ none)
      (hsize : result.nparams ≤ t.getAppArgsList.length)
      (hparams : t.getAppArgsList.take result.nparams = As.toList)
      (hargs : ∀ a ∈ t.getAppArgsList, RestoreFragment a ∧ a.AvoidsConsts names) :
      RestoreReady result env As names auxLevels t
  | bvar (i : Nat) : RestoreReady result env As names auxLevels (.bvar i)
  | fvar (fv : FVarId) : RestoreReady result env As names auxLevels (.fvar fv)
  | sort (u : Level) : RestoreReady result env As names auxLevels (.sort u)
  | const (c : Name) (ls : List Level) (h : restoreHead result env As c = none) :
      RestoreReady result env As names auxLevels (.const c ls)
  | app {fn arg : Expr}
      (h : ∀ c ls, (Expr.app fn arg).getAppFn = .const c ls →
        restoreHead result env As c = none) :
      RestoreReady result env As names auxLevels fn →
      RestoreReady result env As names auxLevels arg →
      RestoreReady result env As names auxLevels (.app fn arg)
  | lam {name : Name} {dom body : Expr} {bi : BinderInfo} :
      RestoreReady result env As names auxLevels dom →
      RestoreReady result env As names auxLevels body →
      RestoreReady result env As names auxLevels (.lam name dom body bi)
  | forallE {name : Name} {dom body : Expr} {bi : BinderInfo} :
      RestoreReady result env As names auxLevels dom →
      RestoreReady result env As names auxLevels body →
      RestoreReady result env As names auxLevels (.forallE name dom body bi)

theorem RestoreReady.fragment
    (H : RestoreReady result env As names auxLevels e) : RestoreFragment e := by
  induction H with
  | @hit t c hfn _ _ _ hargs =>
    rw [← Expr.mkAppList_getAppArgsList t, hfn]
    generalize t.getAppArgsList = args at hargs
    suffices ∀ f, RestoreFragment f → RestoreFragment (Expr.mkAppList f args) from
      this _ (.const _ _)
    induction args with
    | nil => intro f hf; exact hf
    | cons a args ih =>
      intro f hf
      exact ih (fun x hx => hargs x (by simp [hx])) _ (.app hf (hargs a (by simp)).1)
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | app _ _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihd ihb => exact .lam ihd ihb
  | forallE _ _ ihd ihb => exact .forallE ihd ihb

theorem RestorationMapAgreement.notRecursor_of_head
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hhead : restoreHead result env As c ≠ none) : auxRec.find? c = none := by
  cases hfind : auxRec.find? c with
  | none => rfl
  | some new =>
    exfalso
    apply A.recursorNotHead c new hfind
    rcases Option.ne_none_iff_exists.mp hhead with ⟨H, hH⟩
    rcases A.head As c H hH.symm with ⟨h, hh, _⟩
    exact List.mem_map.mpr ⟨h, List.mem_of_find?_eq_some hh,
      by simpa using List.find?_some hh⟩

/-- Restoration of a constant that is not an executable replacement head is
the executable recursor renaming. -/
theorem RestorationMapAgreement.go_const
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hhead : restoreHead result env As c = none) (levels : List VLevel)
    (args : List VExpr) :
    Restoration.expr.go r (.const c levels) args =
      some (VExpr.mkApps (.const ((auxRec.find? c).getD c) levels) args) := by
  simp [Restoration.expr.go,
    Restoration.heads_find?_eq_none (A.headNone As c hhead), A.recursorName]

/-- **Commutation of executable restoration with `Restoration.expr`** on an
opened body. `input` is traversed by `Expr.replace` with `restoreNestedNode`
over the opened parameters `As`; its translation `s` (in the lowered
environment) and the translation `t` of the executable output (in the
restored environment) are related by `Restoration.expr.go r s [] = some t`.
The second component is the spine-extended form used for applications. -/
theorem ExprReplacement.restorationCommutes
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {As : Array Expr}
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (HAs : ∀ a ∈ As.toList, ∃ fv, a = .fvar fv)
    {input output : Expr} {Δs Δt : VLCtx} {s t : VExpr}
    (Hready : RestoreReady result env As r.restorableNames auxLevels input)
    (Hrep : ExprReplacement (result.restoreNestedNode env As auxRec) input output)
    (Hshape : VLCtx.VLamShape Δs Δt)
    (Hs : TrExprS sourceEnv Us Δs input s) (Ht : TrExprS targetEnv Us Δt output t) :
    Restoration.expr.go r s [] = some t ∧
    ((∀ c ls, input.getAppFn = .const c ls → restoreHead result env As c = none) →
      ∀ args, Restoration.expr.go r s args = some (VExpr.mkApps t args)) := by
  induction Hready generalizing output s t Δs Δt with
  | @hit input c hfn hhead hsize hparams hargs =>
    refine ⟨?_, fun hnone => absurd (hnone c auxLevels hfn) hhead⟩
    rcases Option.ne_none_iff_exists.mp hhead with ⟨H, hH⟩
    have hH := hH.symm
    have hnotrec := A.notRecursor_of_head hhead
    rcases A.head As c H hH with ⟨h, hfind, hnparams, hlevels⟩
    have hnode := restoreNestedNode_eq_of_restoreHead result env As auxRec input
      (fun c' ls' heq => by
        subst heq
        cases hfn
        exact hnotrec) hfn hH hsize
    have houtput := Hrep.output_of_hit hnode
    subst houtput
    generalize hL : input.getAppArgsList = L at hsize hparams hargs Ht
    have hinput : input = Expr.mkAppList (.const c auxLevels) L := by
      rw [← hL, ← hfn, Expr.mkAppList_getAppArgsList]
    subst hinput
    rcases checkPositivityStep.TrExprS.mkAppList_inv Hs with
      ⟨fn', L', hfn', hL', rfl⟩
    cases hfn' with
    | const hc hlsV hlen =>
    rcases checkPositivityStep.TrExprS.mkAppList_inv Ht with
      ⟨Hv, R', hHv, hR', rfl⟩
    rcases hlevels _ hlsV with ⟨huvars, hsem⟩
    -- the opened parameters translate identically on both sides
    have hP : List.Forall₂ (TrExprS targetEnv Us Δt) As.toList
        (L'.take result.nparams) := by
      have htake := forall₂_take result.nparams hL'
      rw [hparams] at htake
      exact Hshape.transfer_fvars HAs htake
    have hHvEq := hsem Δt _ Hv Hshape.right hP hHv
    have hR'Eq : R' = L'.drop result.nparams :=
      (RestoreFragment.translations_eq
        (fun a ha => (hargs a (List.mem_of_mem_drop ha)).1) Hshape
        (forall₂_drop result.nparams hL') hR').symm
    subst hHvEq hR'Eq
    have hfree : List.Forall₂ (fun x y => Restoration.expr.go r x [] = some y) L' L' := by
      apply forall₂_self
      intro x hx
      rcases forall₂_mem_right hL' x hx with ⟨a, ha, hax⟩
      have hc := (hargs a ha).1.translation_containsAnyConst Hshape.left
        (hargs a ha).2 hax
      simpa [VExpr.mkApps] using Restoration.expr.go_of_not_contains r hc []
    rw [Restoration.expr.go_mkApps r hfree, List.append_nil]
    have hlength : L.length = L'.length := forall₂_length hL'
    have hle : result.nparams ≤ L'.length := by omega
    simp [Restoration.expr.go, hfind, HeadSpecialization.apply, huvars, hle,
      hnparams, Lean4Lean.VExpr.mkApps_append]
  | bvar i =>
    have hnn : result.restoreNestedNode env As auxRec (.bvar i) = none :=
      restoreNestedNode_eq_none_of_restoreHead result env As auxRec _
        (by intro _ _ h; cases h) (by intro _ _ h; simp [Expr.getAppFn] at h)
    cases Hrep with
    | hit hhit => rw [hnn] at hhit; cases hhit
    | bvar _ =>
      have heq := (RestoreFragment.bvar i).translation_eq Hshape Hs Ht
      subst heq
      have hc := (RestoreFragment.bvar i).translation_containsAnyConst (names := r.restorableNames) Hshape.left
        (.bvar i) Hs
      exact ⟨by simpa [VExpr.mkApps] using Restoration.expr.go_of_not_contains r hc [],
        fun _ args => Restoration.expr.go_of_not_contains r hc args⟩
  | fvar fv =>
    have hnn : result.restoreNestedNode env As auxRec (.fvar fv) = none :=
      restoreNestedNode_eq_none_of_restoreHead result env As auxRec _
        (by intro _ _ h; cases h) (by intro _ _ h; simp [Expr.getAppFn] at h)
    cases Hrep with
    | hit hhit => rw [hnn] at hhit; cases hhit
    | fvar _ =>
      have heq := (RestoreFragment.fvar fv).translation_eq Hshape Hs Ht
      subst heq
      have hc := (RestoreFragment.fvar fv).translation_containsAnyConst (names := r.restorableNames) Hshape.left
        (.fvar fv) Hs
      exact ⟨by simpa [VExpr.mkApps] using Restoration.expr.go_of_not_contains r hc [],
        fun _ args => Restoration.expr.go_of_not_contains r hc args⟩
  | sort u =>
    have hnn : result.restoreNestedNode env As auxRec (.sort u) = none :=
      restoreNestedNode_eq_none_of_restoreHead result env As auxRec _
        (by intro _ _ h; cases h) (by intro _ _ h; simp [Expr.getAppFn] at h)
    cases Hrep with
    | hit hhit => rw [hnn] at hhit; cases hhit
    | sort _ =>
      have heq := (RestoreFragment.sort u).translation_eq Hshape Hs Ht
      subst heq
      have hc := (RestoreFragment.sort u).translation_containsAnyConst (names := r.restorableNames) Hshape.left
        (.sort u) Hs
      exact ⟨by simpa [VExpr.mkApps] using Restoration.expr.go_of_not_contains r hc [],
        fun _ args => Restoration.expr.go_of_not_contains r hc args⟩
  | const c ls hnone =>
    cases Hs with
    | const hc hls hlen =>
    by_cases hrec : ∃ new, auxRec.find? c = some new
    · rcases hrec with ⟨new, hnew⟩
      have hout := Hrep.output_of_hit
        (restoreNestedNode_recursor result env As auxRec c new ls hnew)
      subst hout
      cases Ht with
      | const _ hls' _ =>
      cases hls.symm.trans hls'
      refine ⟨?_, fun _ args => ?_⟩ <;> rw [A.go_const (As := As) hnone] <;>
        simp [hnew, VExpr.mkApps]
    · have hnone' : auxRec.find? c = none := by
        cases h : auxRec.find? c with
        | none => rfl
        | some new => exact absurd ⟨new, h⟩ hrec
      have hnn : result.restoreNestedNode env As auxRec (.const c ls) = none :=
        restoreNestedNode_eq_none_of_restoreHead result env As auxRec _
          (fun c' ls' heq => by cases heq; exact hnone')
          (fun c' ls' h => by
            simp [Expr.getAppFn] at h
            rcases h with ⟨rfl, rfl⟩
            exact hnone)
      cases Hrep with
      | hit hhit => rw [hnn] at hhit; cases hhit
      | const _ =>
        cases Ht with
        | const _ hls' _ =>
        cases hls.symm.trans hls'
        refine ⟨?_, fun _ args => ?_⟩ <;> rw [A.go_const (As := As) hnone] <;>
          simp [hnone', VExpr.mkApps]
  | @app fn arg hN _ _ ihf iha =>
    have hnn : result.restoreNestedNode env As auxRec (.app fn arg) = none :=
      restoreNestedNode_eq_none_of_restoreHead result env As auxRec _
        (by intro _ _ h; cases h) hN
    cases Hrep with
    | hit hhit => rw [hnn] at hhit; cases hhit
    | app _ hf ha =>
      simp only [Expr.updateApp!] at Ht
      cases Hs with
      | app _ _ hsf hsa =>
      cases Ht with
      | app _ _ htf hta =>
      have hNf : ∀ c ls, fn.getAppFn = .const c ls → restoreHead result env As c = none :=
        fun c ls h => hN c ls (by simpa [Expr.getAppFn] using h)
      have h1 := (iha ha Hshape hsa hta).1
      have h2 := (ihf hf Hshape hsf htf).2 hNf
      refine ⟨?_, fun _ args => ?_⟩ <;>
        simp only [Restoration.expr.go, h1, h2] <;> rfl
  | @lam name dom body bi _ _ ihd ihb =>
    have hnn : result.restoreNestedNode env As auxRec (.lam name dom body bi) = none :=
      restoreNestedNode_eq_none_of_restoreHead result env As auxRec _
        (by intro _ _ h; cases h) (by intro _ _ h; simp [Expr.getAppFn] at h)
    cases Hrep with
    | hit hhit => rw [hnn] at hhit; cases hhit
    | lam _ hd hb =>
      simp only [Expr.updateLambdaE!] at Ht
      cases Hs with
      | lam _ hsd hsb =>
      cases Ht with
      | lam _ htd htb =>
      have h1 := (ihd hd Hshape hsd htd).1
      have h2 := (ihb hb (.cons Hshape) hsb htb).1
      refine ⟨?_, fun _ args => ?_⟩ <;> simp [Restoration.expr.go, h1, h2, VExpr.mkApps]
  | @forallE name dom body bi _ _ ihd ihb =>
    have hnn : result.restoreNestedNode env As auxRec (.forallE name dom body bi) = none :=
      restoreNestedNode_eq_none_of_restoreHead result env As auxRec _
        (by intro _ _ h; cases h) (by intro _ _ h; simp [Expr.getAppFn] at h)
    cases Hrep with
    | hit hhit => rw [hnn] at hhit; cases hhit
    | forallE _ hd hb =>
      simp only [Expr.updateForallE!] at Ht
      cases Hs with
      | forallE _ _ hsd hsb =>
      cases Ht with
      | forallE _ _ htd htb =>
      have h1 := (ihd hd Hshape hsd htd).1
      have h2 := (ihb hb (.cons Hshape) hsb htb).1
      refine ⟨?_, fun _ args => ?_⟩ <;> simp [Restoration.expr.go, h1, h2, VExpr.mkApps]

/-! ### Opening closed translations -/

/-- Converse of `TrExprS.abstract`: instantiating an abstracted binder with
the free variable it stands for preserves the translation. -/
theorem TrExprS.instantiateFVar {env : VEnv} {Us : List Name}
    {Δ₀ : VLCtx} {v₀ : FVarId} {d₀ : VLocalDecl} {dk k : Nat} {Δ₁ Δ : VLCtx}
    {e : Expr} {e' : VExpr}
    (W : VLCtx.Abstract Δ₀ v₀ d₀ dk k Δ₁ Δ)
    (H : TrExprS env Us Δ e e') (hfresh : e.FVarIdsIn (· ≠ v₀)) :
    TrExprS env Us Δ₁ (e.instantiate1' (.fvar v₀) dk) e' := by
  induction H generalizing dk k Δ₁ with
  | bvar h1 =>
    rename_i x A Δ' i
    have hfind := W.find? (v := .inl i) (by nofun)
    simp only [Expr.instantiate1']
    by_cases hlt : i < dk
    · simp only [hlt, if_true] at hfind ⊢
      exact .bvar (hfind ▸ h1)
    · by_cases heq : i = dk
      · subst heq
        simp only [Nat.lt_irrefl, if_true, if_false] at hfind ⊢
        rw [hfind] at h1
        simpa [Expr.liftLooseBVars'] using (TrExprS.fvar h1 : TrExprS env Us Δ₁ (.fvar v₀) x)
      · simp only [hlt, heq, if_false] at hfind ⊢
        exact .bvar (hfind ▸ h1)
  | @fvar Δ x A fv h1 =>
    have hne : fv ≠ v₀ := hfresh
    have hfind := W.find? (v := .inr fv) (by simpa using hne)
    exact .fvar (hfind ▸ h1)
  | sort h1 => exact .sort h1
  | const h1 h2 h3 => exact .const h1 h2 h3
  | app h1 h2 _ _ ih1 ih2 =>
    exact .app (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W hfresh.1) (ih2 W hfresh.2)
  | lam h1 _ _ ih1 ih2 =>
    exact .lam (W.toCtx ▸ h1) (ih1 W hfresh.1) (ih2 W.succ hfresh.2)
  | forallE h1 h2 _ _ ih1 ih2 =>
    exact .forallE (W.toCtx ▸ h1) (W.toCtx ▸ h2) (ih1 W hfresh.1) (ih2 W.succ hfresh.2)
  | letE h1 _ _ _ ih1 ih2 ih3 =>
    exact .letE (W.toCtx ▸ h1) (ih1 W hfresh.1) (ih2 W hfresh.2.1) (ih3 W.succ hfresh.2.2)
  | lit h1 h2 ih =>
    refine .lit h1 ?_
    have := ih W (FVarsIn_to_FVarIdsIn FVarsIn.toConstructor)
    rwa [Expr.instantiate1'_eq_self Closed.toConstructor.looseBVarRange_le] at this
  | mdata _ ih => exact .mdata (ih W hfresh)
  | proj _ h2 ih => exact .proj (ih W hfresh) (W.toCtx ▸ h2)


/-- The fvar-form context of an opened parameter telescope: the innermost
parameter first, every entry an ordinary binder with no dependencies. -/
def fvarScope : List FVarId → List VExpr → VLCtx
  | f :: fs, d :: ds => fvarScope fs ds ++ [(some (f, []), .vlam d)]
  | _, _ => []

theorem fvarScope_vlamShape :
    ∀ (fvars : List FVarId) (left right : List VExpr),
      left.length = right.length →
      VLCtx.VLamShape (fvarScope fvars left) (fvarScope fvars right)
  | [], _, _, _ => by simp [fvarScope]; exact .nil
  | _ :: _, [], [], _ => by simp [fvarScope]; exact .nil
  | _ :: _, [], _ :: _, h => by simp at h
  | _ :: _, _ :: _, [], h => by simp at h
  | f :: fs, l :: ls, r :: rs, h => by
    simp only [fvarScope]
    exact VLCtx.VLamShape.append (fvarScope_vlamShape fs ls rs (by simpa using h))
      (.cons .nil)

private theorem abstract_prefix (Δb : VLCtx) (f : FVarId) (d : VLocalDecl) :
    ∀ pre : List VExpr,
      VLCtx.Abstract Δb f d pre.length pre.length
        (pre.map (fun t => ((none : Option (FVarId × List FVarId)), VLocalDecl.vlam t)) ++
          (some (f, []), d) :: Δb)
        (pre.map (fun t => ((none : Option (FVarId × List FVarId)), VLocalDecl.vlam t)) ++
          (none, d) :: Δb)
  | [] => .zero
  | t :: pre => by
    simpa [VLocalDecl.depth] using (abstract_prefix Δb f d pre).succ (d := .vlam t)

/-- Opening a de Bruijn parameter telescope with fresh free variables
preserves the translation of its body. -/
theorem TrExprS.instantiateRevFVars {env : VEnv} {Us : List Name} :
    ∀ (fvars : List FVarId) (domains : List VExpr) (Δb : VLCtx) (X : Expr) (v : VExpr),
      fvars.length = domains.length → fvars.Nodup → X.FVarIdsIn (· ∉ fvars) →
      TrExprS env Us (abstractForallContext domains Δb) X v →
      TrExprS env Us (fvarScope fvars domains ++ Δb)
        (X.instantiateRevList (fvars.map .fvar)) v
  | [], domains, Δb, X, v, hlen, _, _, H => by
    have : domains = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst this
    simpa [fvarScope, abstractForallContext] using H
  | f :: fs, [], _, _, _, hlen, _, _, _ => by simp at hlen
  | f :: fs, d :: ds, Δb, X, v, hlen, hnodup, hfresh, H => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.nodup_cons] at hnodup
    have W := abstract_prefix Δb f (.vlam d) ds.reverse
    have Hctx : abstractForallContext (d :: ds) Δb =
        ds.reverse.map (fun t => ((none : Option (FVarId × List FVarId)),
          VLocalDecl.vlam t)) ++ (none, .vlam d) :: Δb := by
      simp [abstractForallContext]
    rw [Hctx] at H
    have H1 := TrExprS.instantiateFVar W H
      (hfresh.mono fun fv hfv heq => hfv (heq ▸ List.mem_cons_self))
    have Hctx' : ds.reverse.map (fun t => ((none : Option (FVarId × List FVarId)),
          VLocalDecl.vlam t)) ++ (some (f, []), .vlam d) :: Δb =
        abstractForallContext ds ((some (f, []), .vlam d) :: Δb) := by
      simp [abstractForallContext]
    rw [Hctx'] at H1
    have hfresh1 : (X.instantiate1' (.fvar f) ds.reverse.length).FVarIdsIn (· ∉ fs) :=
      (hfresh.mono fun fv hfv hmem => hfv (List.mem_cons_of_mem _ hmem)).instantiate1_go
        (show (Expr.fvar f).FVarIdsIn (· ∉ fs) from hnodup.1)
    have IH := TrExprS.instantiateRevFVars fs ds _ _ v hlen hnodup.2 hfresh1 H1
    have hcomm := Expr.instantiateRevList_instantiate1'_fvars X f fs 0 0
    simp only [Nat.zero_add, Nat.add_zero] at hcomm
    rw [List.length_reverse, ← hlen, hcomm] at IH
    simpa [fvarScope, List.append_assoc] using IH

/-- The leading `n` forall domains lie in the restoration fragment and are
free of restorable names. -/
inductive ForallDomainsReady (names : List Name) : Nat → Expr → Prop
  | zero (e : Expr) : ForallDomainsReady names 0 e
  | succ {name : Name} {dom body : Expr} {bi : BinderInfo} {n : Nat} :
      RestoreFragment dom → dom.AvoidsConsts names →
      ForallDomainsReady names n body →
      ForallDomainsReady names (n + 1) (.forallE name dom body bi)

/-- Two expressions with the same concrete forall prefix have the same
translated prefix domains, which are free of restorable names. -/
theorem Expr.SameForallPrefix.translatedDomains_eq {names : List Name}
    {env₁ env₂ : VEnv} {Us : List Name}
    (Hsame : Expr.SameForallPrefix n left right)
    (Hready : ForallDomainsReady names n left) :
    ∀ {Δ₁ Δ₂ : VLCtx} {D₁ D₂ : List VExpr} {X₁ X₂ : VExpr},
      VLCtx.VLamShape Δ₁ Δ₂ →
      TrExprS env₁ Us Δ₁ left (VExpr.wrapForalls D₁ X₁) →
      TrExprS env₂ Us Δ₂ right (VExpr.wrapForalls D₂ X₂) →
      D₁.length = n → D₂.length = n →
      D₁ = D₂ ∧ ∀ d ∈ D₁, d.containsAnyConst names = false := by
  induction Hsame with
  | nil =>
    intro Δ₁ Δ₂ D₁ D₂ X₁ X₂ _ _ _ h₁ h₂
    rw [List.eq_nil_of_length_eq_zero h₁, List.eq_nil_of_length_eq_zero h₂]
    simp
  | cons Hsame ih =>
    intro Δ₁ Δ₂ D₁ D₂ X₁ X₂ Hshape H₁ H₂ h₁ h₂
    cases Hready with
    | succ hf ha hrest =>
    cases D₁ with
    | nil => simp at h₁
    | cons d₁ D₁ =>
    cases D₂ with
    | nil => simp at h₂
    | cons d₂ D₂ =>
    simp only [VExpr.wrapForalls, List.foldr_cons] at H₁ H₂
    cases H₁ with
    | forallE _ _ hd₁ hb₁ =>
    cases H₂ with
    | forallE _ _ hd₂ hb₂ =>
    have hd := hf.translation_eq Hshape hd₁ hd₂
    subst hd
    have hfree := hf.translation_containsAnyConst Hshape.left ha hd₁
    rcases ih hrest (.cons Hshape) hb₁ hb₂ (by simpa using h₁) (by simpa using h₂) with
      ⟨hD, hfrees⟩
    subst hD
    refine ⟨rfl, ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hfree
    · exact hfrees d hd

private theorem fvarIdsIn_of_trExprS_abstractForallContext
    (H : TrExprS env Us (abstractForallContext domains []) e e') (P : FVarId → Prop) :
    e.FVarIdsIn P := by
  apply FVarsIn_to_FVarIdsIn
  apply H.fvarsIn.mono
  intro fv hfv
  simp [abstractForallContext, VLCtx.fvars] at hfv

/-- **Closed-term commutation for forall telescopes** (generated recursor
and constructor types). For a closed lowered type `input` whose first
`result.nparams` binders are the common parameters, the executable
restoration `output` (see `restoreNested_refines` and
`NestedRestoration.opening`) satisfies: the abstract restoration of the
lowered translation is the restored translation. -/
theorem NestedRestorationOpening.restorationCommutes
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {input output suffix : Expr}
    {s t : VExpr}
    (Hopen : NestedRestorationOpening result env auxRec input output)
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (Hready : RestoreReady result env Hopen.params r.restorableNames auxLevels
      Hopen.body)
    (Htel : Expr.ForallTelescope input result.nparams suffix)
    (Hdomains : ForallDomainsReady r.restorableNames result.nparams input)
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
  -- the opened body is the residual instantiated with the selected variables
  rcases Hopen.opening.forallResidualData Htel with ⟨fvars', hAs, _, hbody⟩
  have hfvars : fvars'.map Expr.fvar = Hopen.selection.fvars.map Expr.fvar := by
    have h1 : Hopen.params.toList = Hopen.selection.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList hparams
    rw [h1] at hAs
    simpa using hAs.symm
  rw [hfvars] at hbody
  -- source side
  rcases TrExprS.forallTelescope_shape_with_context Htel Hs with
    ⟨Ds, sR, hDs, rfl, HsR⟩
  have HbodyS := TrExprS.instantiateRevFVars Hopen.selection.fvars Ds [] suffix sR
    (hlen.trans hDs.symm) hnodup
    (fvarIdsIn_of_trExprS_abstractForallContext HsR _) HsR
  rw [← hbody, List.append_nil] at HbodyS
  -- target side
  rcases TrExprS.forallTelescope_shape_with_context
      (Hopen.outputPrefixTelescope Htel) Ht with ⟨Dt, tR, hDt, rfl, HtR⟩
  rw [Expr.abstractN_eq_abstractList_of_closed hnodup hrestored] at HtR
  have HbodyT := TrExprS.instantiateRevFVars Hopen.selection.fvars Dt [] _ tR
    (hlen.trans hDt.symm) hnodup
    (fvarIdsIn_of_trExprS_abstractForallContext HtR _) HtR
  rw [TypeChecker.Expr.abstractList_instantiateRevList_eq_self hnodup hrestored,
    List.append_nil] at HbodyT
  -- the opened bodies commute
  have Hbody := (ExprReplacement.restorationCommutes A HAs Hready Hopen.replacement
    (fvarScope_vlamShape _ Ds Dt (hDs.trans hDt.symm)) HbodyS HbodyT).1
  -- and the unchanged parameter prefix has the same, restoration-free domains
  have Hsame := Hopen.sameForallPrefix Htel (FVarsIn_to_FVarIdsIn Hinput) hclosed
  rcases Hsame.translatedDomains_eq Hdomains .nil Hs Ht hDs hDt with ⟨hD, hfree⟩
  subst hD
  exact Restoration.expr_wrapForalls r hfree Hbody

/-- `restoreNested` form of `NestedRestorationOpening.restorationCommutes`.
The side conditions on the opened body are quantified over the opening,
whose fresh variables are chosen by the executable. -/
theorem NestedRestoration.restorationCommutes
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {input output suffix : Expr}
    {s t : VExpr}
    (H : NestedRestoration result env auxRec input output)
    (hparams : result.params.size = result.nparams)
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (Hready : ∀ Hopen : NestedRestorationOpening result env auxRec input output,
      RestoreReady result env Hopen.params r.restorableNames auxLevels Hopen.body ∧
        Closed Hopen.restoredBody)
    (Htel : Expr.ForallTelescope input result.nparams suffix)
    (Hdomains : ForallDomainsReady r.restorableNames result.nparams input)
    (Hinput : input.FVarsIn fun _ => False) (hclosed : Closed input)
    (Hs : TrExprS sourceEnv Us [] input s) (Ht : TrExprS targetEnv Us [] output t) :
    r.expr s = some t := by
  rcases H.opening hparams with ⟨Hopen⟩
  exact Hopen.restorationCommutes A (Hready Hopen).1 Htel Hdomains Hinput hclosed
    (Hready Hopen).2 Hs Ht

/-- Closed commutation for `restoreNested` itself. -/
theorem restoreNested_restorationCommutes
    {r : Restoration} {result : Lean4Lean.ElimNestedInductive.Result}
    {env : Environment} {auxRec : NameMap Name} {sourceEnv targetEnv : VEnv}
    {Us : List Name} {auxLevels : List Level} {input suffix : Expr}
    {s t : VExpr}
    (hparams : result.params.size = result.nparams)
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (Hready : ∀ Hopen : NestedRestorationOpening result env auxRec input
        (result.restoreNested env input auxRec),
      RestoreReady result env Hopen.params r.restorableNames auxLevels Hopen.body ∧
        Closed Hopen.restoredBody)
    (Htel : Expr.ForallTelescope input result.nparams suffix)
    (Hdomains : ForallDomainsReady r.restorableNames result.nparams input)
    (Hinput : input.FVarsIn fun _ => False) (hclosed : Closed input)
    (Hs : TrExprS sourceEnv Us [] input s)
    (Ht : TrExprS targetEnv Us [] (result.restoreNested env input auxRec) t) :
    r.expr s = some t :=
  (restoreNested_refines result env auxRec input
    (Htel.restorePrefix (Nat.le_refl _))).restorationCommutes hparams A Hready Htel
    Hdomains Hinput hclosed Hs Ht

/-- The restored recursor type is the abstract restoration of the lowered
recursor type (the `type` field of `RestoredRecursorRealization`, once the
lowered translation is identified with `g.recursorType owner`). -/
theorem RecursorRestoration.typeRestorationCommutes
    {r : Restoration} {auxLevels : List Level} {sourceEnv targetEnv : VEnv}
    {suffix : Expr} {s t : VExpr}
    (H : RecursorRestoration result env auxRec allIndNames oldRecName newRecName
      oldInfo newInfo)
    (hparams : result.params.size = result.nparams)
    (A : RestorationMapAgreement r result env auxRec targetEnv oldInfo.levelParams
      auxLevels)
    (Hready : ∀ Hopen : NestedRestorationOpening result env auxRec oldInfo.type
        newInfo.type,
      RestoreReady result env Hopen.params r.restorableNames auxLevels Hopen.body ∧
        Closed Hopen.restoredBody)
    (Htel : Expr.ForallTelescope oldInfo.type result.nparams suffix)
    (Hdomains : ForallDomainsReady r.restorableNames result.nparams oldInfo.type)
    (Hinput : oldInfo.type.FVarsIn fun _ => False) (hclosed : Closed oldInfo.type)
    (Hs : TrExprS sourceEnv oldInfo.levelParams [] oldInfo.type s)
    (Ht : TrExprS targetEnv newInfo.levelParams [] newInfo.type t) :
    r.expr s = some t := by
  rw [H.levelParams] at Ht
  exact H.type.restorationCommutes hparams A Hready Htel Hdomains Hinput hclosed Hs Ht

/-! ### Names -/

theorem _root_.Lean4Lean.InductiveSignature.Restoration.restoredHeadName_of_not_mem
    {r : Restoration} {name : Name} (h : name ∉ r.heads.map (·.auxiliary)) :
    r.restoredHeadName name = name := by
  simp [InductiveSignature.Restoration.restoredHeadName,
    Restoration.heads_find?_eq_none h]

theorem nameMap_getD_eq (m : NameMap Name) (k d : Name) :
    Std.TreeMap.getD m k d = (m.find? k).getD d := by
  simp only [NameMap.find?]
  exact Std.TreeMap.getD_eq_getD_getElem?

/-- The recursor name chosen by `restoreRecursorDecl`
(`recNameMap.getD recName recName`) is `r.recursorName`. -/
theorem RestorationMapAgreement.restoredRecursorName
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (oldRecName : Name) :
    Std.TreeMap.getD auxRec oldRecName oldRecName = r.recursorName oldRecName := by
  rw [nameMap_getD_eq, A.recursorName]

theorem RestorationMapAgreement.restoreRecursor_name
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (allIndNames : List Name) (oldRecName : Name) (info : RecursorVal) :
    (result.restoreRecursor env auxRec allIndNames oldRecName
      (Std.TreeMap.getD auxRec oldRecName oldRecName) info).name =
      r.recursorName oldRecName := by
  simp [Lean4Lean.ElimNestedInductive.Result.restoreRecursor,
    A.restoredRecursorName]

theorem RecursorRestoration.name_eq_recursorName
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (H : RecursorRestoration result env auxRec allIndNames oldRecName newRecName
      oldInfo newInfo)
    (hnew : newRecName = Std.TreeMap.getD auxRec oldRecName oldRecName) :
    newInfo.name = r.recursorName oldRecName := by
  rw [H.name, hnew, A.restoredRecursorName]

/-- `restoreCtorName` agrees with `Restoration.restoredHeadName` on the
constructors of auxiliary families. -/
theorem RestorationMapAgreement.restoreCtorName
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hfamily : result.aux2nested.find? c = none)
    (hctor : result.getNestedIfAuxCtor env c = some (nested, auxI)) :
    result.restoreCtorName env c = r.restoredHeadName c := by
  rcases A.ctorTarget c nested auxI hfamily hctor with ⟨I, ls, hI, hname⟩
  simp [Lean4Lean.ElimNestedInductive.Result.restoreCtorName, hctor, hI, hname,
    Id.run]

/-- Rule constructor names of an auxiliary recursor are restored to the
abstract head targets. -/
theorem RestorationMapAgreement.restoreRule_ctor_auxiliary
    (A : RestorationMapAgreement r result env auxRec targetEnv Us auxLevels)
    (hne : newRecName ≠ oldRecName)
    (hfamily : result.aux2nested.find? rule.ctor = none)
    (hctor : result.getNestedIfAuxCtor env rule.ctor = some (nested, auxI)) :
    (result.restoreRule env auxRec oldRecName newRecName rule).ctor =
      r.restoredHeadName rule.ctor := by
  simp [Lean4Lean.ElimNestedInductive.Result.restoreRule, hne,
    A.restoreCtorName hfamily hctor]

/-- Rule constructor names of a primary recursor are unchanged, as are their
abstract restorations. -/
theorem restoreRule_ctor_primary {r : Restoration}
    {result : Lean4Lean.ElimNestedInductive.Result} {env : Environment}
    {auxRec : NameMap Name} {oldRecName : Name} {rule : RecursorRule}
    (hnot : rule.ctor ∉ r.heads.map (·.auxiliary)) :
    (result.restoreRule env auxRec oldRecName oldRecName rule).ctor =
      r.restoredHeadName rule.ctor := by
  simp [Lean4Lean.ElimNestedInductive.Result.restoreRule,
    InductiveSignature.Restoration.restoredHeadName_of_not_mem hnot]

/-! ### Whole rule right-hand sides -/

/-- The production rule RHS restoration commutes with `Restoration.expr`:
the abstract restoration of the old RHS's translation is the translation of
the restored RHS. The parameter lambda domains are unchanged by both. -/
theorem RestoredRuleRhsTranslation.restorationCommutes
    {r : Restoration} {auxLevels : List Level}
    (H : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldRule newRule Hrule sourceEnv targetEnv Us)
    (A : RestorationMapAgreement r result prodEnv auxRec targetEnv Us auxLevels)
    (Hready : RestoreReady result prodEnv H.opening.params r.restorableNames
      auxLevels H.opening.body)
    (Hshape : VLCtx.VLamShape H.sourceScope H.targetScope)
    (Hdomains : ∀ d ∈ H.targetScope.toCtx,
      d.containsAnyConst r.restorableNames = false) :
    r.expr (VExpr.wrapLams H.targetScope.toCtx.reverse H.sourceBody) =
      some (VExpr.wrapLams H.targetScope.toCtx.reverse H.targetBody) := by
  have HAs : ∀ a ∈ H.opening.params.toList, ∃ fv, a = .fvar fv := by
    intro a ha
    rw [H.opening.selection.expressions] at ha
    simp at ha
    rcases ha with ⟨fv, _, rfl⟩
    exact ⟨fv, rfl⟩
  have Hshape' : VLCtx.VLamShape (abstractForallContext [] H.sourceScope)
      (abstractForallContext [] H.targetScope) := by
    simpa [abstractForallContext] using Hshape
  have Hbody := (ExprReplacement.restorationCommutes A HAs Hready
    H.opening.replacement Hshape' H.body.sourceTranslation
    H.body.targetTranslation).1
  exact Restoration.expr_wrapLams r (fun d hd => Hdomains d (by simpa using hd)) Hbody

/-- Item for `RestoredRuleRealization.equation`: any translation of the old
(lowered) RHS restores to a translation of the restored RHS. -/
theorem RestoredRuleRhsTranslation.restoredRhs
    {r : Restoration} {auxLevels : List Level} {loweredEnv : VEnv}
    (H : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldRule newRule Hrule sourceEnv targetEnv Us)
    (A : RestorationMapAgreement r result prodEnv auxRec targetEnv Us auxLevels)
    (Hready : RestoreReady result prodEnv H.opening.params r.restorableNames
      auxLevels H.opening.body)
    (Hshape : VLCtx.VLamShape H.sourceScope H.targetScope)
    (Hdomains : ∀ d ∈ H.targetScope.toCtx,
      d.containsAnyConst r.restorableNames = false)
    (Hfragment : RestoreFragment oldRule.rhs)
    (Hlowered : TrExprS loweredEnv Us [] oldRule.rhs rhs) :
    ∃ rhs', r.expr rhs = some rhs' ∧ TrExprS targetEnv Us [] newRule.rhs rhs' := by
  have heq := Hfragment.translation_eq .nil Hlowered H.sourceTranslation
  subst heq
  exact ⟨_, H.restorationCommutes A Hready Hshape Hdomains, H.restoredTranslation⟩

end VerifyInductive
end Lean4Lean
