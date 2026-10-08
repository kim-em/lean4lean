import Lean4Lean.Verify.TypeChecker.WHNF

namespace Lean4Lean

open Lean hiding Environment Exception

namespace TypeChecker

/-- Two expressions agree after simultaneously closing two ordered lists of
free variables.  This is the concrete alpha relation used by the executable
checker: it does not choose a global renaming and is insensitive to unrelated
locals in either ambient context. -/
def ExprAlphaUnder (left right : List FVarId)
    (e₁ e₂ : Expr) : Prop :=
  e₁.abstractList left = e₂.abstractList right

theorem ExprAlphaUnder.refl (e : Expr) (binders : List FVarId) :
    ExprAlphaUnder binders binders e e := rfl

/-- Closing a free variable after lifting below `d` binders is the same as
closing it outside those binders and lifting the resulting loose variable.
This is the value-side algebra needed by substitution under binders. -/
theorem Expr.abstract1_liftLooseBVars_alpha
    (value : Expr) (fv : FVarId) (k d : Nat) :
    (value.liftLooseBVars' k d).abstract1 fv (k + d) =
      (value.abstract1 fv k).liftLooseBVars' k d := by
  induction value generalizing k d <;>
    grind [Expr.abstract1, Expr.liftLooseBVars']

/-- Abstracting a free variable commutes with substituting a bound variable.
This is the single-binder algebra behind alpha-equivariance of `let` beta
reduction. -/
theorem Expr.abstract1_instantiate1'_alpha
    (body value : Expr) (fv : FVarId) (d : Nat) :
    (body.instantiate1' value d).abstract1 fv d =
      (body.abstract1 fv (d + 1)).instantiate1'
        (value.abstract1 fv 0) d := by
  induction body generalizing d with
  | bvar index =>
      by_cases hbelow : index < d
      · have hbelowSucc : index < d + 1 := by omega
        simp [Expr.instantiate1', Expr.abstract1, hbelow, hbelowSucc]
      by_cases heq : index = d
      · subst index
        simpa [Expr.instantiate1', Expr.abstract1] using
          Expr.abstract1_liftLooseBVars_alpha value fv 0 d
      · have habove : d < index := by omega
        have hnotBelowSucc : ¬index < d + 1 := by omega
        have hsubNotBelow : ¬index - 1 < d := by omega
        have hplusNotBelow : ¬index + 1 < d := by omega
        have hplusNe : index + 1 ≠ d := by omega
        simp [Expr.instantiate1', Expr.abstract1, hbelow, heq,
          hnotBelowSucc, hsubNotBelow, hplusNotBelow, hplusNe,
          Nat.sub_add_cancel (by omega : 1 ≤ index)]
  | fvar id =>
      by_cases h : (fv == id) = true
      · simp [Expr.instantiate1', Expr.abstract1, h]
      · simp [Expr.instantiate1', Expr.abstract1, h]
  | mvar | sort | const | lit => rfl
  | app fn arg ihFn ihArg =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihFn, ihArg]
  | lam name domain body bi ihDomain ihBody =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihDomain]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ihBody (d + 1)
  | forallE name domain body bi ihDomain ihBody =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihDomain]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ihBody (d + 1)
  | letE name type value body nondep ihType ihValue ihBody =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihType, ihValue]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ihBody (d + 1)
  | mdata data body ihBody =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihBody]
  | proj name index body ihBody =>
      simp only [Expr.instantiate1', Expr.abstract1]
      rw [ihBody]

/-- Ordered local declarations corresponding under simultaneous closure.
At ordinal `i`, each declaration type is closed only over the preceding
binders.  Later and unrelated ambient locals are intentionally unconstrained;
the locality theorem for a checker operation must separately show that its
input and every declaration it follows use only this aligned spine (plus any
literally shared outer free variables). -/
structure LocalContext.OrderedBinderRenaming
    (leftCtx rightCtx : LocalContext)
    (left right : List FVarId) : Prop where
  length_eq : left.length = right.length
  left_nodup : left.Nodup
  right_nodup : right.Nodup
  declarations : ∀ i (hiLeft : i < left.length)
      (hiRight : i < right.length),
    ∃ leftIndex leftName leftType leftBi leftKind,
      leftCtx.find? (left[i]'hiLeft) =
        some (.cdecl leftIndex (left[i]'hiLeft) leftName leftType leftBi
          leftKind) ∧
    ∃ rightIndex rightName rightType rightBi rightKind,
      rightCtx.find? (right[i]'hiRight) =
        some (.cdecl rightIndex (right[i]'hiRight) rightName rightType rightBi
          rightKind) ∧
      ExprAlphaUnder (left.take i) (right.take i) leftType rightType

/-- The empty generated spine is aligned in arbitrary ambient contexts. -/
theorem LocalContext.OrderedBinderRenaming.empty
    (leftCtx rightCtx : LocalContext) :
    LocalContext.OrderedBinderRenaming leftCtx rightCtx [] [] where
  length_eq := rfl
  left_nodup := List.nodup_nil
  right_nodup := List.nodup_nil
  declarations i hi := by simp at hi

theorem Inner.getLCtx_run (methods : Methods) (context : Context)
    (state : State) :
    (getLCtx : RecM LocalContext) methods context state =
      .ok (context.lctx, state) := by
  rfl

theorem readContext_run (context : Context) (state : State) :
    (readThe Context : M Context) context state =
      .ok (context, state) := by
  rfl

/-- Closing more free variables shifts an already-bound variable above the
closure cutoff once per variable. -/
private theorem Expr.abstractList_bvar_ge_alpha
    (fvars : List FVarId) (k n : Nat) :
    (Expr.bvar (k + n)).abstractList fvars k =
      .bvar (k + n + fvars.length) := by
  induction fvars generalizing n with
  | nil => simp
  | cons fv rest ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      rw [if_neg (by omega)]
      have hindex : k + n + 1 = k + (n + 1) := by omega
      rw [hindex, ih (n := n + 1)]
      congr 1
      simp only [List.length_cons]
      omega

/-- Closing the variable at an exact ordinal in a duplicate-free binder
spine depends only on that ordinal and the spine length. -/
private theorem Expr.abstractList_fvarAt_alpha
    (H : fvars.Nodup) (i : Nat) (hi : i < fvars.length) :
    (Expr.fvar fvars[i]).abstractList fvars k =
      .bvar (k + (fvars.length - 1 - i)) := by
  induction fvars generalizing i k with
  | nil => simp at hi
  | cons head tail ih =>
      simp only [List.nodup_cons] at H
      cases i with
      | zero =>
          simp only [List.getElem_cons_zero, Expr.abstractList]
          rw [show (Expr.fvar head).abstract1 head k = .bvar k by
            simp [Expr.abstract1]]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Expr.abstractList_bvar_ge_alpha tail k 0
      | succ i =>
          have hiTail : i < tail.length := by simpa using hi
          have hne : head ≠ tail[i] := by
            intro heq
            exact H.1 (heq ▸ List.getElem_mem hiTail)
          simp only [List.getElem_cons_succ, Expr.abstractList]
          rw [show (Expr.fvar tail[i]).abstract1 head k =
              .fvar tail[i] by simp [Expr.abstract1, hne]]
          rw [ih H.2 i hiTail (k := k)]
          apply congrArg Expr.bvar
          simp only [List.length_cons]
          omega

/-- Closing a free variable disjoint from the generated binder spine leaves
it unchanged. -/
private theorem Expr.abstractList_fvar_fresh_alpha
    (H : fv ∉ fvars) :
    (Expr.fvar fv).abstractList fvars k = .fvar fv := by
  induction fvars with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.mem_cons, not_or] at H
      simp only [Expr.abstractList]
      rw [show (Expr.fvar fv).abstract1 head k = .fvar fv by
        simp [Expr.abstract1, Ne.symm H.1]]
      exact ih H.2

/-- Closing a duplicate-free free-variable spine and reopening it with the
same identifiers is a left inverse on well-scoped expressions.  This makes
the canonical closed form injective on every concrete WHNF cache key used in
the paired runs. -/
theorem Expr.abstractList_instantiateRevList_eq_self
    (hnd : fvars.Nodup) (hclosed : Closed e k) :
    (e.abstractList fvars k).instantiateRevList
        (fvars.map Expr.fvar) k = e := by
  induction e generalizing k with
  | bvar i =>
      rw [Lean.Expr.abstractList_bvar_lt (i := i) (k := k) fvars hclosed]
      exact Expr.instantiateRevList_bvar_fvars_lt fvars i k hclosed
  | fvar fv =>
      by_cases hmem : fv ∈ fvars
      · obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
        have hselected := Expr.abstractList_fvarAt_alpha
          (fvars := fvars) hnd i hi (k := k)
        rw [hget] at hselected
        rw [hselected]
        have hrestore := Expr.instantiateRevList_bvar_fvars_getElem
          fvars i k hi
        rwa [hget] at hrestore
      · rw [Expr.abstractList_fvar_fresh_alpha hmem]
        exact Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])
  | mvar id => simp [Closed] at hclosed
  | sort level =>
      have habstract : (Expr.sort level).abstractList fvars k =
          .sort level := by
        induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1]
      rw [habstract]
      exact Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])
  | const name levels =>
      rw [Lean.Expr.abstractList_const]
      exact Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])
  | lit value =>
      have habstract : (Expr.lit value).abstractList fvars k =
          .lit value := by
        induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1]
      rw [habstract]
      exact Expr.instantiateRevList'_eq_self (by simp [Expr.looseBVarRange'])
  | app fn arg ihFn ihArg =>
      rcases hclosed with ⟨hfn, harg⟩
      simp only [Lean.Expr.abstractList_app, Expr.instantiateRevList_app]
      rw [ihFn hfn, ihArg harg]
  | lam name domain body bi ihDomain ihBody =>
      rcases hclosed with ⟨hdomain, hbody⟩
      simp only [Lean.Expr.abstractList_lam, Expr.instantiateRevList_lam]
      rw [ihDomain hdomain, ihBody hbody]
  | forallE name domain body bi ihDomain ihBody =>
      rcases hclosed with ⟨hdomain, hbody⟩
      simp only [Lean.Expr.abstractList_forallE,
        Expr.instantiateRevList_forallE]
      rw [ihDomain hdomain, ihBody hbody]
  | letE name type value body nondep ihType ihValue ihBody =>
      rcases hclosed with ⟨htype, hvalue, hbody⟩
      simp only [Lean.Expr.abstractList_letE,
        Expr.instantiateRevList_letE]
      rw [ihType htype, ihValue hvalue, ihBody hbody]
  | mdata data body ihBody =>
      simp only [Lean.Expr.abstractList_mdata,
        Expr.instantiateRevList_mdata]
      rw [ihBody hclosed]
  | proj name index body ihBody =>
      simp only [Lean.Expr.abstractList_proj,
        Expr.instantiateRevList_proj]
      rw [ihBody hclosed]

end TypeChecker
end Lean4Lean
