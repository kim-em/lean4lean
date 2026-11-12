import Lean4Lean.Verify.Expr.Telescope
import Lean4Lean.Verify.LocalContext

/-! # Abstraction and application spines of expressions

Syntactic lemmas about `Lean.Expr`: abstraction over free variables (`abstractN`, `abstractList`,
`abstract1`), instantiation, reopening, application spines (`mkAppN`, `mkAppList`, `getAppFn`,
`getAppArgs`), loose bound variable ranges and forall-domain lists. Nothing here mentions the
abstract typing judgment.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Source-side residual substitution matching complete application of a
forall telescope.  At each step the outer binder lies beneath all still-inner
binders in the already-open body, hence the decreasing `args.length` cutoff. -/
def Expr.instantiateForallBody : Expr → List Expr → Expr
  | body, [] => body
  | body, arg :: args =>
      instantiateForallBody (body.instantiate1' arg args.length) args

theorem Expr.getAppFn_mkAppN (fn : Expr) (args : Array Expr) :
    (mkAppN fn args).getAppFn = fn.getAppFn := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [List.foldl_cons]
    simpa [Expr.getAppFn] using ih (.app fn arg)

/-- An application spine headed by a local variable cannot be one of Lean's
distinguished parameter-annotation applications. -/
theorem Expr.isAppOfArity_eq_false_of_getAppFn_fvar
    {e : Expr} (h : e.getAppFn = .fvar fv) (name : Name) (arity : Nat) :
    e.isAppOfArity name arity = false := by
  induction e generalizing arity with
  | app fn arg ihFn _ =>
    cases arity with
    | zero => rfl
    | succ arity =>
      apply ihFn
      simpa only [Expr.getAppFn] using h
  | _ => cases arity <;> simp_all [Expr.getAppFn, Expr.isAppOfArity]

theorem Expr.getAppArgsList_mkAppN (fn : Expr) (args : Array Expr) :
    (mkAppN fn args).getAppArgsList = fn.getAppArgsList ++ args.toList := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [Expr.getAppArgsList_app, List.append_assoc]

@[simp] theorem Expr.foldl_mkApp_eq (args : List Expr) (fn : Expr) :
    args.foldl Lean.mkApp fn = args.foldl Expr.app fn := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [List.foldl_cons, Lean.mkApp]
    exact ih (.app fn arg)

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem Expr.consumeTypeAnnotationsVerified_eq_self {dom : Expr}
    (hopt : dom.isOptParam = false) (hauto : dom.isAutoParam = false)
    (hout : dom.isOutParam = false) (hsemi : dom.isSemiOutParam = false) :
    (dom.consumeTypeAnnotationsVerified annOk) = dom := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ dom
  all_goals simp_all [Expr.isOptParam, Expr.isAutoParam,
    Expr.isOutParam, Expr.isSemiOutParam, Expr.isAppOfArity]

/-- Removing binder annotations only selects subexpressions of the original
domain, so it cannot introduce a new free-variable dependency. -/
theorem Expr.consumeTypeAnnotationsVerified_fvarsIn
    (H : FVarsIn P e) : FVarsIn P (e.consumeTypeAnnotationsVerified annOk) := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ e
  case case1 ih => exact ih H.1.2
  case case2 => exact H
  case case3 ih => exact ih H.2
  case case4 => exact H
  case case5 => exact H

/-- Syntactic forall spine of a constructor type exactly as walked by the
executable constructor check: `k` leading `forallE` binders followed by a
constant-headed codomain.  No `mdata` or `letE` sits on the spine. -/
inductive Expr.ForallSpine : Expr → Nat → Prop
  | codomain {e : Expr} {name : Name} {levels : List Level}
      (hhead : e.getAppFn = .const name levels) : ForallSpine e 0
  | step {name : Name} {dom body : Expr} {bi : BinderInfo} {k : Nat}
      (H : ForallSpine body k) : ForallSpine (.forallE name dom body bi) (k + 1)

/-- Substituting a free variable cannot create a constant application head. -/
theorem Expr.getAppFn_instantiate1'_const
    {e : Expr} {fv : FVarId} {d : Nat} {name : Name} {levels : List Level}
    (H : (e.instantiate1' (.fvar fv) d).getAppFn = .const name levels) :
    e.getAppFn = .const name levels := by
  induction e generalizing d with
  | app f a ihf _ =>
    simp only [Expr.instantiate1', Expr.getAppFn] at H ⊢
    exact ihf H
  | bvar i =>
    simp only [Expr.instantiate1'] at H
    split at H
    · simp [Expr.getAppFn] at H
    · split at H
      · simp [Expr.liftLooseBVars', Expr.getAppFn] at H
      · simp [Expr.getAppFn] at H
  | const _ _ => simpa [Expr.instantiate1'] using H
  | fvar _ | mvar _ | sort _ | lit _ | mdata _ _ _ | proj _ _ _ _
  | lam _ _ _ _ _ _ | forallE _ _ _ _ _ _ | letE _ _ _ _ _ _ _ _ =>
    simp [Expr.instantiate1', Expr.getAppFn] at H

/-- Substituting a free variable cannot create a forall binder. -/
theorem Expr.instantiate1'_fvar_forallE_inv
    {e : Expr} {fv : FVarId} {d : Nat} {name : Name} {dom body : Expr}
    {bi : BinderInfo}
    (H : e.instantiate1' (.fvar fv) d = .forallE name dom body bi) :
    ∃ dom' body', e = .forallE name dom' body' bi ∧
      dom = dom'.instantiate1' (.fvar fv) d ∧
      body = body'.instantiate1' (.fvar fv) (d + 1) := by
  cases e with
  | forallE name' dom' body' bi' =>
    simp only [Expr.instantiate1', Expr.forallE.injEq] at H
    rcases H with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨dom', body', rfl, rfl, rfl⟩
  | bvar i =>
    simp only [Expr.instantiate1'] at H
    split at H
    · cases H
    · split at H
      · simp [Expr.liftLooseBVars'] at H
      · cases H
  | const _ _ | fvar _ | mvar _ | sort _ | lit _ | mdata _ _ | proj _ _ _
  | lam _ _ _ _ | app _ _ | letE _ _ _ _ _ =>
    simp [Expr.instantiate1'] at H

theorem Expr.ForallSpine.of_instantiate1'_fvar
    {e : Expr} {fv : FVarId} {d k : Nat}
    (H : ForallSpine (e.instantiate1' (.fvar fv) d) k) : ForallSpine e k := by
  generalize he : e.instantiate1' (.fvar fv) d = e' at H
  induction H generalizing e d with
  | codomain hhead =>
    subst he
    exact .codomain (Expr.getAppFn_instantiate1'_const hhead)
  | step _ ih =>
    rcases Expr.instantiate1'_fvar_forallE_inv he with ⟨dom', body', rfl, _, hb⟩
    exact .step (ih hb.symm)

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Replacing universe parameters by universe expressions without metavariables
does not introduce a universe metavariable. -/
theorem _root_.Lean.Level.substParams'_hasMVar_false
    (Hu : u.hasMVar' = false)
    (Hs : ∀ name, (s name).hasMVar' = false) :
    (Lean.Level.substParams' s red u).hasMVar' = false := by
  induction u generalizing red with
  | zero | param | mvar => simp_all [Lean.Level.substParams', Lean.Level.hasMVar']
  | succ u ih =>
      simp only [Lean.Level.substParams', Lean.Level.hasMVar'] at Hu ⊢
      exact ih Hu
  | max u v ihu ihv =>
      simp only [Lean.Level.hasMVar'] at Hu
      have Hu' := Bool.or_eq_false_iff.mp Hu
      simp only [Lean.Level.substParams']
      split
      · exact Lean.Level.mkLevelMax'_hasMVar_false _ _
          (ihu Hu'.1) (ihv Hu'.2)
      · simp [Lean.Level.hasMVar', ihu Hu'.1, ihv Hu'.2]
  | imax u v ihu ihv =>
      simp only [Lean.Level.hasMVar'] at Hu
      have Hu' := Bool.or_eq_false_iff.mp Hu
      simp only [Lean.Level.substParams']
      split
      · exact Lean.Level.mkLevelIMax'_hasMVar_false _ _
          (ihu Hu'.1) (ihv Hu'.2)
      · simp [Lean.Level.hasMVar', ihu Hu'.1, ihv Hu'.2]

theorem _root_.Lean4Lean.Expr.eqv_fvar_eq
    (H : (((.fvar fv : Expr) == e)) = true) : e = .fvar fv := by
  cases e <;> simp [(· == ·), Expr.eqv'] at H
  rename_i fv'
  have : fv = fv' := beq_iff_eq.mp H
  cases this
  rfl

end VerifyInductive

namespace VerifyInductive
attribute [local simp] Lean.Expr.abstractList_const Lean.Expr.abstractList_app Lean.Expr.abstractList_lam
  Lean.Expr.abstractList_forallE Lean.Expr.abstractList_letE Lean.Expr.abstractList_mdata
  Lean.Expr.abstractList_proj

theorem Expr.abstractN_bvar_lt (fvs : List FVarId) (_h : n < k) :
    (Expr.bvar n).abstractN fvs k = .bvar n := rfl

@[simp] theorem Expr.abstractN_app :
    (Expr.app fn arg).abstractN fvs k = .app (fn.abstractN fvs k) (arg.abstractN fvs k) := rfl

theorem Expr.abstractN_mkAppN :
    (mkAppN fn args).abstractN fvs k =
      mkAppN (fn.abstractN fvs k) (args.map fun arg => arg.abstractN fvs k) := by
  unfold mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  simp only [Array.toList_map]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [Expr.abstractN]

theorem Expr.abstractN_fvar_of_not_mem (hmem : fv ∉ fvs) :
    (Expr.fvar fv).abstractN fvs k = .fvar fv := by
  simp [Expr.abstractN, Expr.lastRevIdx?_eq_none_of_not_mem hmem]

theorem Expr.abstractList_mkAppN :
    (mkAppN fn args).abstractList fvs k =
      mkAppN (fn.abstractList fvs k)
        (args.map fun arg => arg.abstractList fvs k) := by
  unfold mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  simp only [Array.toList_map]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => simp
  | cons arg args ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp

theorem Expr.mkAppRange_to_end
    (fn : Expr) (args : Array Expr) (start : Nat)
    (hstart : start ≤ args.size) :
    mkAppRange fn start args.size args =
      Expr.mkAppList fn (args.toList.drop start) := by
  apply Expr.mkAppRange_eq
      (l₁ := args.toList.take start) (l₂ := args.toList.drop start)
      (l₃ := [])
  · simp
  · simp [List.length_take, Nat.min_eq_left hstart]
  · simp

theorem Expr.mkAppRange_from_zero
    (fn : Expr) (args : Array Expr) (stop : Nat)
    (hstop : stop ≤ args.size) :
    mkAppRange fn 0 stop args =
      Expr.mkAppList fn (args.toList.take stop) := by
  apply Expr.mkAppRange_eq
      (l₁ := []) (l₂ := args.toList.take stop)
      (l₃ := args.toList.drop stop)
  · simp
  · rfl
  · simp [List.length_take, Nat.min_eq_left hstop]

theorem Expr.getAppArgsList_mkAppList_const
    (name : Name) (levels : List Level) (args : List Expr) :
    (Expr.mkAppList (.const name levels) args).getAppArgsList = args := by
  rw [Expr.getAppArgsList_mkAppList, Expr.getAppArgsList_const]
  simp

/-- Abstracting free variables below `extra` freshly introduced binders is
the same operation as abstracting at the original depth and weakening the
result.  Closedness rules out pre-existing loose variables at the insertion
cut, so the two de Bruijn presentations agree exactly. -/
theorem Expr.abstractList_add_eq_liftLooseBVars
    (Hclosed : Closed e depth) (Hnodup : fvars.Nodup) :
    e.abstractList fvars (depth + extra) =
      (e.abstractList fvars depth).liftLooseBVars' depth extra := by
  induction e generalizing depth extra with
  | bvar i =>
    simp only [Closed] at Hclosed
    rw [Expr.abstractList_bvar_lt fvars (by omega),
      Expr.abstractList_bvar_lt fvars Hclosed]
    simp [Expr.liftLooseBVars', Hclosed]
  | fvar fv =>
    by_cases hmem : fv ∈ fvars
    · rcases List.getElem_of_mem hmem with ⟨i, hi, hget⟩
      subst fv
      rw [Expr.abstractList_fvar_getElem Hnodup i hi,
        Expr.abstractList_fvar_getElem Hnodup i hi]
      simp only [Expr.liftLooseBVars']
      rw [if_neg (by omega)]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · rw [Expr.abstractList_fvar_of_not_mem hmem,
        Expr.abstractList_fvar_of_not_mem hmem]
      rfl
  | sort =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | const =>
    simp [Expr.liftLooseBVars']
  | mvar =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | lit =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | app fn arg ihFn ihArg =>
    rcases Hclosed with ⟨Hfn, Harg⟩
    simp [Expr.liftLooseBVars', ihFn Hfn, ihArg Harg]
  | lam name dom body bi ihDom ihBody =>
    rcases Hclosed with ⟨Hdom, Hbody⟩
    simp only [Expr.abstractList_lam, Expr.liftLooseBVars']
    rw [ihDom Hdom]
    rw [show depth + extra + 1 = (depth + 1) + extra by omega]
    rw [ihBody Hbody]
  | forallE name dom body bi ihDom ihBody =>
    rcases Hclosed with ⟨Hdom, Hbody⟩
    simp only [Expr.abstractList_forallE, Expr.liftLooseBVars']
    rw [ihDom Hdom]
    rw [show depth + extra + 1 = (depth + 1) + extra by omega]
    rw [ihBody Hbody]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    rcases Hclosed with ⟨Hty, Hvalue, Hbody⟩
    simp only [Expr.abstractList_letE, Expr.liftLooseBVars']
    rw [ihTy Hty, ihValue Hvalue]
    rw [show depth + extra + 1 = (depth + 1) + extra by omega]
    rw [ihBody Hbody]
  | mdata md body ih =>
    simpa [Expr.liftLooseBVars'] using ih Hclosed
  | proj name idx body ih =>
    simpa [Expr.liftLooseBVars'] using ih Hclosed

/-- Weakening below an abstraction cutoff commutes with closing free
variables, provided the abstraction is moved past the inserted binders. -/
theorem Expr.liftLooseBVars'_abstractList_add
    (e : Expr) (fvars : List FVarId) (start cutoff amount : Nat)
    (Hcutoff : start ≤ cutoff) (Hnodup : fvars.Nodup) :
    (e.liftLooseBVars' start amount).abstractList fvars (cutoff + amount) =
      (e.abstractList fvars cutoff).liftLooseBVars' start amount := by
  induction e generalizing start cutoff amount with
  | bvar i =>
    by_cases hstart : i < start
    · rw [show (Expr.bvar i).liftLooseBVars' start amount = .bvar i by
          simp [Expr.liftLooseBVars', hstart],
        Expr.abstractList_bvar_lt fvars (by omega),
        Expr.abstractList_bvar_lt fvars (by omega)]
      simp [Expr.liftLooseBVars', hstart]
    · by_cases hcut : i < cutoff
      · rw [show (Expr.bvar i).liftLooseBVars' start amount =
              .bvar (i + amount) by
            simp [Expr.liftLooseBVars', hstart],
          Expr.abstractList_bvar_lt fvars (by omega),
          Expr.abstractList_bvar_lt fvars hcut]
        simp [Expr.liftLooseBVars', hstart]
      · obtain ⟨n, rfl⟩ : ∃ n, i = cutoff + n :=
          ⟨i - cutoff, by omega⟩
        have hge : ¬ cutoff + n < start := by omega
        have hgeAbstract :
            ¬ cutoff + n + fvars.length < start := by omega
        rw [show (Expr.bvar (cutoff + n)).liftLooseBVars' start amount =
              .bvar ((cutoff + amount) + n) by
            simp [Expr.liftLooseBVars', hge]; omega,
          Expr.abstractList_bvar_ge,
          Expr.abstractList_bvar_ge]
        simp [Expr.liftLooseBVars', hgeAbstract]
        omega
  | fvar fv =>
    simp only [Expr.liftLooseBVars']
    by_cases hmem : fv ∈ fvars
    · rcases List.getElem_of_mem hmem with ⟨i, hi, hget⟩
      subst fv
      rw [Expr.abstractList_fvar_getElem Hnodup i hi,
        Expr.abstractList_fvar_getElem Hnodup i hi]
      simp only [Expr.liftLooseBVars']
      rw [if_neg (by omega)]
      congr 1
      omega
    · rw [Expr.abstractList_fvar_of_not_mem hmem,
        Expr.abstractList_fvar_of_not_mem hmem]
      rfl
  | sort =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | const =>
    simp [Expr.liftLooseBVars']
  | mvar =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | lit =>
    induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1,
      Expr.liftLooseBVars']
  | app fn arg ihFn ihArg =>
    simp [Expr.liftLooseBVars', ihFn start cutoff amount Hcutoff,
      ihArg start cutoff amount Hcutoff]
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.liftLooseBVars', Expr.abstractList_lam]
    rw [ihDom start cutoff amount Hcutoff]
    rw [show cutoff + amount + 1 = (cutoff + 1) + amount by omega]
    rw [ihBody (start + 1) (cutoff + 1) amount (by omega)]
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.liftLooseBVars', Expr.abstractList_forallE]
    rw [ihDom start cutoff amount Hcutoff]
    rw [show cutoff + amount + 1 = (cutoff + 1) + amount by omega]
    rw [ihBody (start + 1) (cutoff + 1) amount (by omega)]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp only [Expr.liftLooseBVars', Expr.abstractList_letE]
    rw [ihTy start cutoff amount Hcutoff,
      ihValue start cutoff amount Hcutoff]
    rw [show cutoff + amount + 1 = (cutoff + 1) + amount by omega]
    rw [ihBody (start + 1) (cutoff + 1) amount (by omega)]
  | mdata md body ih =>
    simpa [Expr.liftLooseBVars'] using
      ih start cutoff amount Hcutoff
  | proj name idx body ih =>
    simpa [Expr.liftLooseBVars'] using
      ih start cutoff amount Hcutoff

/-- If closing a list of free variables yields a term scoped by exactly the
new de Bruijn prefix, the original term had no loose variables at the
abstraction cut. -/
theorem Expr.closed_of_abstractList
    (Hclosed : Closed (e.abstractList fvars depth)
      (depth + fvars.length)) :
    Closed e depth := by
  induction e generalizing depth with
  | bvar i =>
    by_cases hi : i < depth
    · exact hi
    · have heq : i = depth + (i - depth) := by omega
      rw [heq, Expr.abstractList_bvar_ge] at Hclosed
      simpa only [Closed] using (show i < depth from by
        simp only [Closed] at Hclosed
        omega)
  | fvar => trivial
  | sort => trivial
  | const => trivial
  | mvar id =>
    have heq : (Expr.mvar id).abstractList fvars depth =
        .mvar id := by
      clear Hclosed
      induction fvars <;> simp_all [Expr.abstractList, Expr.abstract1]
    rw [heq] at Hclosed
    exact Hclosed
  | lit => trivial
  | app fn arg ihFn ihArg =>
    rw [Expr.abstractList_app] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hfn, Harg⟩
    exact ⟨ihFn Hfn, ihArg Harg⟩
  | lam name dom body bi ihDom ihBody =>
    rw [Expr.abstractList_lam] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hdom, Hbody⟩
    refine ⟨ihDom Hdom, ihBody ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  | forallE name dom body bi ihDom ihBody =>
    rw [Expr.abstractList_forallE] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hdom, Hbody⟩
    refine ⟨ihDom Hdom, ihBody ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  | letE name ty value body nondep ihTy ihValue ihBody =>
    rw [Expr.abstractList_letE] at Hclosed
    simp only [Closed] at Hclosed ⊢
    rcases Hclosed with ⟨Hty, Hvalue, Hbody⟩
    refine ⟨ihTy Hty, ihValue Hvalue, ihBody ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Hbody
  | mdata md body ih =>
    rw [Expr.abstractList_mdata] at Hclosed
    simpa only [Closed] using ih Hclosed
  | proj name idx body ih =>
    rw [Expr.abstractList_proj] at Hclosed
    simpa only [Closed] using ih Hclosed

theorem Expr.abstractN_fvar_getElem
    (hnd : fvs.Nodup) (i : Nat) (hi : i < fvs.length) :
    (Expr.fvar fvs[i]).abstractN fvs k = .bvar (k + (fvs.length - 1 - i)) := by
  rw [Expr.abstractN_eq_abstractList hnd _ _ (by simp [Expr.looseBVarRange'])]
  exact Expr.abstractList_fvar_getElem hnd i hi

theorem Expr.abstractN_fvarArray
    (fvs : List FVarId) (k : Nat) (hnd : fvs.Nodup) :
    ((fvs.map Expr.fvar).toArray.map fun e => e.abstractN fvs k) =
      (List.ofFn fun i : Fin fvs.length =>
        Expr.bvar (k + (fvs.length - 1 - i))).toArray := by
  apply Array.ext
  · simp
  · intro i h1 h2
    have hi : i < fvs.length := by simpa using h1
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractN_fvar_getElem hnd i hi

theorem Expr.abstractList_fvarArray
    (fvs : List FVarId) (k : Nat) (hnd : fvs.Nodup) :
    ((fvs.map Expr.fvar).toArray.map fun e => e.abstractList fvs k) =
      (List.ofFn fun i : Fin fvs.length =>
        Expr.bvar (k + (fvs.length - 1 - i))).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    simp only [Array.getElem_map, List.getElem_toArray,
      List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractList_fvar_getElem hnd i (by simpa using hiLeft)

/-- Close an expression over one free-variable parameter array and reopen it
with another. -/
def Expr.reopenParams (e : Expr) (params restoreAs : Array Expr) : Expr :=
  (e.abstract params).instantiateRev restoreAs

/-- Transparent list model of parameter reopening at an arbitrary de Bruijn
depth. -/
def Expr.reopenFVarsAt (e : Expr) (fvars restoreFvars : List FVarId)
    (k : Nat := 0) : Expr :=
  (e.abstractList fvars k).instantiateRevList
    (restoreFvars.map Expr.fvar) k

theorem Expr.reopenFVarsAt_eq_self_of_abstract
    (Habstract : ∀ k, e.abstractList fvars k = e)
    (Hrange : e.looseBVarRange' = 0) (k : Nat) :
    Expr.reopenFVarsAt e fvars restoreFvars k = e := by
  unfold Expr.reopenFVarsAt
  rw [Habstract]
  exact Expr.instantiateRevList'_eq_self (by omega)

theorem Expr.abstractList_eq_self_of_abstract1
    (e : Expr) (H : ∀ fv k, e.abstract1 fv k = e)
    (fvars : List FVarId) (k : Nat) :
    e.abstractList fvars k = e := by
  induction fvars with
  | nil => simp
  | cons fv fvars ih => simp [Expr.abstractList, H, ih]

theorem Expr.reopenFVarsAt_of_abstract1_eq_self
    (H : ∀ fv depth, e.abstract1 fv depth = e)
    (Hrange : e.looseBVarRange' = 0) (fvars restoreFvars : List FVarId)
    (k : Nat) : Expr.reopenFVarsAt e fvars restoreFvars k = e := by
  apply Expr.reopenFVarsAt_eq_self_of_abstract
    (fun depth => Expr.abstractList_eq_self_of_abstract1 e H fvars depth)
    Hrange

theorem Expr.reopenFVarsAt_bvar
    (hsize : restoreFvars.length = fvars.length) (i k : Nat) :
    Expr.reopenFVarsAt (.bvar i) fvars restoreFvars k = .bvar i := by
  unfold Expr.reopenFVarsAt
  by_cases hi : i < k
  · rw [Expr.abstractList_bvar_lt fvars hi]
    exact Expr.instantiateRevList_bvar_fvars_lt restoreFvars i k hi
  · obtain ⟨n, rfl⟩ : ∃ n, i = k + n := by
      exact ⟨i - k, by omega⟩
    rw [Expr.abstractList_bvar_ge]
    rw [← hsize]
    exact Expr.instantiateRevList_bvar_fvars_ge restoreFvars k n

theorem Expr.reopenFVarsAt_selected
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (i : Nat) (hi : i < fvars.length) (k : Nat) :
    Expr.reopenFVarsAt (.fvar fvars[i]) fvars restoreFvars k =
      .fvar restoreFvars[i] := by
  unfold Expr.reopenFVarsAt
  rw [Expr.abstractList_fvar_getElem hnd i hi]
  rw [← hsize]
  exact Expr.instantiateRevList_bvar_fvars_getElem restoreFvars i k
    (by omega)

theorem Expr.reopenFVarsAt_fvar_exists
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (fv : FVarId) (k : Nat) :
    ∃ restored, Expr.reopenFVarsAt (.fvar fv) fvars restoreFvars k =
      .fvar restored := by
  by_cases hfv : fv ∈ fvars
  · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
    exact ⟨restoreFvars[i], Expr.reopenFVarsAt_selected hnd hsize i hi k⟩
  · refine ⟨fv, Expr.reopenFVarsAt_eq_self_of_abstract
      (fun depth => Expr.abstractList_fvar_of_not_mem hfv)
      (by simp [Expr.looseBVarRange']) k⟩

/-- Close-and-reopen free-variable renaming is independent of the de Bruijn
depth at which the surrounding syntax traversal encounters the expression. -/
theorem Expr.reopenFVarsAt_depth_independent
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (e : Expr) (k₁ k₂ : Nat) :
    Expr.reopenFVarsAt e fvars restoreFvars k₁ =
      Expr.reopenFVarsAt e fvars restoreFvars k₂ := by
  induction e generalizing k₁ k₂ with
  | bvar i =>
    rw [Expr.reopenFVarsAt_bvar hsize,
      Expr.reopenFVarsAt_bvar hsize]
  | fvar fv =>
    by_cases hfv : fv ∈ fvars
    · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
      rw [Expr.reopenFVarsAt_selected hnd hsize i hi,
        Expr.reopenFVarsAt_selected hnd hsize i hi]
    · have habstract : ∀ k, (Expr.fvar fv).abstractList fvars k = .fvar fv := by
        intro k
        exact Expr.abstractList_fvar_of_not_mem hfv
      rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
          (by simp [Expr.looseBVarRange']) k₁,
        Expr.reopenFVarsAt_eq_self_of_abstract habstract
          (by simp [Expr.looseBVarRange']) k₂]
  | mvar id =>
    have habstract : ∀ k, (Expr.mvar id).abstractList fvars k = .mvar id := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.mvar id) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | sort u =>
    have habstract : ∀ k, (Expr.sort u).abstractList fvars k = .sort u := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.sort u) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | const name levels =>
    have habstract : ∀ k, (Expr.const name levels).abstractList fvars k =
        .const name levels := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.const name levels) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | lit literal =>
    have habstract : ∀ k, (Expr.lit literal).abstractList fvars k =
        .lit literal := by
      exact Expr.abstractList_eq_self_of_abstract1
        (.lit literal) (by intro fv k; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₁,
      Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange']) k₂]
  | app fn arg ihFn ihArg =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_app,
      Expr.instantiateRevList_app]
    change Expr.app (Expr.reopenFVarsAt fn fvars restoreFvars k₁)
        (Expr.reopenFVarsAt arg fvars restoreFvars k₁) =
      Expr.app (Expr.reopenFVarsAt fn fvars restoreFvars k₂)
        (Expr.reopenFVarsAt arg fvars restoreFvars k₂)
    rw [ihFn k₁ k₂, ihArg k₁ k₂]
  | lam name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_lam,
      Expr.instantiateRevList_lam]
    change Expr.lam name (Expr.reopenFVarsAt dom fvars restoreFvars k₁)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₁ + 1)) bi =
      Expr.lam name (Expr.reopenFVarsAt dom fvars restoreFvars k₂)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₂ + 1)) bi
    rw [ihDom k₁ k₂, ihBody (k₁ + 1) (k₂ + 1)]
  | forallE name dom body bi ihDom ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_forallE,
      Expr.instantiateRevList_forallE]
    change Expr.forallE name (Expr.reopenFVarsAt dom fvars restoreFvars k₁)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₁ + 1)) bi =
      Expr.forallE name (Expr.reopenFVarsAt dom fvars restoreFvars k₂)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₂ + 1)) bi
    rw [ihDom k₁ k₂, ihBody (k₁ + 1) (k₂ + 1)]
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_letE,
      Expr.instantiateRevList_letE]
    change Expr.letE name (Expr.reopenFVarsAt ty fvars restoreFvars k₁)
        (Expr.reopenFVarsAt value fvars restoreFvars k₁)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₁ + 1)) nondep =
      Expr.letE name (Expr.reopenFVarsAt ty fvars restoreFvars k₂)
        (Expr.reopenFVarsAt value fvars restoreFvars k₂)
        (Expr.reopenFVarsAt body fvars restoreFvars (k₂ + 1)) nondep
    rw [ihTy k₁ k₂, ihValue k₁ k₂, ihBody (k₁ + 1) (k₂ + 1)]
  | mdata md body ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_mdata,
      Expr.instantiateRevList_mdata]
    change Expr.mdata md (Expr.reopenFVarsAt body fvars restoreFvars k₁) =
      Expr.mdata md (Expr.reopenFVarsAt body fvars restoreFvars k₂)
    rw [ihBody k₁ k₂]
  | proj name idx body ihBody =>
    simp only [Expr.reopenFVarsAt, Expr.abstractList_proj,
      Expr.instantiateRevList_proj]
    change Expr.proj name idx (Expr.reopenFVarsAt body fvars restoreFvars k₁) =
      Expr.proj name idx (Expr.reopenFVarsAt body fvars restoreFvars k₂)
    rw [ihBody k₁ k₂]

/-- Constant application heads are likewise reflected by free-variable
reopening. -/
theorem Expr.getAppFn_reopenFVarsAt_eq_const
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (e : Expr) (k : Nat)
    (H : (Expr.reopenFVarsAt e fvars restoreFvars k).getAppFn =
      .const name levels) :
    e.getAppFn = .const name levels := by
  induction e generalizing k with
  | app fn arg ihFn ihArg =>
    apply ihFn
    simpa [Expr.reopenFVarsAt, Expr.getAppFn] using H
  | bvar i =>
    rw [Expr.reopenFVarsAt_bvar hsize] at H
    exact H
  | fvar fv =>
    by_cases hfv : fv ∈ fvars
    · rcases List.mem_iff_getElem.mp hfv with ⟨i, hi, rfl⟩
      rw [Expr.reopenFVarsAt_selected hnd hsize i hi] at H
      cases H
    · have habstract : ∀ depth,
          (Expr.fvar fv).abstractList fvars depth = .fvar fv := by
        intro depth
        exact Expr.abstractList_fvar_of_not_mem hfv
      rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
        (by simp [Expr.looseBVarRange'])] at H
      exact H
  | mvar id =>
    have habstract : ∀ depth,
        (Expr.mvar id).abstractList fvars depth = .mvar id := by
      exact Expr.abstractList_eq_self_of_abstract1 (.mvar id)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | sort u =>
    have habstract : ∀ depth,
        (Expr.sort u).abstractList fvars depth = .sort u := by
      exact Expr.abstractList_eq_self_of_abstract1 (.sort u)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | const sourceName sourceLevels =>
    have habstract : ∀ depth,
        (Expr.const sourceName sourceLevels).abstractList fvars depth =
          .const sourceName sourceLevels := by
      exact Expr.abstractList_eq_self_of_abstract1 (.const sourceName sourceLevels)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | lit literal =>
    have habstract : ∀ depth,
        (Expr.lit literal).abstractList fvars depth = .lit literal := by
      exact Expr.abstractList_eq_self_of_abstract1 (.lit literal)
        (by intro fv depth; simp [Expr.abstract1]) fvars
    rw [Expr.reopenFVarsAt_eq_self_of_abstract habstract
      (by simp [Expr.looseBVarRange'])] at H
    exact H
  | lam name dom body bi ihDom ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | forallE name dom body bi ihDom ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | letE name ty value body nondep ihTy ihValue ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | mdata md body ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H
  | proj typeName idx body ihBody =>
    simp [Expr.reopenFVarsAt, Expr.getAppFn] at H

/-- The implementation's array operation is the depth-zero instance of the
transparent free-variable reopening model, provided the expression has no
loose bound variables.  Without that premise the exact `Expr.abstract` leaves
loose bound variables in place while the sequential list model shifts them. -/
theorem Expr.reopenParams_eq_reopenFVarsAt
    (hnd : fvars.Nodup)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hrestore : restoreAs = (restoreFvars.map Expr.fvar).toArray)
    (hlb : e.looseBVarRange' = 0) :
    Expr.reopenParams e params restoreAs =
      Expr.reopenFVarsAt e fvars restoreFvars 0 := by
  subst params
  subst restoreAs
  simp only [Expr.reopenParams, Expr.reopenFVarsAt,
    Expr.abstract_eq_of_closed e fvars hnd hlb,
    Expr.instantiateRev_eq, Expr.instantiate_eq, Array.toList_reverse,
    Expr.instantiateList_reverse]

/-- Reopening at the depth of a syntax traversal agrees with the operational
depth-zero parameter reopening for expressions without loose bound
variables. -/
theorem Expr.reopenFVarsAt_eq_reopenParams
    (hnd : fvars.Nodup) (hsize : restoreFvars.length = fvars.length)
    (hparams : params = (fvars.map Expr.fvar).toArray)
    (hrestore : restoreAs = (restoreFvars.map Expr.fvar).toArray)
    (e : Expr) (k : Nat) (hlb : e.looseBVarRange' = 0) :
    Expr.reopenFVarsAt e fvars restoreFvars k =
      Expr.reopenParams e params restoreAs := by
  rw [Expr.reopenFVarsAt_depth_independent hnd hsize e k 0]
  exact (Expr.reopenParams_eq_reopenFVarsAt hnd hparams hrestore hlb).symm

theorem Expr.reopenFVarsAt_app (fvars restoreFvars : List FVarId) (k : Nat) :
    Expr.reopenFVarsAt (.app fn arg) fvars restoreFvars k =
      .app (Expr.reopenFVarsAt fn fvars restoreFvars k)
        (Expr.reopenFVarsAt arg fvars restoreFvars k) := by
  simp [Expr.reopenFVarsAt]

theorem Expr.reopenFVarsAt_const (fvars restoreFvars : List FVarId) (k : Nat) :
    Expr.reopenFVarsAt (.const name levels) fvars restoreFvars k =
      .const name levels :=
  Expr.reopenFVarsAt_of_abstract1_eq_self
    (by intro fv depth; simp [Expr.abstract1])
    (by simp [Expr.looseBVarRange']) fvars restoreFvars k

theorem Expr.reopenFVarsAt_mkAppList (fvars restoreFvars : List FVarId)
    (k : Nat) :
    Expr.reopenFVarsAt (Expr.mkAppList fn args) fvars restoreFvars k =
      Expr.mkAppList (Expr.reopenFVarsAt fn fvars restoreFvars k)
        (args.map fun arg => Expr.reopenFVarsAt arg fvars restoreFvars k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons arg args ih =>
    simp only [Expr.mkAppList, List.map_cons]
    rw [ih, Expr.reopenFVarsAt_app]

theorem Expr.reopenFVarsAt_of_getAppFn_const (fvars restoreFvars : List FVarId)
    (k : Nat) (hhead : input.getAppFn = .const name levels) :
    Expr.reopenFVarsAt input fvars restoreFvars k =
      Expr.mkAppList (.const name levels)
        (input.getAppArgsList.map fun arg =>
          Expr.reopenFVarsAt arg fvars restoreFvars k) := by
  calc
    Expr.reopenFVarsAt input fvars restoreFvars k =
        Expr.reopenFVarsAt
          (Expr.mkAppList input.getAppFn input.getAppArgsList)
          fvars restoreFvars k :=
      congrArg (fun e => Expr.reopenFVarsAt e fvars restoreFvars k)
        (Expr.mkAppList_getAppArgsList input).symm
    _ = Expr.mkAppList
          (Expr.reopenFVarsAt input.getAppFn fvars restoreFvars k)
          (input.getAppArgsList.map fun arg =>
            Expr.reopenFVarsAt arg fvars restoreFvars k) :=
      Expr.reopenFVarsAt_mkAppList fvars restoreFvars k
    _ = _ := by
      rw [hhead, Expr.reopenFVarsAt_const]

theorem Expr.abstractList_fvarArray_of_disjoint
    (xs binders : List FVarId) (k : Nat)
    (hdisjoint : ∀ fv, fv ∈ xs → fv ∉ binders) :
    ((xs.map Expr.fvar).toArray.map fun e => e.abstractList binders k) =
      (xs.map Expr.fvar).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    have hi : i < xs.length := by simpa using hiRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map]
    exact Expr.abstractList_fvar_of_not_mem <|
      hdisjoint xs[i] (List.getElem_mem hi)

theorem Expr.abstractN_fvarArray_of_disjoint
    (xs binders : List FVarId) (k : Nat)
    (hdisjoint : ∀ fv, fv ∈ xs → fv ∉ binders) :
    ((xs.map Expr.fvar).toArray.map fun e => e.abstractN binders k) =
      (xs.map Expr.fvar).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    have hi : i < xs.length := by simpa using hiRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_map]
    exact Expr.abstractN_fvar_of_not_mem <|
      hdisjoint xs[i] (List.getElem_mem hi)

/-- Closing one free variable does not change the head of an application
spine, except for closing that head itself. -/
theorem Expr.getAppFn_abstract1 (e : Expr) (fv : FVarId) (k : Nat := 0) :
    (e.abstract1 fv k).getAppFn = e.getAppFn.abstract1 fv k := by
  induction e generalizing k with
  | app fn arg ihFn _ =>
    simpa [Expr.abstract1, Expr.getAppFn] using ihFn k
  | bvar i => simp [Expr.abstract1, Expr.getAppFn]
  | fvar other =>
    by_cases h : (fv == other) = true <;>
      simp [Expr.abstract1, Expr.getAppFn, h]
  | mvar | sort | const | lam | forallE | letE | lit | mdata | proj =>
    simp [Expr.abstract1, Expr.getAppFn]

/-- Closing free variables does not change the head of an application spine,
except for closing that head itself. -/
theorem Expr.getAppFn_abstractList (e : Expr) (fvars : List FVarId)
    (k : Nat := 0) :
    (e.abstractList fvars k).getAppFn =
      e.getAppFn.abstractList fvars k := by
  induction fvars generalizing e with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    rw [ih]
    exact congrArg (fun head => head.abstractList fvars k)
      (Expr.getAppFn_abstract1 e fv k)

/-- Closing one free variable acts pointwise on the arguments of an
application spine and preserves their order. -/
theorem Expr.getAppArgsList_abstract1 (e : Expr) (fv : FVarId)
    (k : Nat := 0) :
    (e.abstract1 fv k).getAppArgsList =
      e.getAppArgsList.map fun arg => arg.abstract1 fv k := by
  induction e generalizing k with
  | app fn arg ihFn _ =>
    simp only [Expr.abstract1, Expr.getAppArgsList_app, ihFn,
      List.map_append, List.map_cons, List.map_nil]
  | bvar i => simp [Expr.abstract1, Expr.getAppArgsList]
  | fvar other =>
    by_cases h : (fv == other) = true <;>
      simp [Expr.abstract1, Expr.getAppArgsList, h]
  | mvar | sort | const | lam | forallE | letE | lit | mdata | proj =>
    simp [Expr.abstract1, Expr.getAppArgsList]

/-- Closing free variables acts pointwise on the arguments of an application
spine and preserves their order. -/
theorem Expr.getAppArgsList_abstractList (e : Expr)
    (fvars : List FVarId) (k : Nat := 0) :
    (e.abstractList fvars k).getAppArgsList =
      e.getAppArgsList.map fun arg => arg.abstractList fvars k := by
  induction fvars generalizing e with
  | nil => simp
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    calc
      ((e.abstract1 fv k).abstractList fvars k).getAppArgsList =
          (e.abstract1 fv k).getAppArgsList.map
            (fun arg => arg.abstractList fvars k) := ih _
      _ = (e.getAppArgsList.map fun arg => arg.abstract1 fv k).map
            (fun arg => arg.abstractList fvars k) :=
        congrArg (fun args => args.map
          (fun arg => arg.abstractList fvars k))
          (Expr.getAppArgsList_abstract1 e fv k)
      _ = e.getAppArgsList.map fun arg =>
          (arg.abstract1 fv k).abstractList fvars k := by
        simp only [List.map_map]
        apply congrArg (fun f => List.map f e.getAppArgsList)
        funext arg
        rfl

/-- Array form of `getAppArgsList_abstractList`. -/
theorem Expr.getAppArgs_abstractList (e : Expr) (fvars : List FVarId)
    (k : Nat := 0) :
    (e.abstractList fvars k).getAppArgs =
      e.getAppArgs.map fun arg => arg.abstractList fvars k := by
  apply Array.toList_inj.mp
  simp only [Expr.getAppArgs_toList, Expr.getAppArgsList_abstractList,
    Array.toList_map]

/-- Closing a free variable cannot manufacture a constant. -/
theorem Expr.abstract1_eq_const
    {e : Expr} {fv : FVarId} {k : Nat} {name : Name}
    {levels : List Level}
    (H : e.abstract1 fv k = .const name levels) :
    e = .const name levels := by
  induction e generalizing k with
  | bvar i => simp [Expr.abstract1] at H
  | fvar other =>
    by_cases h : (fv == other) = true <;> simp [Expr.abstract1, h] at H
  | mvar | sort | lit => simp [Expr.abstract1] at H
  | const => simpa [Expr.abstract1] using H
  | app | lam | forallE | letE | mdata | proj =>
    simp [Expr.abstract1] at H

/-- Iterated closing likewise reflects constant syntax. -/
theorem Expr.abstractList_eq_const
    {e : Expr} {fvars : List FVarId} {k : Nat} {name : Name}
    {levels : List Level}
    (H : e.abstractList fvars k = .const name levels) :
    e = .const name levels := by
  induction fvars generalizing e with
  | nil => exact H
  | cons fv fvars ih =>
    simp only [Expr.abstractList] at H
    exact Expr.abstract1_eq_const (ih H)

/-- A resulting free variable was already that exact free variable in the source. -/
theorem Expr.abstract1_eq_fvar
    {e : Expr} {target fv : FVarId} {k : Nat}
    (H : e.abstract1 fv k = .fvar target) :
    e = .fvar target := by
  induction e generalizing k with
  | bvar i => simp [Expr.abstract1] at H
  | fvar other =>
    by_cases h : (fv == other) = true
    · simp [Expr.abstract1, h] at H
    · simp only [Expr.abstract1, h] at H
      cases H
      rfl
  | mvar | sort | const | lit => simp [Expr.abstract1] at H
  | app | lam | forallE | letE | mdata | proj =>
    simp [Expr.abstract1] at H

/-- Reflection of a free variable through a list abstraction. -/
theorem Expr.abstractList_eq_fvar
    {e : Expr} {target : FVarId} {fvars : List FVarId} {k : Nat}
    (H : e.abstractList fvars k = .fvar target) :
    e = .fvar target := by
  induction fvars generalizing e with
  | nil => exact H
  | cons fv fvars ih =>
    simp only [Expr.abstractList] at H
    have Hinter : e.abstract1 fv k = .fvar target := ih H
    exact Expr.abstract1_eq_fvar (target := target) (fv := fv)
      Hinter

/-- Closing free variables changes leaves but never the outer expression
constructor, so in particular it cannot create or remove a leading forall. -/
@[simp] theorem Expr.abstractList_isForall
    (e : Expr) (fvars : List FVarId) (k : Nat := 0) :
    (e.abstractList fvars k).isForall = e.isForall := by
  induction fvars generalizing e k with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList]
    rw [ih]
    cases e <;> simp only [Expr.abstract1, Expr.isForall]
    case fvar fvarId =>
      by_cases h : (fv == fvarId) = true
      · rw [if_pos h]
      · rw [if_neg h]

theorem Expr.abstractN_indexBVars
    (binders : List FVarId) (n k : Nat) (_hk : n < k) :
    ((List.ofFn fun i : Fin n =>
        Expr.bvar (1 + (n - 1 - i))).toArray.map
      fun e => e.abstractN binders k) =
    (List.ofFn fun i : Fin n =>
      Expr.bvar (1 + (n - 1 - i))).toArray := by
  apply Array.ext
  · simp
  · intro i hiLeft hiRight
    simp only [Array.getElem_map, List.getElem_toArray, List.getElem_ofFn]
    rfl

/-- An expression with a forall binder is a forall, so stripping a top-level type
annotation leaves it unchanged. -/
theorem Expr.ForallBinderAt.consumeTypeAnnotationsVerified_eq_self
    (H : Expr.ForallBinderAt source i domain) :
    (source.consumeTypeAnnotationsVerified annOk) = source := by
  cases H with
  | here => apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl
  | there _ => apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl

/-- Simultaneous free-variable abstraction raises a closed loose-variable
boundary by exactly the number of introduced binders. -/
theorem Expr.abstractN_looseBVarRange_le
    {e : Expr} {fvs : List FVarId} {k : Nat}
    : (e.abstractN fvs k).looseBVarRange' ≤
        max k e.looseBVarRange' + fvs.length := by
  induction e generalizing k with
  | bvar i => simp [Expr.abstractN, Expr.looseBVarRange']; omega
  | fvar v =>
    simp only [Expr.abstractN]
    split
    · rename_i r hr
      have := Expr.lastRevIdx?_lt_length hr
      simp [Expr.looseBVarRange']; omega
    · simp [Expr.looseBVarRange']
  | mdata _ e ih | proj _ _ e ih => simpa [Expr.abstractN, Expr.looseBVarRange'] using ih
  | app f a ihf iha =>
    simp only [Expr.abstractN, Expr.looseBVarRange', Nat.max_le]
    constructor <;> [have := @ihf k; have := @iha k] <;> omega
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    simp only [Expr.abstractN, Expr.looseBVarRange', Nat.max_le]
    have h1 := @iht k; have h2 := @ihb (k + 1)
    constructor <;> omega
  | letE _ t v b _ iht ihv ihb =>
    simp only [Expr.abstractN, Expr.looseBVarRange', Nat.max_le]
    have h1 := @iht k; have h2 := @ihv k; have h3 := @ihb (k + 1)
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  | const _ _ | sort _ | mvar _ | lit _ => simp [Expr.abstractN, Expr.looseBVarRange']

/-- Application spines preserve a common loose-variable bound. -/
theorem Expr.mkAppN_looseBVarRange_le
    (Hfn : fn.looseBVarRange' ≤ k)
  (Hargs : ∀ arg ∈ args, arg.looseBVarRange' ≤ k) :
    (mkAppN fn args).looseBVarRange' ≤ k := by
  unfold mkAppN
  rw [← Array.foldl_toList]
  have Hlist : ∀ arg ∈ args.toList, arg.looseBVarRange' ≤ k := by
    intro arg harg
    exact Hargs arg (Array.mem_toList_iff.mp harg)
  generalize args.toList = list at Hlist
  induction list generalizing fn with
  | nil => exact Hfn
  | cons arg rest ih =>
      simp only [List.foldl_cons]
      apply ih
      · simpa [Lean.Expr.looseBVarRange', Nat.max_le] using
          And.intro Hfn (Hlist arg (by simp))
      · intro other hother
        exact Hlist other (by simp [hother])

@[simp] theorem Expr.instantiate1'_mkAppN :
    (mkAppN fn args).instantiate1' value k =
      mkAppN (fn.instantiate1' value k)
        (args.map fun arg => arg.instantiate1' value k) := by
  unfold mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  rw [Array.toList_map]
  generalize args.toList = list
  induction list generalizing fn with
  | nil => rfl
  | cons arg rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      exact ih (fn := fn.app arg)

theorem Expr.ForallTelescope.consumeTypeAnnotationsVerified_eq_self_of_pos
    (H : Expr.ForallTelescope outer arity body) (hpos : 0 < arity) :
    (outer.consumeTypeAnnotationsVerified annOk) = outer := by
  cases H with
  | nil => simp at hpos
  | cons _ => apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl

/-- Removing a possible top-level binder annotation preserves the number of
leading forall binders.  In the zero-binder case the residual may itself be
the annotation payload, so it is retained existentially. -/
theorem Expr.ForallTelescope.consumeTypeAnnotationsVerified_arity
    (H : Expr.ForallTelescope outer arity body) :
    ∃ residual, Expr.ForallTelescope (outer.consumeTypeAnnotationsVerified annOk)
      arity residual := by
  cases H with
  | nil => exact ⟨_, .nil _⟩
  | @cons body arity result name dom bi Htail =>
      have houter :
          ((Expr.forallE name dom body bi).consumeTypeAnnotationsVerified annOk) =
            Expr.forallE name dom body bi := by
        apply Expr.consumeTypeAnnotationsVerified_eq_self <;> rfl
      exact ⟨_, houter ▸ Expr.ForallTelescope.cons Htail⟩

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

@[simp] theorem Expr.levelParamsIn_instantiate1_fvar (e : Expr) (fv : FVarId) (k : Nat) :
    (e.instantiate1' (.fvar fv) k).levelParamsIn params = e.levelParamsIn params := by
  induction e generalizing k <;> simp [Expr.instantiate1', Expr.levelParamsIn, *]
  case bvar i =>
    split
    · rfl
    · split <;> rfl

theorem Expr.levelParamsIn_consumeTypeAnnotationsVerified {e : Expr}
    (H : e.levelParamsIn params = true) : (e.consumeTypeAnnotationsVerified annOk).levelParamsIn params = true := by
  fun_induction Expr.consumeTypeAnnotationsVerified _ e
  all_goals simp_all [Expr.levelParamsIn]

/-- Strip the type annotations from every domain of a forall telescope. This is the closed
syntax obtained by reopening its binders with unannotated local declaration types. -/
def Expr.consumeForallTypes (ok : Name → Bool) : Expr → Expr
  | .forallE name domain body bi =>
    .forallE name (domain.consumeTypeAnnotationsVerified ok) (Expr.consumeForallTypes ok body) bi
  | source => source

namespace VerifyInductive

theorem Expr.getAppArgs_slice_toList (e : Expr) (n : Nat) :
    ((e.getAppArgs[n:] : Array Expr)).toList = e.getAppArgsList.drop n := by
  rw [← Expr.getAppArgs_toList]
  let suffix := e.getAppArgs.toSubarray n
  calc
    (Std.Slice.toArray suffix).toList = suffix.toList := by
      exact (congrArg Array.toList
        (Subarray.toArray_eq_sliceToArray (s := suffix)).symm).trans
          Subarray.toList_toArray
    _ = e.getAppArgs.toList.drop n := by
      rw [List.drop_eq_drop_min]
      simp only [suffix, Subarray.toList_eq, Array.array_toSubarray,
        Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
        Array.toList_extract, List.extract_eq_take_drop,
        Array.length_toList]
      apply List.take_of_length_le
      simp

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

theorem Expr.ForallTelescope.inferImplicit
    (H : Expr.ForallTelescope e arity residual)
    (max : Nat) (inferBinderTypes : Bool) :
    ∃ residual',
      Expr.ForallTelescope (e.inferImplicit max inferBinderTypes) arity
        residual' := by
  induction max generalizing e arity residual with
  | zero => exact ⟨residual, by simpa [Expr.inferImplicit] using H⟩
  | succ max ih =>
    cases H with
    | nil => exact ⟨_, .nil _⟩
    | cons Htail =>
      rcases ih Htail with ⟨residual', Htail'⟩
      exact ⟨residual', by
        simp only [Expr.inferImplicit]
        exact Expr.ForallTelescope.cons Htail'⟩

/-- `inferImplicit` changes binder annotations only, so the terminal
expression of a forall telescope is preserved literally. -/
theorem Expr.ForallTelescope.inferImplicit_sameResidual
    (H : Expr.ForallTelescope e arity residual)
    (Hresidual : residual.isForall = false)
    (max : Nat) (inferBinderTypes : Bool) :
    Expr.ForallTelescope (e.inferImplicit max inferBinderTypes) arity
      residual := by
  induction max generalizing e arity residual with
  | zero => simpa [Expr.inferImplicit] using H
  | succ max ih =>
    cases H with
    | nil =>
      have heq : e.inferImplicit (max + 1) inferBinderTypes = e := by
        cases e <;> simp_all [Expr.inferImplicit, Expr.isForall]
      rw [heq]
      exact .nil _
    | cons Htail =>
      simp only [Expr.inferImplicit]
      exact Expr.ForallTelescope.cons (ih Htail Hresidual)

end VerifyInductive

end Lean4Lean

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

theorem Expr.consumeTypeAnnotationsVerified_eq_of_head {ok : Name → Bool} {e : Expr}
    (hhead : e.getAppFn = .const name levels) (hok : ok name = false) :
    (e.consumeTypeAnnotationsVerified ok) = e := by
  fun_induction Expr.consumeTypeAnnotationsVerified ok e
  case case1 n ls first second hannotation ih =>
    have hname : n = name := by simpa [Expr.getAppFn, Expr.constName!] using congrArg Expr.constName! hhead
    subst n
    simp [hok] at hannotation
  case case3 n ls arg hannotation ih =>
    have hname : n = name := by simpa [Expr.getAppFn, Expr.constName!] using congrArg Expr.constName! hhead
    subst n
    simp [hok] at hannotation
  all_goals rfl

theorem Expr.abstractList_fullApp
    (fvars : List FVarId) (hnd : fvars.Nodup) (name : Name) (levels : List Level) :
    (mkAppN (.const name levels) (fvars.map Expr.fvar).toArray).abstractList fvars =
      Expr.mkAppList (.const name levels)
        (List.ofFn fun i : Fin fvars.length => Expr.bvar (fvars.length - 1 - i)) := by
  rw [Expr.abstractList_mkAppN, Expr.abstractList_const,
    Expr.abstractList_fvarArray fvars 0 hnd, Expr.mkAppN_eq_mkAppList]
  simp

/-- The first `n` forall binders of an expression, closed with `Prop` in place of the residual.
Applied to a motive type it drops the major and the elimination sort, so that the index
domains can be read in the source universes. -/
def Expr.forallDomainsOnly : Nat → Expr → Expr
  | 0, _ => .sort .zero
  | n + 1, .forallE name domain body bi =>
      .forallE name domain (forallDomainsOnly n body) bi
  | _, _ => .sort .zero

theorem Expr.ForallTelescope.domainsOnly
    (H : Expr.ForallTelescope source n residual) :
    Expr.ForallTelescope (Expr.forallDomainsOnly n source) n (.sort .zero) := by
  induction H with
  | nil => exact .nil _
  | cons H ih => exact .cons ih

theorem Expr.forallDomainsOnly_abstract1 (n : Nat) (source : Expr) (fv : FVarId) (k : Nat) :
    Expr.forallDomainsOnly n (source.abstract1 fv k) =
      (Expr.forallDomainsOnly n source).abstract1 fv k := by
  induction n generalizing source k with
  | zero => rfl
  | succ n ih =>
    cases source <;> simp [Expr.forallDomainsOnly, Expr.abstract1, ih]
    all_goals split <;> rfl

theorem Expr.forallDomainsOnly_abstractList (n : Nat) (source : Expr)
    (fvars : List FVarId) (k : Nat := 0) :
    Expr.forallDomainsOnly n (source.abstractList fvars k) =
      (Expr.forallDomainsOnly n source).abstractList fvars k := by
  induction fvars generalizing source k with
  | nil => rfl
  | cons fv fvars ih =>
    simp only [Expr.abstractList, ih, Expr.forallDomainsOnly_abstract1]

theorem Expr.forallDomainsOnly_abstractN (n : Nat) (source : Expr) (xs : List FVarId) (k : Nat) :
    Expr.forallDomainsOnly n (source.abstractN xs k) =
      (Expr.forallDomainsOnly n source).abstractN xs k := by
  induction n generalizing source k with
  | zero => rfl
  | succ n ih =>
    cases source <;> simp [Expr.forallDomainsOnly, Expr.abstractN, ih]
    all_goals split <;> rfl

end Lean4Lean.VerifyInductive

namespace Lean4Lean

theorem _root_.Lean.Expr.liftLooseBVars'_liftLooseBVars' (e : Lean.Expr) (k d₁ d₂ : Nat) :
    (e.liftLooseBVars' k d₁).liftLooseBVars' k d₂ = e.liftLooseBVars' k (d₁ + d₂) := by
  induction e generalizing k <;> simp_all [Lean.Expr.liftLooseBVars']
  split <;> (try split) <;> omega

end Lean4Lean

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The first `n` binders of `consumed` are those of `raw` with each domain unannotated
(`consumeTypeAnnotationsVerified`); the bodies after the `n`-th binder are unrelated. -/
inductive Expr.UnannotatedForallPrefix (ok : Name → Bool) : Nat → Lean.Expr → Lean.Expr → Prop
  | zero (raw consumed : Lean.Expr) : UnannotatedForallPrefix ok 0 raw consumed
  | succ : UnannotatedForallPrefix ok n body body' →
      UnannotatedForallPrefix ok (n + 1) (.forallE name dom body bi)
        (.forallE name' (dom.consumeTypeAnnotationsVerified ok) body' bi')

/-- Removing the type annotations of a telescope's domains (`consumeForallTypes`) and keeping
only its first `n` domains gives an unannotated prefix of the telescope. -/
theorem Expr.ForallTelescope.unannotatedForallPrefix
    (H : Expr.ForallTelescope raw n residual) :
    Expr.UnannotatedForallPrefix ok n raw
      (Expr.forallDomainsOnly n (Lean4Lean.Expr.consumeForallTypes ok raw)) := by
  induction H with
  | nil => exact .zero _ _
  | cons _ ih => exact .succ ih

/-- Closing a list of distinct free variables over itself yields the descending de Bruijn spine
above the abstraction depth. -/
theorem Expr.abstractList_fvar_spine (fvs : List FVarId) (hnd : fvs.Nodup) (k : Nat) :
    (fvs.map Expr.fvar).map (fun e => e.abstractList fvs k) =
      List.ofFn fun j : Fin fvs.length => Expr.bvar (k + (fvs.length - 1 - j)) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < fvs.length := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractList_fvar_getElem hnd i hi

/-- Closing a prefix of distinct free variables over a longer distinct list
places each at its descending position above the trailing variables. -/
theorem Expr.abstractList_fvar_prefix_spine (fvs rest : List FVarId)
    (hnd : (fvs ++ rest).Nodup) (k : Nat) :
    (fvs.map Expr.fvar).map (fun e => e.abstractList (fvs ++ rest) k) =
      List.ofFn fun j : Fin fvs.length => Expr.bvar ((k + rest.length) + (fvs.length - 1 - j)) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < fvs.length := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn]
    have h := Expr.abstractList_fvar_getElem hnd (fvs := fvs ++ rest) i (by simp; omega) (k := k)
    rw [List.getElem_append_left hi] at h
    rw [h]
    congr 1
    simp only [List.length_append]
    omega

/-- Bound variables below the abstraction depth are untouched. -/
theorem Expr.abstractList_bvar_spine (n below : Nat) (fvs : List FVarId) (k : Nat)
    (h : below + n ≤ k) :
    (List.ofFn fun j : Fin n => Expr.bvar (below + (n - 1 - j))).map
        (fun e => e.abstractList fvs k) =
      List.ofFn fun j : Fin n => Expr.bvar (below + (n - 1 - j)) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractList_bvar_lt fvs (by omega)

theorem Expr.abstractList_mkAppList_depth (head : Expr) (args : List Expr)
    (fvars : List FVarId) (depth : Nat) :
    (Expr.mkAppList head args).abstractList fvars depth =
      Expr.mkAppList (head.abstractList fvars depth)
        (args.map fun arg => arg.abstractList fvars depth) := by
  induction args generalizing head with
  | nil => rfl
  | cons arg args ih =>
    simpa only [Expr.mkAppList, List.map_cons, Expr.abstractList_app] using ih (.app head arg)

theorem Expr.liftLooseBVars'_mkAppList (head : Expr) (args : List Expr) (start amount : Nat) :
    (Expr.mkAppList head args).liftLooseBVars' start amount =
      Expr.mkAppList (head.liftLooseBVars' start amount)
        (args.map fun arg => arg.liftLooseBVars' start amount) := by
  induction args generalizing head with
  | nil => rfl
  | cons arg args ih =>
    simpa only [Expr.mkAppList, List.map_cons, Expr.liftLooseBVars'] using ih (.app head arg)

/-- The first `n` binder domains of a forall telescope, exactly as they sit in
the expression: the `i`-th domain still carries loose bound variables
`0, …, i - 1` for the `i` binders before it. -/
def Expr.forallDomainList : Nat → Expr → List Expr
  | 0, _ => []
  | n + 1, .forallE _ domain body _ => domain :: forallDomainList n body
  | _, _ => []

theorem Expr.ForallTelescope.forallDomainList_length
    (H : Expr.ForallTelescope source n residual) :
    (Expr.forallDomainList n source).length = n := by
  induction H with
  | nil => simp [Expr.forallDomainList]
  | cons _ ih => simp [Expr.forallDomainList, ih]

/-- Abstracting free variables of a forall telescope abstracts its `i`-th
literal domain at cutoff advanced by the `i` binders before it. -/
theorem Expr.ForallTelescope.forallDomainList_abstractList
    (H : Expr.ForallTelescope source n residual) (fvs : List FVarId) (k : Nat)
    {i : Nat} (hi : i < n) :
    (Expr.forallDomainList n (source.abstractList fvs k))[i]! =
      (Expr.forallDomainList n source)[i]!.abstractList fvs (k + i) := by
  induction H generalizing k i with
  | nil => omega
  | cons _ ih =>
    rw [Expr.abstractList_forallE]
    cases i with
    | zero => simp [Expr.forallDomainList]
    | succ i =>
      simp only [Expr.forallDomainList, List.getElem!_cons_succ]
      rw [ih (k + 1) (by omega)]
      congr 1
      omega

/-- `abstract1` is injective: loose bound variables below the cutoff are
fixed, those at or above it are shifted by one, and only the abstracted variable becomes the
cutoff itself. -/
theorem Expr.abstract1_injective {v : FVarId} :
    ∀ {e e' : Expr} {k : Nat}, e.abstract1 v k = e'.abstract1 v k → e = e' := by
  intro e
  induction e with
  | bvar i =>
    intro e' k h
    cases e' with
    | bvar i' =>
      simp only [Expr.abstract1, Expr.bvar.injEq] at h
      congr 1; split at h <;> split at h <;> omega
    | fvar w =>
      simp only [Expr.abstract1] at h
      by_cases hw : v = w
      · subst hw; simp at h; split at h <;> omega
      · simp [hw] at h
    | _ => simp [Expr.abstract1] at h
  | fvar u =>
    intro e' k h
    cases e' with
    | bvar i' =>
      simp only [Expr.abstract1] at h
      by_cases hu : v = u
      · subst hu; simp at h; split at h <;> omega
      · simp [hu] at h
    | fvar w =>
      simp only [Expr.abstract1] at h
      by_cases hu : v = u <;> by_cases hw : v = w <;> simp_all
    | _ =>
      simp only [Expr.abstract1] at h
      by_cases hu : v = u <;> simp [hu] at h
  | app f a ihf iha =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [ihf h.1, iha h.2]
  | lam n t b bi iht ihb =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, iht h.2.1, ihb h.2.2.1, h.2.2.2]
  | forallE n t b bi iht ihb =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, iht h.2.1, ihb h.2.2.1, h.2.2.2]
  | letE n t val b nd iht ihv ihb =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, iht h.2.1, ihv h.2.2.1, ihb h.2.2.2.1, h.2.2.2.2]
  | mdata m b ih =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, ih h.2]
  | proj s i b ih =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try (split at h <;> simp at h))
    rw [h.1, h.2.1, ih h.2.2]
  | _ =>
    intro e' k h
    cases e' <;> simp [Expr.abstract1] at h <;> (try split at h) <;> simp_all

theorem Expr.abstractList_injective :
    ∀ {xs : List FVarId} {e e' : Expr} {k : Nat},
      e.abstractList xs k = e'.abstractList xs k → e = e'
  | [], _, _, _, h => by simpa using h
  | _ :: _, _, _, _, h => Expr.abstract1_injective (Expr.abstractList_injective h)

theorem Expr.forallDomainList_forallDomainsOnly :
    ∀ (n : Nat) (e : Expr), Expr.forallDomainList n (Expr.forallDomainsOnly n e) =
      Expr.forallDomainList n e
  | 0, _ => rfl
  | n + 1, e => by
    cases e <;> simp [Expr.forallDomainsOnly, Expr.forallDomainList,
      Expr.forallDomainList_forallDomainsOnly n]

theorem Expr.forallDomainList_fvarsIn {P : FVarId → Prop} :
    ∀ (n : Nat) {e : Expr}, FVarsIn P e → ∀ d ∈ Expr.forallDomainList n e, FVarsIn P d
  | 0, _, _ => by simp [Expr.forallDomainList]
  | n + 1, e, h => by
    cases e with
    | forallE name dom body bi =>
      intro d hd
      simp only [Expr.forallDomainList, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact h.1
      · exact Expr.forallDomainList_fvarsIn n h.2 d hd
    | _ => simp [Expr.forallDomainList]

theorem Expr.forallDomainList_levelParamsIn {Us : List Name} :
    ∀ (n : Nat) {e : Expr}, e.levelParamsIn Us = true →
      ∀ d ∈ Expr.forallDomainList n e, d.levelParamsIn Us = true
  | 0, _, _ => by simp [Expr.forallDomainList]
  | n + 1, e, h => by
    cases e with
    | forallE name dom body bi =>
      simp only [Expr.levelParamsIn, Bool.and_eq_true] at h
      intro d hd
      simp only [Expr.forallDomainList, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact h.1
      · exact Expr.forallDomainList_levelParamsIn n h.2 d hd
    | _ => simp [Expr.forallDomainList]

end Lean4Lean.VerifyInductive

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open scoped _root_.List
open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Instantiating an abstracted free variable with itself restores the
expression. -/
theorem Expr.instantiate1'_abstract1_self (v : FVarId) :
    ∀ (e : Expr) (k : Nat), (e.abstract1 v k).instantiate1' (.fvar v) k = e
  | .bvar i, k => by
    simp only [Expr.abstract1, Expr.instantiate1']
    by_cases h : i < k
    · simp [h]
    · have h1 : ¬ i + 1 < k := by omega
      have h2 : i + 1 ≠ k := by omega
      simp [h, h1, h2]
  | .fvar w, k => by
    by_cases h : v = w
    · subst h
      simp [Expr.abstract1, Expr.instantiate1', Expr.liftLooseBVars']
    · have : (v == w) = false := by simpa using h
      simp [Expr.abstract1, Expr.instantiate1', this]
  | .mdata m e, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v e k]
  | .proj s i e, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v e k]
  | .app f a, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v f k,
      Expr.instantiate1'_abstract1_self v a k]
  | .lam n t b bi, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v t k,
      Expr.instantiate1'_abstract1_self v b (k + 1)]
  | .forallE n t b bi, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v t k,
      Expr.instantiate1'_abstract1_self v b (k + 1)]
  | .letE n t val b bi, k => by
    simp [Expr.abstract1, Expr.instantiate1', Expr.instantiate1'_abstract1_self v t k,
      Expr.instantiate1'_abstract1_self v val k,
      Expr.instantiate1'_abstract1_self v b (k + 1)]
  | .const .., _ | .sort _, _ | .mvar _, _ | .lit _, _ => by
    simp [Expr.abstract1, Expr.instantiate1']

theorem Expr.closed_mkAppList_fvars {f : Expr} (hf : Closed f) :
    ∀ (fvs : List FVarId), Closed (Expr.mkAppList f (fvs.map Expr.fvar))
  | [] => hf
  | fv :: fvs => by
    simp only [List.map_cons, Expr.mkAppList]
    exact Expr.closed_mkAppList_fvars (f := .app f (.fvar fv)) ⟨hf, trivial⟩ fvs

end VerifyInductive

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open VerifyInductive

theorem Expr.abstractN_mkAppList (fn : Lean.Expr) (args : List Lean.Expr) (xs : List FVarId)
    (k : Nat) :
    (Lean.Expr.mkAppList fn args).abstractN xs k =
      Lean.Expr.mkAppList (fn.abstractN xs k) (args.map fun a => a.abstractN xs k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons a l ih => simp only [Lean.Expr.mkAppList, ih, List.map_cons]; rfl

theorem Expr.instantiate1'_mkAppList (fn : Lean.Expr) (args : List Lean.Expr) (v : Lean.Expr)
    (k : Nat) :
    (Lean.Expr.mkAppList fn args).instantiate1' v k =
      Lean.Expr.mkAppList (fn.instantiate1' v k) (args.map fun a => a.instantiate1' v k) := by
  induction args generalizing fn with
  | nil => rfl
  | cons a l ih => simp only [Lean.Expr.mkAppList, ih, List.map_cons]; rfl

theorem Expr.closed_mkAppList {fn : Lean.Expr} {args : List Lean.Expr} {k : Nat}
    (hfn : Closed fn k) (hargs : ∀ a ∈ args, Closed a k) :
    Closed (Lean.Expr.mkAppList fn args) k := by
  induction args generalizing fn with
  | nil => exact hfn
  | cons a l ih =>
    exact ih ⟨hfn, hargs a (by simp)⟩ (fun b hb => hargs b (by simp [hb]))

/-- Abstracting a duplicate-free list of variables in its own order yields the
canonical descending bound-variable spine. -/
theorem Expr.abstractN_fvars_spine {xs : List FVarId} (hnd : xs.Nodup) (k : Nat) :
    (xs.map Lean.Expr.fvar).map (fun a => a.abstractN xs k) =
      (List.range xs.length).reverse.map fun i => Lean.Expr.bvar (k + i) := by
  apply List.ext_getElem
  · simp
  · intro l h1 h2
    simp only [List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range]
    simp only [List.length_map] at h1
    rw [Expr.abstractN_fvar_getElem hnd l h1]

theorem VerifyInductive.Expr.SameForallLambdaPrefix.instantiate1'
    (H : Expr.SameForallLambdaPrefix n forallBody lambdaBody) (v : Lean.Expr) (k : Nat) :
    Expr.SameForallLambdaPrefix n
      (forallBody.instantiate1' v k) (lambdaBody.instantiate1' v k) := by
  induction H generalizing k with
  | nil => exact .nil
  | cons H ih =>
    simp only [Lean.Expr.instantiate1']
    exact .cons (ih (k + 1))

theorem VerifyInductive.Expr.ForallTelescope.forallDomainList_abstractN
    (H : Expr.ForallTelescope source n residual) (fvs : List FVarId) (k : Nat)
    {i : Nat} (hi : i < n) :
    (Expr.forallDomainList n (source.abstractN fvs k))[i]! =
      (Expr.forallDomainList n source)[i]!.abstractN fvs (k + i) := by
  induction H generalizing k i with
  | nil => omega
  | cons _ ih =>
    simp only [Lean.Expr.abstractN]
    cases i with
    | zero => simp [Expr.forallDomainList]
    | succ i =>
      simp only [Expr.forallDomainList, List.getElem!_cons_succ]
      rw [ih (k + 1) (by omega)]
      congr 1
      omega

/-- A forall telescope with closed residual whose `i`-th domain is closed at
depth `k + i` is closed at depth `k`. -/
theorem VerifyInductive.Expr.ForallTelescope.closed_of_domains
    (H : Expr.ForallTelescope source n residual) (k : Nat)
    (hdom : ∀ i < n, Closed (Expr.forallDomainList n source)[i]! (k + i))
    (hres : Closed residual (k + n)) : Closed source k := by
  induction H generalizing k with
  | nil => simpa using hres
  | @cons body arity result name dom bi Htel ih =>
    refine ⟨?_, ih (k + 1) ?_ ?_⟩
    · simpa [Expr.forallDomainList] using hdom 0 (by omega)
    · intro i hi
      have := hdom (i + 1) (by omega)
      simpa [Expr.forallDomainList, Nat.add_assoc, Nat.add_comm 1] using this
    · simpa [Nat.add_assoc, Nat.add_comm 1] using hres

end Lean4Lean
