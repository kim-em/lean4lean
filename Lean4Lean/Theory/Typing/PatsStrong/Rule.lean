import Lean4Lean.Theory.Typing.PatsStrong.Spec

/-! # The per-rule argument: `PatStrong` of an ι rule from its generic strong typing

PORT_PLAN §4.3 splits the argument into (i) spine inversion of the redex, (ii) alignment of the
constructor's parameters/indices/levels with the recursor's through uniqueness and head
inversion, (iii) instantiation of the generic rule by the actual arguments, (iv) conversion to
the redex's type. This file proves (iii) and (iv) (`IotaRuleData.patStrong`) from a precise
statement of what (i)–(ii) deliver (`IotaRuleData.Aligned`, produced by the stub
`IotaRuleData.align`) and strong uniqueness of typing (stub `HasTypeStrong.uniqS`). Both stubs
take `StrongHeadInversion env` and nothing about `PatsStrongOn env`.

Everything here assumes `Ordered env` only where #43 would assume `OrderedStrong env`: the
substitution is `IsDefEqStrong.instOuter_telescope` (one `instN` per argument), never
`substEq'`. -/

namespace Lean4Lean

open VExpr

/-! ## Pattern plumbing -/

/-- `Pattern.varN_pathOf` at the last argument. -/
theorem Pattern.varN_pathOf_succ_eq {q : Pattern} {n : Nat} (hi : n < n+1) :
    (Pattern.varN_pathOf (q := q) (n+1) n hi : Option (q.varN n).Path) = none := by
  have h : (dite (n = n) (fun _ => (none : Option (q.varN n).Path))
      (fun h => some (Pattern.varN_pathOf n n (by omega)))) = none := dif_pos rfl
  exact h

/-- `Pattern.varN_pathOf` at an earlier argument. -/
theorem Pattern.varN_pathOf_succ_ne {q : Pattern} {n i : Nat} (hi : i < n+1) (hik : ¬ i = n) :
    (Pattern.varN_pathOf (q := q) (n+1) i hi : Option (q.varN n).Path) =
      some (Pattern.varN_pathOf n i (by omega)) := by
  have h : (dite (i = n) (fun _ => (none : Option (q.varN n).Path))
      (fun _ => some (Pattern.varN_pathOf n i (by omega)))) =
      some (Pattern.varN_pathOf n i (by omega)) := dif_neg hik
  exact h

/-- Inverse of `Pattern.matches_varN_const`: a match of the spine pattern `(const c).varN n`
is a constant applied to `n` arguments, the hole of argument `i` holding that argument. -/
theorem Pattern.matches_varN_const_inv {c : Name} : ∀ {n : Nat} {e : VExpr} {ls : List VLevel}
    {g : ((Pattern.const c).varN n).Path → VExpr},
    ((Pattern.const c).varN n).Matches e ls g →
    ∃ (args : List VExpr) (h : args.length = n), e = (VExpr.const c ls).mkApps args ∧
      ∀ i (hi : i < n), g (Pattern.varN_pathOf n i hi) = args[i]'(h ▸ hi)
  | 0, e, ls, g, h => by
    cases h
    exact ⟨[], rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | n+1, e, ls, g, h => by
    cases h with
    | @var _ f' _ g1 a' h1 =>
      obtain ⟨args, hlen, rfl, hg⟩ := matches_varN_const_inv h1
      refine ⟨args ++ [a'], by simp [hlen], by simp [VExpr.mkApps_append], fun i hi => ?_⟩
      by_cases hik : i = n
      · subst hik
        rw [Pattern.varN_pathOf_succ_eq]
        simp [hlen]
      · rw [Pattern.varN_pathOf_succ_ne hi hik]
        simp only [Option.elim]
        rw [hg i (by omega), List.getElem_append_left (by omega)]

theorem VExpr.instL_mkApps (f : VExpr) (l : List VExpr) (ls : List VLevel) :
    (f.mkApps l).instL ls = (f.instL ls).mkApps (l.map (·.instL ls)) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih => simp [VExpr.mkApps_cons, ih, VExpr.instL]

theorem VExpr.instL_bvarsDesc (lo n : Nat) (ls : List VLevel) :
    (VExpr.bvarsDesc lo n).map (·.instL ls) = VExpr.bvarsDesc lo n := by
  simp [VExpr.bvarsDesc, List.map_map, Function.comp_def, VExpr.instL]

namespace VEnv

variable {env : VEnv} {U : Nat}

/-! ## Context lemmas in the strong system -/

theorem CtxStrong.instL {ls : List VLevel} {U' : Nat} (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {Γ : List VExpr}, CtxStrong env U Γ → CtxStrong env U' (Γ.map (VExpr.instL ls))
  | [], _ => trivial
  | _ :: Γ, ⟨h, _, hA⟩ => ⟨CtxStrong.instL hls h, _, hA.instL hls⟩

/-- A strong context over the empty context is a strong context over any strong `Γ`: its
entries are closed at their depth and weaken by `Ctx.LiftN.right`. -/
theorem CtxStrong.append_closed (henv : Ordered env) {Γ : List VExpr} (hΓ : CtxStrong env U Γ) :
    ∀ {Δ : List VExpr}, CtxStrong env U Δ → CtxStrong env U (Δ ++ Γ)
  | [], _ => hΓ
  | A :: Δ, ⟨h, u, hA⟩ => by
    have hcl : CtxClosed Δ := CtxWF.closed henv (CtxStrong.defeq h)
    have hAcl : A.ClosedN Δ.length := hA.defeq.closedN henv hcl
    have := hA.weakN henv (Ctx.LiftN.right hcl Γ)
    rw [hAcl.liftN_eq (Nat.le_refl _)] at this
    show CtxStrong env U (A :: (Δ ++ Γ))
    exact ⟨CtxStrong.append_closed henv hΓ h, u, this⟩

/-- A strong judgement over the empty context weakens to any strong `Γ` below its context. -/
theorem IsDefEqStrong.weak_below (henv : Ordered env) {Δ : List VExpr} {e₁ e₂ A : VExpr}
    (hΔ : CtxStrong env U Δ) (H : env.IsDefEqStrong U Δ e₁ e₂ A) (Γ : List VExpr) :
    env.IsDefEqStrong U (Δ ++ Γ) e₁ e₂ A := by
  have hcl : CtxClosed Δ := CtxWF.closed henv hΔ.defeq
  have ⟨h1, h2, h3⟩ := H.defeq.closedN' henv.closed hcl
  have := H.weakN henv (Ctx.LiftN.right hcl Γ)
  rwa [h1.liftN_eq (Nat.le_refl _), h2.liftN_eq (Nat.le_refl _), h3.liftN_eq (Nat.le_refl _)] at this

/-! ## Stubs: steps (i)–(ii) -/

/-- **STUB** (wave 1D, derivable from `StrongHeadInversion`): uniqueness of typing in the strong
system. Two strong typings of one term have strongly equal types. On the branch this is
`HasTypeStrong.uniq_chain_of_chainHeadInjectivity` (a chain, by induction on `HasTypeStrong`:
the `base` cases are syntax-directed, `app` uses `forallE_forallE`, the `defeq` case extends
the chain) followed by `TypeChain.collapse_of_chainHeadInjectivity` (the chain's sort levels
are reconciled by `sort_sort`). Needs `Ordered env` and `StrongHeadInversion env` only. -/
theorem HasTypeStrong.uniqS (_henv : Ordered env) (_hshi : StrongHeadInversion env)
    {Γ : List VExpr} {e A B : VExpr} (_hΓ : CtxStrong env U Γ)
    (_h1 : env.HasTypeStrong U Γ e A true) (_h2 : env.HasTypeStrong U Γ e B true) :
    ∃ u, env.IsDefEqStrong U Γ A B (.sort u) := sorry

namespace IotaRuleData

/-- The redex of an ι rule: recursor at `us` applied to `pre` (parameters, motives, minors,
indices) and to the constructor at `cus` applied to `cargs` (parameters, fields). -/
def redex (D : IotaRuleData) (us cus : List VLevel) (pre cargs : List VExpr) : VExpr :=
  (VExpr.const D.recName us).mkApps (pre ++ [(VExpr.const D.ctorName cus).mkApps cargs])

/-- The actual arguments of the rule's holes: the recursor's parameters/motives/minors and the
constructor's fields. -/
def args (D : IotaRuleData) (pre cargs : List VExpr) : List VExpr :=
  pre.take D.k ++ cargs.drop D.np

theorem args_length (D : IotaRuleData) {pre cargs : List VExpr}
    (hpre : pre.length = D.k + D.nind) (hcargs : cargs.length = D.np + D.nf) :
    (D.args pre cargs).length = D.k + D.nf := by
  simp [args, hpre, hcargs]

/-- **What steps (i)–(ii) deliver** for a strongly typed redex, relative to the generic data
`(U, doms, B)` of the rule: the actual arguments are strongly typed at the generic telescope
instantiated by `us` and by the earlier arguments, and the redex's type is strongly equal to
the generic type instantiated the same way. -/
structure Aligned (env : VEnv) (U₀ : Nat) (Γ : List VExpr) (us : List VLevel)
    (args : List VExpr) (U : Nat) (doms : List VExpr) (B A : VExpr) : Prop where
  len : us.length = U
  wf : ∀ l ∈ us, l.WF U₀
  args_typed : ∀ j (hj : j < args.length) (hj' : j < doms.length),
    env.IsDefEqStrong U₀ Γ args[j] args[j] ((doms[j].instL us).instOuter (args.take j))
  type_eq : ∃ u, env.IsDefEqStrong U₀ Γ A ((B.instL us).instOuter args) (.sort u)

/-- **STUB** (wave 1D, steps (i)–(ii)): alignment of a strongly typed redex with the generic
instance of its rule. Intended proof: (i) `IsDefEqStrong.hasType'` turns `he` into a
`HasTypeStrong` derivation; inverting it along the recursor spine (the `base`/`app` cases, with
`forallE_forallE` to match the function's type against the recursor's Π-telescope read off
`ShapeAt.rec_find`) types each argument of `pre` at the recursor telescope and the major at
`T (block levels of us) (pre.take np ++ pre.drop k)`; inverting the major's own spine types it
at `T cus' cpar' (indices of the constructor)`; `uniqS` relates the two types by a chain and
`former_args` (with `ShapeAt.rigid`) gives `block levels of us ≈ cus'` and `SpineArgsEqS` for
the parameters and indices. (ii) The fields `cargs.drop np` are typed at the constructor's
field telescope at `cargs.take np`; the strong parameter equalities and
`IsDefEqStrong.instDF` retype them at the recursor's parameters, which is `args_typed` for the
field positions (the parameter/motive/minor positions are direct). `type_eq`: the generic
redex typing instantiated by `args` (`instOuter_telescope`) is typed at
`(B.instL us).instOuter args`; congruence (`appDF`/`constDF` with the alignment equalities)
makes it strongly equal to the actual redex, and `uniqS` against `he` gives `type_eq`.
Needs `Ordered env`, `OnTypes env (EnvStrong env)` and `StrongHeadInversion env`; not
`PatsStrongOn env`. -/
theorem align (_henv : Ordered env) (_hshi : StrongHeadInversion env)
    (_hstrong : OnTypes env (EnvStrong env)) (D : IotaRuleData) (_hsh : D.Shape env)
    {U : Nat} {doms idx cpar : List VExpr} {cls : List VLevel} {B : VExpr}
    (_hdl : doms.length = D.k + D.nf) (_hil : idx.length = D.nind) (_hcl : cpar.length = D.np)
    (_hΓg : CtxStrong env U doms.reverse)
    (_heg : env.IsDefEqStrong U doms.reverse (D.genericRedex U idx cls cpar)
      (D.genericRedex U idx cls cpar) B)
    {U₀ : Nat} {Γ : List VExpr} (_hΓ : CtxStrong env U₀ Γ) {us cus : List VLevel}
    {pre cargs : List VExpr} {A : VExpr}
    (_hpre : pre.length = D.k + D.nind) (_hcargs : cargs.length = D.np + D.nf)
    (_he : env.IsDefEqStrong U₀ Γ (D.redex us cus pre cargs) (D.redex us cus pre cargs) A) :
    Aligned env U₀ Γ us (D.args pre cargs) U doms B A := sorry

/-! ## Steps (iii) and (iv) -/

/-- The reduct `addRecRule` registers, applied to a match, is the template at `us` applied to
the actual arguments. -/
theorem rhsR_apply (D : IotaRuleData) {us : List VLevel} {pre cargs : List VExpr}
    (hpre : pre.length = D.np + D.nm + D.nmin + D.nind) (hcargs : cargs.length = D.np + D.nf)
    {g1 : ((Pattern.const D.recName).varN (D.np + D.nm + D.nmin + D.nind)).Path → VExpr}
    {g2 : ((Pattern.const D.ctorName).varN (D.np + D.nf)).Path → VExpr}
    (hg1 : ∀ i (hi : i < D.np + D.nm + D.nmin + D.nind),
      g1 (Pattern.varN_pathOf _ i hi) = pre[i]'(hpre ▸ hi))
    (hg2 : ∀ i (hi : i < D.np + D.nf), g2 (Pattern.varN_pathOf _ i hi) = cargs[i]'(hcargs ▸ hi)) :
    Pattern.RHS.apply (p := D.pattern) us (Sum.elim g1 g2) D.rhsR.1 =
      (D.rhs.instL us).mkApps (D.args pre cargs) := by
  simp only [rhsR, SimplePattern.iotaRHS]
  exact SimplePattern.iotaRHS'_apply _ _ _ _ _ _ _ _ _ (Sum.elim g1 g2) hpre hcargs hg1 hg2

/-- The generic reduct at `us`, instantiated by the actual arguments, is the template at `us`
applied to them. -/
theorem genericReduct_instOuter (D : IotaRuleData) (us : List VLevel) {args : List VExpr}
    (hlen : args.length = D.k + D.nf) :
    (D.genericReduct.instL us).instOuter args = (D.rhs.instL us).mkApps args := by
  simp only [genericReduct, VExpr.instL_mkApps, VExpr.instL_bvarsDesc, VExpr.instOuter_mkApps]
  rw [(D.hrhs.instL (ls := us)).instOuter_eq, ← hlen, VExpr.instOuter_bvarsDesc]

/-- **Steps (iii) and (iv).** Given the alignment of a strongly typed redex with the generic
instance of its rule, the reduct is strongly typed at the redex's type: the generic reduct
typing is level-instantiated, moved below `Γ`, instantiated along the telescope by
`IsDefEqStrong.instOuter_telescope`, and converted along `type_eq`. Needs `Ordered env`
only. -/
theorem reduct_typed (henv : Ordered env) (D : IotaRuleData)
    {U : Nat} {doms : List VExpr} {B : VExpr}
    (hdl : doms.length = D.k + D.nf) (hΓg : CtxStrong env U doms.reverse)
    (hrg : env.IsDefEqStrong U doms.reverse D.genericReduct D.genericReduct B)
    {U₀ : Nat} {Γ : List VExpr} (hΓ : CtxStrong env U₀ Γ) {us : List VLevel}
    {args : List VExpr} {A : VExpr} (hlen : args.length = D.k + D.nf)
    (hal : Aligned env U₀ Γ us args U doms B A) :
    env.IsDefEqStrong U₀ Γ ((D.rhs.instL us).mkApps args) ((D.rhs.instL us).mkApps args) A := by
  -- level instantiation of the generic typing and its context
  have hrg₁ := hrg.instL hal.wf
  have hΓg₁ := hΓg.instL hal.wf
  rw [List.map_reverse] at hrg₁ hΓg₁
  -- below `Γ`
  have hΓg₂ := CtxStrong.append_closed henv hΓ hΓg₁
  have hrg₂ := IsDefEqStrong.weak_below henv hΓg₁ hrg₁ Γ
  -- along the telescope
  have hinst := IsDefEqStrong.instOuter_telescope (args := args) (doms := doms.map (VExpr.instL us))
    henv hΓ hΓg₂ hrg₂ (by simp [hlen, hdl]) (fun j hj hj' => by
      have hj'' : j < doms.length := by simpa using hj'
      rw [List.getElem_map]
      exact hal.args_typed j hj hj'')
  rw [D.genericReduct_instOuter us hlen] at hinst
  -- conversion to the redex's type
  obtain ⟨u, hA⟩ := hal.type_eq
  have hu : u.WF U₀ := hA.defeq.sort_r henv hΓ.defeq
  exact .defeqDF hu hA.symm hinst

/-- **`PatStrong` of an ι rule** from its generic strong typing and shape, through the
alignment stub: a strongly typed redex matching the rule has a strongly typed reduct at the
same type. The one theorem about this environment's own rules; it uses `PatsStrongOn env`
nowhere. -/
theorem patStrong (henv : Ordered env) (hshi : StrongHeadInversion env)
    (hstrong : OnTypes env (EnvStrong env)) (D : IotaRuleData)
    (hgen : D.GenericStrong env) (hsh : D.Shape env) : PatStrong env D.pattern D.rhsR := by
  intro U₀ Γ e A m1 m2 chk hΓ hm he _ _
  -- the match: recursor spine applied to constructor spine
  simp only [pattern, SimplePattern.toPattern] at hm
  cases hm with
  | app hm1 hm2 =>
  obtain ⟨pre, hpre, rfl, hg1⟩ := Pattern.matches_varN_const_inv hm1
  obtain ⟨cargs, hcargs, rfl, hg2⟩ := Pattern.matches_varN_const_inv hm2
  have hpre' : pre.length = D.k + D.nind := hpre
  have hcargs' : cargs.length = D.np + D.nf := hcargs
  rw [D.rhsR_apply hpre hcargs hg1 hg2]
  obtain ⟨cus, he'⟩ : ∃ cus, env.IsDefEqStrong U₀ Γ (D.redex m1 cus pre cargs) (D.redex m1 cus pre cargs) A :=
    ⟨_, by simp only [redex, VExpr.mkApps_append, VExpr.mkApps_cons, VExpr.mkApps_nil]; exact he⟩
  obtain ⟨U, doms, idx, cpar, cls, B, hdl, hil, hcl, hΓg, heg, hrg⟩ := hgen
  have hal := D.align henv hshi hstrong hsh hdl hil hcl hΓg heg hΓ hpre' hcargs' he'
  exact D.reduct_typed henv hdl hΓg hrg hΓ (D.args_length hpre' hcargs') hal

end IotaRuleData

/-- `PatsStrongOn` of a `Stage` environment with head inversion: every registered rule is an
ι rule with generic strong typing and shape, so `IotaRuleData.patStrong` applies. -/
theorem Stage.patsStrongOn (hst : Stage env) (hshi : StrongHeadInversion env) : PatsStrongOn env := by
  intro p r hp
  obtain ⟨D, rfl, rfl, hgen, hsh⟩ := hst.rules hp
  exact D.patStrong hst.ordered hshi hst.strong hgen hsh

end VEnv
end Lean4Lean
