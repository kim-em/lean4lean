import Lean4Lean.Verify.Inductive.Nested.AuxRecNames

/-! # Input-side avoidance of the auxiliary constructor names by the lowered rules

The restored-equation junction modulo the renamed auxiliary recursor names
(`restoredEquations_of_realizationModulo`, `Nested/AuxRecNames.lean`) needs the
residue `NestedValidatedRunResult.LoweredRulesAvoid heads X`: in the lowered
rule right-hand sides, the trailing arguments of the hits, the literals and the
parameter domains avoid `X`. Only the restorable names of `X` matter
(`RestoredRulesRealizationModulo.filter_restorable`), and those are auxiliary
constructor names (`restorableRenamed_auxCtorNames`: lowered auxiliary recursor
names are never renamed, and auxiliary family names are numeric `_nested.i`
while renamed names are string extensions `Main.rec_k`).

`NestedValidatedRunResult.loweredRulesAvoid_auxCtorNames` proves the avoidance
of all auxiliary constructor names from the run alone. Auxiliary constructors do
occur in the lowered rules, as the constructor applications `c params fields`
of the minor premises, so complete avoidance is false; the argument is:

* `envHitShape_auxCtorNames`, `whnfHitOKFacts_auxCtorNames`: the type checker's
  hit-shape invariant (`TypeChecker.whnf.hitShape`) instantiated at the head
  set `E.auxCtorNames`, without parameters, at the level list `badLevels
  lparams` of length `lparams.length + 1`. `Expr.HitShape names [] ls e` says
  that every occurrence of `names` in `e` carries the levels `ls`. Every
  constant of the recursor-pass environment has a type avoiding the auxiliary
  constructor names, so the environment condition holds at any level list.
* `CompletedRecursorConstruction.ruleRhsTrail`: the trailing provenance chain
  (the counterpart of `ruleRhsHitShape`) for the predicate
  `Expr.HitTrailWith heads np (Expr.HitShape names [] ls)`: the `whnf` regions
  R1 to R3, the constructor field domains, the motives, the major premises and
  the recursive calls mention `names` only at `ls`; the minors' constructor
  applications are hits whose trailing arguments are field variables. The
  parameter domains avoid `names`.
* `HitTrailWith.toHitTrailAvoids`: the hit-shape chain at the declaration's
  levels (`recursorHitShape_hitHeads`) says that every occurrence of an
  auxiliary constructor is at `lparams.map Level.param`; at the trailing
  positions occurrences are also at `badLevels lparams`, which differs, so
  there are none.
-/

namespace Lean.Expr

open Lean4Lean

/-! ### Trailing-argument conditions at hits -/

/-- `HitTrailWith heads np Q e`: in `e`, every argument after the first `np` of an
application spine headed by a constant of `heads` satisfies `Q`. The generalization of
`HitTrailAvoids` (without its literal clause) to an arbitrary condition. -/
inductive HitTrailWith (heads : List Name) (np : Nat) (Q : Expr → Prop) : Expr → Prop
  | bvar (i : Nat) : HitTrailWith heads np Q (.bvar i)
  | fvar (fv : FVarId) : HitTrailWith heads np Q (.fvar fv)
  | mvar (mv : MVarId) : HitTrailWith heads np Q (.mvar mv)
  | sort (u : Level) : HitTrailWith heads np Q (.sort u)
  | const (c : Name) (us : List Level) : HitTrailWith heads np Q (.const c us)
  | lit (l : Literal) : HitTrailWith heads np Q (.lit l)
  | app {f a : Expr} : HitTrailWith heads np Q f → HitTrailWith heads np Q a →
      (∀ c us, (Expr.app f a).getAppFn = .const c us → c ∈ heads →
        ∀ x ∈ ((Expr.app f a).getAppArgsList).drop np, Q x) →
      HitTrailWith heads np Q (.app f a)
  | lam {n : Name} {t b : Expr} {bi : BinderInfo} :
      HitTrailWith heads np Q t → HitTrailWith heads np Q b →
      HitTrailWith heads np Q (.lam n t b bi)
  | forallE {n : Name} {t b : Expr} {bi : BinderInfo} :
      HitTrailWith heads np Q t → HitTrailWith heads np Q b →
      HitTrailWith heads np Q (.forallE n t b bi)
  | letE {n : Name} {t v b : Expr} {nd : Bool} :
      HitTrailWith heads np Q t → HitTrailWith heads np Q v →
      HitTrailWith heads np Q b →
      HitTrailWith heads np Q (.letE n t v b nd)
  | mdata {m : MData} {e : Expr} : HitTrailWith heads np Q e →
      HitTrailWith heads np Q (.mdata m e)
  | proj {s : Name} {i : Nat} {e : Expr} : HitTrailWith heads np Q e →
      HitTrailWith heads np Q (.proj s i e)

namespace HitTrailWith

variable {heads : List Name} {np : Nat} {Q : Expr → Prop}

/-- Spine arguments inherit `HitTrailWith`. -/
theorem of_mem_getAppArgsList {e : Expr} (H : HitTrailWith heads np Q e) :
    ∀ a ∈ e.getAppArgsList, HitTrailWith heads np Q a := by
  induction e with
  | app f a ihf _ =>
    cases H with
    | app hf ha _ =>
      intro x hx
      rw [getAppArgsList_app] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact ihf hf x hx
      · rw [List.mem_singleton.1 hx]; exact ha
  | _ => intro x hx; simp [getAppArgsList] at hx

/-- `consumeTypeAnnotationsVerified` returns a subterm reached through application
arguments, so it preserves `HitTrailWith`. -/
theorem consumeTypeAnnotationsVerified {e : Expr} (H : HitTrailWith heads np Q e) :
    HitTrailWith heads np Q e.consumeTypeAnnotationsVerified := by
  fun_induction Expr.consumeTypeAnnotationsVerified e
  case case1 name us type v _ ih =>
    exact ih (H.of_mem_getAppArgsList type (by simp [getAppArgsList]))
  case case2 => exact H
  case case3 name us type _ ih =>
    exact ih (H.of_mem_getAppArgsList type (by simp [getAppArgsList]))
  case case4 => exact H
  case case5 => exact H

private theorem getAppFn_app' (f a : Expr) : (Expr.app f a).getAppFn = f.getAppFn := rfl

/-- An application whose function is not headed by a constant (a variable, say). -/
theorem app_of_not_const {f a : Expr} (hf : HitTrailWith heads np Q f)
    (ha : HitTrailWith heads np Q a) (hfn : ∀ c us, f.getAppFn ≠ .const c us) :
    HitTrailWith heads np Q (.app f a) :=
  .app hf ha fun c us h _ => absurd h (hfn c us)

/-- A spine with a `HitTrailWith` head whose arguments all satisfy `Q` and
`HitTrailWith`, and whose head arguments satisfy `Q` when its head is a constant. -/
theorem mkAppList_of_args {f : Expr} {args : List Expr} (hf : HitTrailWith heads np Q f)
    (hfargs : ∀ c us, f.getAppFn = .const c us → ∀ x ∈ f.getAppArgsList, Q x)
    (hargs : ∀ a ∈ args, HitTrailWith heads np Q a ∧ Q a) :
    HitTrailWith heads np Q (f.mkAppList args) := by
  induction args generalizing f with
  | nil => exact hf
  | cons a rest ih =>
    simp only [mkAppList]
    refine ih ?_ ?_ fun x hx => hargs x (.tail _ hx)
    · refine .app hf (hargs a (.head _)).1 fun c us hfn _ x hx => ?_
      rw [getAppArgsList_app] at hx
      rcases List.mem_append.1 (List.mem_of_mem_drop hx) with hx | hx
      · exact hfargs c us hfn x hx
      · rw [List.mem_singleton.1 hx]; exact (hargs a (.head _)).2
    · intro c us hfn x hx
      rw [getAppArgsList_app] at hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hfargs c us hfn x hx
      · rw [List.mem_singleton.1 hx]; exact (hargs a (.head _)).2

/-- A constant applied to arguments that all satisfy `Q` and `HitTrailWith`. -/
theorem const_mkAppList {c : Name} {us : List Level} {args : List Expr}
    (hargs : ∀ a ∈ args, HitTrailWith heads np Q a ∧ Q a) :
    HitTrailWith heads np Q ((Expr.const c us).mkAppList args) :=
  mkAppList_of_args (.const _ _) (fun _ _ _ x hx => by simp [getAppArgsList] at hx) hargs

/-! #### Abstraction -/

private theorem abstractN_fvar_cases (xs : List FVarId) (v : FVarId) (d : Nat) :
    (∃ j, abstractN xs (.fvar v) d = .bvar j) ∨ abstractN xs (.fvar v) d = .fvar v := by
  simp only [abstractN]
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr rfl

theorem getAppFn_abstractN (xs : List FVarId) :
    ∀ (e : Expr) (d : Nat), (abstractN xs e d).getAppFn = abstractN xs e.getAppFn d
  | .app f _, d => by
    simp only [abstractN, getAppFn]
    exact getAppFn_abstractN xs f d
  | .fvar v, d => by
    rcases abstractN_fvar_cases xs v d with ⟨j, h⟩ | h <;> simp [getAppFn, h]
  | .bvar _, _ | .mvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .lam .., _ | .forallE .., _ | .letE .., _ | .mdata .., _ | .proj .., _ => rfl

theorem getAppArgsList_abstractN (xs : List FVarId) :
    ∀ (e : Expr) (d : Nat),
      (abstractN xs e d).getAppArgsList = e.getAppArgsList.map (abstractN xs · d)
  | .app f a, d => by
    simp only [abstractN, getAppArgsList_app, List.map_append, List.map_cons, List.map_nil]
    rw [getAppArgsList_abstractN xs f d]
  | .fvar v, d => by
    rcases abstractN_fvar_cases xs v d with ⟨j, h⟩ | h <;> simp [getAppArgsList, h]
  | .bvar _, _ | .mvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .lam .., _ | .forallE .., _ | .letE .., _ | .mdata .., _ | .proj .., _ => rfl

theorem eq_const_of_abstractN {xs : List FVarId} {d : Nat} {c : Name} {us : List Level} :
    ∀ {x : Expr}, abstractN xs x d = .const c us → x = .const c us
  | .fvar v, h => by
    rcases abstractN_fvar_cases xs v d with ⟨j, h'⟩ | h' <;> rw [h'] at h <;> cases h
  | .const _ _, h => h
  | .bvar _, h | .mvar _, h | .sort _, h | .lit _, h => by cases h
  | .app .., h | .lam .., h | .forallE .., h | .letE .., h | .mdata .., h | .proj .., h => by
    simp [abstractN] at h

/-- Abstraction preserves `HitTrailWith` when it preserves `Q`. -/
theorem abstractN {xs : List FVarId} {e : Expr} (H : HitTrailWith heads np Q e)
    (hQ : ∀ x d, Q x → Q (x.abstractN xs d)) (d : Nat) :
    HitTrailWith heads np Q (e.abstractN xs d) := by
  induction H generalizing d with
  | bvar => exact .bvar _
  | fvar v =>
    rcases abstractN_fvar_cases xs v d with ⟨j, h⟩ | h <;> rw [h]
    · exact .bvar _
    · exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit => exact .lit _
  | @app f a _ _ htrail ihf iha =>
    refine .app (ihf d) (iha d) ?_
    intro c us hfn hc x hx
    have hfn' : (Expr.app f a).getAppFn = .const c us := by
      have h := getAppFn_abstractN xs (.app f a) d
      simp only [Expr.abstractN] at h
      rw [h] at hfn
      exact eq_const_of_abstractN hfn
    have hargs := getAppArgsList_abstractN xs (.app f a) d
    simp only [Expr.abstractN] at hargs
    rw [hargs, ← List.map_drop] at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact hQ y d (htrail c us hfn' hc y hy)
  | lam _ _ ihd ihb => exact .lam (ihd d) (ihb (d + 1))
  | forallE _ _ ihd ihb => exact .forallE (ihd d) (ihb (d + 1))
  | letE _ _ _ iht ihv ihb => exact .letE (iht d) (ihv d) (ihb (d + 1))
  | mdata _ ih => exact .mdata (ih d)
  | proj _ ih => exact .proj (ih d)

private theorem go_cdecls {isLambda : Bool} {lctx : LocalContext}
    (hQ : ∀ (ys : List FVarId) x d, Q x → Q (x.abstractN ys d)) :
    ∀ {l : List FVarId}, (∀ x ∈ l, ∃ i fv n ty bi kind,
      lctx.find? x = some (.cdecl i fv n ty bi kind) ∧ HitTrailWith heads np Q ty) →
    ∀ {b}, HitTrailWith heads np Q b →
      HitTrailWith heads np Q (LocalContext.mkBindingListN.go isLambda lctx l b)
  | [], _, _, H => H
  | x :: l, hx, b, H => by
    obtain ⟨i, fv, n, ty, bi, kind, hfind, hty⟩ := hx x (.head _)
    simp only [LocalContext.mkBindingListN.go]
    refine go_cdecls hQ (fun y hy => hx y (.tail _ hy)) ?_
    simp only [LocalContext.mkBindingList1N, hfind]
    have hty' := hty.abstractN (hQ l.reverse) 0
    cases isLambda
    · exact .forallE hty' H
    · exact .lam hty' H

/-- Closing a telescope of `cdecl` variables with `HitTrailWith` types. -/
theorem mkBinding {isLambda : Bool} {lctx : LocalContext} {ys : List FVarId} {b : Expr}
    (H : HitTrailWith heads np Q b) (hQ : ∀ (ys : List FVarId) x d, Q x → Q (x.abstractN ys d))
    (hdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind,
      lctx.find? y = some (.cdecl i fv n ty bi kind) ∧ HitTrailWith heads np Q ty) :
    HitTrailWith heads np Q (lctx.mkBinding isLambda ⟨ys.map .fvar⟩ b) := by
  rw [LocalContext.mkBinding_eqN]
  simp only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core]
  exact go_cdecls hQ (fun y hy => hdecl y (List.mem_reverse.1 hy)) (H.abstractN (hQ ys) 0)

/-- `mkBinding` over `cdecl` variables, with the type condition read off any
declaration of the variables. -/
theorem mkBinding' {isLambda : Bool} {lctx : LocalContext} {ys : List FVarId} {b : Expr}
    (H : HitTrailWith heads np Q b) (hQ : ∀ (ys : List FVarId) x d, Q x → Q (x.abstractN ys d))
    (hcdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind, lctx.find? y = some (.cdecl i fv n ty bi kind))
    (hty : ∀ y ∈ ys, ∀ d, lctx.find? y = some d → HitTrailWith heads np Q d.type) :
    HitTrailWith heads np Q (lctx.mkBinding isLambda ⟨ys.map .fvar⟩ b) := by
  refine mkBinding H hQ fun y hy => ?_
  obtain ⟨i, fv, n, ty, bi, kind, hfind⟩ := hcdecl y hy
  exact ⟨i, fv, n, ty, bi, kind, hfind, hty y hy _ hfind⟩

theorem mkForall' {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId} {b : Expr}
    (hxs : xs = (ys.map Expr.fvar).toArray)
    (H : HitTrailWith heads np Q b) (hQ : ∀ (ys : List FVarId) x d, Q x → Q (x.abstractN ys d))
    (hcdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind, lctx.find? y = some (.cdecl i fv n ty bi kind))
    (hty : ∀ y ∈ ys, ∀ d, lctx.find? y = some d → HitTrailWith heads np Q d.type) :
    HitTrailWith heads np Q (lctx.mkForall xs b) := by
  subst hxs
  simpa [LocalContext.mkForall] using mkBinding' (isLambda := false) H hQ hcdecl hty

theorem mkLambda' {lctx : LocalContext} {xs : Array Expr} {ys : List FVarId} {b : Expr}
    (hxs : xs = (ys.map Expr.fvar).toArray)
    (H : HitTrailWith heads np Q b) (hQ : ∀ (ys : List FVarId) x d, Q x → Q (x.abstractN ys d))
    (hcdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind, lctx.find? y = some (.cdecl i fv n ty bi kind))
    (hty : ∀ y ∈ ys, ∀ d, lctx.find? y = some d → HitTrailWith heads np Q d.type) :
    HitTrailWith heads np Q (lctx.mkLambda xs b) := by
  subst hxs
  simpa [LocalContext.mkLambda] using mkBinding' (isLambda := true) H hQ hcdecl hty

end HitTrailWith

end Lean.Expr

namespace Lean.Expr

open Lean4Lean

/-! ### Hit shape without parameters

`HitShape names [] ls e` says that every occurrence of a constant of `names` in
`e` carries the levels `ls`. Two such facts at different level lists exclude
the names altogether. -/

namespace HitShape

variable {heads : List Name} {ls : List Level}

theorem app_inv_nil {f a : Expr} (H : HitShape heads [] ls (.app f a)) :
    HitShape heads [] ls f ∧ HitShape heads [] ls a := by
  generalize he : Expr.app f a = e at H
  cases H with
  | app hf ha => cases he; exact ⟨hf, ha⟩
  | hitHead => simp at he
  | _ => cases he

/-- Forgetting the parameters of the hits. -/
theorem params_nil {params : List Expr} {e : Expr} (H : HitShape heads params ls e)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv) : HitShape heads [] ls e := by
  induction H with
  | hitHead hc =>
    refine HitShape.mkAppList (by simpa [mkAppList] using (HitShape.hitHead hc :
      HitShape heads [] ls ((Expr.const _ ls).mkAppList []))) fun p hpm => ?_
    obtain ⟨fv, rfl⟩ := hp p hpm
    exact .fvar _
  | app _ _ ihf iha => exact .app ihf iha
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- Shrinking the head set of a parameterless hit shape. -/
theorem nil_mono {names : List Name} {e : Expr} (H : HitShape heads [] ls e)
    (hsub : ∀ n ∈ names, n ∈ heads) : HitShape names [] ls e := by
  induction H with
  | @hitHead c hc =>
    by_cases hcn : c ∈ names
    · exact .hitHead hcn
    · simpa [mkAppList] using (HitShape.const hcn : HitShape names [] ls (.const c ls))
  | app _ _ ihf iha => exact .app ihf iha
  | const hc => exact .const fun h => hc (hsub _ h)
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- Abstraction preserves a parameterless hit shape. -/
theorem nil_abstractN {e : Expr} (H : HitShape heads [] ls e) (ys : List FVarId) (d : Nat) :
    HitShape heads [] ls (e.abstractN ys d) :=
  H.abstractN_of_disjoint (by simp) d

/-- Two parameterless hit shapes at different levels exclude the heads. -/
theorem avoids_of_two {ls' : List Level} {e : Expr} (H : HitShape heads [] ls e)
    (H' : HitShape heads [] ls' e) (hne : ls ≠ ls')
    (hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts heads) : e.AvoidsConsts heads := by
  induction H with
  | @hitHead c hc =>
    simp only [Expr.mkAppList] at H' ⊢
    rcases H'.const_inv with h | ⟨-, h, -⟩
    · exact absurd hc h
    · exact absurd h hne
  | app _ _ ihf iha =>
    obtain ⟨hf, ha⟩ := H'.app_inv_nil
    exact .app _ _ (ihf hf) (iha ha)
  | const hc => exact .const _ _ hc
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact hlit _
  | lam _ _ iht ihb =>
    obtain ⟨ht, hb⟩ := H'.lam_inv
    exact .lam _ _ _ _ (iht ht) (ihb hb)
  | forallE _ _ iht ihb =>
    obtain ⟨ht, hb⟩ := H'.forallE_inv
    exact .forallE _ _ _ _ (iht ht) (ihb hb)
  | letE _ _ _ iht ihv ihb =>
    obtain ⟨ht, hv, hb⟩ := H'.letE_inv
    exact .letE _ _ _ _ _ (iht ht) (ihv hv) (ihb hb)
  | mdata _ ih => exact .mdata _ _ (ih H'.mdata_inv)
  | proj _ ih => exact .proj _ _ _ (ih H'.proj_inv)

end HitShape

/-- The bound-variable form forgets to a parameterless hit shape. -/
theorem HitShapeB.toNil {heads : List Name} {n : Nat} {ls : List Level} {d : Nat} {e : Expr}
    (H : HitShapeB heads n ls d e) : HitShape heads [] ls e := by
  induction H with
  | hitHead hc =>
    refine HitShape.mkAppList (by simpa [mkAppList] using (HitShape.hitHead hc :
      HitShape heads [] ls ((Expr.const _ ls).mkAppList []))) fun p hpm => ?_
    simp only [hitParamBVars, List.mem_map] at hpm
    obtain ⟨_, -, rfl⟩ := hpm
    exact .bvar _
  | app _ _ ihf iha => exact .app ihf iha
  | const hc => exact .const hc
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | lit => exact .lit _
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

namespace HitTrailWith

variable {heads names : List Name} {np : Nat} {ls : List Level}

/-- A parameterless hit shape holds hereditarily, so in particular at trailing
arguments. -/
theorem of_hitShape_nil {e : Expr} (H : HitShape names [] ls e) :
    HitTrailWith heads np (HitShape names [] ls) e := by
  induction e with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit => exact .lit _
  | app f a ihf iha =>
    obtain ⟨hf, ha⟩ := H.app_inv_nil
    exact .app (ihf hf) (iha ha) fun _ _ _ _ x hx =>
      H.of_mem_getAppArgsList (by simp) (List.mem_of_mem_drop hx)
  | lam _ _ _ _ iht ihb => exact .lam (iht H.lam_inv.1) (ihb H.lam_inv.2)
  | forallE _ _ _ _ iht ihb => exact .forallE (iht H.forallE_inv.1) (ihb H.forallE_inv.2)
  | letE _ _ _ _ _ iht ihv ihb =>
    exact .letE (iht H.letE_inv.1) (ihv H.letE_inv.2.1) (ihb H.letE_inv.2.2)
  | mdata _ _ ih => exact .mdata (ih H.mdata_inv)
  | proj _ _ _ ih => exact .proj (ih H.proj_inv)

/-- **From trailing hit shape at impossible levels to trailing avoidance.** If
the trailing arguments of the hits of `e` mention `names` only at the levels
`ls`, while `e` mentions `names` only at the levels `ls' ≠ ls`, then the
trailing arguments avoid `names`, hence every `X ⊆ names`. -/
theorem toHitTrailAvoids {ls' : List Level} {X : List Name} {e : Expr}
    (H : HitTrailWith heads np (HitShape names [] ls) e) (H' : HitShape names [] ls' e)
    (hne : ls ≠ ls') (hX : ∀ n ∈ X, n ∈ names)
    (hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts names) :
    e.HitTrailAvoids heads X np := by
  induction H with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit l => exact .lit _ ((hlit l).mono hX)
  | @app f a _ _ htrail ihf iha =>
    obtain ⟨hf, ha⟩ := H'.app_inv_nil
    refine .app (ihf hf) (iha ha) fun c us hfn hc x hx => ?_
    have hx' := H'.of_mem_getAppArgsList (by simp) (List.mem_of_mem_drop hx)
    exact ((htrail c us hfn hc x hx).avoids_of_two hx' hne hlit).mono hX
  | lam _ _ iht ihb => exact .lam (iht H'.lam_inv.1) (ihb H'.lam_inv.2)
  | forallE _ _ iht ihb => exact .forallE (iht H'.forallE_inv.1) (ihb H'.forallE_inv.2)
  | letE _ _ _ iht ihv ihb =>
    exact .letE (iht H'.letE_inv.1) (ihv H'.letE_inv.2.1) (ihb H'.letE_inv.2.2)
  | mdata _ ih => exact .mdata (ih H'.mdata_inv)
  | proj _ ih => exact .proj (ih H'.proj_inv)

end HitTrailWith

/-! ### Lambda prefixes -/

private theorem lamPrefix_go {names : List Name} {lctx : LocalContext} :
    ∀ {l : List FVarId}, (∀ x ∈ l, ∃ i fv n ty bi kind,
      lctx.find? x = some (.cdecl i fv n ty bi kind) ∧ ty.AvoidsConsts names) →
    ∀ {k b}, LamPrefixAvoids names k b →
      LamPrefixAvoids names (k + l.length) (LocalContext.mkBindingListN.go true lctx l b)
  | [], _, _, _, H => H
  | x :: l, hx, k, b, H => by
    obtain ⟨i, fv, n, ty, bi, kind, hfind, hty⟩ := hx x (.head _)
    simp only [LocalContext.mkBindingListN.go]
    have := lamPrefix_go (l := l) (fun y hy => hx y (.tail _ hy)) (k := k + 1)
      (b := LocalContext.mkBindingList1N true lctx l.reverse x b) (by
        simp only [LocalContext.mkBindingList1N, hfind, if_true]
        exact .succ (hty.abstractN _ 0) H)
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- Closing `cdecl` variables whose types avoid `names` with `mkLambda` gives a
lambda prefix avoiding `names`. -/
theorem LamPrefixAvoids.mkLambda {names : List Name} {lctx : LocalContext}
    {ys : List FVarId} (b : Expr)
    (hdecl : ∀ y ∈ ys, ∃ i fv n ty bi kind,
      lctx.find? y = some (.cdecl i fv n ty bi kind) ∧ ty.AvoidsConsts names) :
    LamPrefixAvoids names ys.length (lctx.mkLambda ⟨ys.map .fvar⟩ b) := by
  simp only [LocalContext.mkLambda]
  rw [LocalContext.mkBinding_eqN]
  simp only [LocalContext.mkBindingListN, LocalContext.mkBindingListN.core]
  simpa using lamPrefix_go (l := ys.reverse) (fun y hy => hdecl y (List.mem_reverse.1 hy))
    (LamPrefixAvoids.zero (b.abstractN ys))

end Lean.Expr

namespace Lean.Expr

theorem LeadingBinders.avoidsConsts {names : List Name} {k : Nat} {e body : Expr}
    (H : LeadingBinders k e body) (h : e.AvoidsConsts names) : body.AvoidsConsts names := by
  induction H with
  | zero => exact h
  | forallE _ ih => cases h; exact ih ‹_›
  | lam _ ih => cases h; exact ih ‹_›

end Lean.Expr

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- `RecursorIndexTrace.hitShape` at an arbitrary parameter list. -/
theorem RecursorIndexTrace.hitShapeAt
    {heads : List Name} {params : List Expr} {ls : List Level} {env : Environment}
    {stats : AddInductive.InductiveStats}
    (W : WhnfHitOKFacts heads params ls env)
    (hp : ∀ p ∈ params, ∃ fv, p = .fvar fv)
    (hsp : ∀ p ∈ stats.params.toList, ∃ fv, p = .fvar fv)
    {final : AddInductive.Context} (henv : final.env = env)
    (hparamDecls : ∀ fv ∈ ExprArrayFVarIds stats.params, ∀ d,
      final.lctx.find? fv = some d → d.HitOK env heads params ls)
    {header : Expr} (hheader : header.HitOK env heads params ls)
    {i : Nat} {type : Expr} {indices : Array Expr}
    (T : RecursorIndexTrace stats final header i type indices) :
    type.HitOK env heads params ls ∧
      ∀ fv ∈ ExprArrayFVarIds indices, ∀ d, final.lctx.find? fv = some d →
        d.HitOK env heads params ls := by
  induction T with
  | start call =>
    exact ⟨call.hitShape W henv (fun _ h => h.elim) hheader,
      by simp [ExprArrayFVarIds]⟩
  | @param i name dom body normalized bi _ hi call ih =>
    obtain ⟨hty, -⟩ := ih
    obtain ⟨-, hbody⟩ := hty.forallE_inv
    have hparam : (stats.params[i]!).HitOK env heads params ls := by
      have hmem : stats.params[i]! ∈ stats.params.toList := by
        rw [getElem!_pos stats.params i hi]
        exact Array.getElem_mem_toList hi
      obtain ⟨fv, hfv⟩ := hsp _ hmem
      rw [hfv]
      exact Expr.HitOK.fvar
    exact ⟨call.hitShape W henv hparamDecls (hbody.instantiate1 hp hparam),
      by simp [ExprArrayFVarIds]⟩
  | @index indices name dom body normalized bi x _ member declaration call ih =>
    obtain ⟨hty, hidx⟩ := ih
    obtain ⟨hdom, hbody⟩ := hty.forallE_inv
    have hall : ∀ fv ∈ ExprArrayFVarIds (indices.push (.fvar x)), ∀ d,
        final.lctx.find? fv = some d → d.HitOK env heads params ls := by
      rw [ExprArrayFVarIds_push_fvar]
      intro fv hfv d hfind
      rcases List.mem_append.mp hfv with h | h
      · exact hidx fv h d hfind
      · rw [List.mem_singleton.mp h] at hfind
        obtain ⟨index, userName, binderInfo, kind, hx⟩ := declaration
        rw [hx] at hfind
        cases hfind
        exact LocalDecl.HitOK.of_cdecl (hdom.consumeTypeAnnotationsVerified hp)
    refine ⟨call.hitShape W henv (fun fv hfv d hfind => ?_)
      (hbody.instantiate1 hp Expr.HitOK.fvar), hall⟩
    rcases hfv with h | h
    · exact hparamDecls fv h d hfind
    · exact hall fv h d hfind

section TrailAssembly

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
    sourceEnv indTypes ctorEnv}

/-- **Inputs of the trailing-argument provenance** of a completed recursor
construction, for a name list `names` and the levels `ls` (in the application,
the auxiliary constructor names at levels that no translated constant
carries): parameter declarations, family headers and constructor types avoid
`names` and satisfy the projection condition, constructor types have the
parameter telescope, and the generated recursor names and the family names of
the majors are not in `names`. -/
structure CompletedRecursorConstruction.TrailInputs
    (H : CompletedRecursorConstruction R) (names : List Name) (ls : List Level) : Prop where
  paramDecls : ∀ fv ∈ H.params.fvars, ∀ d, H.localContext.lctx.find? fv = some d →
    d.HitOK H.localContext.env names [] ls ∧ d.type.AvoidsConsts names
  familyHeaders : ∀ i, i < indTypes.size → (indTypes[i]!.type).AvoidsConsts names ∧
    (indTypes[i]!.type).ProjsOK (projHitOK H.localContext.env names)
  constructorTypes : ∀ i, i < indTypes.size → ∀ ctor ∈ indTypes[i]!.ctors,
    (∃ body, Expr.LeadingBinders stats.params.size ctor.type body) ∧
      ctor.type.AvoidsConsts names ∧
      ctor.type.ProjsOK (projHitOK H.localContext.env names)
  recursorNames : ∀ i, i < stats.indConsts.size → Lean.mkRecName indTypes[i]!.name ∉ names
  familyNames : ∀ i, i < H.recInfos.size → ∀ n lv, stats.indConsts[i]! = .const n lv →
    n ∉ names

namespace CompletedRecursorConstruction

variable (H : CompletedRecursorConstruction R)

private theorem hQ {names : List Name} {ls : List Level} :
    ∀ (ys : List FVarId) x d, Expr.HitShape names [] ls x →
      Expr.HitShape names [] ls (x.abstractN ys d) :=
  fun ys _ d h => h.nil_abstractN ys d

/-- **Trailing provenance of one generated minor**: its field declarations are
`cdecl`s whose types mention `names` only at `ls`; its declared type satisfies
`HitTrailWith` for the condition "mentions `names` only at `ls`" (the only
other occurrences are the minor's constructor application, whose trailing
arguments are fields); the call templates of its rule blueprint mention
`names` only at `ls`. -/
theorem minorTrail {names : List Name} {ls : List Level} (I : H.TrailInputs names ls)
    (W : WhnfHitOKFacts names [] ls H.localContext.env)
    (heads : List Name) (np : Nat)
    (owner : Nat) (howner : owner < H.recInfos.size) (localIndex : Nat)
    (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (∀ y ∈ (H.origins.minorShapes owner howner localIndex hlocal).fields_bound.fvars,
      ∃ i fv n ty bi kind, (H.origins.minorShapes owner howner localIndex
          hlocal).sourceFullContext.lctx.find? y = some (.cdecl i fv n ty bi kind) ∧
        ty.HitShape names [] ls) ∧
    (H.origins.minorShapes owner howner localIndex hlocal).origin.HitTrailWith heads np
      (Expr.HitShape names [] ls) ∧
    (∀ j, j < (H.origins.minorShapes owner howner localIndex hlocal).hypotheses.size →
      (H.recInfos[owner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).template.HitShape
        names [] ls ∧
      (H.recInfos[owner]!.ruleBlueprints[localIndex]!.recursiveCalls[j]!).targetTypeIdx <
        stats.indConsts.size) := by
  have hsourceOwner := H.sourceOwner howner
  have hsrc := H.minorSources.rows owner howner hsourceOwner localIndex hlocal
  have hcallRoots : RecInfoRuleBlueprintOriginAt stats
      (H.origins.minorShapes owner howner localIndex hlocal)
      H.recInfos[owner]!.minors[localIndex]!
      H.recInfos[owner]!.ruleBlueprints[localIndex]! :=
    H.blueprints.entry owner howner localIndex hlocal
  obtain ⟨Hsem⟩ := H.blueprintSemantics.entry owner howner localIndex hlocal
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at hsrc hcallRoots Hsem ⊢
  generalize H.recInfos[owner]!.ruleBlueprints[localIndex]! = B at hcallRoots Hsem ⊢
  obtain ⟨-, -, hsourceCtors, -, traversal, htrav, -, -, -, -, hvalid, hmotiveApp, -, -,
    hsrcLE⟩ := hsrc
  obtain ⟨origins, hshape, hstats, -, F, -⟩ := Hsem
  obtain ⟨-, -, -, -, -, callOrigins, -, hcallShape, -, -, Hcalls⟩ := hcallRoots
  have hcallOrigins : callOrigins = origins :=
    Option.some.inj (hcallShape.symm.trans hshape)
  subst callOrigins
  have hT : traversal = F.traversal := Option.some.inj (htrav.symm.trans F.traversal_eq)
  subst hT
  have hp : ∀ p ∈ ([] : List Expr), ∃ fv, p = .fvar fv := by simp
  have Hroot := F.rootWF.toBindingContextWF
  have hTL : BindingContextLE F.traversal.terminalContext H.localContext :=
    F.terminalExtension.contextLE
  -- Field declarations (the lowered constructor's syntactic domains).
  have Hprefix : RecursorParamPrefix stats 0 S.constructor.type
      F.traversal.parameterTail := by
    have := F.traversal.parameterPrefix
    rwa [F.traversal_stats, F.traversal_constructor] at this
  have hctorMem : S.constructor ∈ indTypes[owner]!.ctors := by
    rw [← hsourceCtors]; exact List.mem_of_getElem? S.sourceConstructor
  obtain ⟨⟨body, Hlead⟩, havoid, hproj⟩ := I.constructorTypes owner hsourceOwner _ hctorMem
  have Htail' := Hprefix.hitOK (ls := ls) H.params.expressions
    ⟨body, Hlead, Expr.HitShapeB.of_avoidsConsts (Hlead.avoidsConsts havoid) 0⟩ hproj
  have Htail : F.traversal.parameterTail.HitOK H.localContext.env names [] ls :=
    ⟨Htail'.1.params_nil H.params_fvar, Htail'.2⟩
  obtain ⟨hterm, hfieldsTerm⟩ := F.traversal.decisions.hitOK Hroot hp Htail
  rw [F.traversal_fields] at hfieldsTerm
  have hfieldDecls : ∀ y ∈ S.fields_bound.fvars, ∃ i fv n ty bi kind,
      S.sourceFullContext.lctx.find? y = some (.cdecl i fv n ty bi kind) ∧
        ty.HitShape names [] ls := by
    intro y hy
    obtain ⟨fv, index, name, type, bi, kind, hfv, hmem, hfind, htype⟩ :=
      hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hy)
    cases hfv
    refine ⟨index, y, name, type, bi, kind, ?_, htype.1⟩
    rw [← hsrcLE.declarations y (S.fields_bound.members y hy),
      hTL.declarations y hmem, hfind]
  -- Parameters are variables of the field traversal's terminal context.
  have hparamTerm : ∀ pv, Expr.fvar pv ∈ stats.params →
      pv ∈ F.traversal.terminalContext.lctx.fvars := fun pv h =>
    (F.traversal.decisions.freshBindings Hroot).choose_spec.1.fvars
      (F.parameterSuffix.param_mem h)
  -- Induction hypotheses and recursive calls (regions R2 and R3).
  have hfr : origins.fieldRoot = F.traversal.terminalContext :=
    S.hypothesis_origins_fieldRoot origins F.traversal hshape F.traversal_eq
  have hper : ∀ j, j < S.hypotheses.size →
      (∃ D : BoundFVarDeclarationAt S.sourceFullContext S.hypotheses j,
        D.type.HitShape names [] ls) ∧
      ((B.recursiveCalls[j]!).template.HitShape names [] ls ∧
        (B.recursiveCalls[j]!).targetTypeIdx < stats.indConsts.size) := by
    intro j hj
    obtain ⟨originRoot, sourceType, recL, Rorigin, O, D, hle, hup, hD, hcall⟩ :=
      Hcalls.rooted j hj
    rw [hstats] at hup
    rw [hfr] at hle
    have henv : originRoot.env = H.localContext.env := hle.env_eq.trans hTL.env_eq.symm
    have hscope : Rorigin.HitOKScope H.localContext.env names [] ls
        (fun fv => fv ∈ ExprArrayFVarIds S.fields ∨
          fv ∈ ExprArrayFVarIds stats.params) := by
      refine ⟨hup, fun fv decl hP hfind => ?_⟩
      rw [Rorigin.lctx_eq] at hfind
      rcases hP with hf | hpar
      · rw [S.fields_bound.exprArrayFVarIds] at hf
        obtain ⟨fv', index, name, type, bi, kind, hfv, hmem, hfind', htype⟩ :=
          hfieldsTerm _ (S.fields_bound.mem_fvars_iff.1 hf)
        cases hfv
        rw [hle.declarations fv hmem, hfind'] at hfind
        cases hfind
        exact LocalDecl.HitOK.of_cdecl htype
      · rw [H.params.exprArrayFVarIds] at hpar
        have hmemP := H.params.mem_fvars_iff.1 hpar
        rw [hle.declarations fv (hparamTerm fv hmemP),
          ← hTL.declarations fv (hparamTerm fv hmemP)] at hfind
        exact (I.paramDecls fv hpar decl hfind).1
    have hjr : j < S.recursiveFields.size := by rw [← S.hypotheses_size]; exact hj
    have hfieldMem : S.recursiveFields[j]! ∈ S.fields := by
      rw [← F.traversal_fields]
      apply F.traversal.decisions.selected_subset
      rw [F.traversal_recursiveFields, getElem!_pos S.recursiveFields j hjr]
      exact Array.getElem_mem hjr
    have hfieldP : ∀ fv, S.recursiveFields[j]! = .fvar fv →
        (fun fv => fv ∈ ExprArrayFVarIds S.fields ∨
          fv ∈ ExprArrayFVarIds stats.params) fv := by
      intro fv hfv
      left
      rw [hfv] at hfieldMem
      exact mem_exprArrayFVarIds_of_fvar_mem hfieldMem
    obtain ⟨hargs, hexp, htype⟩ :=
      O.hitShape W hp henv Rorigin hscope hfieldP (by simp)
    refine ⟨⟨D, by rw [hD]; exact htype.consumeTypeAnnotationsVerified hp⟩, ?_⟩
    rw [hcall]
    refine ⟨?_, by
      have := (checkPositivityStep.isValidIndApp?_some O.owner_valid).1
      exact hstats ▸ this⟩
    obtain ⟨ffv, hffv, -⟩ := O.field_fvar
    refine Expr.HitShape.mkLambda_of_disjoint O.arguments_bound.expressions ?_ (by simp) ?_
    · refine .app (Expr.HitShape.mkAppN (.bvar _) (hexp.getAppArgs_slice hp _))
        (Expr.HitShape.mkAppN (by rw [hffv]; exact .fvar ffv) ?_)
      intro a ha
      rw [O.arguments_bound.expressions] at ha
      simp only [List.mem_map] at ha
      obtain ⟨y, -, rfl⟩ := ha
      exact .fvar y
    · intro y hy
      have hyCur : y ∈ O.current.lctx.fvars := O.arguments_bound.members y hy
      obtain ⟨index, name, ty, bi, kind, hfind⟩ := O.current_wf.findCDecl y hyCur
      exact ⟨_, hfind, hargs y hy _ hfind⟩
  refine ⟨hfieldDecls, ?_, fun j hj => (hper j hj).2⟩
  -- The minor premise type.
  rw [← S.consumed_eq]
  refine Expr.HitTrailWith.consumeTypeAnnotationsVerified ?_
  rw [S.sourceType_eq, ← S.sourceContext_eq]
  refine Expr.HitTrailWith.mkForall' S.fields_bound.expressions ?_ hQ
    (fun y hy => by
      obtain ⟨i, fv, n, ty, bi, kind, hfind, -⟩ := hfieldDecls y hy
      exact ⟨i, fv, n, ty, bi, kind, hfind⟩)
    (fun y hy d hfind => by
      obtain ⟨i, fv, n, ty, bi, kind, hfind', hty⟩ := hfieldDecls y hy
      rw [hfind] at hfind'
      cases hfind'
      exact Expr.HitTrailWith.of_hitShape_nil hty)
  refine Expr.HitTrailWith.mkForall' S.hypotheses_bound.expressions ?_ hQ ?_ ?_
  · rw [hmotiveApp]
    simp only [AddInductive.getIIndices]
    have hmo := (checkPositivityStep.isValidIndApp?_some hvalid).1
    obtain ⟨mfv, hmfv⟩ := H.motive_fvar hmo
    simp only [AddInductive.getIIndices] at hmfv
    refine Expr.HitTrailWith.app_of_not_const ?_ ?_ ?_
    · refine Expr.HitTrailWith.of_hitShape_nil
        (Expr.HitShape.mkAppN ?_ (hterm.1.getAppArgs_slice hp _))
      rw [hmfv]; exact .fvar mfv
    · rw [Lean4Lean.VerifyInductive.Expr.mkAppN_eq_mkAppList,
        Lean4Lean.VerifyInductive.Expr.mkAppN_eq_mkAppList, ← Expr.mkAppList_append]
      refine Expr.HitTrailWith.const_mkAppList fun a ha => ?_
      have hfv : ∃ fv, a = .fvar fv := by
        rcases List.mem_append.1 ha with ha | ha
        · exact H.params_fvar a ha
        · obtain ⟨y, rfl, -⟩ := BoundFVarArray.fvar_of_mem S.fields_bound
            (Array.mem_toList_iff.1 ha)
          exact ⟨y, rfl⟩
      obtain ⟨fv, rfl⟩ := hfv
      exact ⟨.fvar _, .fvar _⟩
    · intro c us h
      rw [Lean4Lean.VerifyInductive.Expr.mkAppN_eq_mkAppList,
        Expr.getAppFn_mkAppList, hmfv] at h
      cases h
  · intro y hy
    obtain ⟨j, hjl, hjy⟩ := List.mem_iff_getElem.1 hy
    have hj : j < S.hypotheses.size := by
      have := congrArg Array.size S.hypotheses_bound.expressions
      simp at this; omega
    obtain ⟨D, -⟩ := (hper j hj).1
    have hDy : D.fvar = y := by
      obtain ⟨_, hget⟩ := S.hypotheses_bound.getElem_eq_fvar j hj
      have := D.expression.symm.trans hget
      rw [← hjy]; exact Expr.fvar.inj this
    subst hDy
    exact ⟨_, _, _, _, _, _, D.declaration⟩
  · intro y hy d hfind
    obtain ⟨j, hjl, hjy⟩ := List.mem_iff_getElem.1 hy
    have hj : j < S.hypotheses.size := by
      have := congrArg Array.size S.hypotheses_bound.expressions
      simp at this; omega
    obtain ⟨D, hDshape⟩ := (hper j hj).1
    have hDy : D.fvar = y := by
      obtain ⟨_, hget⟩ := S.hypotheses_bound.getElem_eq_fvar j hj
      have := D.expression.symm.trans hget
      rw [← hjy]; exact Expr.fvar.inj this
    subst hDy
    rw [D.declaration] at hfind
    cases hfind
    exact Expr.HitTrailWith.of_hitShape_nil hDshape

end CompletedRecursorConstruction

end TrailAssembly

end VerifyInductive
end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

section TrailAssembly2

variable {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
  {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
  {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
  {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
    sourceEnv indTypes ctorEnv}

namespace CompletedRecursorConstruction

variable (H : CompletedRecursorConstruction R) {names : List Name} {ls : List Level}

/-- Index declarations of every family (region R1). -/
theorem indexDeclNil (I : H.TrailInputs names ls)
    (W : WhnfHitOKFacts names [] ls H.localContext.env)
    {k : Nat} (hk : k < H.recInfos.size) {y : FVarId}
    (hy : Expr.fvar y ∈ H.recInfos[k]!.indices) :
    ∃ d, H.localContext.lctx.find? y = some d ∧ d.HitShape names [] ls := by
  obtain ⟨type, T⟩ := H.minorSources.traces k hk
  have hparamDecls : ∀ fv ∈ ExprArrayFVarIds stats.params, ∀ d,
      H.localContext.lctx.find? fv = some d →
        d.HitOK H.localContext.env names [] ls := by
    intro fv hfv d hfind
    rw [H.params.exprArrayFVarIds] at hfv
    exact (I.paramDecls fv hfv d hfind).1
  obtain ⟨-, hidx⟩ := T.hitShapeAt W (by simp) H.params_fvar rfl hparamDecls
    (Expr.HitOK.of_avoids (I.familyHeaders k (H.sourceOwner hk)).1
      (I.familyHeaders k (H.sourceOwner hk)).2)
  have hyMem : y ∈ (H.bindings.indices k hk).fvars :=
    (H.bindings.indices k hk).mem_fvars_iff.2 hy
  obtain ⟨index, name, ty, bi, kind, hfind⟩ :=
    H.localWF.findCDecl y ((H.bindings.indices k hk).members y hyMem)
  refine ⟨_, hfind, (hidx y ?_ _ hfind).hitShape⟩
  rw [(H.bindings.indices k hk).exprArrayFVarIds]
  exact hyMem

/-- Major premise declarations: `I params indices` with `I ∉ names`. -/
theorem majorDeclNil (I : H.TrailInputs names ls) {y : FVarId}
    (hy : Expr.fvar y ∈ H.recInfos.map (·.major)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧ d.HitShape names [] ls := by
  refine H.origins.majors.declHitShape (fun i hi => ?_) hy
  have hi' : i < H.recInfos.size := by simpa using hi
  rw [H.majorShapes.shape i hi']
  refine Expr.HitShape.consumeTypeAnnotationsVerified ?_ (by simp)
  obtain ⟨n, hn⟩ := H.indConst_eq hi'
  rw [hn]
  refine Expr.HitShape.mkAppN (Expr.HitShape.mkAppN (.const (I.familyNames i hi' n _ hn))
    fun a ha => ?_) fun a ha => ?_
  · obtain ⟨fv, rfl⟩ := H.params_fvar a ha
    exact .fvar fv
  · obtain ⟨fv, rfl, -⟩ := BoundFVarArray.fvar_of_mem (H.bindings.indices i hi')
      (Array.mem_toList_iff.1 ha)
    exact .fvar fv

/-- Motive declarations: `∀ indices, ∀ (t : I params indices), Sort u`. -/
theorem motiveDeclNil (I : H.TrailInputs names ls)
    (W : WhnfHitOKFacts names [] ls H.localContext.env)
    {y : FVarId} (hy : Expr.fvar y ∈ H.recInfos.map (·.motive)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧ d.HitShape names [] ls := by
  refine H.origins.motives.declHitShape (fun i hi => ?_) hy
  have hi' : i < H.recInfos.size := by simpa using hi
  rw [H.motiveShapes.shape i hi']
  refine Expr.HitShape.mkForall_of_disjoint (H.bindings.indices i hi').expressions ?_
    (by simp) (fun y hy => H.indexDeclNil I W hi'
      ((H.bindings.indices i hi').mem_fvars_iff.1 hy))
  refine Expr.HitShape.mkForall_of_disjoint (H.bindings.major i hi').expressions (.sort _)
    (by simp) (fun y hy => H.majorDeclNil I ?_)
  have h := (H.bindings.major i hi').mem_fvars_iff.1 hy
  simp only [List.mem_toArray, List.mem_singleton] at h
  rw [h]
  exact Array.mem_map.2 ⟨_, H.mem_recInfos hi', rfl⟩

/-- Minor premise declarations. -/
theorem minorDeclTrail (I : H.TrailInputs names ls)
    (W : WhnfHitOKFacts names [] ls H.localContext.env) (heads : List Name) (np : Nat)
    {y : FVarId} (hy : Expr.fvar y ∈ H.recInfos.flatMap (·.minors)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧
      d.type.HitTrailWith heads np (Expr.HitShape names [] ls) := by
  obtain ⟨i, hi, hget⟩ := Array.mem_iff_getElem.mp hy
  obtain ⟨D⟩ := H.bindings.flatMinors.declarationAt H.localWF i hi
  obtain ⟨Fm⟩ := H.origins.flatMinorOrigin D
  have hDy : D.fvar = y := Expr.fvar.inj (D.expression.symm.trans hget)
  subst hDy
  refine ⟨_, D.declaration, ?_⟩
  show D.type.HitTrailWith heads np (Expr.HitShape names [] ls)
  rw [Fm.originType_eq]
  have howner := Fm.owner_lt
  have hlocal : Fm.localIndex < H.origins.minorTypes[Fm.owner]!.size := by
    rw [(H.origins.minors Fm.owner howner).size_eq, getElem!_pos H.recInfos Fm.owner howner]
    exact Fm.local_lt
  have hsrc := H.minorSources.rows Fm.owner howner (H.sourceOwner howner) Fm.localIndex hlocal
  rw [← hsrc.1]
  exact (H.minorTrail I W heads np Fm.owner howner Fm.localIndex hlocal).2.1

private theorem cdecl_of_mem {xs : Array Expr} (B : BoundFVarArray H.localContext xs)
    {y : FVarId} (hy : y ∈ B.fvars) :
    ∃ i fv n ty bi kind, H.localContext.lctx.find? y = some (.cdecl i fv n ty bi kind) := by
  obtain ⟨index, name, type, bi, kind, hfind⟩ := H.localWF.findCDecl y (B.members y hy)
  exact ⟨index, y, name, type, bi, kind, hfind⟩

private theorem type_of_find {P : Expr → Prop} {y : FVarId}
    (h : ∃ d, H.localContext.lctx.find? y = some d ∧ P d.type) :
    ∀ d, H.localContext.lctx.find? y = some d → P d.type := by
  obtain ⟨d', hd', hP⟩ := h
  intro d hd
  rw [hd'] at hd
  cases hd
  exact hP

private theorem nil_type {y : FVarId}
    (h : ∃ d, H.localContext.lctx.find? y = some d ∧ d.HitShape names [] ls)
    (hc : ∃ i fv n ty bi kind, H.localContext.lctx.find? y = some (.cdecl i fv n ty bi kind)) :
    ∃ d, H.localContext.lctx.find? y = some d ∧ d.type.HitShape names [] ls := by
  obtain ⟨d, hd, hs⟩ := h
  obtain ⟨i, fv, n, ty, bi, kind, hc⟩ := hc
  rw [hc] at hd
  cases hd
  exact ⟨_, hc, hs⟩

/-- **Trailing provenance of the generated rule right-hand sides.** Every rule
right-hand side `blueprint.build ...` satisfies `HitTrailWith` for the
condition "mentions `names` only at `ls`", and its parameter domains avoid
`names`. -/
theorem ruleRhsTrail (I : H.TrailInputs names ls)
    (W : WhnfHitOKFacts names [] ls H.localContext.env) (heads : List Name) (np : Nat)
    (owner : Nat) (howner : owner < H.recInfos.size) (lvls : List Level)
    (blueprint : AddInductive.RecRuleBlueprint)
    (hmem : blueprint ∈ H.recInfos[owner]!.ruleBlueprints.toList) :
    (blueprint.build indTypes stats (H.recInfos.map (·.motive))
        (H.recInfos.flatMap (·.minors)) lvls H.localContext.lctx).rhs.HitTrailWith heads np
      (Expr.HitShape names [] ls) ∧
    (blueprint.build indTypes stats (H.recInfos.map (·.motive))
        (H.recInfos.flatMap (·.minors)) lvls H.localContext.lctx).rhs.LamPrefixAvoids names
      stats.params.size := by
  have hp : ∀ p ∈ ([] : List Expr), ∃ fv, p = .fvar fv := by simp
  obtain ⟨localIndex, hlocalB, hget⟩ := List.mem_iff_getElem.1 hmem
  have hlocalB' : localIndex < H.recInfos[owner]!.ruleBlueprints.size := by simpa using hlocalB
  have hlocal : localIndex < H.origins.minorTypes[owner]!.size := by
    rw [← H.blueprints.rows_size owner howner]; exact hlocalB'
  have hB : H.recInfos[owner]!.ruleBlueprints[localIndex]! = blueprint := by
    rw [getElem!_pos _ localIndex hlocalB']; simpa using hget
  obtain ⟨hfieldDecls, -, hcalls⟩ := H.minorTrail I W heads np owner howner localIndex hlocal
  have hentry := H.blueprints.entry owner howner localIndex hlocal
  rw [hB] at hcalls hentry
  obtain ⟨-, hBfields, hBlctx, hBminor, traversal, origins, -, hshape, -, -, hcallOrigins⟩ :=
    hentry
  have hcallsSize := hcallOrigins.size_eq
  generalize H.origins.minorShapes owner howner localIndex hlocal = S at *
  -- the minor variable
  have hminorsSize : localIndex < H.recInfos[owner]!.minors.size := by
    rw [← (H.origins.minors owner howner).size_eq]; exact hlocal
  have hminorMem : blueprint.minor ∈ H.recInfos[owner]!.minors := by
    rw [hBminor, getElem!_pos _ localIndex hminorsSize]; exact Array.getElem_mem hminorsSize
  obtain ⟨minorFv, hminorFv, -⟩ :=
    BoundFVarArray.fvar_of_mem (H.bindings.minors owner howner) hminorMem
  simp only [AddInductive.RecRuleBlueprint.build]
  -- the body
  have hbody : (mkAppN (mkAppN blueprint.minor blueprint.fields)
      (blueprint.recursiveCalls.map fun call =>
        call.build indTypes stats (H.recInfos.map (·.motive))
          (H.recInfos.flatMap (·.minors)) lvls)).HitShape names [] ls := by
    rw [hBfields]
    refine Expr.HitShape.mkAppN (Expr.HitShape.mkAppN (by rw [hminorFv]; exact .fvar _)
      fun a ha => ?_) fun a ha => ?_
    · obtain ⟨y, rfl, -⟩ := BoundFVarArray.fvar_of_mem S.fields_bound
        (Array.mem_toList_iff.1 ha)
      exact .fvar y
    · simp only [Array.toList_map, List.mem_map] at ha
      obtain ⟨call, hcall, rfl⟩ := ha
      obtain ⟨j, hj, hcallj⟩ := List.mem_iff_getElem.1 hcall
      have hj' : j < blueprint.recursiveCalls.size := by simpa using hj
      have hcallEq : blueprint.recursiveCalls[j]! = call := by
        rw [getElem!_pos _ j hj']; simpa using hcallj
      obtain ⟨htemplate, htarget⟩ := hcalls j (by rw [← hcallsSize]; exact hj')
      rw [hcallEq] at htemplate htarget
      simp only [AddInductive.RecCallBlueprint.build]
      refine htemplate.instantiate1 ?_ hp
      refine Expr.HitShape.mkAppN (Expr.HitShape.mkAppN
        (Expr.HitShape.mkAppN (.const (I.recursorNames _ htarget)) fun a ha => ?_)
          fun a ha => ?_) fun a ha => ?_
      · obtain ⟨fv, rfl⟩ := H.params_fvar a ha
        exact .fvar fv
      · obtain ⟨fv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.bindings.motives
          (Array.mem_toList_iff.1 ha)
        exact .fvar fv
      · obtain ⟨fv, rfl, -⟩ := BoundFVarArray.fvar_of_mem H.bindings.flatMinors
          (Array.mem_toList_iff.1 ha)
        exact .fvar fv
  have hQ : ∀ (ys : List FVarId) x d, Expr.HitShape names [] ls x →
      Expr.HitShape names [] ls (x.abstractN ys d) :=
    fun ys _ d h => h.nil_abstractN ys d
  -- the fields lambda
  have hfields : (blueprint.lctx.mkLambda blueprint.fields
      (mkAppN (mkAppN blueprint.minor blueprint.fields)
        (blueprint.recursiveCalls.map fun call =>
          call.build indTypes stats (H.recInfos.map (·.motive))
            (H.recInfos.flatMap (·.minors)) lvls))).HitShape names [] ls := by
    revert hbody
    rw [hBlctx, hBfields]
    intro hbody
    refine Expr.HitShape.mkLambda_of_disjoint S.fields_bound.expressions hbody (by simp)
      fun y hy => ?_
    obtain ⟨i, fv, n, ty, bi, kind, hfind, hty⟩ := hfieldDecls y hy
    exact ⟨_, hfind, hty⟩
  constructor
  · refine Expr.HitTrailWith.mkLambda' H.params.expressions ?_ hQ H.paramCDecls
      (fun y hy d hfind => Expr.HitTrailWith.of_hitShape_nil
        (Expr.HitShape.of_avoidsConsts (I.paramDecls y hy d hfind).2))
    refine Expr.HitTrailWith.mkLambda' H.bindings.motives.expressions ?_ hQ
      (fun y hy => H.cdecl_of_mem H.bindings.motives hy)
      (fun y hy => H.type_of_find (P := fun t => t.HitTrailWith heads np
          (Expr.HitShape names [] ls)) (by
        obtain ⟨d, hd, hs⟩ := H.nil_type (H.motiveDeclNil I W
          (H.bindings.motives.mem_fvars_iff.1 hy)) (H.cdecl_of_mem H.bindings.motives hy)
        exact ⟨d, hd, Expr.HitTrailWith.of_hitShape_nil hs⟩))
    refine Expr.HitTrailWith.mkLambda' H.bindings.flatMinors.expressions ?_ hQ
      (fun y hy => H.cdecl_of_mem H.bindings.flatMinors hy)
      (fun y hy => H.type_of_find (P := fun t => t.HitTrailWith heads np
          (Expr.HitShape names [] ls))
        (H.minorDeclTrail I W heads np (H.bindings.flatMinors.mem_fvars_iff.1 hy)))
    exact Expr.HitTrailWith.of_hitShape_nil hfields
  · have key : ∀ (ps : Array Expr), ps = (H.params.fvars.map Expr.fvar).toArray → ∀ b,
        (H.localContext.lctx.mkLambda ps b).LamPrefixAvoids names ps.size := by
      intro ps hps b
      subst hps
      simpa using Expr.LamPrefixAvoids.mkLambda (lctx := H.localContext.lctx) b fun y hy => by
        obtain ⟨i, fv, n, ty, bi, kind, hfind⟩ := H.paramCDecls y hy
        exact ⟨i, fv, n, ty, bi, kind, hfind, (I.paramDecls y hy _ hfind).2⟩
    exact key _ H.params.expressions _

end CompletedRecursorConstruction

end TrailAssembly2

end VerifyInductive
end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Major family names are not constructor names. -/
theorem CompletedRecursorConstruction.familyNames_not_mem
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) {names : List Name}
    (hnames : ∀ n ∈ names, n ∈ decl.types.flatMap (fun t => t.ctors.map (·.name)))
    (hnodup : (InductiveSignature.familyNames decl.types).Nodup) :
    ∀ i, i < H.recInfos.size → ∀ n lv, stats.indConsts[i]! = .const n lv → n ∉ names := by
  intro i hi n lv hn hmem
  have hi' : i < decl.types.length := by rw [← H.recInfos_size_eq]; exact hi
  have h := H.validStats.indConstAt hi'
  rw [getElem!_def, h] at hn
  cases hn
  exact familyName_not_mem_ctorNames hnodup _ (List.getElem_mem hi') (hnames _ hmem)

/-- The parameter declarations of a completed recursor construction avoid every
name fresh in the source environment and satisfy the projection condition. -/
theorem CompletedRecursorConstruction.paramDecls_trail
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) {env : Environment} {heads : List Name}
    {ls : List Level}
    (hfresh : ∀ name ∈ heads, sourceEnv.constants name = none)
    (hproj : ∀ s info, sourceEnv.projections s info → projHitOK env heads s) :
    ∀ fv ∈ H.params.fvars, ∀ d, H.localContext.lctx.find? fv = some d →
      d.HitOK env heads [] ls ∧ d.type.AvoidsConsts heads := by
  intro fv hfv d hfind
  have hparam : Expr.fvar fv ∈ stats.params := H.params.mem_fvars_iff.1 hfv
  have hc : fv ∈ c.lctx.fvars := by
    obtain ⟨fvars, hparams, hdecls⟩ :=
      cachedParameterDecls_fvars R.sourceMaterialized.cachedScope
    have hmem : Expr.fvar fv ∈ stats.params.toList.reverse := by simpa using hparam
    rw [hparams] at hmem
    simp only [List.mem_map, Expr.fvar.injEq, exists_eq_right] at hmem
    rw [← R.sourceContext.lctx_eq, R.sourceContext.mlctx_wf.tr.fvars_eq,
      R.sourceMaterialized.scopeDecomposition, VLCtx.fvars_append, hdecls]
    exact List.mem_append_right _ hmem
  have hfind' : c.lctx.find? fv = some d := by
    rw [← hfind]; exact (H.localExtends.declarations fv hc).symm
  have hfresh' : ∀ name ∈ heads, R.sourceContext.venv.constants name = none := by
    rw [R.sourceContextVEnv]; exact hfresh
  have hproj' : ∀ s info, R.sourceContext.venv.projections s info →
      projHitOK env heads s := by
    rw [R.sourceContextVEnv]; exact hproj
  obtain ⟨htype, hvalue⟩ := R.sourceContext.declAvoids hfresh' hfind'
  obtain ⟨ptype, pvalue⟩ := R.sourceContext.declProjsOK hproj' hfind'
  refine ⟨⟨⟨Expr.HitShape.of_avoidsConsts htype, ptype⟩, fun v hv => ?_⟩, htype⟩
  cases d with
  | cdecl => simp [LocalDecl.value?] at hv
  | ldecl _ _ _ _ val nd _ =>
    have hval : val = v := by cases nd <;> simpa [LocalDecl.value?] using hv
    subst hval
    exact ⟨Expr.HitShape.of_avoidsConsts hvalue, pvalue⟩

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {safety : DefinitionSafety} {outEnv : Environment}

/-- The auxiliary constructor names of a nested run: the constructor names of
the lowered families after the source families. -/
def NestedValidatedRunResult.auxCtorNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) : List Name :=
  (E.production.loweredDecl.types.drop sourceDecl.types.length).flatMap
    fun t => t.ctors.map (·.name)

/-- A level list of length `lparams.length + 1`, carried by no well-formed
occurrence of a constant of the run's declaration. -/
def badLevels (lparams : List Name) : List Level :=
  List.replicate (lparams.length + 1) .zero

theorem badLevels_ne (lparams : List Name) : badLevels lparams ≠ lparams.map Level.param := by
  intro h
  have := congrArg List.length h
  simp [badLevels] at this

theorem NestedValidatedRunResult.auxCtorNames_auxHeads
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    ∀ n ∈ E.auxCtorNames, n ∈ E.auxHeads := by
  intro n hn
  obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
  exact List.mem_flatMap.2 ⟨t, ht, List.mem_cons_of_mem _ hn⟩

theorem NestedValidatedRunResult.auxCtorNames_hitHeads
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    ∀ n ∈ E.auxCtorNames, n ∈ E.hitHeads :=
  fun n hn => E.auxHeads_subset_hitHeads n (E.auxCtorNames_auxHeads n hn)

theorem NestedValidatedRunResult.auxCtorNames_ctor
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv) :
    ∀ n ∈ E.auxCtorNames, ∃ t ∈ E.production.loweredDecl.types, ∃ c ∈ t.ctors, c.name = n := by
  intro n hn
  obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hn
  exact ⟨t, List.mem_of_mem_drop ht, c, hc, rfl⟩

section RunEnvTrail

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- The auxiliary constructor names are absent from the header environment, so
every lowered constructor type avoids them. -/
theorem NestedValidatedRunResult.ctorType_avoids_auxCtorNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {owner : InductiveType} (howner : owner ∈ E.production.indTypes.toList)
    {ctor : Constructor} (hctor : ctor ∈ owner.ctors) :
    ctor.type.AvoidsConsts E.auxCtorNames := by
  obtain ⟨-, -, -, -, -, -, -, hnodupAll⟩ := E.auxHeadsFacts wf Hsources
  have hnodup : (InductiveSignature.familyNames E.production.loweredDecl.types).Nodup :=
    (List.nodup_append.1 hnodupAll).1
  obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr howner hctor
  refine checkPositivityStep.TrExprS.sourceAvoidsFresh (fun n hn => ?_) htr
  obtain ⟨t, ht, c, hc, rfl⟩ := E.auxCtorNames_ctor n hn
  exact E.ctorNames_fresh_headerVEnv wf hnodup ht hc

/-- **The environment condition of the type checker's hit-shape invariant at
the auxiliary constructor names, without parameters, at `badLevels`.** Every
constant of the recursor-pass environment other than an auxiliary constructor
has a type avoiding the auxiliary constructor names (old constants: they are
fresh in the source; family headers: translated in the source; lowered
constructors: translated in the header environment, where every lowered
constructor name is fresh), and so do the auxiliary constructors themselves,
so their types are (parameterless) head types at any level list. -/
theorem NestedValidatedRunResult.envHitShape_auxCtorNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    EnvHitShape E.production.ctorEnv E.auxCtorNames 0 (badLevels lparams) := by
  have hfresh : ∀ n ∈ E.auxCtorNames, sourceProdEnv.find? n = none :=
    fun n hn => E.hitHeads_fresh wf n (E.auxCtorNames_hitHeads n hn)
  have hpres : ∀ {n ci}, sourceProdEnv.find? n = some ci →
      E.production.ctorEnv.find? n = some ci := E.ctorEnv_preserves wf
  have hwfP : E.production.c.env.constants.WF := by
    rw [E.productionEnv]; exact (wf.tr (safety := .unsafe)).map_wf
  have horigin : ∀ {n ci}, E.production.ctorEnv.find? n = some ci →
      sourceProdEnv.find? n = some ci ∨
      (∃ indType ∈ E.production.indTypes.toList, ∃ info : InductiveVal,
        ci = .inductInfo info ∧ n = indType.name ∧ info.type = indType.type ∧
        info.levelParams = lparams) ∨
      (∃ owner ∈ E.production.indTypes.toList, ∃ ctor ∈ owner.ctors, ∃ info : ConstructorVal,
        ci = .ctorInfo info ∧ n = ctor.name ∧ info.type = ctor.type ∧
        info.levelParams = lparams) := by
    intro n ci h
    have := E.production.ctorEnv_origin hwfP h
    rwa [E.productionEnv, E.productionLParams] at this
  have hfreshN : ∀ {n ci}, sourceProdEnv.find? n = some ci → n ∉ E.auxCtorNames :=
    fun h hn => by rw [hfresh _ hn] at h; cases h
  let sf : DefinitionSafety := if isUnsafe then .unsafe else .safe
  have hheaderV : E.production.headers.context.venv.Ordered :=
    E.production.headers.context.checking.tr.wf.ordered
  have hheaderSub : ∀ s info, E.production.headers.context.venv.projections s info →
      ∃ info', (ves.venv sf).projections s info' := by
    intro s info h
    rw [VEnv.addConstVals_projections_eq E.production.constructors.core.typesAdded,
      E.production_initialEnv] at h
    exact ⟨info, h⟩
  -- every new constant type avoids the auxiliary constructor names
  have hnewAvoids : ∀ {n ci}, E.production.ctorEnv.find? n = some ci →
      sourceProdEnv.find? n = none → ci.type.AvoidsConsts E.auxCtorNames := by
    intro n ci h hnew
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, rfl, htype, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, rfl, htype, -⟩
    · rw [hold] at hnew; cases hnew
    · show info.type.AvoidsConsts _
      rw [htype]
      obtain ⟨e', htr⟩ := E.familyType_tr hmem
      exact avoids_of_tr wf hfresh _ htr
    · show info.type.AvoidsConsts _
      rw [htype]
      exact E.ctorType_avoids_auxCtorNames wf Hsources howner hctor
  refine {
    prims := ?prims
    strs := ?strs
    type_avoids := ?type_avoids
    value_avoids := ?value_avoids
    rules_avoid := ?rules_avoid
    head_kind := ?head_kind
    head_type := ?head_type
    rec_major := ?rec_major
    type_projs := ?type_projs
    value_projs := ?value_projs
    rules_projs := ?rules_projs }
  case prims =>
    intro n hn hmem
    exact E.production.nonprimitive_familyNames (E.hitHeads_subset (E.auxCtorNames_hitHeads n hmem))
      (hitPrimNames_primitive n hn)
  case strs =>
    intro hs n hn hmem
    exact (E.envHitShape wf Hsources).strs hs n hn (E.auxCtorNames_hitHeads n hmem)
  case type_avoids =>
    intro n ci h hn
    cases hold : sourceProdEnv.find? n with
    | some ci' =>
      have := hpres hold
      rw [h] at this
      cases this
      exact (old_type_avoids wf hfresh hold).1
    | none => exact hnewAvoids h hold
  case value_avoids =>
    intro n ci v h hv
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · exact (old_value_avoids wf hfresh hold hv).1
    · cases hv
    · cases hv
  case rules_avoid =>
    intro n r h rule hrule
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · exact (old_rules_avoid wf hfresh hold hrule).1
    · cases heq
    · cases heq
  case head_kind =>
    intro n ci h hn
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · exact absurd hn (hfreshN hold)
    · exact .inl ⟨info, rfl⟩
    · exact .inr ⟨info, rfl⟩
  case head_type =>
    intro n ci h hn
    have hnew : sourceProdEnv.find? n = none := by
      cases hold : sourceProdEnv.find? n with
      | none => rfl
      | some ci' => exact absurd hn (hfreshN hold)
    have hav := hnewAvoids h hnew
    refine ⟨_, .zero _, ?_⟩
    show Expr.HitShapeB _ _ _ _ (ci.type.instantiateLevelParams ci.levelParams _)
    rw [Expr.instantiateLevelParams_eq]
    refine (Expr.HitShapeB.of_avoidsConsts hav 0).instantiateLevelParamsCore' fun l hl => ?_
    simp only [badLevels, List.mem_replicate] at hl
    rw [hl.2]
    rfl
  case rec_major =>
    intro n r h
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · exact old_rec_major wf hpres hfresh hold
    · cases heq
    · cases heq
  case type_projs =>
    intro n ci h
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -, htype, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -, htype, -⟩
    · obtain ⟨e', htr⟩ := (old_type_avoids wf hfresh hold).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · show info.type.ProjsOK _
      rw [htype]
      obtain ⟨e', htr⟩ := E.familyType_tr hmem
      exact projsOK_of_tr_sub wf hpres hfresh sf (wf.tr (safety := sf)).wf.ordered
        (fun s i h => ⟨i, h⟩) htr
    · show info.type.ProjsOK _
      rw [htype]
      obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr howner hctor
      exact projsOK_of_tr_sub wf hpres hfresh sf hheaderV hheaderSub htr
  case value_projs =>
    intro n ci v h hv
    rcases horigin h with hold | ⟨indType, hmem, info, rfl, -⟩ |
        ⟨owner, howner, ctor, hctor, info, rfl, -⟩
    · obtain ⟨e', htr⟩ := (old_value_avoids wf hfresh hold hv).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · cases hv
    · cases hv
  case rules_projs =>
    intro n r h rule hrule
    rcases horigin h with hold | ⟨indType, hmem, info, heq, -⟩ |
        ⟨owner, howner, ctor, hctor, info, heq, -⟩
    · obtain ⟨e', htr⟩ := (old_rules_avoid wf hfresh hold hrule).2
      exact projsOK_of_unsafe_tr wf hpres hfresh htr
    · cases heq
    · cases heq

/-- **`whnf` preserves "mentions the auxiliary constructors only at
`badLevels`"** in the recursor pass of an exact validated nested run. -/
theorem NestedValidatedRunResult.whnfHitOKFacts_auxCtorNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    WhnfHitOKFacts E.auxCtorNames [] (badLevels lparams)
      E.production.production.localContext.env := by
  refine .of_env ?_ (fun a ha => by simp at ha)
  rw [E.recursorPassEnv]
  exact E.envHitShape_auxCtorNames wf Hsources

/-- **The trailing-provenance inputs of an exact validated nested run** at the
auxiliary constructor names and `badLevels`. -/
theorem NestedValidatedRunResult.trailInputs_of
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes) :
    E.production.production.toCompletedRecursorConstruction.TrailInputs
      E.auxCtorNames (badLevels lparams) := by
  let sf : DefinitionSafety := if isUnsafe then .unsafe else .safe
  have hfresh : ∀ n ∈ E.auxCtorNames, sourceProdEnv.find? n = none :=
    fun n hn => E.hitHeads_fresh wf n (E.auxCtorNames_hitHeads n hn)
  have hpres : ∀ {n ci}, sourceProdEnv.find? n = some ci →
      E.production.production.toCompletedRecursorConstruction.localContext.env.find?
        n = some ci := by
    intro n ci h
    have := E.ctorEnv_preserves wf h
    rw [← E.recursorPassEnv] at this
    exact this
  obtain ⟨-, -, -, -, -, -, -, hnodup⟩ := E.auxHeadsFacts wf Hsources
  have hnp : result.nparams = nparams := by
    obtain ⟨_, Hrun, _, _⟩ := E.lowering
    exact Hrun.resultNParams
  have hheaderV : E.production.headers.context.venv.Ordered :=
    E.production.headers.context.checking.tr.wf.ordered
  have hheaderSub : ∀ s info, E.production.headers.context.venv.projections s info →
      ∃ info', (ves.venv sf).projections s info' := by
    intro s info h
    rw [VEnv.addConstVals_projections_eq E.production.constructors.core.typesAdded,
      E.production_initialEnv] at h
    exact ⟨info, h⟩
  have hmem : ∀ i, i < E.production.indTypes.size →
      E.production.indTypes[i]! ∈ E.production.indTypes.toList := by
    intro i hi
    rw [getElem!_pos E.production.indTypes i hi]
    exact Array.getElem_mem_toList hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine E.production.production.toCompletedRecursorConstruction.paramDecls_trail
      (fun n hn => ?_) (fun s info h => ?_)
    · rw [E.production_initialEnv]
      cases hc : (ves.venv sf).constants n with
      | none => rfl
      | some ci =>
        obtain ⟨ci', hfind, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨ci, hc⟩
        rw [hfresh n hn] at hfind; cases hfind
    · rw [E.production_initialEnv] at h
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hlookup, -⟩ :=
        (wf.tr (safety := sf)).wf.ordered.projectionShape h
      obtain ⟨ci, hci, -⟩ := (wf.tr (safety := sf)).find?_iff.2 ⟨_, hlookup⟩
      exact projHitOK_of_old wf hpres hfresh hci
  · intro i hi
    obtain ⟨e', htr⟩ := E.familyType_tr (hmem i hi)
    exact ⟨avoids_of_tr wf hfresh _ htr,
      projsOK_of_tr_sub wf hpres hfresh sf (wf.tr (safety := sf)).wf.ordered
        (fun s i h => ⟨i, h⟩) htr⟩
  · intro i hi ctor hctor
    obtain ⟨⟨e', htr⟩, -⟩ := E.ctorType_tr (hmem i hi) hctor
    refine ⟨?_, E.ctorType_avoids_auxCtorNames wf Hsources (hmem i hi) hctor,
      projsOK_of_tr_sub wf hpres hfresh sf hheaderV hheaderSub htr⟩
    obtain ⟨body, hl, -⟩ := E.ctorTypes_headType wf Hsources _ (hmem i hi) ctor hctor
    rw [E.statsParamsSize, hnp]
    exact ⟨body, hl.leadingBinders⟩
  · exact E.production.production.toCompletedRecursorConstruction.recursorNames_not_mem
      (fun _ hh => E.hitHeads_subset (E.auxCtorNames_hitHeads _ hh)) hnodup
  · refine E.production.production.toCompletedRecursorConstruction.familyNames_not_mem
      (fun n hn => ?_) (List.nodup_append.1 hnodup).1
    obtain ⟨t, ht, hn⟩ := List.mem_flatMap.1 hn
    exact List.mem_flatMap.2 ⟨t, List.mem_of_mem_drop ht, hn⟩

end RunEnvTrail

end VerifyInductive
end Lean4Lean

namespace Lean.Expr

/-- `LamPrefixAvoids` mono in the avoided names. -/
theorem LamPrefixAvoids.mono {names names' : List Name} {k : Nat} {e : Expr}
    (H : LamPrefixAvoids names k e) (hsub : ∀ n ∈ names', n ∈ names) :
    LamPrefixAvoids names' k e := by
  induction H with
  | zero => exact .zero _
  | succ hd _ ih => exact .succ (hd.mono hsub) ih

/-- `HitTrailAvoids` mono in the avoided names. -/
theorem HitTrailAvoids.mono {heads names names' : List Name} {np : Nat} {e : Expr}
    (H : e.HitTrailAvoids heads names np) (hsub : ∀ n ∈ names', n ∈ names) :
    e.HitTrailAvoids heads names' np := by
  induction H with
  | bvar => exact .bvar _
  | fvar => exact .fvar _
  | mvar => exact .mvar _
  | sort => exact .sort _
  | const => exact .const _ _
  | lit _ h => exact .lit _ (h.mono hsub)
  | app _ _ h ihf iha =>
    exact .app ihf iha fun c us hfn hc x hx => (h c us hfn hc x hx).mono hsub
  | lam _ _ ihd ihb => exact .lam ihd ihb
  | forallE _ _ ihd ihb => exact .forallE ihd ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

/-- A lambda prefix avoiding `names` around a body in parameterless hit shape
is in parameterless hit shape. -/
theorem LamPrefixAvoids.hitShape_nil {names : List Name} {ls : List Level} {k : Nat}
    {e body : Expr} (H : LamPrefixAvoids names k e) (hl : LeadingBinders k e body)
    (hb : HitShape names [] ls body) : HitShape names [] ls e := by
  induction H generalizing body with
  | zero => cases hl; exact hb
  | succ hd _ ih =>
    cases hl with
    | lam hl' => exact .lam (.of_avoidsConsts hd) (ih hl' hb)

end Lean.Expr

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

theorem NestedValidatedRunResult.LoweredRulesAvoid.mono
    {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceEnv : VEnv} {sourceDecl : VInductDecl} {lparams : List Name}
    {nparams : Nat} {isUnsafe : Bool} {safety : DefinitionSafety}
    {outEnv : Environment}
    {E : NestedValidatedRunResult result sourceProdEnv sourceTypes sourceEnv
      sourceDecl lparams nparams isUnsafe safety outEnv}
    {heads X Y : List Name} (H : E.LoweredRulesAvoid heads X) (hsub : ∀ n ∈ Y, n ∈ X) :
    E.LoweredRulesAvoid heads Y :=
  fun owner rec hfind rule hrule =>
    ⟨(H owner rec hfind rule hrule).1.mono hsub, (H owner rec hfind rule hrule).2.mono hsub⟩

section RunTrail

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- The lowered recursor found at a generated owner's recursor name is the
owner's generated entry. -/
theorem NestedValidatedRunResult.generatedEntryOfFind
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (owner : Fin E.production.production.generationSignature.families.size)
    {rec : RecursorVal}
    (hfind : E.loweredEnv.find?
        (E.production.production.canonicalGeneration.recursorName owner) =
      some (.recInfo rec)) :
    ∃ hi : owner.val < E.production.production.entries.length,
      (E.production.production.generated.entry owner.val hi).info = rec := by
  rcases E.production.production.metadataRealization owner with
    ⟨rec', hrec, _, M⟩
  have hlen : owner.val < E.production.production.entries.length := by
    rw [E.production.production.entries_length_eq]
    exact owner.isLt
  refine ⟨hlen, ?_⟩
  have hmem := List.getElem_mem (l := E.production.production.entries)
    (n := owner.val) hlen
  have hfind' := E.production.production.findRecursorOfMem
    (info := (E.production.production.entries[owner.val]'hlen).1) hmem
  have hrec' : (E.production.production.entries[owner.val]'hlen).1 = .recInfo rec' := hrec
  rw [hrec'] at hfind'
  change E.loweredEnv.find? rec'.name = some (.recInfo rec') at hfind'
  have h2 : some (ConstantInfo.recInfo rec') = some (.recInfo rec) := by
    rw [← hfind', M.name]
    exact hfind
  have heq : rec' = rec := by
    injection h2 with h
    injection h
  have hG := (E.production.production.generated.entry owner.val hlen).source_eq
  rw [hrec] at hG
  injection hG with hG
  rw [← heq, hG]

/-- **Input-side avoidance of the auxiliary constructor names by the lowered
recursor rules.** In every rule right-hand side of every lowered recursor of an
exact validated nested run, the trailing arguments of the hits (of any head
list), the literals and the parameter domains avoid the auxiliary constructor
names.

The proof runs the trailing provenance chain (`ruleRhsTrail`) at the auxiliary
constructor names without parameters, at the impossible levels `badLevels`
(`whnfHitOKFacts_auxCtorNames`): the regions computed by `whnf`, the
constructor field domains, the index domains and the parameter domains mention
the auxiliary constructors only at `badLevels`, and the only other occurrences
are the minors' constructor applications, whose trailing arguments are fields.
The hit-shape chain at the declaration's levels (`recursorHitShape_hitHeads`)
says that every occurrence is at `lparams.map Level.param ≠ badLevels`, so the
trailing occurrences do not exist. -/
theorem NestedValidatedRunResult.loweredRulesAvoid_auxCtorNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    (heads : List Name) :
    E.LoweredRulesAvoid heads E.auxCtorNames := by
  intro owner rec hfind rule hrule
  obtain ⟨hi, hinfo⟩ := E.generatedEntryOfFind owner hfind
  let C := E.production.production
  have howner : owner.val < C.recInfos.size := by rw [← C.generated.length]; exact hi
  have hrule' : rule ∈ (C.generated.entry owner.val hi).info.rules := by rw [hinfo]; exact hrule
  -- the declaration-level hit shape
  have W := E.whnfHitOKFacts wf Hsources
  rw [← E.statsLevels] at W
  have HS := (C.generatedHitShape (E.hitShapeInputs_of wf Hsources) W owner.val hi).2 rule hrule'
  -- the trailing provenance at `badLevels`
  rw [(C.generated.entry owner.val hi).rules_eq] at hrule'
  simp only [List.mem_map] at hrule'
  obtain ⟨blueprint, hmem, rfl⟩ := hrule'
  obtain ⟨HT, HL⟩ := C.toCompletedRecursorConstruction.ruleRhsTrail
    (E.trailInputs_of wf Hsources) (E.whnfHitOKFacts_auxCtorNames wf Hsources)
    heads result.nparams owner.val howner
    (AddInductive.getRecLevels C.elimLevel E.production.stats.levels) blueprint hmem
  have hsize : E.production.stats.params.size = result.nparams := E.statsParamsSize
  obtain ⟨body, hl, hb⟩ := HS
  rw [hsize] at HL hl
  rw [E.statsLevels] at hb
  have Hglob := HL.hitShape_nil hl
    ((hb.toNil).nil_mono (fun n hn => E.auxCtorNames_hitHeads n hn))
  obtain ⟨-, -, -, -, -, hreserved, -, -⟩ := E.auxHeadsFacts wf Hsources
  have hlit : ∀ l : Literal, (Expr.lit l).AvoidsConsts E.auxCtorNames :=
    avoidsConsts_lit_of_reserved fun n hn => hreserved n (E.auxCtorNames_auxHeads n hn)
  exact ⟨HT.toHitTrailAvoids Hglob (badLevels_ne lparams) (fun _ h => h) hlit, HL⟩

end RunTrail

end VerifyInductive
end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open InductiveSignature

namespace VerifyInductive

/-! ### Shape of the auxiliary family names -/

private theorem nestedAuxFold_keys (P : Name → Prop) :
    ∀ (entries : List (Expr × Name)) (map : Std.TreeMap Name Expr Name.quickCmp),
      (∀ entry ∈ entries, P entry.2) →
      (∀ name nested, map[name]? = some nested → P name) →
      ∀ name nested, (entries.foldl
        (fun (map : Std.TreeMap Name Expr Name.quickCmp)
          (entry : Expr × Name) => map.insert entry.2 entry.1) map)[name]? = some nested →
        P name
  | [], _, _, Hmap => Hmap
  | entry :: entries, map, Hentries, Hmap => by
    simp only [List.foldl_cons]
    refine nestedAuxFold_keys P entries _ (fun e he => Hentries e (.tail _ he)) ?_
    intro query value hfind
    rw [Std.TreeMap.getElem?_insert] at hfind
    split at hfind
    next hcmp =>
      rw [← Std.LawfulEqCmp.eq_of_compare hcmp]
      exact Hentries entry (.head _)
    next => exact Hmap query value hfind

/-- **The auxiliary family names of a lowering run are numeric**:
`Name.mkNum `_nested i` (`mkUniqueName`). -/
theorem NestedLoweringRun.resultFamilyNamesIndexedOfEmpty
    {env : Environment} {fuel nparams : Nat} {types : List InductiveType}
    {initialState finalState : Lean4Lean.ElimNestedInductive.State}
    {result : Lean4Lean.ElimNestedInductive.Result}
    (H : NestedLoweringRun env fuel nparams types initialState (result, finalState))
    (hempty : initialState.nestedAux = #[]) :
    ∀ (name : Name) (nested : Expr),
      (show Std.TreeMap Name Expr Name.quickCmp from result.aux2nested)[name]? = some nested →
      ∃ i, name = Name.mkNum `_nested i := by
  have Hnames := H.resultNamesWF (NestedAuxNamesWF.empty initialState hempty)
  rw [H.resultAuxMap]
  change ∀ (name : Name) (nested : Expr), (finalState.nestedAux.foldl
      (fun (map : Std.TreeMap Name Expr Name.quickCmp)
        (entry : Expr × Name) => map.insert entry.2 entry.1) {})[name]? = some nested →
      ∃ i, name = Name.mkNum `_nested i
  rw [← Array.foldl_toList]
  refine nestedAuxFold_keys (fun name => ∃ i, name = Name.mkNum `_nested i) _ _ ?_ ?_
  · intro entry hentry
    obtain ⟨i, hi, -⟩ := Hnames.indexed entry.1 entry.2 (by simpa using hentry)
    exact ⟨i, hi⟩
  · intro name nested hfind; simp at hfind

/-- The lowered families after the source families are named by the
specializations. -/
theorem auxiliarySpecializations_familyNames
    {sourceEnv envTypes : VEnv} {paramCtx : List VExpr} {decl : VInductDecl}
    {env : VEnv} {leaf : Nat → VExpr → VExpr → Prop}
    {auxiliaries : List ContainerSpecialization} {generated targets : List VInductiveType}
    (H : List.Forall₂ (AuxiliarySpecializationEvidence sourceEnv envTypes paramCtx decl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion env decl leaf)
      generated targets) :
    ∀ t ∈ targets, ∃ a ∈ auxiliaries, t.name = a.auxiliary := by
  induction H generalizing targets with
  | nil => cases Hexpansion; simp
  | @cons a family _ _ h _ ih =>
    cases Hexpansion with
    | @cons _ target _ _ hexp htail =>
      intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · refine ⟨a, .head _, ?_⟩
        rw [h.auxiliary]
        exact hexp.name
      · obtain ⟨b, hb, hname⟩ := ih htail t ht
        exact ⟨b, .tail _ hb, hname⟩

variable {ves : VEnvs} {result : Lean4Lean.ElimNestedInductive.Result}
    {sourceProdEnv : Environment} {sourceTypes : List InductiveType}
    {sourceDecl : VInductDecl} {lparams : List Name} {nparams : Nat}
    {isUnsafe : Bool} {outEnv : Environment}

/-- **The restorable renamed names are auxiliary constructor names.** A renamed
auxiliary recursor name `Main.rec_k` that is a restorable name is the name of
an auxiliary constructor: lowered auxiliary recursor names are never renamed
(`auxRecName_not_renamed`), and auxiliary family names are numeric
(`_nested.i`) while renamed names are string extensions. -/
theorem NestedValidatedRunResult.restorableRenamed_auxCtorNames
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    ∀ n ∈ ((compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd).filter
        (· ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames),
      n ∈ E.auxCtorNames := by
  intro n hn
  simp only [List.mem_filter, decide_eq_true_eq] at hn
  obtain ⟨hX, hR⟩ := hn
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hX
  obtain ⟨s, hs⟩ := compilationRestoration_recursors_snd_str sourceDecl auxiliaries p hp
  simp only [Restoration.restorableNames, List.mem_append] at hR
  rcases hR with hhead | hfst
  · rw [compilationRestoration_heads_auxiliary,
      auxiliarySpecializations_headNames Haux Hexpansion] at hhead
    obtain ⟨t, ht, hmem⟩ := List.mem_flatMap.1 hhead
    rcases List.mem_cons.1 hmem with hname | hctor
    · exfalso
      obtain ⟨a, ha, hta⟩ := auxiliarySpecializations_familyNames Haux Hexpansion t ht
      obtain ⟨nested, hnested⟩ := D.familyLookup a ha
      rcases E.lowering with ⟨finalState, Hrun, -, -⟩
      obtain ⟨i, hi⟩ := Hrun.resultFamilyNamesIndexedOfEmpty rfl _ _ hnested
      rw [hname, hta, hi] at hs
      simp [Name.mkNum] at hs
    · exact List.mem_flatMap.2 ⟨t, ht, hctor⟩
  · exfalso
    rw [compilationRestoration_recursors_fst] at hfst
    obtain ⟨a, ha, heq⟩ := List.mem_map.1 hfst
    exact E.auxRecName_not_renamed wf Hsources D a ha (heq ▸ hX)

/-- **Input-side avoidance of the restorable renamed names by the lowered
rules**, for a restoration table of `restorationTablesRestoringAll`: the
residue `LoweredRulesAvoid` of the restored-equation junction at the
restorable names among the renamed auxiliary recursor names, discharged from
the run alone (`loweredRulesAvoid_auxCtorNames`,
`restorableRenamed_auxCtorNames`). -/
theorem NestedValidatedRunResult.loweredRulesAvoid_renamed
    (E : NestedValidatedRunResult result sourceProdEnv sourceTypes
      (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl lparams
      nparams isUnsafe (if isUnsafe then .unsafe else .safe) outEnv)
    (wf : ves.WFCore sourceProdEnv) (Hsources : SourceSyntaxChecks sourceTypes)
    {envTypes : VEnv} {generated : List VInductiveType}
    {auxiliaries : List ContainerSpecialization}
    (Haux : List.Forall₂ (AuxiliarySpecializationEvidence
      (ves.venv (if isUnsafe then .unsafe else .safe)) envTypes
      E.production.headers.commonParameterContext sourceDecl)
      auxiliaries generated)
    (Hexpansion : List.Forall₂ (VInductDecl.NestedTypeExpansion
        (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl
        (VInductDecl.NestedAuxiliarySourceAbsolute
          (ves.venv (if isUnsafe then .unsafe else .safe)) sourceDecl generated))
      generated (E.production.loweredDecl.types.drop sourceDecl.types.length))
    (D : RestorationTableData sourceDecl auxiliaries result E.loweredEnv
      (Lean4Lean.mkAuxRecNameMap E.loweredEnv sourceTypes).2 lparams) :
    E.LoweredRulesAvoid E.auxHeads
      (((compilationRestoration sourceDecl auxiliaries).recursors.map Prod.snd).filter
        (· ∈ (compilationRestoration sourceDecl auxiliaries).restorableNames)) :=
  (E.loweredRulesAvoid_auxCtorNames wf Hsources E.auxHeads).mono
    (E.restorableRenamed_auxCtorNames wf Hsources Haux Hexpansion D)

end VerifyInductive
end Lean4Lean
