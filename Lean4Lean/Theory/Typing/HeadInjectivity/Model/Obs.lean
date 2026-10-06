import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Classes

/-! # Observations, subsumption and observation typing (milestone M1)

Atomic observations of the glued model (`docs/inductives/PHASE1B_NOTES.md`, section 9.1):
a term denotes the *set* of its observations, so joins are unions and the typing filter is
a property of single observations.

* `Ob`: the observations. `sort ℓ` (the value is a sort of level `ℓ`, the evaluation of the
  level); `piDom D`, `piDomOb o`, `piCod c C`, `piCodOb c K o` (a Pi type with domain type
  class `D`, a domain with observation `o`, a codomain instance at argument class `c` with
  type class `C`, a codomain instance at an argument of class `c` with observations `K`
  having observation `o`); `app D c K o` (a function with domain class `D` which, applied to
  an argument of class `c` with observations covering `K`, has observation `o`); `rigid n ℓs
  m` and `rigidArg i c` (an application of the rigid constant `n` at levels `ℓs` to `m`
  arguments, the `i`-th of class `c`). The notes' `rigidArgOb` is not needed by the
  rule-free milestone M2 and is omitted.
* `Ob.Le o o'` (`o ≼ o'`, "`o'` is weaker"): structural, with key lists compared
  contravariantly: `app D c K o ≼ app D c K' o'` when `K'` covers `K` (`Covers K' K`: every
  key of `K` is subsumed by one of `K'`) and `o ≼ o'`. Reflexive and transitive.
* `TypedOb o τs` ("`o`, an observation of a value, is typed at the observations `τs` of its
  type"), an inductive predicate. The value's class is not a parameter (deviation from the
  notes, recorded in section 10: it was only needed for typed key observations of the
  omitted `rigidArgOb`).

`TypedOb.strengthen`: typing is stable under replacing the type observations by stronger
ones (this is what transfers typing along `defeqDF`). `TypedOb.not_prop`: nothing is
typed at a list of observations all of which are typed at `[sort 0]` (the observations of a
proposition): the semantic content of proof irrelevance. -/

namespace Lean4Lean
namespace VEnv
namespace Model

/-- Observations. Classes are sets of terms in the target context (`VExpr → Prop`). -/
inductive Ob where
  | sort (ℓ : List Nat → Nat)
  | piDom (D : VExpr → Prop)
  | piDomOb (o : Ob)
  | piCod (c C : VExpr → Prop)
  | piCodOb (c : VExpr → Prop) (K : List Ob) (o : Ob)
  | app (D c : VExpr → Prop) (K : List Ob) (o : Ob)
  | rigid (n : Name) (ℓs : List (List Nat → Nat)) (nargs : Nat)
  | rigidArg (i : Nat) (c : VExpr → Prop)
  /-- The `i`-th argument of a rigid spine has the observation `o`. -/
  | rigidArgOb (i : Nat) (o : Ob)
  /-- A constructor application of `c` at levels `ℓs` to `nargs` arguments. -/
  | ctorHead (c : Name) (ℓs : List (List Nat → Nat)) (nargs : Nat)
  /-- The `i`-th argument of a constructor application has class `c`. -/
  | ctorArg (i : Nat) (c : VExpr → Prop)
  /-- The `i`-th argument of a constructor application has `o`; `pre` records the keys of
  the earlier arguments (an annotation for typing). -/
  | ctorArgOb (i : Nat) (pre : List ((VExpr → Prop) × (VExpr → Prop) × List Ob)) (o : Ob)
  /-- Field `j` of an eta-structure value has `o`; `pre` records the parameter keys and the
  earlier fields' observation lists (an annotation for typing). -/
  | fieldOb (j : Nat) (pre : List ((VExpr → Prop) × (VExpr → Prop) × List Ob)) (o : Ob)

/-- Subsumption: `Ob.Le o o'` says `o'` is weaker than `o`. Key lists are compared
contravariantly, through an explicit choice function (keeping the definition free of
nested occurrences). -/
inductive Ob.Le : Ob → Ob → Prop
  | refl : Ob.Le o o
  | piDomOb : Ob.Le o o' → Ob.Le (.piDomOb o) (.piDomOb o')
  | piCodOb (f : Ob → Ob) : (∀ k ∈ K, f k ∈ K') → (∀ k ∈ K, Ob.Le (f k) k) → Ob.Le o o' →
    Ob.Le (.piCodOb c K o) (.piCodOb c K' o')
  | app (f : Ob → Ob) : (∀ k ∈ K, f k ∈ K') → (∀ k ∈ K, Ob.Le (f k) k) → Ob.Le o o' →
    Ob.Le (.app D c K o) (.app D c K' o')
  | rigidArgOb : Ob.Le o o' → Ob.Le (.rigidArgOb i o) (.rigidArgOb i o')
  | ctorArgOb : Ob.Le o o' → Ob.Le (.ctorArgOb i pre o) (.ctorArgOb i pre o')
  | fieldOb : Ob.Le o o' → Ob.Le (.fieldOb j pre o) (.fieldOb j pre o')

@[inherit_doc] scoped infix:50 " ≼ " => Ob.Le

/-- `Covers K' K`: every observation of `K` is subsumed by one of `K'` (an argument with the
observations `K'` satisfies the demand `K`). -/
def Covers (K' K : List Ob) : Prop := ∀ k ∈ K, ∃ k' ∈ K', k' ≼ k

/-- `Ob.Sub X Y` (`X ⊆ ↑Y`): every observation of `X` is subsumed by one of `Y`. -/
def Ob.Sub (X Y : Ob → Prop) : Prop := ∀ o, X o → ∃ o', Y o' ∧ o' ≼ o

/-! ## Subsumption -/

namespace Ob

theorem _root_.Lean4Lean.VEnv.Model.Covers.choice {K K' : List Ob} (h : Covers K' K) :
    ∃ f : Ob → Ob, (∀ k ∈ K, f k ∈ K') ∧ ∀ k ∈ K, f k ≼ k := by
  classical
  refine ⟨fun k => if hk : k ∈ K then (h k hk).choose else k, ?_, ?_⟩ <;> intro k hk <;>
    simp only [hk, dite_true]
  · exact (h k hk).choose_spec.1
  · exact (h k hk).choose_spec.2

theorem Le.app' (h : Covers K' K) (ho : o ≼ o') : .app D c K o ≼ .app D c K' o' :=
  let ⟨f, h1, h2⟩ := Covers.choice h; .app f h1 h2 ho

theorem Le.piCodOb' (h : Covers K' K) (ho : o ≼ o') : .piCodOb c K o ≼ .piCodOb c K' o' :=
  let ⟨f, h1, h2⟩ := Covers.choice h; .piCodOb f h1 h2 ho

/-- Pre- and post-composition, proved together by induction on the middle derivation
(key lists are contravariant, so each half needs the other on the keys). -/
theorem Le.trans_aux (h : x ≼ y) : (∀ w, w ≼ x → w ≼ y) ∧ (∀ z, y ≼ z → x ≼ z) := by
  induction h with
  | refl => exact ⟨fun _ h => h, fun _ h => h⟩
  | piDomOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .piDomOb (ih.1 _ .refl)
      | piDomOb h => exact .piDomOb (ih.1 _ h)
    · cases hz with
      | refl => exact .piDomOb (ih.2 _ .refl)
      | piDomOb h => exact .piDomOb (ih.2 _ h)
  | piCodOb f hf1 hf2 _ ihk iho =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .piCodOb f hf1 hf2 (iho.1 _ .refl)
      | piCodOb g hg1 hg2 hgo =>
        refine .piCodOb (fun k => f (g k)) (fun k hk => hf1 _ (hg1 k hk))
          (fun k hk => (ihk _ (hg1 k hk)).2 _ (hg2 k hk)) (iho.1 _ hgo)
    · cases hz with
      | refl => exact .piCodOb f hf1 hf2 (iho.2 _ .refl)
      | piCodOb g hg1 hg2 hgo =>
        refine .piCodOb (fun k => g (f k)) (fun k hk => hg1 _ (hf1 k hk))
          (fun k hk => (ihk k hk).1 _ (hg2 _ (hf1 k hk))) (iho.2 _ hgo)
  | rigidArgOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .rigidArgOb (ih.1 _ .refl)
      | rigidArgOb h => exact .rigidArgOb (ih.1 _ h)
    · cases hz with
      | refl => exact .rigidArgOb (ih.2 _ .refl)
      | rigidArgOb h => exact .rigidArgOb (ih.2 _ h)
  | ctorArgOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .ctorArgOb (ih.1 _ .refl)
      | ctorArgOb h => exact .ctorArgOb (ih.1 _ h)
    · cases hz with
      | refl => exact .ctorArgOb (ih.2 _ .refl)
      | ctorArgOb h => exact .ctorArgOb (ih.2 _ h)
  | fieldOb _ ih =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .fieldOb (ih.1 _ .refl)
      | fieldOb h => exact .fieldOb (ih.1 _ h)
    · cases hz with
      | refl => exact .fieldOb (ih.2 _ .refl)
      | fieldOb h => exact .fieldOb (ih.2 _ h)
  | app f hf1 hf2 _ ihk iho =>
    refine ⟨fun w hw => ?_, fun z hz => ?_⟩
    · cases hw with
      | refl => exact .app f hf1 hf2 (iho.1 _ .refl)
      | app g hg1 hg2 hgo =>
        refine .app (fun k => f (g k)) (fun k hk => hf1 _ (hg1 k hk))
          (fun k hk => (ihk _ (hg1 k hk)).2 _ (hg2 k hk)) (iho.1 _ hgo)
    · cases hz with
      | refl => exact .app f hf1 hf2 (iho.2 _ .refl)
      | app g hg1 hg2 hgo =>
        refine .app (fun k => g (f k)) (fun k hk => hg1 _ (hf1 k hk))
          (fun k hk => (ihk k hk).1 _ (hg2 _ (hf1 k hk))) (iho.2 _ hgo)

theorem Le.trans (h1 : x ≼ y) (h2 : y ≼ z) : x ≼ z := (Le.trans_aux h1).2 _ h2

theorem _root_.Lean4Lean.VEnv.Model.Covers.refl : Covers K K := fun k hk => ⟨k, hk, .refl⟩

theorem _root_.Lean4Lean.VEnv.Model.Covers.trans (h1 : Covers K₃ K₂) (h2 : Covers K₂ K₁) : Covers K₃ K₁ := fun k hk =>
  let ⟨k₂, hk₂, l₂⟩ := h2 k hk; let ⟨k₃, hk₃, l₃⟩ := h1 k₂ hk₂; ⟨k₃, hk₃, l₃.trans l₂⟩

theorem _root_.Lean4Lean.VEnv.Model.Covers.nil : Covers K [] := nofun

theorem _root_.Lean4Lean.VEnv.Model.Covers.of_subset (h : ∀ k ∈ K, k ∈ K') : Covers K' K := fun k hk => ⟨k, h k hk, .refl⟩

theorem Sub.refl : Sub X X := fun o h => ⟨o, h, .refl⟩

theorem Sub.trans (h1 : Sub X Y) (h2 : Sub Y Z) : Sub X Z := fun o h =>
  let ⟨o₁, h₁, l₁⟩ := h1 o h; let ⟨o₂, h₂, l₂⟩ := h2 o₁ h₁; ⟨o₂, h₂, l₂.trans l₁⟩

theorem Sub.of_imp (h : ∀ o, X o → Y o) : Sub X Y := fun o ho => ⟨o, h o ho, .refl⟩

/-! ### Inversion -/

theorem Le.sort_inv (h : o ≼ .sort ℓ) : o = .sort ℓ := by cases h; rfl
theorem Le.piDom_inv (h : o ≼ .piDom D) : o = .piDom D := by cases h; rfl
theorem Le.piCod_inv (h : o ≼ .piCod c C) : o = .piCod c C := by cases h; rfl
theorem Le.rigid_inv (h : o ≼ .rigid n ℓs m) : o = .rigid n ℓs m := by cases h; rfl
theorem Le.rigidArg_inv (h : o ≼ .rigidArg i c) : o = .rigidArg i c := by cases h; rfl
theorem Le.ctorHead_inv (h : o ≼ .ctorHead c ℓs n) : o = .ctorHead c ℓs n := by cases h; rfl
theorem Le.ctorArg_inv (h : o ≼ .ctorArg i c) : o = .ctorArg i c := by cases h; rfl

theorem Le.rigidArgOb_inv (h : o ≼ .rigidArgOb i x) : ∃ y, o = .rigidArgOb i y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, rfl, .refl⟩
  | rigidArgOb h => exact ⟨_, rfl, h⟩

theorem Le.ctorArgOb_inv (h : o ≼ .ctorArgOb i pre x) :
    ∃ y, o = .ctorArgOb i pre y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, rfl, .refl⟩
  | ctorArgOb h => exact ⟨_, rfl, h⟩

theorem Le.fieldOb_inv (h : o ≼ .fieldOb j pre x) : ∃ y, o = .fieldOb j pre y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, rfl, .refl⟩
  | fieldOb h => exact ⟨_, rfl, h⟩

theorem Le.piDomOb_inv (h : o ≼ .piDomOb x) : ∃ y, o = .piDomOb y ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, rfl, .refl⟩
  | piDomOb h => exact ⟨_, rfl, h⟩

theorem Le.piCodOb_inv (h : o ≼ .piCodOb c K x) :
    ∃ K₀ y, o = .piCodOb c K₀ y ∧ Covers K K₀ ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | piCodOb f h1 h2 h3 => exact ⟨_, _, rfl, fun k hk => ⟨f k, h1 k hk, h2 k hk⟩, h3⟩

theorem Le.app_inv (h : o ≼ .app D c K x) :
    ∃ K₀ y, o = .app D c K₀ y ∧ Covers K K₀ ∧ y ≼ x := by
  cases h with
  | refl => exact ⟨_, _, rfl, .refl, .refl⟩
  | app f h1 h2 h3 => exact ⟨_, _, rfl, fun k hk => ⟨f k, h1 k hk, h2 k hk⟩, h3⟩

end Ob

/-- Choose, for each element of a list, a related witness: a list of witnesses covering it. -/
theorem exists_list_cover {α β : Type} {P : β → Prop} {R : β → α → Prop} :
    ∀ {L : List α}, (∀ x ∈ L, ∃ y, P y ∧ R y x) →
      ∃ L' : List β, (∀ y ∈ L', P y) ∧ ∀ x ∈ L, ∃ y ∈ L', R y x
  | [], _ => ⟨[], nofun, nofun⟩
  | x :: L, h => by
    obtain ⟨y, hy, hxy⟩ := h x (.head _)
    obtain ⟨L', h1, h2⟩ := exists_list_cover fun x hx => h x (.tail _ hx)
    refine ⟨y :: L', ?_, ?_⟩
    · intro z hz; cases hz with
      | head => exact hy
      | tail _ hz => exact h1 z hz
    · intro z hz; cases hz with
      | head => exact ⟨y, .head _, hxy⟩
      | tail _ hz => let ⟨w, hw, h⟩ := h2 z hz; exact ⟨w, .tail _ hw, h⟩

/-! ## Rigid spine observations -/

/-- A key of a spine observation: domain class, argument class, argument observations. -/
abbrev Key := (VExpr → Prop) × (VExpr → Prop) × List Ob

/-- Wrap an observation in the `app` observations of a spine of keys, outermost first. -/
def wrap (keys : List Key) (o : Ob) : Ob := keys.foldr (fun k o => .app k.1 k.2.1 k.2.2 o) o

@[simp] theorem wrap_nil : wrap [] o = o := rfl
@[simp] theorem wrap_cons : wrap (k :: ks) o = .app k.1 k.2.1 k.2.2 (wrap ks o) := rfl

theorem wrap_append : wrap (ks ++ ks') o = wrap ks (wrap ks' o) := by
  simp [wrap, List.foldr_append]

/-- The innermost observations of a rigid spine after the keys `keys`. -/
def RigidEnd (n : Name) (ℓs : List (List Nat → Nat)) (keys : List Key) (r : Ob) : Prop :=
  r = .rigid n ℓs keys.length ∨ ∃ i, ∃ h : i < keys.length, r = .rigidArg i (keys[i]).2.1

/-- An observation that is not an `app` observation. -/
def Ob.NotApp : Ob → Prop
  | .app .. => False
  | _ => True

theorem RigidEnd.notApp (h : RigidEnd n ℓs keys r) : r.NotApp := by
  rcases h with rfl | ⟨_, _, rfl⟩ <;> trivial

/-- Spines of non-`app` endpoints are determined by the wrapped observation. -/
theorem wrap_inj {ks ks' : List Key} (h : wrap ks o = wrap ks' o') (ho : o.NotApp)
    (ho' : o'.NotApp) : ks = ks' ∧ o = o' := by
  induction ks generalizing ks' with
  | nil =>
    cases ks' with
    | nil => exact ⟨rfl, h⟩
    | cons k ks' => subst h; cases ho
  | cons k ks ih =>
    cases ks' with
    | nil => subst h; cases ho'
    | cons k' ks' =>
      simp only [wrap_cons, Ob.app.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      have := ih h4
      exact ⟨by rw [← this.1]; obtain ⟨_, _, _⟩ := k; obtain ⟨_, _, _⟩ := k'; simp_all, this.2⟩

/-! ## Observation typing -/

section
variable (env : VEnv) (U : Nat) (Δ : List VExpr)

/-- `TypedOb o τs`: the observation `o` of a value is typed at the observations `τs` of its
type. Sorts are typed at their successor; type observations at some sort, a codomain
observation at a level that vanishes whenever the Pi's level does (so that observations of
propositions are typed at `sort 0` only); an `app` observation needs the Pi's domain class,
its keys typed at observations of the domain, its argument class typed, and its result
typed at observations of the codomain instance at a key list it covers. -/
inductive TypedOb : Ob → List Ob → Prop
  | sort : .sort (fun ns => ℓ ns + 1) ∈ τs → TypedOb (.sort ℓ) τs
  | piDom : .sort ℓ ∈ τs → TypedOb (.piDom D) τs
  | piDomOb : .sort ℓ ∈ τs → TypedOb (.piDomOb o) τs
  | piCod : .sort ℓ ∈ τs → TypedOb (.piCod c C) τs
  | piCodOb : .sort ℓ ∈ τs → TypedOb o [.sort ℓ'] → (∀ ns, ℓ ns = 0 → ℓ' ns = 0) →
    TypedOb (.piCodOb c K o) τs
  | app : .piDom D ∈ τs → (∀ x ∈ τd, .piDomOb x ∈ τs) → (∀ k ∈ K, TypedOb k τd) →
    TypedElCls env U Δ D c → (∀ x ∈ τc, ∃ K₀, .piCodOb c K₀ x ∈ τs ∧ Covers K K₀) →
    TypedOb o τc → TypedOb (.app D c K o) τs
  | rigid : .sort ℓ ∈ τs → TypedOb (.rigid n ℓs m) τs
  | rigidArg : .sort ℓ ∈ τs → TypedOb (.rigidArg i c) τs
  | rigidArgOb : .sort ℓ ∈ τs → TypedOb (.rigidArgOb i o) τs

end

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

/-- Typing is stable under replacing the type observations by stronger ones. -/
theorem TypedOb.strengthen (H : TypedOb env U Δ o τs) (h : Covers τs' τs) :
    TypedOb env U Δ o τs' := by
  induction H generalizing τs' with
  | sort h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .sort h2
  | piDom h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piDom h2
  | piDomOb h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piDomOb h2
  | piCod h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piCod h2
  | piCodOb h1 h3 h4 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .piCodOb h2 h3 h4
  | rigid h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .rigid h2
  | rigidArg h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .rigidArg h2
  | rigidArgOb h1 => let ⟨_, h2, l⟩ := h _ h1; cases l.sort_inv; exact .rigidArgOb h2
  | @app _ τd K _ c τc _ hD hd _ hc hcod _ ihk iho =>
    have ⟨_, h2, l⟩ := h _ hD; cases l.piDom_inv
    have ⟨τd', hd1, hd2⟩ := exists_list_cover (L := τd) (P := fun y => Ob.piDomOb y ∈ τs')
      (R := fun y x => y ≼ x) fun x hx => by
        have ⟨_, h3, l⟩ := h _ (hd x hx)
        have ⟨y, e, l'⟩ := l.piDomOb_inv; subst e; exact ⟨y, h3, l'⟩
    have ⟨τc', hc1, hc2⟩ := exists_list_cover (L := τc)
      (P := fun y => ∃ K₀, Ob.piCodOb c K₀ y ∈ τs' ∧ Covers K K₀)
      (R := fun y x => y ≼ x) fun x hx => by
        have ⟨K₀, h3, hK⟩ := hcod x hx
        have ⟨_, h4, l⟩ := h _ h3
        have ⟨K₁, y, e, hK₁, l'⟩ := l.piCodOb_inv; subst e
        exact ⟨y, ⟨K₁, h4, hK.trans hK₁⟩, l'⟩
    exact .app h2 hd1 (fun k hk => ihk k hk hd2) hc hc1 (iho hc2)

theorem TypedOb.mono (H : TypedOb env U Δ o τs) (h : ∀ τ ∈ τs, τ ∈ τs') :
    TypedOb env U Δ o τs' := H.strengthen (.of_subset h)

/-- The observation of the zero level. -/
abbrev zeroF : List Nat → Nat := fun _ => 0

theorem TypedOb.not_sort_zero (H : TypedOb env U Δ (.sort ℓ) [.sort zeroF]) : False := by
  cases H with
  | sort h =>
    simp only [List.mem_singleton, Ob.sort.injEq] at h
    exact Nat.succ_ne_zero _ (congrFun h [])

theorem TypedOb.sort_congr (H : TypedOb env U Δ o [.sort ℓ]) (e : ∀ ns, ℓ ns = ℓ' ns) :
    TypedOb env U Δ o [.sort ℓ'] := by
  have : ℓ = ℓ' := funext e
  subst this; exact H

/-- **Proof irrelevance, semantically**: nothing is typed at a list of observations each of
which is typed at `[sort 0]`. -/
theorem TypedOb.not_prop (H : TypedOb env U Δ o τs)
    (h : ∀ τ ∈ τs, TypedOb env U Δ τ [.sort zeroF]) : False := by
  induction H with
  | sort h1 | piDom h1 | piDomOb h1 | piCod h1 | piCodOb h1 | rigid h1 | rigidArg h1
  | rigidArgOb h1 =>
    exact (h _ h1).not_sort_zero
  | app _ _ _ _ hcod _ _ iho =>
    refine iho fun x hx => ?_
    have ⟨_, h3, _⟩ := hcod x hx
    cases h _ h3 with
    | piCodOb h4 h5 h6 =>
      simp only [List.mem_singleton, Ob.sort.injEq] at h4; subst h4
      exact h5.sort_congr fun ns => h6 ns rfl

end Model
end VEnv
end Lean4Lean
