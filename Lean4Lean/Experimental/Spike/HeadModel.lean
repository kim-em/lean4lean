import Lean4Lean.Theory.Typing.HeadInversion

/-! # Phase 1 spike: the separation half of `HeadInversion` from a sound model

`VEnv.HeadInversion` mixes two kinds of statement.

* *Separation*: `sort_sort` (levels of equal sorts are `≈`), `sort_forallE`, `sort_rigid`,
  `forallE_rigid`, and the head/level part of `rigid_rigid` (`c = c'` and `ls ≈ ls'`).
  These only say that a chain cannot connect two types with different *head classes*.
* *Injectivity*: `forallE_forallE`, the argument part of `rigid_rigid`, `former_args` and
  `proj_fieldType`. These produce *declarative* derivations between components.

This file shows that the separation half needs no logical relation and no adequacy
theorem: it follows from any compositional model that is sound for `IsDefEq` and assigns
the expected head class to sorts, Pi types and saturated rigid applications. The model is
an interface (`HeadModel`); nothing here constructs one. A shape model in the style of
`Experimental/ShapeLogRel.lean`, with sort shapes carrying the evaluated level and inductive
type shapes carrying the family name and evaluated levels, is the intended instance (see
`Spike/README.md`, section "Separation from soundness alone").

The injectivity half is where the semantic route meets the obstruction recorded in
`Spike/ReadThrough.lean`.

No `sorry` and no axioms. -/

namespace Lean4Lean
namespace Spike
open VEnv

/-- The head class of a semantic type value. Levels are recorded by their evaluation
functions, so equality of head classes gives `≈` on levels (`VLevel.equiv_def'`). -/
inductive HeadClass where
  | sort (lvl : List Nat → Nat)
  | pi
  | rigid (c : Name) (lvls : List (List Nat → Nat))
  | other

/-- A model of the declarative calculus, read at the base valuation of each context, that
classifies the heads of types.

`den U Γ e` is the denotation of `e` in context `Γ` (for the shape semantics: the set of
shapes approximating `e` under the valuation that sends every variable of `Γ` to the
bottom shape, `Valuation.nil`). Soundness is required only in well-formed contexts and
only for the equalities themselves. -/
structure HeadModel (env : VEnv) where
  D : Type
  den : Nat → List VExpr → VExpr → D
  sound : ∀ {U Γ e₁ e₂ A}, OnCtx Γ (env.IsType U) →
    env.IsDefEq U Γ e₁ e₂ A → den U Γ e₁ = den U Γ e₂
  head : D → HeadClass
  head_sort : ∀ {U Γ u}, head (den U Γ (.sort u)) = .sort u.eval
  head_forallE : ∀ {U Γ A B}, head (den U Γ (.forallE A B)) = .pi
  /-- Saturated rigid applications (those typed at a sort) have a rigid head that records
  the family and the evaluated universe levels. -/
  head_rigid : ∀ {U Γ c ls args u}, OnCtx Γ (env.IsType U) → env.Rigid c →
    env.HasType U Γ (.mkApps (.const c ls) args) (.sort u) →
    head (den U Γ (.mkApps (.const c ls) args)) = .rigid c (ls.map (·.eval))

/-- The separation half of `VEnv.HeadInversion`. The first five fields are verbatim fields
of `HeadInversion` (with `rigid_heads` the head/level conjuncts of `rigid_rigid`). -/
structure HeadSeparation (env : VEnv) : Prop where
  sort_sort : ∀ {U Γ u v}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.sort u) (.sort v) → u ≈ v
  sort_forallE : ∀ {U Γ u A B}, OnCtx Γ (env.IsType U) →
    ¬env.TypeChain U Γ (.sort u) (.forallE A B)
  sort_rigid : ∀ {U Γ c u ls args}, OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.sort u) (.mkApps (.const c ls) args)
  forallE_rigid : ∀ {U Γ c A B ls args}, OnCtx Γ (env.IsType U) → env.Rigid c →
    ¬env.TypeChain U Γ (.forallE A B) (.mkApps (.const c ls) args)
  rigid_heads : ∀ {U Γ c c' ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.Rigid c' →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls'

namespace HeadModel
variable {env : VEnv} (M : HeadModel env)

/-- A chain of sort-typed links is sound in the model. -/
theorem den_chain {U Γ A B} (hΓ : OnCtx Γ (env.IsType U)) (H : env.TypeChain U Γ A B) :
    M.den U Γ A = M.den U Γ B := by
  induction H with
  | single h => let ⟨_, h⟩ := h; exact M.sound hΓ h
  | tail _ h ih => let ⟨_, h⟩ := h; exact ih.trans (M.sound hΓ h)

theorem head_chain {U Γ A B} (hΓ : OnCtx Γ (env.IsType U)) (H : env.TypeChain U Γ A B) :
    M.head (M.den U Γ A) = M.head (M.den U Γ B) := congrArg M.head (M.den_chain hΓ H)

/-- A sort-typed rigid application at an endpoint of a chain. -/
private theorem rigid_head_of_chain_l {U Γ c ls args B} (hΓ : OnCtx Γ (env.IsType U))
    (hc : env.Rigid c) (H : env.TypeChain U Γ (.mkApps (.const c ls) args) B) :
    M.head (M.den U Γ (.mkApps (.const c ls) args)) = .rigid c (ls.map (·.eval)) :=
  let ⟨_, h⟩ := H.isType_l; M.head_rigid hΓ hc h

private theorem rigid_head_of_chain_r {U Γ c ls args A} (hΓ : OnCtx Γ (env.IsType U))
    (hc : env.Rigid c) (H : env.TypeChain U Γ A (.mkApps (.const c ls) args)) :
    M.head (M.den U Γ (.mkApps (.const c ls) args)) = .rigid c (ls.map (·.eval)) :=
  let ⟨_, h⟩ := H.isType_r; M.head_rigid hΓ hc h

private theorem forall₂_equiv_of_map_eval {ls ls' : List VLevel}
    (h : ls.map (·.eval) = ls'.map (·.eval)) : List.Forall₂ (· ≈ ·) ls ls' := by
  induction ls generalizing ls' with
  | nil => cases ls' with | nil => exact .nil | cons => cases h
  | cons l ls ih =>
    cases ls' with
    | nil => cases h
    | cons l' ls' =>
      simp only [List.map_cons, List.cons.injEq] at h
      exact .cons (VLevel.equiv_def'.2 h.1) (ih h.2)

/-- **Separation from soundness.** Every model of the `HeadModel` interface yields the
separation half of `HeadInversion`. -/
theorem separation (M : HeadModel env) : HeadSeparation env where
  sort_sort hΓ H := by
    have := M.head_chain hΓ H
    rw [M.head_sort, M.head_sort] at this
    exact VLevel.equiv_def'.2 (HeadClass.sort.inj this)
  sort_forallE hΓ H := by
    have := M.head_chain hΓ H
    rw [M.head_sort, M.head_forallE] at this
    cases this
  sort_rigid hΓ hc H := by
    have := M.head_chain hΓ H
    rw [M.head_sort, M.rigid_head_of_chain_r hΓ hc H] at this
    cases this
  forallE_rigid hΓ hc H := by
    have := M.head_chain hΓ H
    rw [M.head_forallE, M.rigid_head_of_chain_r hΓ hc H] at this
    cases this
  rigid_heads hΓ hc hc' H := by
    have := M.head_chain hΓ H
    rw [M.rigid_head_of_chain_l hΓ hc H, M.rigid_head_of_chain_r hΓ hc' H] at this
    obtain ⟨rfl, h⟩ := HeadClass.rigid.inj this
    exact ⟨rfl, forall₂_equiv_of_map_eval h⟩

end HeadModel

/-- The separation half is exactly the corresponding part of `HeadInversion`. -/
theorem HeadInversion.toHeadSeparation {env : VEnv} (h : env.HeadInversion) :
    HeadSeparation env where
  sort_sort := h.sort_sort
  sort_forallE := h.sort_forallE
  sort_rigid := h.sort_rigid
  forallE_rigid := h.forallE_rigid
  rigid_heads hΓ hc hc' H := let ⟨h1, h2, _⟩ := h.rigid_rigid hΓ hc hc' H; ⟨h1, h2⟩

end Spike
end Lean4Lean
