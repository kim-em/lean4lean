import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong

/-! Structural inversion theorems for definitional equality. -/

namespace Lean4Lean
namespace VEnv

theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := sorry

theorem IsDefEqU.forallE_inv_stratified (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B'))
    (h2 : env.HasTypeStratified U Γ (.forallE A B) V true n)
    (h3 : env.HasTypeStratified U Γ (.forallE A' B') V' true n') :
    (∃ u, env.IsDefEq U Γ A A' (.sort u) ∧ env.HasTypeStratified U Γ A (.sort u) true n) ∧
    ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) ∧
      env.HasTypeStratified U (A::Γ) B (.sort u) true n ∧
      env.HasTypeStratified U (A'::Γ) B' (.sort u) true n' := sorry

theorem IsDefEqU.forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.forallE A B) (.forallE A' B')) :
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ u, env.IsDefEq U (A::Γ) B B' (.sort u) :=
  let ⟨_, eq⟩ := h1
  let ⟨h2, h3⟩ := (eq.strong henv hΓ).hasType'
  let ⟨_, h2⟩ := h2.stratify
  let ⟨_, h3⟩ := h3.stratify
  let ⟨⟨_, a1, _⟩, _, a2, _⟩ := IsDefEqU.forallE_inv_stratified henv hΓ h1 h2 h3
  ⟨⟨_, a1⟩, _, a2⟩

theorem IsDefEqU.sort_forallE_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U)) :
    ¬env.IsDefEqU U Γ (.sort u) (.forallE A B) := sorry

/-- A constant is *rigid* when no definitional rule of the environment is headed by it
after stripping the lambda binders that wrap stored rules: it has no delta rule, and it is
not a recursor. Inductive type constants are rigid. -/
def _root_.Lean4Lean.VEnv.Rigid (env : VEnv) (c : Name) : Prop :=
  ∀ df, env.defeqs df → ∀ ls, df.lhs.stripLams.getAppFnArgs.1 ≠ .const c ls

/-- Injectivity of applications of a rigid constant, at the type level: two definitionally
equal types headed by the same rigid constant have equivalent universe levels and pairwise
definitionally equal arguments.

This is the same class of statement as `forallE_inv_stratified` and `sort_inv`: all of them
are consequences of confluence for the calculus, which is the open metatheory of this
development (see `ChurchRosser.lean`). -/
theorem IsDefEqU.rigidApp_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hrigid : env.Rigid c)
    (h1 : env.IsDefEqU U Γ (VExpr.mkApps (.const c ls) args) (VExpr.mkApps (.const c ls') args'))
    (h2 : env.HasType U Γ (VExpr.mkApps (.const c ls) args) (.sort u)) :
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args' := sorry

/-- `rigidApp_inv` for the head of a registered structure. A registered structure type
is an inductive type constant of the environment, hence rigid; deriving that from the
declaration trace is routine once the nested auxiliary rules record their left-hand side
shape, and until then this is stated separately so that the projection metatheory depends
on exactly one injectivity fact. -/
theorem IsDefEqU.structApp_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections c info)
    (h1 : env.IsDefEqU U Γ (VExpr.mkApps (.const c ls) args) (VExpr.mkApps (.const c ls') args'))
    (h2 : env.HasType U Γ (VExpr.mkApps (.const c ls) args) (.sort u)) :
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args' := sorry
