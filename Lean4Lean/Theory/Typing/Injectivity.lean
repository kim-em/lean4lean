import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.ProjectionRigidity

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

/-- Field types of one projection computed at definitionally equal major types are
definitionally equal at the sort recorded by the first typing, and their recorded
universe levels are equivalent.

Keep each field's original stratified typing at its own literal sort. Even equivalent
universe expressions can require a conversion step: a constant stored at `Sort 1`
has stratification height one there, but needs height two at `Sort (max 0 1)`.
Retyping the second field at the first literal sort with unchanged height would be
false. `IsDefEq.uniq` instead retains both original bounds and uses the level equality.

This remains an independent foundation obligation: its proof must establish field
congruence and sort coherence without using the uniqueness theorem that consumes it. -/
theorem IsDefEqU.fieldType_inv_stratified (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections typeName info)
    (hlevels₁ : ∀ l ∈ levels₁, l.WF U) (huvars₁ : levels₁.length = info.uvars)
    (hparams₁ : params₁.length = info.nparams) (hindices₁ : indexArgs₁.length = info.nindices)
    (hfield₁ : info.fieldType typeName levels₁ params₁ index sourceMajor₁ = some fieldType₁)
    (hsource₁ : env.HasType U Γ sourceMajor₁
      (VExpr.mkApps (.const typeName levels₁) (params₁ ++ indexArgs₁)))
    (hlevels₂ : ∀ l ∈ levels₂, l.WF U) (huvars₂ : levels₂.length = info.uvars)
    (hparams₂ : params₂.length = info.nparams) (hindices₂ : indexArgs₂.length = info.nindices)
    (hfield₂ : info.fieldType typeName levels₂ params₂ index sourceMajor₂ = some fieldType₂)
    (hsource₂ : env.HasType U Γ sourceMajor₂
      (VExpr.mkApps (.const typeName levels₂) (params₂ ++ indexArgs₂)))
    (hclosed : info.ctorType.Closed)
    (hmajor : env.IsDefEqU U Γ sourceMajor₁ sourceMajor₂)
    (htypes : env.IsDefEqU U Γ
      (VExpr.mkApps (.const typeName levels₁) (params₁ ++ indexArgs₁))
      (VExpr.mkApps (.const typeName levels₂) (params₂ ++ indexArgs₂)))
    (hF₁ : env.HasTypeStratified U Γ fieldType₁ (.sort fieldLevel₁) true n)
    (hF₂ : env.HasTypeStratified U Γ fieldType₂ (.sort fieldLevel₂) true n') :
    env.IsDefEq U Γ fieldType₁ fieldType₂ (.sort fieldLevel₁) ∧
      fieldLevel₁ ≈ fieldLevel₂ := sorry

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

/-- A registered structure head is rigid by its declaration history, so the
general rigid-head injectivity theorem applies. -/
theorem IsDefEqU.structApp_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (hinfo : env.projections c info)
    (h1 : env.IsDefEqU U Γ (VExpr.mkApps (.const c ls) args) (VExpr.mkApps (.const c ls') args'))
    (h2 : env.HasType U Γ (VExpr.mkApps (.const c ls) args) (.sort u)) :
    List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args' :=
  IsDefEqU.rigidApp_inv henv hΓ (henv.projectionRigid hinfo) h1 h2
