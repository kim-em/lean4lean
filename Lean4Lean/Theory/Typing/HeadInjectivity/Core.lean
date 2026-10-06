import Lean4Lean.Theory.Typing.TypeChain

/-! # Chain-level head injectivity and the injectivity fields of head inversion

`HeadInjectivityCore` is the hypothesis of the syntactic layer: injectivity of type heads
along `TypeChain`s, to be supplied by a semantic model (see
`docs/inductives/PHASE1B_NOTES.md`, sections 3 and 5). `HeadInjectivity` is what the
syntactic layer derives from it: the four injectivity fields of `VEnv.HeadInversion`
(`HeadInversion.lean`), stated exactly as there. This directory must not import
`HeadInversion.lean`, `UniqueTyping.lean`, `Injectivity.lean`, `ChurchRosser.lean`,
`FullReduction.lean` or `HeadReduction.lean`. -/

namespace Lean4Lean
namespace VEnv

/-- Chain-level head injectivity: the hypothesis of the syntactic layer.

`sort_sort`, `rigid_rigid` and `former_args` are the fields of `HeadInversion` of the
same names; `forallE_chain` is the chain-level form of `forallE_forallE`, relating the
domains and codomains by chains rather than by single definitional equalities. -/
structure HeadInjectivityCore (env : VEnv) : Prop where
  sort_sort : ∀ {U Γ u v}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.sort u) (.sort v) → u ≈ v
  forallE_chain : ∀ {U Γ A B A' B'}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.forallE A B) (.forallE A' B') →
    env.TypeChain U Γ A A' ∧ env.TypeChain U (A :: Γ) B B'
  rigid_rigid : ∀ {U Γ c c' ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.Rigid c' →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args'
  former_args : ∀ {U Γ c ci doms w ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.constants c = some ci → ci.type = .wrapForalls doms (.sort w) →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c ls') args') →
    SpineArgsEq env U Γ (ci.type.instL ls) args args'

/-- The four injectivity fields of `VEnv.HeadInversion`, stated exactly as there
(`rigid_args` is `rigid_rigid` with only the argument conclusion). Derived from
`HeadInjectivityCore` in `HeadInjectivity/Fields.lean`. -/
structure HeadInjectivity (env : VEnv) : Prop where
  forallE_forallE : ∀ {U Γ A B A' B'}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.forallE A B) (.forallE A' B') →
    (∃ u, env.IsDefEq U Γ A A' (.sort u)) ∧ ∃ v, env.IsDefEq U (A :: Γ) B B' (.sort v)
  rigid_args : ∀ {U Γ c c' ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.Rigid c' →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args') →
    List.Forall₂ (env.IsDefEqU U Γ) args args'
  former_args : ∀ {U Γ c ci doms w ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.constants c = some ci → ci.type = .wrapForalls doms (.sort w) →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c ls') args') →
    SpineArgsEq env U Γ (ci.type.instL ls) args args'
  /-- Two typings of one projection select chain-related field types, given the data of
  both projection typings, sources related at the first major type, and the two major
  types related by a chain. -/
  proj_fieldType : ∀ {U Γ typeName info index
      levels₁ params₁ indexArgs₁ sourceMajor₁ fieldType₁ fieldLevel₁
      levels₂ params₂ indexArgs₂ sourceMajor₂ fieldType₂ fieldLevel₂},
    OnCtx Γ (env.IsType U) → env.projections typeName info → info.ctorType.Closed →
    (∀ l ∈ levels₁, l.WF U) → levels₁.length = info.uvars →
    params₁.length = info.nparams → indexArgs₁.length = info.nindices →
    info.fieldType typeName levels₁ params₁ index sourceMajor₁ = some fieldType₁ →
    env.HasType U Γ fieldType₁ (.sort fieldLevel₁) →
    (info.resultLevel.inst levels₁).IsNeverZero ∨ fieldLevel₁ ≈ .zero →
    (∀ l ∈ levels₂, l.WF U) → levels₂.length = info.uvars →
    params₂.length = info.nparams → indexArgs₂.length = info.nindices →
    info.fieldType typeName levels₂ params₂ index sourceMajor₂ = some fieldType₂ →
    env.HasType U Γ fieldType₂ (.sort fieldLevel₂) →
    (info.resultLevel.inst levels₂).IsNeverZero ∨ fieldLevel₂ ≈ .zero →
    env.IsDefEq U Γ sourceMajor₁ sourceMajor₂
      (.mkApps (.const typeName levels₁) (params₁ ++ indexArgs₁)) →
    env.TypeChain U Γ (.mkApps (.const typeName levels₁) (params₁ ++ indexArgs₁))
      (.mkApps (.const typeName levels₂) (params₂ ++ indexArgs₂)) →
    env.TypeChain U Γ fieldType₁ fieldType₂

end VEnv
end Lean4Lean
