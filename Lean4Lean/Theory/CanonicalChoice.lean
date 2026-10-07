import Lean4Lean.Theory.CanonicalEq

/-! # Canonical `Nonempty` and choice in an abstract environment -/

namespace Lean4Lean

/-- The stored type of `Nonempty.{u}`: `Sort u → Prop`. -/
def canonicalNonemptyType : VExpr :=
  .forallE (.sort (.param 0)) (.sort .zero)

/-- The stored type of `Nonempty.intro.{u}`: `∀ {α : Sort u} (val : α), Nonempty α`. -/
def canonicalNonemptyIntroType : VExpr :=
  .forallE (.sort (.param 0)) (.forallE (.bvar 0)
    (.app (.const ``Nonempty [.param 0]) (.bvar 1)))

/-- The stored type of `Classical.choice.{u}`: `∀ {α : Sort u}, Nonempty α → α`. -/
def canonicalChoiceType : VExpr :=
  .forallE (.sort (.param 0)) (.forallE (.app (.const ``Nonempty [.param 0]) (.bvar 0))
    (.bvar 1))

/-- The environment contains Lean's prelude `Nonempty`, its constructor `Nonempty.intro`
and the axiom `Classical.choice`, with the types that the replay of `Init.Prelude`
installs (`class inductive Nonempty (α : Sort u) : Prop | intro (val : α)`,
`axiom Classical.choice {α : Sort u} : Nonempty α → α`). Each has one universe
parameter, the sort of `α`.

The recursor `Nonempty.rec` is not required: choice is only used to inhabit a type from
a proof of its non-emptiness. -/
def VEnv.HasCanonicalChoice (env : VEnv) : Prop :=
  env.constants ``Nonempty = some ⟨1, canonicalNonemptyType⟩ ∧
  env.constants ``Nonempty.intro = some ⟨1, canonicalNonemptyIntroType⟩ ∧
  env.constants ``Classical.choice = some ⟨1, canonicalChoiceType⟩

/-- Canonical choice is preserved by every extension of the environment. -/
theorem VEnv.HasCanonicalChoice.mono {env env' : VEnv} (hle : env ≤ env')
    (h : env.HasCanonicalChoice) : env'.HasCanonicalChoice :=
  ⟨hle.constants h.1, hle.constants h.2.1, hle.constants h.2.2⟩

/- Sanity check: the explicit terms are the translations of the prelude declarations'
types. -/
example (env : VEnv) : env.HasCanonicalChoice ↔
    env.constants ``Nonempty = some vconst(type_of% @Nonempty) ∧
    env.constants ``Nonempty.intro = some vconst(type_of% @Nonempty.intro) ∧
    env.constants ``Classical.choice = some vconst(type_of% @Classical.choice) := Iff.rfl

end Lean4Lean
