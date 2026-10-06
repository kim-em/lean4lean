import Lean4Lean.Theory.Quot

/-! # Canonical equality in an abstract environment -/

namespace Lean4Lean

/-- The environment contains Lean's prelude equality `Eq`, its constructor
`Eq.refl` and its recursor `Eq.rec`, with the types and the iota rule that the
replay of `Init.Prelude` installs.  Universe parameters follow the production
declarations: `Eq.{u_1}` and `Eq.refl.{u_1}` have one universe parameter (the
sort of `α`, `.param 0`); `Eq.rec.{u, u_1}` has two, the motive universe `u`
(`.param 0`) followed by the sort of `α` (`.param 1`).  `Eq` has two parameters
(`α` and the left endpoint `a`) and one index, so the stored iota rule binds
`α`, `a`, the motive and the minor premise `refl`:

* `Eq : ∀ {α : Sort u_1}, α → α → Prop`;
* `Eq.refl : ∀ {α : Sort u_1} (a : α), @Eq α a a`;
* `Eq.rec : ∀ {α : Sort u_1} {a : α} {motive : ∀ b, @Eq α a b → Sort u},
    motive a (Eq.refl a) → ∀ {b : α} (t : @Eq α a b), motive b t`;
* the iota rule `fun α a motive refl => @Eq.rec α a motive refl a (Eq.refl a)
  ≡ fun α a motive refl => refl`, at type
  `∀ α a motive refl, motive a (Eq.refl a)`.

The rule is in the lambda-wrapped form of `VIotaRuleShape`, the form in which
recursor rules are stored in `VEnv.defeqs`. -/
def VEnv.HasCanonicalEq (env : VEnv) : Prop :=
  env.constants ``Eq = some ⟨1,
    .forallE (.sort (.param 0)) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))⟩ ∧
  env.constants ``Eq.refl = some ⟨1,
    .forallE (.sort (.param 0)) (.forallE (.bvar 0)
      (.app (.app (.app (.const ``Eq [.param 0]) (.bvar 1)) (.bvar 0)) (.bvar 0)))⟩ ∧
  env.constants ``Eq.rec = some ⟨2,
    -- α : Sort u_1
    .forallE (.sort (.param 1)) <|
    -- a : α
    .forallE (.bvar 0) <|
    -- motive : ∀ b : α, Eq α a b → Sort u
    .forallE (.forallE (.bvar 1)
      (.forallE (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 2)) (.bvar 1)) (.bvar 0))
        (.sort (.param 0)))) <|
    -- refl : motive a (Eq.refl α a)
    .forallE (.app (.app (.bvar 0) (.bvar 1))
      (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 2)) (.bvar 1))) <|
    -- b : α
    .forallE (.bvar 3) <|
    -- t : Eq α a b
    .forallE (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.bvar 3)) (.bvar 0)) <|
    -- motive b t
    .app (.app (.bvar 3) (.bvar 1)) (.bvar 0)⟩ ∧
  env.defeqs {
    uvars := 2
    lhs :=
      .lam (.sort (.param 1)) <| .lam (.bvar 0) <|
      .lam (.forallE (.bvar 1)
        (.forallE (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 2)) (.bvar 1)) (.bvar 0))
          (.sort (.param 0)))) <|
      .lam (.app (.app (.bvar 0) (.bvar 1))
        (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 2)) (.bvar 1))) <|
      .app (.app (.app (.app (.app (.app (.const ``Eq.rec [.param 0, .param 1])
        (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.bvar 2))
        (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 3)) (.bvar 2))
    rhs :=
      .lam (.sort (.param 1)) <| .lam (.bvar 0) <|
      .lam (.forallE (.bvar 1)
        (.forallE (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 2)) (.bvar 1)) (.bvar 0))
          (.sort (.param 0)))) <|
      .lam (.app (.app (.bvar 0) (.bvar 1))
        (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 2)) (.bvar 1))) <|
      .bvar 0
    type :=
      .forallE (.sort (.param 1)) <| .forallE (.bvar 0) <|
      .forallE (.forallE (.bvar 1)
        (.forallE (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 2)) (.bvar 1)) (.bvar 0))
          (.sort (.param 0)))) <|
      .forallE (.app (.app (.bvar 0) (.bvar 1))
        (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 2)) (.bvar 1))) <|
      .app (.app (.bvar 1) (.bvar 2))
        (.app (.app (.const ``Eq.refl [.param 1]) (.bvar 3)) (.bvar 2)) }

/-- Canonical equality is preserved by every extension of the environment:
`≤` preserves constants and definitional rules. -/
theorem VEnv.HasCanonicalEq.mono {env env' : VEnv} (hle : env ≤ env')
    (h : env.HasCanonicalEq) : env'.HasCanonicalEq :=
  ⟨hle.constants h.1, hle.constants h.2.1, hle.constants h.2.2.1, hle.defeqs h.2.2.2⟩

/-- The `Eq` clause of `HasCanonicalEq` is the quotient-readiness condition. -/
theorem VEnv.HasCanonicalEq.quotReady {env : VEnv} (h : env.HasCanonicalEq) :
    env.QuotReady := h.1

/- Sanity check: the explicit terms are the translations of the prelude
declarations' types and of the rule `@Eq.rec α a motive refl a (Eq.refl a) ≡ refl`.
The `vconst`/`vdefeq` elaborators number universe parameters in order of first
occurrence (the sort of `α` first), so for `Eq.rec` the two parameters are
swapped back into the production order `[u, u_1]`. -/
example (env : VEnv) : env.HasCanonicalEq ↔
    env.constants ``Eq = some vconst(type_of% @Eq) ∧
    env.constants ``Eq.refl = some vconst(type_of% @Eq.refl) ∧
    env.constants ``Eq.rec = some
      ⟨2, (vconst(type_of% @Eq.rec)).type.instL [.param 1, .param 0]⟩ ∧
    env.defeqs (
      let df := vdefeq(α a motive refl => @Eq.rec α a motive refl a (Eq.refl a) ≡ refl)
      { uvars := 2
        lhs := df.lhs.instL [.param 1, .param 0]
        rhs := df.rhs.instL [.param 1, .param 0]
        type := df.type.instL [.param 1, .param 0] }) := Iff.rfl

end Lean4Lean
