import Lean4Lean.Theory.Typing.Strengthening.ModelObstruction
import Lean4Lean.Theory.Typing.Strengthening.TypingFront

/-! # The model route against the shared statements

The route-B statements of `Model.lean` and `ModelObstruction.lean` against the shared forms of
the problem (`Cancel.lean`, `TypingFront.lean`):

* `cancel_of_freshReflection`: the reflection statement the route needs gives `Cancel`
  outright (soundness above, reflection below); it is false (`extension_not_freshReflection`).
* `typedFront_of_modelRoute`: the two-step form, agreement in inhabited targets to agreement in
  all targets (`ModelStrengthening`) then typed reflection in `Γ` (`TypedReflection`), gives
  `TypedFront`; its second step is false (`extension_not_typedReflection`).
* `keyFaithful_iff_typedFront`, `keyFaithful_iff_propFront`: descending the model's own classes
  is the shared open statement, in its fixed-type form and (under canonical `Eq`) in its
  `Prop` form.

So on the ι pattern calculus the observation model contributes soundness (head inversion above,
which descends to equations between lifted subterms) and nothing towards the leaf: the
`Prop`-typed front `PropFront`, equivalently `TypedFront`, equivalently class descent. -/

namespace Lean4Lean
namespace VEnv.StrengtheningModel
open VEnv VEnv.Strengthening

variable {env : VEnv}

theorem keyFaithful_iff_typedFront' (henv : env.WF) : KeyFaithful env ↔ TypedFront env :=
  keyFaithful_iff_typedFront henv

theorem keyFaithful_iff_propFront (henv : env.WF) (heq : env.HasCanonicalEq) :
    KeyFaithful env ↔ PropFront env :=
  (keyFaithful_iff_typedFront henv).trans (typedFront_iff_propFront henv heq)

/-- Reflection at a common lifted type gives `Cancel` directly. -/
theorem cancel_of_freshReflection (henv : env.WF) (hr : FreshReflection env) : Cancel env :=
  Cancel.of_front henv fun _ _ _ _ _ hΓ H => front_of_freshReflection henv hr hΓ H

/-- The two-step model route: semantic strengthening (inhabited targets to all targets) and
typed reflection in the smaller context give the fixed-type front (the endpoints must be typed
below for typed reflection, which is why the route lands on `TypedFront` and not on `Cancel`;
`Cancel` then needs the closures of `Closures.lean`). -/
theorem typedFront_of_modelRoute (henv : env.WF) (hs : ModelStrengthening env)
    (hr : TypedReflection env) : TypedFront env := by
  intro U Γ Q a b T hΓ hQ ha hb H
  have hK : KEq env U (Q :: Γ) a.lift b.lift := KEq.sound henv ⟨hΓ, hQ⟩ ⟨_, H⟩
  exact hr hΓ ha hb (hs ⟨hΓ, hQ⟩ ((KEq.lift_iff ⟨hΓ, hQ⟩).1 hK))

end VEnv.StrengtheningModel
end Lean4Lean
