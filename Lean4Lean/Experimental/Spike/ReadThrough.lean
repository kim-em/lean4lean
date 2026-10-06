import Lean4Lean.Experimental.Spike.HeadModel

/-! # Phase 1 spike: read-through is forced, and Pi-adequacy then forces reflection

This file isolates, sorry-free, the logical skeleton of the obstruction found by the
Phase 1 spike (`Spike/README.md`, section "The obstruction").

1. `readThrough`: in any model that is sound and compositional in application, an
   eliminator applied to a proof major is interpreted *without looking at whether its
   index check holds*, as soon as the model cannot tell the indices apart. Proof
   irrelevance makes the major invisible (`hmaj`), so the only thing the model could
   inspect is the index, and when the index has the same denotation as the aligned one
   (`hidx`), soundness of the iota rule at the aligned index fixes the value.

2. `check_of_piAdequacy`: suppose a Coquand–Huber adequacy theorem holds in the form that
   `forallE_forallE` needs, namely that a type whose denotation is Pi-headed weak-head
   reduces, by the relation `Red` the logical relation is built on, to a Pi with a typable
   domain (`PiAdequacy`; Carneiro's `LRS.TyDefEq` at a `forallE` shape provides exactly
   this, see `LRS.ValTyPi2` in `Experimental/ShapeLogRel.lean`). If the only `Red` step
   out of the stuck eliminator application requires the index check (`hstuck`), as for a
   typed, checked K-like or singleton iota step, then the index check is derivable.

Instantiated with Lean's `Eq.rec` (present in every environment satisfying
`HasCanonicalEq`), two indices with equal denotations but no derivable conversion, and a
motive whose value at the index is a Pi type, conclusion 2 is equality reflection for a
hypothesis `h : a = b`. That is believed false for this calculus (it would make Lean's
kernel incomplete in an elementary case). See the README for the concrete instances
(distinct variables under the bottom valuation; `fun n => n` against its recursive
eta-expansion; two self-looping definitions) and `Spike/KObstructionExamples.lean` for the
same terms checked by Lean's own elaborator and kernel.

No `sorry` and no axioms. -/

namespace Lean4Lean
namespace Spike
open VEnv

variable {env : VEnv}

/-- The model is compositional in application. For Carneiro's shape semantics this is
immediate from the only two `LE_Interp` constructors that apply to `.app`
(`LE_Interp.bot` and `LE_Interp.app`), which see the argument only through the set of its
approximations. -/
structure HeadModel.Compositional (M : HeadModel env) : Prop where
  app : ∀ {U Γ f f' a a'}, M.den U Γ f = M.den U Γ f' → M.den U Γ a = M.den U Γ a' →
    M.den U Γ (.app f a) = M.den U Γ (.app f' a')

/-- **Read-through is forced.** `F` is an eliminator spine up to (but excluding) its last
index and major; `a`/`r` are the aligned index and the canonical major for which the iota
rule fires (`hiota`); `b`/`h` are an arbitrary index and major. If the model does not
distinguish `b` from `a` (`hidx`) and does not distinguish the majors (`hmaj`, which proof
irrelevance forces for proofs of propositions), then the eliminator at `b`, `h` denotes
the iota result `m`, whether or not `b ≡ a` is derivable. -/
theorem HeadModel.readThrough (M : HeadModel env) (hC : M.Compositional)
    {U Γ F a b r h m A} (hΓ : OnCtx Γ (env.IsType U))
    (hiota : env.IsDefEq U Γ (.app (.app F a) r) m A)
    (hidx : M.den U Γ b = M.den U Γ a) (hmaj : M.den U Γ h = M.den U Γ r) :
    M.den U Γ (.app (.app F b) h) = M.den U Γ m :=
  (hC.app (hC.app rfl hidx) hmaj).trans (M.sound hΓ hiota)

/-- What a Coquand–Huber adequacy theorem provides at Pi-headed types, in the reflexive
form (one type, not a chain). This is strictly weaker than what `forallE_forallE` needs,
so the obstruction below applies to every Phase 1 design that proves `forallE_forallE`
through such a theorem. `Red U Γ` is the (reflexive-transitive) weak-head reduction on
which the logical relation is built. -/
structure PiAdequacy (M : HeadModel env) where
  Red : Nat → List VExpr → VExpr → VExpr → Prop
  adequate : ∀ {U Γ T u}, OnCtx Γ (env.IsType U) → env.HasType U Γ T (.sort u) →
    M.head (M.den U Γ T) = .pi → ∃ B F, Red U Γ T (.forallE B F) ∧ env.IsType U Γ B

/-- **Pi-adequacy forces the index check.**

The stuck term is `T := ((F b) h) y`: an eliminator at index `b` and major `h`, applied to
one more argument `y`. Its aligned twin `((F a) r) y` reduces by iota to `m y`, and `m y'`
is a Pi type by beta (`hβ`), where `y'` is any term the model does not distinguish from
`y` (`hy`; in the `Eq.rec` instance `y : Q b` and `y' : Q a` are two variables, both
denoting bottom). If the only way `Red` can leave `T` is through the index check `check`
(`hstuck`), then `check` holds.

In the `Eq.rec` instance `check` is `Γ ⊢ a ≡ b : α`, so this is equality reflection for the
hypothesis `h : a = b`. -/
theorem check_of_piAdequacy (M : HeadModel env) (hC : M.Compositional) (P : PiAdequacy M)
    {U Γ F a b r h m y y' A B₀ C₀ u w} {check : Prop} (hΓ : OnCtx Γ (env.IsType U))
    (hiota : env.IsDefEq U Γ (.app (.app F a) r) m A)
    (hidx : M.den U Γ b = M.den U Γ a) (hmaj : M.den U Γ h = M.den U Γ r)
    (hy : M.den U Γ y = M.den U Γ y')
    (hβ : env.IsDefEq U Γ (.app m y') (.forallE B₀ C₀) (.sort w))
    (hT : env.HasType U Γ (.app (.app (.app F b) h) y) (.sort u))
    (hstuck : ∀ X, P.Red U Γ (.app (.app (.app F b) h) y) X →
      X = .app (.app (.app F b) h) y ∨ check) :
    check := by
  have hden : M.den U Γ (.app (.app (.app F b) h) y) = M.den U Γ (.forallE B₀ C₀) :=
    (hC.app (M.readThrough hC hΓ hiota hidx hmaj) hy).trans (M.sound hΓ hβ)
  have hpi : M.head (M.den U Γ (.app (.app (.app F b) h) y)) = .pi := by
    rw [hden, M.head_forallE]
  obtain ⟨B, F', hred, -⟩ := P.adequate hΓ hT hpi
  obtain h' | h' := hstuck _ hred
  · cases h'
  · exact h'

/-- The same skeleton for a *data-valued* conclusion, which is how the obstruction reaches
the separation-free part of the logical relation as well: if the relation at a rigid
(inductive-type) shape demands weak-head reduction to a rigid-headed application, as it
must for large elimination over that type to be adequate, then again the check follows.
`R` is a predicate on reducts ("is a rigid-headed application", "is a constructor
application", ...) that the stuck term itself does not satisfy. -/
theorem check_of_adequacy_at {Red : Nat → List VExpr → VExpr → VExpr → Prop}
    {R : VExpr → Prop} {U Γ T} {check : Prop}
    (hadeq : ∃ X, Red U Γ T X ∧ R X) (hT : ¬R T)
    (hstuck : ∀ X, Red U Γ T X → X = T ∨ check) : check := by
  obtain ⟨X, hred, hR⟩ := hadeq
  obtain rfl | h' := hstuck X hred
  · exact absurd hR hT
  · exact h'

end Spike
end Lean4Lean
