import Lean4Lean.Theory.Typing.Strengthening.Klop.Env.Minimal
import Lean4Lean.Theory.Typing.Strengthening.Klop.Sound.Fundamental

/-! # Strengthening of definitional equality fails

`IsDefEqU.weakN_iff` (`Theory/Typing/UniqueTyping.lean`) states that two terms which do not
mention some binders of a context, and are definitionally equal in that context, are
definitionally equal in the context without those binders. This directory proves that the
statement is false for well-formed environments, even with the prelude's `Eq`:
`not_weakN_iff_of_canonicalEq` and `not_weakN_iff_of_setModel`.

## The example

`Eq.rec` at a constant motive is a non-left-linear rule: `@Eq.rec T a (fun _ _ => T) E b h ≡ E`
exactly when `a ≡ b`. Together with looping definitions, which `VDecl.mutualDef` admits, this
is the setting of Klop's counterexample to confluence. Take canonical `Eq` and

```text
T   : Type                         (axiom)
E   : T                            (axiom)
P   : Prop                         (axiom)
H   : ∀ x y : T, x = y             (axiom)
C   : T → T := fun x => @Eq.rec T x (fun _ _ => T) E (C x) (H x (C x))
Fix : P → T := fun p => C (Fix p)
```

Under a hypothesis `z : P`, the term `Fix z` is a fixed point of `C`, so the `Eq.rec` in
`C (Fix z)` has definitionally equal endpoints and computes: `Fix z ≡ C (Fix z) ≡ E`, hence
`C E ≡ C (Fix z) ≡ Fix z ≡ E` (`KlopEnv.above`). In the empty context `C E ≡ E` is not
derivable (`KlopInventory.separated`), although neither term mentions `z`.

## The proof

* `Klop/Derivation.lean`: the derivation of `C E ≡ E` under `z : P`, in any well-formed
  environment with canonical `Eq` and the six declarations (`KlopEnv`).
* `Klop/Env/`: a well-formed environment with canonical `Eq`, the six declarations and nothing
  else (`exists_minimalKlopEnv`, with the exact inventory `KlopInventory`).
* `Klop/SetModel.lean`: the set theory the model is built in. It asks for no universe of sets.
* `Klop/Model/`: the model. A term has a denotation `den ρ e` and, independently, an untyped
  proof value `pval e`. `T` denotes a three-element set, `E` its element `0`, `C` the cyclic
  successor (which has no fixed point), `P` the empty proposition and `Fix` the trivial proof
  `•`, so `⟦C E⟧ = 1` and `⟦E⟧ = 0` (`den_CE_ne_E`). A proposition denotes a *candidate*, a set
  of proof values closed under weak head reduction; every proof denotes `•`, which is proof
  irrelevance. The candidate of `a = b` contains the value `r` of `Eq.refl` only when `a` and
  `b` are the same element, and `H x y` has a value that never reduces to `r`, so `Eq.rec`
  may compute by cases on the value of its major premise.
* `Klop/Sound/`: the fundamental theorem `KlopInventory.sound`. Every derivable judgment of an
  environment with the Klop inventory, at universe-parameter count `0`, satisfies the
  semantic judgment `Sem` (both sides have the same denotation, an element of the denotation
  of the type, and their values realize it when it is a proposition), the uniformity clause
  `SemU`, and the head invariant `SpineOK` used for the ι rule.

## Universes without a universe of sets

The semantic universe `𝒰ₙ` has to be a set containing the denotation of every type of level
`n`, including Π-types over `𝒰ₙ₋₁` and iterations of these. It is cut out by separation from
the set of records of finite Π-depth over the lower universes (`Model/Bound.lean`), which
exists by replacement and union over `Nat`. That every valid type has finite depth
(`ValidAny.exists_dpLe`) is not automatic: a family of types indexed by a type could have
unbounded depth. It holds because function spaces contain only *uniform* functions, those
sending families of arguments of bounded depth to families of results of bounded depth, level
by level (`Model/Uniform.lean`), and the fundamental theorem shows that every term denotes
one (`SemU`).

## The set model

`ZFSet.{0}` is a `SetModel`, which makes the result unconditional. This repository does not
depend on Mathlib, so the instance is not built here and the theorems take a `SetModel` as a
hypothesis.

Every theorem in this directory is proved without `sorry`, and nothing outside it depends on
it.
-/

namespace Lean4Lean
namespace VEnv.Strengthening

/-- In an environment with the Klop inventory, `C E ≡ E` is not derivable in the empty
context: in any set model the two terms denote `1` and `0`. -/
theorem KlopInventory.separated (𝕊 : SetModel) {env : VEnv}
    (henv : env.WF) (heq : env.HasCanonicalEq) (K : KlopInventory env) :
    K.toKlopEnv.Separated 0 := by
  rintro ⟨A, H⟩
  exact 𝕊.den_CE_ne_E (fun _ => 𝕊.star) (K.den_sound 𝕊 henv heq H _)

/-- **Strengthening of definitional equality is false even with canonical `Eq`**, given a
set model (of which `ZFSet.{0}` is one): the statement of `IsDefEqU.weakN_iff` with the extra
hypothesis `env.HasCanonicalEq` fails in the minimal Klop environment. -/
theorem not_weakN_iff_of_canonicalEq (𝕊 : SetModel) :
    ¬ ∀ {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr},
      env.WF → env.HasCanonicalEq → OnCtx Γ' (env.IsType U) → Ctx.LiftN n k Γ Γ' →
      (env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2) := by
  intro H
  obtain ⟨env, henv, heq, K⟩ := exists_minimalKlopEnv
  exact K.toKlopEnv.not_strengthening henv heq (K.separated 𝕊 henv heq)
    (fun hΓ W => H henv heq hΓ W)

/-- **The statement of `IsDefEqU.weakN_iff` is false**, given a set model (of which
`ZFSet.{0}` is one). -/
theorem not_weakN_iff_of_setModel (𝕊 : SetModel) :
    ¬ ∀ {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr} {e1 e2 : VExpr},
      env.WF → OnCtx Γ' (env.IsType U) → Ctx.LiftN n k Γ Γ' →
      (env.IsDefEqU U Γ' (e1.liftN n k) (e2.liftN n k) ↔ env.IsDefEqU U Γ e1 e2) :=
  fun H => not_weakN_iff_of_canonicalEq 𝕊 fun henv _ hΓ W => H henv hΓ W

end VEnv.Strengthening
end Lean4Lean
