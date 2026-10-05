import Lean4Lean.Theory.Typing.Basic

/-!
Run with `lake env lean docs/inductives/SingletonStrengthening.lean`.

Source admissibility and the exact declarative equality chain for the
strengthening countermodel in STRENGTHENING.md. The opaque axioms below are
object-language source declarations, not new axioms in the verification
development. This file is not imported by the checker or theory.

The final theorem checks the combination of the branch's actual inference
rules. Neither it nor the source declarations formalize the complete
VEnv.WF installation or the semantic interpretation of all abstract terms.
-/
namespace InductiveStrengtheningPressure

axiom C : Type
axiom F : C → Type
axiom c : C
axiom P : F c → Prop
axiom leftMap : F c → F c
axiom rightMap : F c → F c

inductive I : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : I c v (leftMap v)

inductive J : (n : C) → F n → F n → Prop where
  | mk (v : F c) (h : P v) : J c v (rightMap v)

#check I.rec
#check J.rec

def left (K : (v : F c) → P v → Type) (v : F c)
    (p : I c v (leftMap v)) : Type :=
  I.rec (motive := fun _ _ _ _ => Type) K p

def right (K : (v : F c) → P v → Type) (v : F c)
    (p : J c v (rightMap v)) : Type :=
  J.rec (motive := fun _ _ _ _ => Type) K p

-- Each constructor computation is literal iota.
example (K : (v : F c) → P v → Type) (v : F c) (q : P v) :
    left K v (I.mk v q) = K v q := rfl

example (K : (v : F c) → P v → Type) (v : F c) (q : P v) :
    right K v (J.mk v q) = K v q := rfl

-- Each major replacement is definitionally proof irrelevant.
example (v : F c) (q : P v) (p : I c v (leftMap v)) : p = I.mk v q := rfl
example (v : F c) (q : P v) (p : J c v (rightMap v)) : p = J.mk v q := rfl

-- This Lean equality proof records the congruence/transitivity chain;
-- it is not a claim that kernel reduction directly compares the endpoints.
theorem withProof (K : (v : F c) → P v → Type) (v : F c)
    (p : I c v (leftMap v)) (r : J c v (rightMap v)) (q : P v) :
    left K v p = right K v r := by
  calc
    left K v p = left K v (I.mk v q) := congrArg (left K v) (show p = I.mk v q from rfl)
    _ = K v q := rfl
    _ = right K v (J.mk v q) := rfl
    _ = right K v r := congrArg (right K v) (show J.mk v q = r from rfl)

open Lean Lean.Elab.Command in
run_elab do
  for name in [``I.rec, ``J.rec] do
    let some (.recInfo info) := (← getEnv).find? name | throwError "not a recursor"
    unless info.levelParams.length == 1 && info.numParams == 0 &&
        info.numIndices == 3 && info.numMinors == 1 do
      throwError "unexpected source recursor metadata"
    logInfo m!"{name}: large singleton elimination accepted, three indices, zero parameters; isK={info.k}"

end InductiveStrengtheningPressure

namespace InductiveStrengtheningPressure.Abstract
open Lean4Lean
open Lean4Lean.VEnv

/-- The exact declarative chain, at a shared sort, uses no inversion,
uniqueness, strengthening, or equality datatype. In the source example
`ctorI` and `ctorJ` contain the fresh proof, but the two endpoints do not.

This checks the inference-rule combination. The natural typing/iota
premises come from the declared recursors; this theorem alone does not
construct the full finite installation/WF derivation for those declarations. -/
theorem proofMajorJoin {env : VEnv} {U : Nat} {Γ : List VExpr}
    {familyI familyJ p r ctorI ctorJ recI recJ result : VExpr} {u : VLevel}
    (hi : HasType env U Γ familyI (.sort .zero))
    (hj : HasType env U Γ familyJ (.sort .zero))
    (hp : HasType env U Γ p familyI) (hr : HasType env U Γ r familyJ)
    (hci : HasType env U Γ ctorI familyI) (hcj : HasType env U Γ ctorJ familyJ)
    (hfi : HasType env U Γ recI (.forallE familyI (.sort u)))
    (hfj : HasType env U Γ recJ (.forallE familyJ (.sort u)))
    (hii : IsDefEq env U Γ (.app recI ctorI) result (.sort u))
    (hij : IsDefEq env U Γ (.app recJ ctorJ) result (.sort u)) :
    IsDefEq env U Γ (.app recI p) (.app recJ r) (.sort u) := by
  have left : IsDefEq env U Γ (.app recI p) (.app recI ctorI) (.sort u) :=
    .appDF hfi (.proofIrrel hi hp hci)
  have right : IsDefEq env U Γ (.app recJ r) (.app recJ ctorJ) (.sort u) :=
    .appDF hfj (.proofIrrel hj hr hcj)
  exact (left.trans hii).trans (right.trans hij).symm

#print axioms proofMajorJoin
end InductiveStrengtheningPressure.Abstract
