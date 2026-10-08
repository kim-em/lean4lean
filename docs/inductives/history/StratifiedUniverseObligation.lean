import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
The former `fieldType_inv_stratified` conclusion retyped a field at an equivalent
literal sort without increasing its stratification height. This certificate
checks the obstruction to that bound: a constant stored at `Sort 1` has height
one, but its typing at `Sort (max 0 1)` requires height two.

The constant lookup remains an explicit premise. These proofs do not construct
a full projection environment. The existing `ProjectionWithoutCasesOn` source
fixture has a field of type `Nat`, whose stored type is `Sort 1`, so the issue
is relevant to an ordinary accepted projection. The repaired foundation
statement retains the two original typings and returns universe equivalence;
it does not claim to have proved field congruence or type uniqueness.
-/

namespace Lean4Lean.VEnv.StratifiedUniverseObligation
open VExpr

theorem noConstAtZero (h : HasTypeStratified env U Γ (.const c ls) A b 0) : False := by
  generalize he : VExpr.const c ls = e at h
  generalize hn : (0 : Nat) = n at h
  induction h with
  | base _ ih => exact ih he hn
  | sort' => cases he
  | bvar | const | elim | app | proj | lam | forallE | defeq => cases hn

theorem constAtOne (h : HasTypeStratified env U Γ (.const c ls) A true 1) :
    ∃ ci, env.constants c = some ci ∧ A = ci.type.instL ls := by
  cases h with
  | base h =>
    cases h with
    | const hc _ _ _ => exact ⟨_, hc, rfl⟩
  | defeq _ _ _ _ h => exact (noConstAtZero h).elim

def one : VLevel := .succ .zero
def otherOne : VLevel := .max .zero one

theorem levelsEquiv : one ≈ otherOne := by
  funext xs
  simp [one, otherOne, VLevel.eval]

theorem noRetagAtOne (hc : env.constants c = some ⟨0, .sort one⟩) :
    ¬ HasTypeStratified env 0 Γ (.const c []) (.sort otherOne) true 1 := by
  intro h
  obtain ⟨ci, hci, ht⟩ := constAtOne h
  have he := Option.some.inj (hc.symm.trans hci)
  subst ci
  cases ht

theorem typedAtOne (hc : env.constants c = some ⟨0, .sort one⟩) :
    HasTypeStratified env 0 Γ (.const c []) (.sort one) true 1 := by
  apply HasTypeStratified.base
  apply HasTypeStratified.const hc (by simp) rfl
  exact .base (.sort' (by trivial) (by trivial) rfl)

theorem typedAtOtherOne (hc : env.constants c = some ⟨0, .sort one⟩) :
    HasTypeStratified env 0 Γ (.const c []) (.sort otherOne) true 2 := by
  refine .defeq (u := .succ one) (by trivial)
    (.sortDF (by trivial) (by exact ⟨True.intro, True.intro⟩) levelsEquiv)
    (.base (.sort' (by trivial) (by trivial) rfl))
    (.base (.sort' (l := otherOne) (l' := one) (by exact ⟨True.intro, True.intro⟩) (by trivial)
      levelsEquiv.symm)) (typedAtOne hc)

#print axioms noRetagAtOne
#print axioms typedAtOne
#print axioms typedAtOtherOne

end Lean4Lean.VEnv.StratifiedUniverseObligation
