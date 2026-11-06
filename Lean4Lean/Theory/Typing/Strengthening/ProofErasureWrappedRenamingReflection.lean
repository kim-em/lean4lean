import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWrappedHeadCut

/-! # Variable renaming reflects wrapped constant heads

A variable map cannot introduce a constant or a lambda. Beneath a lambda it
also cannot turn an older variable into the fresh bound variable, so it cannot
create an identity wrapper. Injectivity of the variable map is unnecessary.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean ProofShape
variable {κ : ProofShape.Subst} {e : ProofShape}

private theorem variable_map_lift
    (H : ∀ i, ∃ j, κ i = ProofShape.bvar j) :
    ∀ i, ∃ j, κ.lift i = ProofShape.bvar j := by
  intro i
  cases i with
  | zero => exact ⟨0, rfl⟩
  | succ i =>
    obtain ⟨j, Ej⟩ := H i
    exact ⟨j+1, by simp [ProofShape.Subst.lift, Ej, ProofShape.liftN, liftVar, Nat.add_comm]⟩

private theorem fresh_bvar_of_rename
    (H : ∀ i, ∃ j, κ i = ProofShape.bvar j)
    (E : e.subst κ.lift = ProofShape.bvar 0) : e = .bvar 0 := by
  cases e <;> try cases E
  rename_i i
  cases i with
  | zero => rfl
  | succ i =>
    obtain ⟨j, Ej⟩ := H i
    simp [ProofShape.subst, ProofShape.Subst.lift, Ej, ProofShape.liftN, liftVar] at E

/-- Any variable renaming reflects wrapped constant heads, even when the
renaming identifies free variables. Identity wrappers cannot be manufactured
because lifted renaming preserves the distinction of the fresh variable. -/
theorem WrappedConstHead.of_variable_rename
    (Hκ : ∀ i, ∃ j, κ i = ProofShape.bvar j)
    (H : WrappedConstHead c (e.subst κ)) : WrappedConstHead c e := by
  induction e generalizing κ with
  | proof | sort | proj | forallE => cases H
  | bvar i =>
    obtain ⟨j, Ej⟩ := Hκ i
    simp only [ProofShape.subst, Ej] at H
    cases H
  | const => cases H; exact .const
  | lam A b _ ih =>
    cases H with
    | lam H => exact .lam (ih (variable_map_lift Hκ) H)
  | app f a ihf iha =>
    simp only [ProofShape.subst] at H
    generalize EF : f.subst κ = F at H
    cases H with
    | app H => exact .app (ihf Hκ (EF.symm ▸ H))
    | identity H =>
      cases f <;> simp only [ProofShape.subst] at EF
      all_goals try cases EF
      · rename_i i
        obtain ⟨j, Ej⟩ := Hκ i
        simp only [Ej] at EF
        cases EF
      · obtain ⟨_, Eb⟩ := ProofShape.lam.inj EF
        have Eb := fresh_bvar_of_rename Hκ Eb
        subst Eb
        exact .identity (iha Hκ H)

end Lean4Lean.VEnv.Strengthening
