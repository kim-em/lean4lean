import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextSpineInversion

/-! # Syntactic fixed points of erased computation

A local test excluding primitive and beta roots at every subterm certifies that
all finite compatible computations have the original literal endpoint.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape

/-- No primitive or beta redex occurs at any position, including annotations. -/
def NormalSyntax (Step : ProofShape → ProofShape → Prop) (e : ProofShape) : Prop :=
  (∀ out, ¬ Step e out) ∧ match e with
  | .app f a => (∀ A b, f ≠ .lam A b) ∧ NormalSyntax Step f ∧ NormalSyntax Step a
  | .proj _ _ m => NormalSyntax Step m
  | .lam A b | .forallE A b => NormalSyntax Step A ∧ NormalSyntax Step b
  | _ => True

/-- The local test excludes a primitive at its outermost position. -/
theorem NormalSyntax.no_step (hn : NormalSyntax Step e) : ¬ Step e out := by
  cases e <;> exact hn.1 out

/-- Beta paths fix syntactically normal shapes. -/
theorem BetaRed.fixed_of_normal (H : BetaRed a b) (hn : NormalSyntax Step a) : b = a := by
  induction H with
  | refl => rfl
  | trans _ _ ih1 ih2 =>
    have E := ih1 hn
    exact (ih2 (E.symm ▸ hn)).trans E
  | app _ _ ihf iha => exact congr (congrArg ProofShape.app (ihf hn.2.2.1)) (iha hn.2.2.2)
  | proj _ ih => exact congrArg _ (ih hn.2)
  | lam _ _ ihA ihb => exact congr (congrArg ProofShape.lam (ihA hn.2.1)) (ihb hn.2.2)
  | forallE _ _ ihA ihB => exact congr (congrArg ProofShape.forallE (ihA hn.2.1)) (ihB hn.2.2)
  | beta => exact (hn.2.1 _ _ rfl).elim

/-- The local normality test excludes all finite computations, not just roots. -/
theorem NormalSyntax.fixed (hn : NormalSyntax Step a) : ComputeFixed Step a := by
  intro b H
  induction H with
  | base H => exact (hn.no_step H).elim
  | beta H => exact H.fixed_of_normal hn
  | trans _ _ ih1 ih2 =>
    have E := ih1 hn
    exact (ih2 (E.symm ▸ hn)).trans E
  | app _ _ ihf iha => exact congr (congrArg ProofShape.app (ihf hn.2.2.1)) (iha hn.2.2.2)
  | proj _ ih => exact congrArg _ (ih hn.2)
  | lam _ _ ihA ihb => exact congr (congrArg ProofShape.lam (ihA hn.2.1)) (ihb hn.2.2)
  | forallE _ _ ihA ihB => exact congr (congrArg ProofShape.forallE (ihA hn.2.1)) (ihB hn.2.2)

end Lean4Lean.VEnv.Strengthening.ProofShape
