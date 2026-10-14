import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedBinderComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNormalSyntax

/-! # Constant-spine inversion for scoped computation -/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean

/-- The constant at the head of an erased application spine, when present. -/
def constHead : ProofShape → Option Name
  | .const c _ => some c
  | .app f _ => constHead f
  | _ => none

/-- Adding arguments leaves the head constant unchanged. -/
theorem constHead_mkApps (f : ProofShape) (args : List ProofShape) :
    constHead (mkApps f args) = constHead f := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (.app f a)

/-- A visible pattern match retains the head of its registered pattern. -/
theorem Matches.constHead (H : Matches p a ls captures) : a.constHead = p.constHead := by
  induction H with
  | const => rfl
  | var _ ih => exact ih
  | app _ _ ih _ => exact ih

private theorem const_spine_app (E : mkApps (.const c ls) args = .app f a) :
    ∃ args₀, args = args₀ ++ [a] ∧ f = mkApps (.const c ls) args₀ := by
  induction args using List.snoc_induction with
  | nil => cases E
  | snoc args x _ =>
    rw [mkApps_snoc] at E
    obtain ⟨rfl, rfl⟩ := ProofShape.app.inj E
    exact ⟨args, rfl, rfl⟩

/-- Beta paths preserve a constant head and compute only its arguments. -/
theorem BetaRed.const_spine (R : BetaRed (mkApps (.const c ls) args) out) :
    ∃ args', out = mkApps (.const c ls) args' ∧ List.Forall₂ BetaRed args args' := by
  generalize E : mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | refl => exact ⟨args, E.symm, Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨args₁, rfl, H₁⟩ := ih₁ E
    obtain ⟨args₂, HE, H₂⟩ := ih₂ rfl
    exact ⟨_, HE, Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') H₁ H₂⟩
  | app Rf Ra ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := const_spine_app E
    obtain ⟨args', rfl, H⟩ := ihf rfl
    exact ⟨args' ++ [_], mkApps_snoc.symm, H.append' (.cons Ra .nil)⟩
  | proj | lam | forallE | beta =>
    have H := congrArg constHead E
    simp only [constHead_mkApps, constHead] at H
    cases H

/-- If no primitive contracts a chosen constant spine, a finite scoped path
preserves that head and supplies a path for every argument at the same context. -/
theorem ScopedCompute.const_spine
    (hn : ∀ {Δ args out}, ¬ Step Δ (mkApps (.const c ls) args) out)
    (R : ScopedCompute Step Δ (mkApps (.const c ls) args) out) :
    ∃ args', out = mkApps (.const c ls) args' ∧
      List.Forall₂ (ScopedCompute Step Δ) args args' := by
  generalize E : mkApps (.const c ls) args = source at R
  induction R generalizing args with
  | base H => exact (hn (E ▸ H)).elim
  | beta H =>
    cases E
    obtain ⟨args', HE, HA⟩ := H.const_spine
    exact ⟨_, HE, HA.imp (fun _ _ h => .beta h)⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨args₁, rfl, H₁⟩ := ih₁ E
    obtain ⟨args₂, HE, H₂⟩ := ih₂ rfl
    exact ⟨_, HE, Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') H₁ H₂⟩
  | app Rf Ra ihf _ =>
    obtain ⟨args₀, rfl, rfl⟩ := const_spine_app E
    obtain ⟨args', rfl, H⟩ := ihf rfl
    exact ⟨args' ++ [_], mkApps_snoc.symm, H.append' (.cons Ra .nil)⟩
  | proj | lam | forallE =>
    have H := congrArg constHead E
    simp only [constHead_mkApps, constHead] at H
    cases H

/-- A proof marker cannot change when primitives require visible computation
heads. No typing of the marker is assumed. -/
theorem ScopedCompute.proof_fixed
    (hroot : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ .proof out) : out = .proof := by
  generalize E : ProofShape.proof = source at R
  induction R with
  | base H => exact (E ▸ hroot H).elim
  | beta H =>
    cases E
    exact H.fixed_of_normal (Step := fun _ _ => False) ⟨fun _ H => H, trivial⟩
  | trans _ _ ih₁ ih₂ =>
    have H₁ := ih₁ E
    exact (ih₂ (E.trans H₁.symm)).trans H₁
  | app | proj | lam | forallE => cases E

end Lean4Lean.VEnv.Strengthening.ProofShape
