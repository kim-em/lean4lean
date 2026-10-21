import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedFirstBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpines

/-! # First head beta with pending application arguments

The decomposition retains computations of every supplied argument and the full
post-beta tail, including applications still pending at that first contraction.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean

private theorem lambda_spine_app (E : mkApps (.lam A b) args = .app f x) :
    ∃ args₀, args = args₀ ++ [x] ∧ f = mkApps (.lam A b) args₀ := by
  induction args using List.snoc_induction with
  | nil => cases E
  | snoc args a _ =>
    rw [mkApps_snoc] at E
    obtain ⟨rfl, rfl⟩ := ProofShape.app.inj E
    exact ⟨args, rfl, rfl⟩

private theorem lambda_spine_lam (E : mkApps (.lam A b) args = .lam C d) :
    args = [] ∧ A = C ∧ b = d := by
  cases args using List.snoc_induction with
  | nil => exact ⟨rfl, (ProofShape.lam.inj E).1, (ProofShape.lam.inj E).2⟩
  | snoc args a => rw [mkApps_snoc] at E; cases E

private theorem lambda_spine_not_primitive (A b : ProofShape) (args : List ProofShape) :
    ¬ PrimitiveHead (mkApps (.lam A b) args) := by
  induction args using List.snoc_induction with
  | nil => exact id
  | snoc args a ih => simpa only [mkApps_snoc, PrimitiveHead] using ih

private theorem beta_lambda_spine (R : BetaRed (mkApps (.lam A b) args) out) :
    (∃ A' b' args', out = mkApps (.lam A' b') args' ∧
      BetaRed (.lam A b) (.lam A' b') ∧ List.Forall₂ BetaRed args args') ∨
    (∃ A' b' x' xs', BetaRed (.lam A b) (.lam A' b') ∧
      List.Forall₂ BetaRed args (x' :: xs') ∧ BetaRed (mkApps (b'.inst x') xs') out) := by
  generalize E : mkApps (.lam A b) args = source at R
  induction R generalizing A b args with
  | refl => exact .inl ⟨A, b, args, E.symm, .refl, Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl)⟩
  | beta =>
    obtain ⟨args₀, rfl, EF⟩ := lambda_spine_app E
    obtain ⟨rfl, rfl, rfl⟩ := lambda_spine_lam EF.symm
    exact .inr ⟨_, _, _, [], .refl, .cons .refl .nil, .refl⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨A', b', args', rfl, RF, RX⟩ | ⟨A', b', x', xs', RF, RX, RT⟩
    · rcases ih₂ rfl with ⟨A'', b'', args'', EO, RF', RX'⟩ | ⟨A'', b'', x'', xs'', RF', RX', RT⟩
      · exact .inl ⟨A'', b'', args'', EO, RF.trans RF',
          Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') RX RX'⟩
      · exact .inr ⟨A'', b'', x'', xs'', RF.trans RF',
          Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') RX RX', RT⟩
    · exact .inr ⟨A', b', x', xs', RF, RX, RT.trans R₂⟩
  | app RF RX ihf ihx =>
    rename_i fOut x xOut
    obtain ⟨args₀, rfl, rfl⟩ := lambda_spine_app E
    rcases ihf rfl with ⟨A', b', args', rfl, RF', RX'⟩ | ⟨A', b', x', xs', RF', RX', RT⟩
    · exact .inl ⟨A', b', args' ++ [_], mkApps_snoc.symm, RF', RX'.append' (.cons RX .nil)⟩
    · refine .inr ⟨A', b', x', xs' ++ [xOut], RF', ?_, ?_⟩
      · exact RX'.append' (.cons RX .nil)
      · rw [mkApps_snoc]
        exact .app RT .refl
  | lam RA RB =>
    obtain ⟨rfl, rfl, rfl⟩ := lambda_spine_lam E
    exact .inl ⟨_, _, [], rfl, .lam RA RB, .nil⟩
  | proj | forallE =>
    cases args using List.snoc_induction with
    | nil => cases E
    | snoc args a => rw [mkApps_snoc] at E; cases E

/-- Until its first head beta, a lambda spine only computes its function and
arguments. After that beta the exact contractum with its pending arguments
computes to the original output. All argument paths and the tail are retained. -/
theorem ScopedCompute.lambda_spine_or_beta
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (mkApps (.lam A b) args) out) :
    (∃ A' b' args', out = mkApps (.lam A' b') args' ∧
      ScopedCompute Step Δ (.lam A b) (.lam A' b') ∧ List.Forall₂ (ScopedCompute Step Δ) args args') ∨
    (∃ A' b' x' xs', ScopedCompute Step Δ (.lam A b) (.lam A' b') ∧
      List.Forall₂ (ScopedCompute Step Δ) args (x' :: xs') ∧ ScopedCompute Step Δ (mkApps (b'.inst x') xs') out) := by
  generalize E : mkApps (.lam A b) args = source at R
  induction R generalizing A b args with
  | base H => exact (lambda_spine_not_primitive A b args (E ▸ hhead H)).elim
  | beta H =>
    cases E
    rcases beta_lambda_spine H with ⟨A', b', args', EO, RF, RX⟩ | ⟨A', b', x', xs', RF, RX, RT⟩
    · exact .inl ⟨A', b', args', EO, .beta RF, RX.imp (fun _ _ H => .beta H)⟩
    · exact .inr ⟨A', b', x', xs', .beta RF, RX.imp (fun _ _ H => .beta H), .beta RT⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    rcases ih₁ E with ⟨A', b', args', rfl, RF, RX⟩ | ⟨A', b', x', xs', RF, RX, RT⟩
    · rcases ih₂ rfl with ⟨A'', b'', args'', EO, RF', RX'⟩ | ⟨A'', b'', x'', xs'', RF', RX', RT⟩
      · exact .inl ⟨A'', b'', args'', EO, RF.trans RF',
          Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') RX RX'⟩
      · exact .inr ⟨A'', b'', x'', xs'', RF.trans RF',
          Lean4Lean.List.Forall₂.trans (fun _ _ _ h h' => h.trans h') RX RX', RT⟩
    · exact .inr ⟨A', b', x', xs', RF, RX, RT.trans R₂⟩
  | app RF RX ihf ihx =>
    rename_i fOut x xOut
    obtain ⟨args₀, rfl, rfl⟩ := lambda_spine_app E
    rcases ihf rfl with ⟨A', b', args', rfl, RF', RX'⟩ | ⟨A', b', x', xs', RF', RX', RT⟩
    · exact .inl ⟨A', b', args' ++ [_], mkApps_snoc.symm, RF', RX'.append' (.cons RX .nil)⟩
    · refine .inr ⟨A', b', x', xs' ++ [xOut], RF', ?_, ?_⟩
      · exact RX'.append' (.cons RX .nil)
      · rw [mkApps_snoc]
        exact .app RT .refl
  | lam RA RB =>
    obtain ⟨rfl, rfl, rfl⟩ := lambda_spine_lam E
    exact .inl ⟨_, _, [], rfl, .lam RA RB, .nil⟩
  | proj | forallE =>
    cases args using List.snoc_induction with
    | nil => cases E
    | snoc args a => rw [mkApps_snoc] at E; cases E

/-- Reaching a literal universe from a nonempty lambda spine forces a first
head beta, with every pending argument and the exact tail still available. -/
theorem ScopedCompute.lambda_spine_sort
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedCompute Step Δ (mkApps (.lam A b) args) (.sort v)) :
    ∃ A' b' x' xs', ScopedCompute Step Δ (.lam A b) (.lam A' b') ∧
      List.Forall₂ (ScopedCompute Step Δ) args (x' :: xs') ∧
      ScopedCompute Step Δ (mkApps (b'.inst x') xs') (.sort v) := by
  rcases R.lambda_spine_or_beta hhead with ⟨_, _, args', E, _, _⟩ | H
  · cases args' using List.snoc_induction with
    | nil => cases E
    | snoc args a => rw [mkApps_snoc] at E; cases E
  · exact H

end Lean4Lean.VEnv.Strengthening.ProofShape
