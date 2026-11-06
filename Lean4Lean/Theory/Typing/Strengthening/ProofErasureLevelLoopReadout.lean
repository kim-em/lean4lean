import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelRecursiveTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout

/-! # Diagonal annotation readout through explicit universe computation

Ordinary primitive-head exclusion does not cover sort universe roots. Direct
inversion of the full level core nevertheless retains diagonal bodies and loop
ancestry. Raw inferred comparison of the loops therefore exposes an inferred
comparison of their original annotations, including all universe conversions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private beta_diagonal_inv no_eta_diagonal no_constructor_diagonal no_constructor_loop
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params] {D : Definitions}

private theorem no_loop_root (H : ErasedLevelCore D (.app (diagonal A) (diagonal B)) out) : False := by
  rcases H with H | H
  · exact erased_iota_primitive_head H
  · cases H

/-- Full level-core computation changes only a diagonal's annotation. -/
theorem ProofShape.Compute.level_diagonal_inv
    (R : ProofShape.Compute (ErasedLevelCore D) (diagonal A) out) :
    ∃ A', out = diagonal A' ∧ ProofShape.Compute (ErasedLevelCore D) A A' := by
  obtain ⟨A', b', E, RA, RB⟩ := R.level_core_lam_inv
  obtain ⟨arg, EB, RX⟩ := RB.level_core_bvar_app_inv
  obtain rfl := RX.level_core_bvar_fixed
  exact ⟨A', E.trans (congrArg (ProofShape.lam A') EB), RA⟩

private theorem beta_loop_residual
    (R : ProofShape.BetaRed source out)
    (EA : ProofShape.Compute (ErasedLevelCore D) C A)
    (EB : ProofShape.Compute (ErasedLevelCore D) C B)
    (E : source = .app (diagonal A) (diagonal B)) :
    ∃ A' B', out = .app (diagonal A') (diagonal B') ∧
      ProofShape.Compute (ErasedLevelCore D) C A' ∧ ProofShape.Compute (ErasedLevelCore D) C B' := by
  induction R generalizing A B with
  | refl => exact ⟨A, B, E, EA, EB⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, E₁, HA, HB⟩ := ih₁ EA EB E
    exact ih₂ HA HB E₁
  | app RF RX =>
    cases E
    obtain ⟨A', rfl, RA⟩ := beta_diagonal_inv RF
    obtain ⟨B', rfl, RB⟩ := beta_diagonal_inv RX
    exact ⟨A', B', rfl, EA.trans (.beta RA), EB.trans (.beta RB)⟩
  | beta =>
    cases E
    exact ⟨B, B, by simp [diagonal, ProofShape.inst, ProofShape.liftN_zero], EB, EB⟩
  | proj | lam | forallE => cases E

private theorem loop_residual
    (R : ProofShape.Compute (ErasedLevelCore D) source out)
    (EA : ProofShape.Compute (ErasedLevelCore D) C A)
    (EB : ProofShape.Compute (ErasedLevelCore D) C B)
    (E : source = .app (diagonal A) (diagonal B)) :
    ∃ A' B', out = .app (diagonal A') (diagonal B') ∧
      ProofShape.Compute (ErasedLevelCore D) C A' ∧ ProofShape.Compute (ErasedLevelCore D) C B' := by
  induction R generalizing A B with
  | base H => exact (no_loop_root (E ▸ H)).elim
  | beta H => exact beta_loop_residual H EA EB E
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, E₁, HA, HB⟩ := ih₁ EA EB E
    exact ih₂ HA HB E₁
  | app RF RX =>
    cases E
    obtain ⟨A', rfl, RA⟩ := RF.level_diagonal_inv
    obtain ⟨B', rfl, RB⟩ := RX.level_diagonal_inv
    exact ⟨A', B', rfl, EA.trans RA, EB.trans RB⟩
  | proj | lam | forallE => cases E

/-- Every full-core reduct of a loop retains two diagonal annotations descended
from the original one, despite arbitrary duplication and universe changes. -/
theorem ProofShape.Compute.level_selfLoop_inv
    (R : ProofShape.Compute (ErasedLevelCore D) (selfLoop A) out) :
    ∃ A' B', out = .app (diagonal A') (diagonal B') ∧
      ProofShape.Compute (ErasedLevelCore D) A A' ∧ ProofShape.Compute (ErasedLevelCore D) A B' :=
  loop_residual R .refl .refl rfl

private theorem compare_diagonal
    (H : Compare (ErasedLevelCore D) false (diagonal A) (diagonal B)) :
    Compare (ErasedLevelCore D) false A B := by
  generalize EA : diagonal A = a at H
  generalize EB : diagonal B = b at H
  generalize hm : false = mode at H
  induction H generalizing A B with
  | refl => cases ProofShape.lam.inj (EA.trans EB.symm) |>.1; exact .refl
  | lam HD HB => cases hm; cases EA; cases EB; exact HD
  | etaLams HD H => cases hm; cases EA; cases EB; exact HD
  | compute RA RB HC ih =>
    obtain ⟨A', E₁, HA⟩ := (EA ▸ RA).level_diagonal_inv
    obtain ⟨B', E₂, HB⟩ := (EB ▸ RB).level_diagonal_inv
    exact .compute HA HB (ih E₁.symm E₂.symm hm)
  | etaL | etaR | structL | structR => cases hm
  | sort | const | app | proj | forallE => cases EA

/-- Inferred raw checking of diagonals cannot omit their annotations. -/
theorem ProofShape.RawCheckedCompare.level_diagonal_annotations
    (H : RawCheckedCompare (ErasedLevelCore D) false (diagonal A) (diagonal B)) :
    RawCheckedCompare (ErasedLevelCore D) false A B := by
  generalize EA : diagonal A = a at H
  generalize EB : diagonal B = b at H
  generalize hm : false = mode at H
  induction H generalizing A B with
  | base H => cases hm; exact .base (compare_diagonal (EA ▸ EB ▸ H))
  | lam HD HB => cases hm; cases EA; cases EB; exact HD
  | compute RA RB HC ih =>
    obtain ⟨A', E₁, HA⟩ := (EA ▸ RA).level_diagonal_inv
    obtain ⟨B', E₂, HB⟩ := (EB ▸ RB).level_diagonal_inv
    exact .compute HA HB (ih E₁.symm E₂.symm hm)
  | lamCommon => cases hm
  | app | proj | forallE => cases EA

private theorem compare_loops
    (H : Compare (ErasedLevelCore D) mode a b)
    (HA : ProofShape.Compute (ErasedLevelCore D) X A) (HB : ProofShape.Compute (ErasedLevelCore D) X B)
    (HC : ProofShape.Compute (ErasedLevelCore D) Y C) (HF : ProofShape.Compute (ErasedLevelCore D) Y F)
    (EA : a = .app (diagonal A) (diagonal B)) (EB : b = .app (diagonal C) (diagonal F)) :
    Compare (ErasedLevelCore D) false X Y := by
  induction H generalizing X Y A B C F with
  | refl =>
    have E := ProofShape.lam.inj (ProofShape.app.inj (EA.symm.trans EB)).1 |>.1
    exact .compute HA HC (E ▸ .refl)
  | app Hf Hx => cases EA; cases EB; exact .compute HA HC (compare_diagonal Hf)
  | compute Ra Rb H ih =>
    obtain ⟨A', B', EA', HA', HB'⟩ := loop_residual Ra HA HB EA
    obtain ⟨C', F', EB', HC', HF'⟩ := loop_residual Rb HC HF EB
    exact ih HA' HB' HC' HF' EA' EB'
  | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EA.symm.trans E
  | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.symm.trans E
  | structL H | structR H =>
    cases H
    first | exact (no_constructor_loop EA.symm).elim | exact (no_constructor_loop EB.symm).elim
  | sort | const | proj | lam | forallE | etaLams => cases EA

private theorem checked_loops
    (H : RawCheckedCompare (ErasedLevelCore D) mode a b)
    (HA : ProofShape.Compute (ErasedLevelCore D) X A) (HB : ProofShape.Compute (ErasedLevelCore D) X B)
    (HC : ProofShape.Compute (ErasedLevelCore D) Y C) (HF : ProofShape.Compute (ErasedLevelCore D) Y F)
    (EA : a = .app (diagonal A) (diagonal B)) (EB : b = .app (diagonal C) (diagonal F)) :
    RawCheckedCompare (ErasedLevelCore D) false X Y := by
  induction H generalizing X Y A B C F with
  | base H => exact .base (compare_loops H HA HB HC HF EA EB)
  | app Hf Hx => cases EA; cases EB; exact .compute HA HC Hf.level_diagonal_annotations
  | compute Ra Rb H ih =>
    obtain ⟨A', B', EA', HA', HB'⟩ := loop_residual Ra HA HB EA
    obtain ⟨C', F', EB', HC', HF'⟩ := loop_residual Rb HC HF EB
    exact ih HA' HB' HC' HF' EA' EB'
  | proj | lam | forallE | lamCommon => cases EA

/-- Comparing loops in either mode exposes inferred comparison of the original
annotations through the entire level core. No annotation fixedness is assumed. -/
theorem ProofShape.RawCheckedCompare.level_selfLoop_annotations
    (H : RawCheckedCompare (ErasedLevelCore D) mode (selfLoop A) (selfLoop B)) :
    RawCheckedCompare (ErasedLevelCore D) false A B :=
  checked_loops H .refl .refl .refl .refl rfl rfl

private theorem compare_pi_exposure
    (H : Compare (ErasedLevelCore D) false (.forallE A B) e) :
    ∃ C E, ProofShape.Compute (ErasedLevelCore D) e (.forallE C E) := by
  generalize EA : ProofShape.forallE A B = a at H
  generalize hm : false = mode at H
  induction H generalizing A B with
  | refl => cases EA; exact ⟨_, _, .refl⟩
  | forallE => exact ⟨_, _, .refl⟩
  | compute RA RB H ih =>
    obtain ⟨A', B', E, _, _⟩ := (EA ▸ RA).pi_parts (fun H => erased_level_core_no_pi H)
    obtain ⟨C, F, R⟩ := ih E.symm hm
    exact ⟨C, F, RB.trans R⟩
  | etaL | etaR | structL | structR => cases hm
  | sort | const | app | proj | lam | etaLams => cases EA

/-- Inferred raw comparison with a displayed Pi forces full-core Pi exposure
on the other side. Common lambda and untyped head-eta bridges are unavailable. -/
theorem ProofShape.RawCheckedCompare.level_pi_exposure
    (H : RawCheckedCompare (ErasedLevelCore D) false (.forallE A B) e) :
    ∃ C E, ProofShape.Compute (ErasedLevelCore D) e (.forallE C E) := by
  generalize EA : ProofShape.forallE A B = a at H
  generalize hm : false = mode at H
  induction H generalizing A B with
  | base H => exact compare_pi_exposure (hm.symm ▸ EA ▸ H)
  | forallE => exact ⟨_, _, .refl⟩
  | compute RA RB H ih =>
    obtain ⟨A', B', E, _, _⟩ := (EA ▸ RA).pi_parts (fun H => erased_level_core_no_pi H)
    obtain ⟨C, F, R⟩ := ih E.symm hm
    exact ⟨C, F, RB.trans R⟩
  | lamCommon => cases hm
  | app | proj | lam => cases EA

end Lean4Lean.VEnv.Strengthening
