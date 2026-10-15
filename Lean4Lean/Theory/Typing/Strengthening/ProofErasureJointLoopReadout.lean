import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveryExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout

/-! # Diagonal annotation readout for the full joint checker

Carrier-aware application still compares the functions in inferred mode.
Consequently it cannot hide annotation conversion between two self-application
loops. This extends the earlier scoped readout to the full mutual grammar.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private no_eta_diagonal no_constructor_diagonal no_constructor_loop loop_residual
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedLoopReadout
variable [Params]

/-- Either joint comparison mode may be used in common mode. Carrier and
inferred-function subchecks retain their own checking modes. -/
theorem JointCompare.common (H : JointCompare Step Δ mode a b) : JointCompare Step Δ true a b := by
  change JointCheck Step Δ (.compare mode) a b at H
  generalize hk : JointCheckKind.compare mode = kind at H
  induction H generalizing mode with
  | leaf H => exact .leaf H.common
  | app HF HX => exact .app HF HX
  | appCarrier R HF HX => exact .appCarrier R HF HX
  | proj H => exact .proj H
  | lam HA HB ihA ihB => cases hk; exact .lam HA (ihB rfl)
  | forallE HA HB => exact .forallE HA HB
  | lamSorted S S' HA HB ihA ihB => cases hk; exact .lamSorted S S' HA (ihB rfl)
  | forallSorted S S' HA T T' HB => exact .forallSorted S S' HA T T' HB
  | lamCommon H => exact .lamCommon H
  | etaBodyL S H => exact .etaBodyL S H
  | etaBodyR S H => exact .etaBodyR S H
  | structFields hi hx hp hf hadm H => exact .structFields hi hx hp hf hadm H
  | etaLams HD Hη => exact .etaLams HD Hη
  | compute RA RB H ih => exact .compute RA RB (ih hk)
  | symm H ih => exact .symm (ih hk)
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

/-- Inferred joint comparison of diagonals reads their original annotations,
including arbitrary computation and nested recovered application checks. -/
theorem JointCompare.diagonal_annotations
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCompare Step Δ false (diagonal A) (diagonal B)) : JointCompare Step Δ true A B := by
  generalize EA : diagonal A = a at H
  generalize EB : diagonal B = b at H
  change JointCheck Step Δ (.compare false) a b at H
  generalize hk : JointCheckKind.compare false = kind at H
  induction H generalizing A B with
  | leaf H =>
    cases H with
    | refl => cases ProofShape.lam.inj (EA.trans EB.symm) |>.1; exact .leaf .refl
    | sort | const => cases EA
    | etaL | etaR => cases hk
  | lam HD HB => cases EA; cases EB; exact JointCompare.common HD
  | lamSorted _ _ HD HB => cases EA; cases EB; exact HD
  | etaLams HD HE =>
    cases EA; cases EB
    exact (HE.elim no_eta_diagonal no_eta_diagonal).elim
  | compute RA RB HC ih =>
    obtain ⟨A', E₁, HA⟩ := (EA ▸ RA).diagonal_inv hhead
    obtain ⟨B', E₂, HB⟩ := (EB ▸ RB).diagonal_inv hhead
    exact .compute HA HB (ih E₁.symm E₂.symm hk)
  | symm HC ih => exact .symm (ih EB EA hk)
  | structFields => exact (no_constructor_diagonal EA).elim
  | lamCommon | etaBodyL | etaBodyR => cases hk
  | app | appCarrier | proj | forallE | forallSorted => cases EA
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

private theorem compare_loops
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCompare Step Δ mode a b)
    (HA : ScopedCompute Step Δ D A) (HB : ScopedCompute Step Δ D B)
    (HC : ScopedCompute Step Δ E C) (HF : ScopedCompute Step Δ E F)
    (EA : a = .app (diagonal A) (diagonal B))
    (EB : b = .app (diagonal C) (diagonal F)) : JointCompare Step Δ true D E := by
  change JointCheck Step Δ (.compare mode) a b at H
  generalize hk : JointCheckKind.compare mode = kind at H
  induction H generalizing mode D E A B C F with
  | leaf H =>
    cases H with
    | refl =>
      have E := ProofShape.lam.inj (ProofShape.app.inj (EA.symm.trans EB)).1 |>.1
      exact .compute HA HC (E ▸ JointCheck.leaf .refl)
    | sort | const => cases EA
    | etaL H => obtain ⟨_, _, E, _⟩ := H.shape; cases EA.symm.trans E
    | etaR H => obtain ⟨_, _, E, _⟩ := H.shape; cases EB.symm.trans E
  | app Hf Hx | appCarrier _ Hf Hx =>
    cases EA; cases EB
    exact .compute HA HC (JointCompare.diagonal_annotations hhead Hf)
  | compute Ra Rb H ih =>
    obtain ⟨A', B', EA', HA', HB'⟩ := loop_residual hhead Ra HA HB EA
    obtain ⟨C', F', EB', HC', HF'⟩ := loop_residual hhead Rb HC HF EB
    exact ih HA' HB' HC' HF' EA' EB' hk
  | symm H ih => exact .symm (ih HC HF HA HB EB EA hk)
  | structFields => exact (no_constructor_loop EA.symm).elim
  | etaBodyR => cases EB
  | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL | etaLams => cases EA
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

/-- Joint comparison of self-application loops exposes common comparison of
their original annotations. The added carrier-aware application rule does not
bypass the inferred comparison of their diagonal functions. -/
theorem JointCompare.selfLoop_annotations
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : JointCompare Step Δ mode (selfLoop A) (selfLoop B)) : JointCompare Step Δ true A B :=
  compare_loops hhead H .refl .refl .refl .refl rfl rfl

end Lean4Lean.VEnv.Strengthening.ProofShape
