import Lean4Lean.Theory.Typing.Strengthening.PureHeadExposure
import Lean4Lean.Theory.Typing.Strengthening.GuardedEtaLoop

/-! # Boundary and scope tests for beta/eta head exposure

The guarded recursive loop has a finite beta/eta trace despite having no beta-only
bidirectional join. Head exposure also tolerates a syntactic eta annotation that
mentions an inserted binder. A lambda-head analogue is explicitly false.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Developments

/-- The new head analysis includes the finite eta repair of the recursive test. -/
theorem guarded_loop_eta : BetaEta (GuardedEta.omegaTerm c) (GuardedEta.etaOmega c) := by
  have hd : BetaEta (GuardedEta.diagonal c) (GuardedEta.etaDiagonal c) := .lam .refl .eta
  exact .app hd hd

/-- Eta expansion does not falsely make the recursive loop converge to a Pi. -/
theorem guarded_loop_no_pi : ¬ BetaEta (GuardedEta.etaOmega c) (.forallE A B) := by
  intro H
  obtain ⟨D, C, RB⟩ := (guarded_loop_eta.trans H).pi_exposure
  have he := GuardedEta.omega_beta_eq RB
  cases he

/-- A lambda-head version of the theorem is false: eta alone can expose a lambda
from a variable, whose only beta reduct is that same variable. -/
theorem lambda_head_boundary : BetaEta (.bvar i) (.lam A (.app (VExpr.bvar i).lift (.bvar 0))) ∧
    ¬ ∃ D b, BetaRed (.bvar i) (.lam D b) := by
  refine ⟨.eta, ?_⟩
  rintro ⟨D, b, RB⟩
  have he := beta_eq_of_not_hasBeta RB (by simp [HasBeta])
  cases he

def headSource (c : Name) : VExpr :=
  .app (.lam (GuardedEta.domain c) GuardedEta.resultType) (GuardedEta.diagonal c)

def headIntermediate (c : Name) (A : VExpr) : VExpr :=
  .app (.lam A (.app (VExpr.lam (GuardedEta.domain c) GuardedEta.resultType).lift (.bvar 0)))
    (GuardedEta.etaDiagonal c)

/-- A mixed path may eta-expand both function and argument before returning a Pi.
The eta annotation A is arbitrary; no typing of this test path is claimed. -/
theorem head_trace : BetaEta (headSource c) (headIntermediate c A) ∧
    BetaEta (headIntermediate c A) GuardedEta.resultType := by
  refine ⟨.app .eta (.lam .refl .eta), ?_⟩
  have first : BetaEta (headIntermediate c A)
      (.app (.lam (GuardedEta.domain c) GuardedEta.resultType) (GuardedEta.etaDiagonal c)) := by
    simpa only [headIntermediate, inst, inst_lift, instVar_zero] using
      (BetaEta.beta (A := A)
        (b := .app (VExpr.lam (GuardedEta.domain c) GuardedEta.resultType).lift (.bvar 0))
        (a := GuardedEta.etaDiagonal c))
  apply first.trans
  simpa [GuardedEta.resultType, GuardedEta.prop, inst] using
    (BetaEta.beta (A := GuardedEta.domain c) (b := GuardedEta.resultType) (a := GuardedEta.etaDiagonal c))

/-- Scope can fail at an intermediate eta annotation while a beta-only Pi exposure
still exists for the original source. This does not assert replay of that annotation. -/
theorem captured_annotation_head_exposure :
    ¬ (headIntermediate c (.bvar 0)).Skips 1 0 ∧
    ∃ D C, BetaRed (headSource c) (.forallE D C) := by
  refine ⟨by simp [headIntermediate, skips_iff, Skips'], ?_⟩
  exact ((head_trace (c := c) (A := .bvar 0)).1.trans (head_trace (c := c) (A := .bvar 0)).2).pi_exposure

end Lean4Lean.VEnv.Strengthening.PureObservation
