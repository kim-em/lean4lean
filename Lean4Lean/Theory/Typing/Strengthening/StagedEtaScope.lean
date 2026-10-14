import Lean4Lean.Theory.Typing.Strengthening.StagedEtaComputation
import Lean4Lean.Theory.Typing.Strengthening.RecoverySubstitutionBoundary

/-! # All finite eta/K stages retain exact scope reflection

Increasing the interaction depth cannot reproduce captured ambient annotations
or repair exact recovery substitution. General coverage still needs to choose
scoped outputs, and substitution must permit re-synthesis of output types.
-/
namespace Lean4Lean.VEnv.Strengthening.EtaScope
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
variable [Params]

/-- The captured eta expansion is excluded at every finite interaction depth. -/
theorem captured_eta_not_staged (heq : env.HasCanonicalEq)
    (hs : PureObservation.Definitions.Sound D env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hQ : env.HasType univs Γ Q (.sort u)) :
    ¬ StagedEtaCompute D kdepth stage (Q :: Γ) (ident 0).lift (expanded Q) := by
  intro R
  rw [lift_eq_lift'] at R
  obtain ⟨out, hout, _⟩ := R.descend heq hs (Ctx.Lift'.skip .refl) hΓ
    ⟨hΓ, _, hQ⟩ (ident_typed env univs Γ 0)
  apply captured_not_lift (Q := Q)
  rw [hout, ← lift_eq_lift']
  exact .liftN

/-- Exact captured output recovery remains impossible at every stage, even
though the source has an ordinary typing at that precise output type. -/
theorem identity_captured_not_staged_recovery (heq : env.HasCanonicalEq)
    (hs : PureObservation.Definitions.Sound D env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hQ : env.HasType univs Γ Q (.sort u)) :
    ¬ StagedTypeRecovery D kdepth stage (Q :: Γ) (ident 0).lift (capturedPi Q) := by
  intro R
  rw [lift_eq_lift'] at R
  obtain ⟨T, hT, _⟩ := R.descend heq hs (Ctx.Lift'.skip .refl) hΓ
    ⟨hΓ, _, hQ⟩ ⟨_, ident_typed env univs Γ 0⟩
  apply captured_pi_not_scoped (Q := Q)
  rw [hT, ← lift_eq_lift']
  exact .liftN

end Lean4Lean.VEnv.Strengthening.EtaScope
