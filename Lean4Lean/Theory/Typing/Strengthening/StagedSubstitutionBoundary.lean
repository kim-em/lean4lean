import Lean4Lean.Theory.Typing.Strengthening.StagedEtaScope

/-! # No unbounded exact substitution law for staged computation

The argument-recovery premise cannot be replaced by ordinary typing even if the
output is permitted any finite stage. Substituting an identity for a variable
whose declared Pi captures another binder turns a legal recovered eta step into
the exact captured eta target excluded by every stage's descent theorem.
-/
namespace Lean4Lean.VEnv.Strengthening.EtaScope
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
variable [Params]

/-- The source variable's chosen domain comes from its declaration. -/
def variableExpansion (Q : VExpr) : VExpr :=
  .lam (capturedDomain Q).lift (.app (.bvar 1) (.bvar 0))

/-- A lookup certifies eta at the captured declaration before substitution. -/
theorem variable_staged_eta :
    StagedEtaCompute D kdepth 1 (capturedPi Q :: Q :: Γ) (.bvar 0) (variableExpansion Q) :=
  .eta (.bvar .zero)

omit [Params] in
/-- Typed substitution turns the recorded eta output into the captured target. -/
theorem variableExpansion_inst :
    (variableExpansion Q).inst (ident 0).lift = expanded Q := by
  simp [variableExpansion, expanded, inst, instVar, inst_lift]

/-- Ordinary typed substitution cannot preserve exact staged computation at
any stage. This is an obstruction to the certificate law, not strengthening. -/
theorem staged_exact_substitution_failure (heq : env.HasCanonicalEq)
    (hs : PureObservation.Definitions.Sound D env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hQ : env.HasType univs Γ Q (.sort u)) :
    OnCtx (capturedPi Q :: Q :: Γ) (env.IsType univs) ∧
    env.HasType univs (Q :: Γ) (ident 0).lift (capturedPi Q) ∧
    Ctx.InstN (Q :: Γ) (ident 0).lift (capturedPi Q) 0 (capturedPi Q :: Q :: Γ) (Q :: Γ) ∧
    StagedEtaCompute D kdepth 1 (capturedPi Q :: Q :: Γ) (.bvar 0) (variableExpansion Q) ∧
    ∀ stage, ¬ StagedEtaCompute D kdepth stage (Q :: Γ)
      ((.bvar 0 : VExpr).inst (ident 0).lift) ((variableExpansion Q).inst (ident 0).lift) := by
  have hΓQ : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, _, hQ⟩
  have hf : env.HasType univs (Q :: Γ) (ident 0).lift (capturedPi Q) := identity_at_captured_pi
  refine ⟨⟨hΓQ, hf.isType henv hΓQ⟩, hf, .zero, variable_staged_eta, ?_⟩
  intro stage
  simpa only [variableExpansion_inst, inst, instVar_zero, liftN_zero] using
    (captured_eta_not_staged (kdepth := kdepth) (stage := stage) heq hs hΓ hQ)

end Lean4Lean.VEnv.Strengthening.EtaScope
