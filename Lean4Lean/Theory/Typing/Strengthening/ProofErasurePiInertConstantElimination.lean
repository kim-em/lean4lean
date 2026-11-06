import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWrapperElimination
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCertificateDescent

/-! # Removing computed constant wrappers

Under a well-formed unused binder, every body computation has an exact lower
certificate. Reapplying that descent after each annotation change preserves
the lifted-body invariant without a context-conversion or instantiation premise.
The lower path keeps the Pi-inert outer skeleton and its original finite bound.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- A lambda with an initially unused binder retains an exactly lifted body.
Both actual annotations and payloads are reified at their original types;
the lower payload computation retains the unchanged Pi-inert stage.
No transport of a body path across different raw binder contexts is needed. -/
theorem pi_inert_constant_lambda_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T) (hΔ : proofEraseCtx Γ = Δ)
    (R : ScopedCompute (PiInertStage D n) Δ
      (.lam (proofErase Γ A) ((proofErase Γ e).liftN 1)) out) :
    ∃ A' e', env.IsDefEq univs Γ A A' (.sort u) ∧ env.IsDefEq univs Γ e e' T ∧
      out = .lam (proofErase Γ A') ((proofErase Γ e').liftN 1) ∧
      ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
        (proofErase Γ e) (proofErase Γ e') := by
  generalize E : ProofShape.lam (proofErase Γ A) ((proofErase Γ e).liftN 1) = source at R
  induction R using ScopedCompute.rootBeta_induction generalizing Γ A e u T with
  | refl => exact ⟨A, e, hA, ht, E.symm, .refl⟩
  | base H => exact (pi_inert_stage_no_lam (E ▸ H)).elim
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A', e', HA, HE, EO, RE⟩ := ih₁ hΓ hA ht hΔ E
    obtain ⟨A'', e'', HA', HE', EO', RE'⟩ :=
      ih₂ hΓ HA.hasType.2 HE.hasType.2 hΔ EO.symm
    exact ⟨A'', e'', HA.trans HA', HE.trans HE', EO', RE.trans RE'⟩
  | lam RA RB =>
    cases E
    obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hA hΔ rfl
      (RA.mono pi_inert_stage_embed)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have EΓ : proofEraseCtx (A :: Γ) = _ := congrArg (List.cons (proofErase Γ A)) hΔ
    obtain ⟨e', HE, RE, EE⟩ := proofErase_scoped_compute_certificate_descend
      (pi_inert_stage_certificate_descent heq hs n)
      hΓ hΓA Ctx.LiftN.one ht EΓ RB
    refine ⟨A', e', HA, HE, ?_, RE⟩
    rw [EA, EE]
  | beta | app | proj | forallE => cases E

/-- If a computation consumes a constant wrapper, its original payload has
a Pi-inert path to the exact output at the same bound. The annotation can
be any actual type, and the raw argument need not have a typing certificate. -/
theorem pi_inert_constant_wrapper_eliminate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (hout : ∀ A' b' x', out ≠ .app (.lam A' b') x')
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (.app (.lam (proofErase Γ A) ((proofErase Γ e).liftN 1)) x) out) :
    ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (proofErase Γ e) out := by
  rcases R.pi_inert_lambda_app_or_beta with
    ⟨A', b', x', EO, _, _⟩ | ⟨A', b', x', RF, _, RT⟩
  · exact (hout A' b' x' EO).elim
  · obtain ⟨A'', e', _, _, EL, RE⟩ := pi_inert_constant_lambda_readout heq hs hΓ hA ht rfl RF
    cases EL
    apply RE.trans
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id] using RT

/-- Constant expansion at a proper prefix can likewise be removed with
all pending arguments preserved. Computation of the discarded first argument
requires neither typing nor native recovery; every other argument keeps its
original Pi-inert path. The result stays in the same restricted stage. -/
theorem pi_inert_constant_spine_eliminate
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (ht : env.HasType univs Γ e T)
    (hout : ∀ A' b' args', out ≠ ProofShape.mkApps (.lam A' b') args')
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (ProofShape.mkApps (.app (.lam (proofErase Γ A) ((proofErase Γ e).liftN 1)) x) args) out) :
    ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (ProofShape.mkApps (proofErase Γ e) args) out := by
  change ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
    (ProofShape.mkApps (.lam (proofErase Γ A) ((proofErase Γ e).liftN 1)) (x :: args)) out at R
  rcases R.pi_inert_lambda_spine_or_beta with
    ⟨A', b', args', EO, _, _⟩ | ⟨A', b', x', xs', RF, RX, RT⟩
  · exact (hout A' b' args' EO).elim
  · obtain ⟨A'', e', _, _, EL, RE⟩ := pi_inert_constant_lambda_readout heq hs hΓ hA ht rfl RF
    cases EL
    cases RX with
    | cons _ RX =>
      apply (RE.mkApps RX).trans
      simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id] using RT

end Lean4Lean.VEnv.Strengthening
