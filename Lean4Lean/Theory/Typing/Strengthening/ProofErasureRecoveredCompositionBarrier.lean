import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveredThinning
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedCompositionBarrier

/-! # The typed composition boundary survives contextual eta recovery

Recovered eta enlarges the usable endpoint certificates. It does not remove the
constant-body probe obstruction: typed forward beta transport into this stronger
relation still implies the entire proposition front, even with any finite output
stage. The domain extraction is independent of the two type oracles.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private ProofShape.EtaHead.not_probe
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureProbe
variable [Params]

/-- Contextual recovered eta cannot hide the domain comparison of constant-body
lambda probes. Such bodies exclude both head-eta constructors. -/
theorem ProofShape.RecoveredCompare.probe_inv
    (hroot : ∀ {a b}, Step a b → ProofShape.ComputationalRoot a)
    (H : ProofShape.RecoveredCompare Step σ τ mode (.lam A (.sort u)) (.lam B (.sort v))) :
    ProofShape.RecoveredCompare Step σ τ false A B := by
  generalize Ea : ProofShape.lam A (.sort u) = a at H
  generalize Eb : ProofShape.lam B (.sort v) = b at H
  induction H generalizing A B with
  | base H => cases Ea; cases Eb; exact .base (H.probe_inv hroot)
  | lam HA HB => cases Ea; cases Eb; exact HA
  | etaL HR HD HE => cases Ea; exact (ProofShape.EtaHead.not_probe HE).elim
  | etaR HR HD HE => cases Eb; exact (ProofShape.EtaHead.not_probe HE).elim
  | compute Ra Rb HC ih =>
    cases Ea; cases Eb
    obtain ⟨A', EA, HA⟩ := Ra.probe_inv hroot
    obtain ⟨B', EB, HB⟩ := Rb.probe_inv hroot
    exact .compute HA HB (ih EA.symm EB.symm)
  | app | proj | forallE => cases Ea

/-- Missing typed forward beta transport into recovered comparison, with a
stage-zero contextual input and any finite output stage. The theorem below
shows this is at least as strong as PropositionFront, not a smaller obligation. -/
def TypedRecoveredBetaTransport (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ a b c T}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a T → env.HasType univs Γ b T → env.HasType univs Γ c T →
    ErasedRecoveredComparison D 0 true Γ a b →
    ProofShape.BetaRed (proofErase Γ b) (proofErase Γ c) →
    ∃ stage, ErasedRecoveredComparison D stage true Γ a c

/-- Missing common-typed composition for the contextual certificate. Even
arbitrary finite output stages retain the full proposition-front obligation. -/
def TypedRecoveredComposition (D : PureObservation.Definitions) : Prop :=
  ∀ {Γ a b c T i j}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a T → env.HasType univs Γ b T → env.HasType univs Γ c T →
    ErasedRecoveredComparison D i true Γ a b →
    ErasedRecoveredComparison D j true Γ b c →
    ∃ stage, ErasedRecoveredComparison D stage true Γ a c

/-- Typed contextual composition includes forward beta transport. -/
theorem TypedRecoveredComposition.betaTransport (H : TypedRecoveredComposition D) :
    TypedRecoveredBetaTransport D := by
  intro Γ a b c T hΓ ha hb hc HC HB
  exact H hΓ ha hb hc HC (j := 0) (.base (.compute (.beta HB) .refl .refl))

/-- Transport of commonly typed probes would cover every sort-typed domain
conversion by an inferred contextual certificate at some finite stage. -/
theorem TypedRecoveredBetaTransport.sort_coverage (H : TypedRecoveredBetaTransport D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    ∃ stage, ErasedRecoveredComparison D stage false Γ P Q := by
  obtain ⟨mid, T, hf, hm, hg, HC, HB⟩ :=
    domainProbe_typed_eta_beta (Step := ErasedComparedKStage D 0) hΓ hP hQ HPQ
  obtain ⟨stage, HE⟩ := H hΓ hf hm hg (.base HC) HB
  unfold ErasedRecoveredComparison at HE ⊢
  rw [proofErase_domainProbe hΓ hP, proofErase_domainProbe hΓ hQ] at HE
  exact ⟨stage, HE.probe_inv (erased_compared_K_stage_root stage)⟩

/-- The recovered-eta enlargement does not reduce the typed beta-transport
obligation: canonical contextual descent would turn it into PropositionFront. -/
theorem typedRecoveredBetaTransport_implies_propositionFront (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (H : TypedRecoveredBetaTransport D) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hR' : env.HasType univs (Q :: Γ) R.lift (.sort .zero) := hR.weak henv
  obtain ⟨stage, HC⟩ := H.sort_coverage hΓ' hP' hR' (HE.of_l henv hΓ' hP')
  have HC' : ErasedRecoveredComparison D stage false (Q :: Γ)
      (P.lift' (.skip .refl)) (R.lift' (.skip .refl)) := by
    simpa only [← lift_eq_lift'] using HC
  exact (HC'.descend heq hs hΓ hΓ' (.skip .refl) hP hR).2
    rfl (not_isProof_of_sort hΓ hP)

/-- Common-typed contextual composition also retains the whole front. -/
theorem typedRecoveredComposition_implies_propositionFront (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (H : TypedRecoveredComposition D) : PropositionFront :=
  typedRecoveredBetaTransport_implies_propositionFront heq hs H.betaTransport

end Lean4Lean.VEnv.Strengthening
