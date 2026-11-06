import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertArgumentCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCompositionBoundary

/-! # Joined argument histories do not cover arbitrary argument equality

Identity-body observation turns a joined pair into ordinary Pi-inert comparison.
Distinct variables of an empty structure refute that conclusion at every stage,
despite having a strong equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params] {D : Definitions}

/-- Observation through the typed identity body turns joined argument histories
into ordinary common comparison. This is stronger than carrier equality, so
joined histories cannot be inferred from an arbitrary carrier certificate. -/
theorem ArgumentHistory.joined_comparison
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hcore : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (RX : ArgumentHistory D n Γ A (proofErase Γ x) shared)
    (RY : ArgumentHistory D n Γ A (proofErase Γ y) shared) :
    PiInertEvidence D n (.compare true) (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ y) := by
  have IX := RX.interpret heq hs hl hcon hcore hreg hoff hD
  have IY := RY.interpret heq hs hl hcon hcore hreg hoff hD
  have hv : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have LX := (IX.2 hv).pi_inert_evidence heq hs hl hcon hcore hreg hoff hD
  have LY := (IY.2 hv).pi_inert_evidence heq hs hl hcon hcore hreg hoff hD
  rw [← proofErase_instN hΓA hx Ctx.InstN.zero hv] at LX
  rw [← proofErase_instN hΓA hy Ctx.InstN.zero hv] at LY
  simpa only [VExpr.inst, VExpr.instVar_zero] using LX.join hcore LY

/-- Distinct positive empty-structure variables are strongly equal but admit
no joined argument histories at any finite stage or shared output. This blocks
completion of the application case by strengthening its argument premise to
the existing computation-history grammar; it does not refute strengthening. -/
theorem pi_inert_unit_argument_history_failure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hcore : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hindices : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    env.IsDefEqStrong univs Γ (.bvar i) (.bvar j) (.const family ls) ∧
      ∀ n shared, ¬ (ArgumentHistory D n Γ (.const family ls) (proofErase Γ (.bvar i)) shared ∧
        ArgumentHistory D n Γ (.const family ls) (proofErase Γ (.bvar j)) shared) := by
  refine ⟨(IsDefEq.unitLike hi (params := []) hp.symm hindices hf hiT hjT).strong
    henv.orderedStrong hΓ, ?_⟩
  intro n shared ⟨RX, RY⟩
  have H := RX.joined_comparison heq hs hl hcon hcore hreg hoff hD hΓ hS hiT hjT RY
  have HC := H.base .refl .refl
  rw [show proofErase Γ (.bvar i) = .bvar i from if_neg (not_proof_at_positive_type hΓ hS hiT),
    show proofErase Γ (.bvar j) = .bvar j from if_neg (not_proof_at_positive_type hΓ hS hjT)] at HC
  exact hne HC.pi_inert_bvar_injective

end Lean4Lean.VEnv.Strengthening
