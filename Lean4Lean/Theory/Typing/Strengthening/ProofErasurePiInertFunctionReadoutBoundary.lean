import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFunctionReadout

/-! # Function readout requires hidden carrier conversion

Even the completed stage-zero selector histories suffice to test proposed
function-body extraction. Shared application of those histories must reconstruct
unit checking at any semantically equal result type, whose conversion evidence
was absent from the source history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private selector_typing from Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureApplicationBoundary
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params] {D : Definitions}

/-- Shared application of completed histories would synthesize a full history
for two unit variables at any actually equal type. The source is already a
stage-zero history and contains no certificate for that type conversion. -/
theorem FinitePiInertSharedApplication.unit_conversion
    (Happ : FinitePiInertSharedApplication D)
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (HE : env.IsDefEq univs Γ T (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) :
    ∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ T)
      (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) := by
  let S := VExpr.const family ls
  let F := VExpr.forallE S S
  have hF : env.HasType univs Γ F (.sort (.imax (.succ u) (.succ u))) :=
    .forallE hS (hS.weak henv)
  have hid : env.HasType univs Γ (.lam S (.bvar 0)) F := .lam hS (.bvar .zero)
  have hfi : env.HasType univs Γ (.lam F (.app (.bvar 0) (.bvar (i+1))))
      (.forallE F T.lift) := by
    apply HasType.lam hF
    apply (HE.symm.weak henv).defeq
    apply HasType.app (show env.HasType univs (F :: Γ) (.bvar 0) F from .bvar .zero)
    simpa only [HasType, S, VExpr.lift, VExpr.liftN, liftVar_base'] using hiT.weak (B := F) henv
  have hgj : env.HasType univs Γ (.lam F (.app (.bvar 0) (.bvar (j+1))))
      (.forallE F T.lift) := by
    apply HasType.lam hF
    apply (HE.symm.weak henv).defeq
    apply HasType.app (show env.HasType univs (F :: Γ) (.bvar 0) F from .bvar .zero)
    simpa only [HasType, S, VExpr.lift, VExpr.liftN, liftVar_base'] using hjT.weak (B := F) henv
  have HF : PiInertCarrierHistory D 0 (proofEraseCtx Γ) (proofErase Γ (.forallE F T.lift))
      (proofErase Γ (.lam F (.app (.bvar 0) (.bvar (i+1)))))
      (proofErase Γ (.lam F (.app (.bvar 0) (.bvar (j+1))))) :=
    pi_inert_unit_selector_carrier_history heq hi hp hx hf hD hΓ hS hiT hjT
  obtain ⟨n, H⟩ := Happ hΓ hfi hgj hid HF
  simp only [VExpr.inst_lift] at H
  have RI := proofErase_beta_forward hΓ (HasType.app (selector_typing hΓ hS hiT).1 hid)
    (BetaRed.trans .beta .beta)
  have RJ := proofErase_beta_forward hΓ (HasType.app (selector_typing hΓ hS hjT).1 hid)
    (BetaRed.trans .beta .beta)
  have HR := H.endpoint_reducts (.beta RI) (.beta RJ)
  exact ⟨n, by simpa only [VExpr.liftN_zero, VExpr.inst, VExpr.instVar_upper, VExpr.instVar_zero] using HR⟩

/-- Distinct unit variables force actual structural exposure of the converted
type. Ordinary common comparison cannot supply this application result at any
Pi-inert stage. Thus universal shared application must recover hidden carrier
structure, not merely reuse the outer selector comparison. -/
theorem FinitePiInertSharedApplication.unit_conversion_exposure
    (Happ : FinitePiInertSharedApplication D)
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (HE : env.IsDefEq univs Γ T (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) (hne : i ≠ j) :
    ∃ n C, ScopedCompute (PiInertStage D n) (proofEraseCtx Γ) (proofErase Γ T) C ∧ CarrierExposure C := by
  obtain ⟨n, H⟩ := Happ.unit_conversion heq hi hp hx hf hD hΓ hS HE hiT hjT
  have HG := H.base .refl .refl .refl
  rw [show proofErase Γ (.bvar i) = .bvar i from if_neg (not_proof_at_positive_type hΓ hS hiT),
    show proofErase Γ (.bvar j) = .bvar j from if_neg (not_proof_at_positive_type hΓ hS hjT)] at HG
  rcases HG.checked_or_exposed with HC | ⟨C, R, HE, _⟩
  · exact (hne HC.pi_inert_bvar_injective).elim
  · exact ⟨n, C, R, HE⟩

/-- The proposed fresh-body extraction law has the same hidden-carrier burden
even when allowed an arbitrary finite stage. This is a proved consequence of
the missing law, not its proof or a strict-smallness claim. -/
theorem FinitePiInertFunctionBodyReadout.unit_conversion
    (H : FinitePiInertFunctionBodyReadout D)
    (heq : env.HasCanonicalEq)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hS : env.HasType univs Γ (.const family ls) (.sort (.succ u)))
    (HE : env.IsDefEq univs Γ T (.const family ls) (.sort (.succ u)))
    (hiT : env.HasType univs Γ (.bvar i) (.const family ls))
    (hjT : env.HasType univs Γ (.bvar j) (.const family ls)) :
    ∃ n, PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ T)
      (proofErase Γ (.bvar i)) (proofErase Γ (.bvar j)) :=
  FinitePiInertSharedApplication.unit_conversion
    (FinitePiInertFunctionBodyReadout.shared_application H) heq hi hp hx hf hD hΓ hS HE hiT hjT

end Lean4Lean.VEnv.Strengthening
