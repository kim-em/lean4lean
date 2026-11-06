import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaCarrier

/-! # Lambda congruence at the assigned dependent function carrier

Extensional testing of two typed lambdas beta-contracts to their bodies, even
when their written domains differ from the assigned domain. Retained body
histories thus construct the lambda case at the same stage. This is a concrete
strong-induction case, not a claim of general carrier composition or conversion.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Testing a typed lambda at the assigned domain's fresh argument returns its
body by ordinary beta. Written and assigned domains need not be identical. -/
theorem PiInertEvidence.lambda_test
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) :
    PiInertEvidence D stage .compute (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (.app (VExpr.lam C b).lift (.bvar 0))) (proofErase (A :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have ht : env.HasType univs (A :: Γ) (.app (VExpr.lam C b).lift (.bvar 0)) B := by
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar, VExpr.inst] using
      HasType.app (hf.weak henv) (.bvar .zero)
  have RB : VExpr.BetaRed (.app (VExpr.lam C b).lift (.bvar 0)) b := by
    change VExpr.BetaRed (.app (.lam C.lift (b.liftN 1 1)) (.bvar 0)) b
    simpa only [VExpr.inst_liftN_bvar] using
      (VExpr.BetaRed.beta (A := C.lift) (b := b.liftN 1 1) (a := .bvar 0))
  exact PiInertEvidence.core hs hc hΓA ht (.beta (proofErase_beta_forward hΓA ht RB))

/-- Two actual lambdas assigned one Pi inherit the body's full carrier history.
Both written domains may differ from the assigned domain and from each other.
All carrier/endpoint core residuals and future typed substitutions are retained;
no native domain recovery or same-domain annotation restriction is imposed. -/
theorem pi_inert_lambda_carrier_history
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B))
    (hg : env.HasType univs Γ (.lam E c) (.forallE A B))
    (H : PiInertCarrierHistory D stage (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) c)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.forallE A B))
      (proofErase Γ (.lam C b)) (proofErase Γ (.lam E c)) := by
  by_cases hp : IsProof Γ (.lam C b)
  · have hq := isProof_of_common_type hΓ hf hg hp
    have HC : PiInertEvidence D stage (.compare true) (proofEraseCtx Γ)
        (proofErase Γ (.lam C b)) (proofErase Γ (.lam C b)) :=
      (PiInertEvidence.core hs hc hΓ hf .refl).join hc (PiInertEvidence.core hs hc hΓ hf .refl)
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hq]
    rw [proofErase_eq_proof.2 hp] at HC
    exact HC.carrier_history
  have hq : ¬ IsProof Γ (.lam E c) := fun hq => hp (isProof_of_common_type hΓ hg hf hq)
  have HB := PiInertCarrierHistory.prefixes
    (PiInertEvidence.lambda_test hs hc hΓ hA hf) (PiInertEvidence.lambda_test hs hc hΓ hA hg) H
  rw [proofEraseCtx, proofErase_eta_body hΓ hA hf hp, proofErase_eta_body hΓ hA hg hq] at HB
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)]
  exact HB.function hs (DomainSort.of_typed hΓ hA)

end Lean4Lean.VEnv.Strengthening
