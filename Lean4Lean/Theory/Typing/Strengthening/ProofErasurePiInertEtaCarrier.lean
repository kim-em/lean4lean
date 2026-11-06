import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFunctionHistory

/-! # Arbitrary typed function eta has a full carrier history

At the assigned Pi carrier, extensional testing beta-contracts eta before any
comparison of the function's written lambda domain is needed. This includes
neutral and converted functions. It gives carrier evidence, not an unlicensed
promotion to ordinary comparison at an arbitrary non-sort carrier.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- An actual typed core path constructs the interpreted computation evidence.
Only ordinary core confluence is used, at the original typed source. -/
theorem PiInertInterpret.core
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : Compute (ErasedLevelCore D) (proofErase Γ e) out) :
    PiInertInterpret D stage .compute (proofEraseCtx Γ) (proofErase Γ e) out := by
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ht rfl rfl (R.scoped (fun R => .base R))
  refine ⟨⟨Γ, e', T, hΓ, rfl, HE.hasType.2, EE⟩, ?_⟩
  intro a' RA
  obtain ⟨shared, RL, RR⟩ := hc hΓ ht RA R
  exact ⟨shared, RL.in_pi_inert_stage, RR⟩

/-- Ordinary core paths retain every future typed substitution. This seed
requires no Eq-registry assumptions beyond the explicitly supplied core laws. -/
theorem PiInertEvidence.core
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : Compute (ErasedLevelCore D) (proofErase Γ e) out) :
    PiInertEvidence D stage .compute (proofEraseCtx Γ) (proofErase Γ e) out := by
  refine ⟨PiInertInterpret.core hs hc hΓ ht R, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have R' := R.subst (fun R => erased_level_core_subst R) (σ := τ)
  rw [← proofErase_subst_with hΓ₀ WS ht ES] at R' ⊢
  rw [← EΓ₀]
  exact PiInertInterpret.core hs hc hΓ₀ (ht.subst henv.orderedStrong WS hΓ₀) R'

/-- Every typed eta pair has a full carrier history at its assigned Pi, already
at any requested stage including zero. The function can be neutral, converted,
or proof-valued. No native recovery, domain-comparison child, common-mode eta
transport, or global strong-derivation coverage is assumed. -/
theorem pi_inert_eta_carrier_history
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.forallE A B))
      (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) (proofErase Γ f) := by
  have hη := (IsDefEq.eta hf).hasType.1
  have HC : PiInertEvidence D stage (.compare true) (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ f) :=
    (PiInertEvidence.core hs hc hΓ hf .refl).join hc (PiInertEvidence.core hs hc hΓ hf .refl)
  by_cases hp : IsProof Γ f
  · have hηp := (isProof_congr hΓ (IsDefEq.eta hf)).2 hp
    rw [proofErase_eq_proof.2 hηp, proofErase_eq_proof.2 hp]
    rw [proofErase_eq_proof.2 hp] at HC
    exact HC.carrier_history
  have hηn : ¬ IsProof Γ (.lam A (.app f.lift (.bvar 0))) := mt (isProof_congr hΓ (IsDefEq.eta hf)).1 hp
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have test {g} (hg : env.HasType univs Γ g (.forallE A B)) :
      env.HasType univs (A :: Γ) (.app g.lift (.bvar 0)) B := by
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar, VExpr.inst] using
      HasType.app (hg.weak henv) (.bvar .zero)
  have RB : VExpr.BetaRed (.app (VExpr.lam A (.app f.lift (.bvar 0))).lift (.bvar 0))
      (.app f.lift (.bvar 0)) := by
    change VExpr.BetaRed (.app (.lam A.lift ((VExpr.app f.lift (.bvar 0)).liftN 1 1)) (.bvar 0)) _
    simpa only [VExpr.inst_liftN_bvar] using
      (VExpr.BetaRed.beta (A := A.lift) (b := (VExpr.app f.lift (.bvar 0)).liftN 1 1) (a := .bvar 0))
  have HB : PiInertEvidence D stage (.compare true) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) (.app (VExpr.lam A (.app f.lift (.bvar 0))).lift (.bvar 0)))
      (proofErase (A :: Γ) (.app f.lift (.bvar 0))) :=
    (PiInertEvidence.core hs hc hΓA (test hη) (.beta (proofErase_beta_forward hΓA (test hη) RB))).join hc
      (PiInertEvidence.core hs hc hΓA (test hf) .refl)
  have HB' := HB.carrier_history (C := proofErase (A :: Γ) B)
  rw [proofEraseCtx, proofErase_eta_body hΓ hA hη hηn, proofErase_eta_body hΓ hA hf hp] at HB'
  obtain ⟨v, hPi⟩ := hf.isType henv hΓ
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi)]
  exact HB'.function hs (DomainSort.of_typed hΓ hA)

omit [Params] in
/-- The complete eta carrier-history case for the actual environment core.
The function's typing supplies its domain sort; neutral and converted functions
need no separate certificate. -/
theorem EnvironmentCore.eta_carrier_history {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ f A B stage}, OnCtx Γ (env.IsType U) → env.HasType U Γ f (.forallE A B) →
      PiInertCarrierHistory definitions stage (proofEraseCtx Γ) (proofErase Γ (.forallE A B))
        (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) (proofErase Γ f) := by
  letI := henv.params U
  intro Γ f A B stage hΓ hf
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
  exact pi_inert_eta_carrier_history sound (typed_level_core_confluence (fun H => H)) hΓ hA hf

end Lean4Lean.VEnv.Strengthening
