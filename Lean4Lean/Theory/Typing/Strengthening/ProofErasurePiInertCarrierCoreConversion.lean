import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaCarrier

/-! # Whole carrier histories convert across ordinary-core joins

The residual quantifier in a carrier history supports forward carrier reduction.
Combining that fact with the existing backward prefix rule yields conversion
at arbitrary carriers with an ordinary-core common reduct. Guarded paths are
not silently substituted for ordinary-core paths in that residual quantifier.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Every core reduct of a carrier retains the complete history, including
future typed substitutions. The endpoint histories and finite stage are fixed. -/
theorem PiInertCarrierHistory.carrier_reduct
    (H : PiInertCarrierHistory D n Δ C a b) (R : Compute (ErasedLevelCore D) C E) :
    PiInertCarrierHistory D n Δ E a b := by
  refine ⟨fun RE RA RB => H.base (R.trans RE) RA RB, ?_⟩
  intro Δ' τ W E' a' b' RE RA RB
  exact H.future W ((R.subst (fun R => erased_level_core_subst R)).trans RE) RA RB

/-- A target carrier that computes to a core reduct of the old carrier inherits
the whole history. Only the old-to-shared path must be ordinary core; the target
path may use retained guarded Eq computation and other certified prefixes. -/
theorem PiInertCarrierHistory.carrier_join
    (H : PiInertCarrierHistory D n Δ C a b)
    (RC : Compute (ErasedLevelCore D) C shared)
    (RE : PiInertEvidence D n .compute Δ E shared) :
    PiInertCarrierHistory D n Δ E a b :=
  PiInertCarrierHistory.carrier_prefix RE (H.carrier_reduct RC)

/-- Two actual types with an ordinary-core common reduct admit whole-history
conversion at the same stage. The common reduct may be raw syntax, with no
chosen representative or native recovery certificate. Endpoint shapes are
arbitrary and all three residual quantifiers survive. -/
theorem PiInertCarrierHistory.core_convert
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hE : env.HasType univs Γ E (.sort u))
    (H : PiInertCarrierHistory D n (proofEraseCtx Γ) C a b)
    (RC : Compute (ErasedLevelCore D) C shared)
    (RE : Compute (ErasedLevelCore D) (proofErase Γ E) shared) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ E) a b :=
  H.carrier_join RC (PiInertEvidence.core hs hc hΓ hE RE)

/-- Ordinary-core joins give an exact equivalence of the full history predicates
at the two typed carriers. This consumes arbitrary completed histories, rather
than reconstructing only a displayed function or structure constructor case. -/
theorem pi_inert_carrier_history_core_join_iff
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs Γ E (.sort v))
    (RC : Compute (ErasedLevelCore D) (proofErase Γ C) shared)
    (RE : Compute (ErasedLevelCore D) (proofErase Γ E) shared) :
    PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ C) a b ↔
      PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ E) a b :=
  ⟨fun H => H.core_convert hs hc hΓ hE RC RE, fun H => H.core_convert hs hc hΓ hC RE RC⟩

omit [Params] in
/-- Actual environments discharge the core soundness and confluence assumptions.
No canonical-Eq assumption is needed for this ordinary-core conversion rule. -/
theorem EnvironmentCore.carrier_history_core_join_iff {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n Γ C E u v a b shared}, OnCtx Γ (env.IsType U) →
      env.HasType U Γ C (.sort u) → env.HasType U Γ E (.sort v) →
      Compute (ErasedLevelCore definitions) (proofErase Γ C) shared →
      Compute (ErasedLevelCore definitions) (proofErase Γ E) shared →
      (PiInertCarrierHistory definitions n (proofEraseCtx Γ) (proofErase Γ C) a b ↔
        PiInertCarrierHistory definitions n (proofEraseCtx Γ) (proofErase Γ E) a b) := by
  letI := henv.params U
  intro n Γ C E u v a b shared hΓ hC hE RC RE
  exact pi_inert_carrier_history_core_join_iff sound (typed_level_core_confluence (fun H => H))
    hΓ hC hE RC RE

end Lean4Lean.VEnv.Strengthening
