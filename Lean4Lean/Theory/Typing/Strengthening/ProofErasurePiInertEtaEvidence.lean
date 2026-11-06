import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEvidence

/-! # Eta closure of interpreted evidence

A retained whole-Pi comparison supplies domain comparisons at the same stage.
The eta rule consumes these directly, including after future typed substitutions.
This constructs a derived induction case without requiring a new syntactic
CoreFamilyCast node or an arbitrary strong-derivation coverage assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Interpreted whole-Pi comparison supplies a converted lambda's eta readout
at the unchanged Pi-inert stage, uniformly over independent core residuals. -/
theorem PiInertInterpret.eta_readout
    (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (H : PiInertInterpret D stage (.compare comparisonMode) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E))) :
    EtaCoreReadout D (PiInertStage D stage) (proofEraseCtx Γ) u
      (proofErase Γ A) (proofErase Γ (.lam C b)) := by
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB)),
    show proofErase Γ (.forallE C E) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (HasType.forallE hC hE))] at H
  apply eta_core_readout_lambda_of_domains hs hΓ hA hC hf hn
  intro X Y RA RC
  exact (H (.forallE RA .refl) (.forallE RC .refl)).pi_domains_of_no_pi
    (fun R => pi_inert_stage_no_pi R)

/-- Every typed consumer of a converted lambda's eta pair has interpreted
comparison at the original whole-Pi stage, in either checking mode. -/
theorem PiInertInterpret.etaConsumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (H : PiInertInterpret D stage (.compare comparisonMode) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E))) :
    PiInertInterpret D stage (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A (.app (VExpr.lam C b).lift (.bvar 0)))))
      (proofErase Γ (t.inst (.lam C b))) := by
  intro left right RL RR
  exact (PiInertInterpret.eta_readout hs hΓ hA hB hC hE hf hn H).consumer hs hc
    (fun R => pi_inert_stage_core R) (pi_inert_stage_rename heq hs stage)
    hΓ hA hf ht RL RR

/-- The interpreted eta rule survives all future typed substitutions at the
same stage. Nonproof status of the substituted lambda follows from erasure
commutation; no arbitrary substitution closure of comparison is assumed. -/
theorem PiInertEvidence.etaConsumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (H : PiInertEvidence D stage (.compare comparisonMode) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E))) :
    PiInertEvidence D stage (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A (.app (VExpr.lam C b).lift (.bvar 0)))))
      (proofErase Γ (t.inst (.lam C b))) := by
  refine ⟨PiInertInterpret.etaConsumer heq hs hc hΓ hA hB hC hE hf hn ht H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have hA' := hA.subst henv.orderedStrong WS hΓ₀
  have hC' := hC.subst henv.orderedStrong WS hΓ₀
  have hB' := hB.subst henv.orderedStrong (WS.lift henv.ordered hA) ⟨hΓ₀, u, hA'⟩
  have hE' := hE.subst henv.orderedStrong (WS.lift henv.ordered hC) ⟨hΓ₀, u, hC'⟩
  have hPi := HasType.forallE hA hB
  have hPi' := hPi.subst henv.orderedStrong WS hΓ₀
  have ht' := ht.subst henv.orderedStrong (WS.lift henv.ordered hPi) ⟨hΓ₀, _, hPi'⟩
  have hf' := hf.subst henv.orderedStrong WS hΓ₀
  have EF := proofErase_subst_with hΓ₀ WS hf ES
  rw [show proofErase Γ (.lam C b) = .lam _ _ from if_neg hn] at EF
  have hn' : ¬ IsProof Γ₀ ((VExpr.lam C b).subst σ) := by
    intro HP
    rw [proofErase_eq_proof.2 HP] at EF
    cases EF
  have H' : PiInertInterpret D stage (.compare comparisonMode) Δ'
      ((proofErase Γ (.forallE A B)).subst τ) ((proofErase Γ (.forallE C E)).subst τ) := H.future W
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hPi ES,
    ← proofErase_subst_with hΓ₀ WS (HasType.forallE hC hE) ES] at H'
  have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  have hright := ht.instN henv Ctx.InstN.zero hf
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hleft ES,
    ← proofErase_subst_with hΓ₀ WS hright ES]
  simp only [VExpr.subst_inst, VExpr.subst, VExpr.lift_subst_lift]
  rw [show σ.lift 0 = .bvar 0 from rfl]
  intro left right RL RR
  exact PiInertInterpret.etaConsumer heq hs hc hΓ₀ hA' hB' hC' hE' hf' hn' ht' H' RL RR

end Lean4Lean.VEnv.Strengthening
