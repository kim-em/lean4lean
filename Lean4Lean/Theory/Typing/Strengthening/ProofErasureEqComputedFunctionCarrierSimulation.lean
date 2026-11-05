import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqFunctionCarrierSimulation

/-! # Computed function carriers at the typed Eq-prefix boundary

The carrier may first compute to a Pi. Typed replay supplies its actual source
realization, and an outer eta frame retains the original prefix annotation.
Function-body exposure is still an explicit premise, not a completeness claim.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- The function-body exposure result applies at the typed raw interface of
the stage induction. An ambient domain-sort witness is interpreted at the
actual domain recovered from the prefix, including its proof-erasure mode. -/
theorem first_stage_typed_eq_prefix_of_function_body_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.eqRecBeforeMajor v w (.forallE A B) a M m b))
    (SD : DomainSort Δ A u)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (A :: Δ) B C')
    (Ra : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (A :: Δ)
      (.app (a.liftN 1) (etaArgument u)) a')
    (Rb : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (A :: Δ)
      (.app (b.liftN 1) (etaArgument u)) b')
    (HG : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0) (A :: Δ) C' a' b') :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (ProofShape.eqRecBeforeMajor v w (.forallE A B) a M m b)
      (.lam (eqProofType w (.forallE A B) a b) (m.liftN 1)) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨Q, a₀, M₀, m₀, b₀, rfl, EQ, Ea, EM, Em, Eb⟩ := proofErase_eqRecBeforeMajor_inv Ee
  obtain ⟨A₀, B₀, rfl, _, EA, EB⟩ := erase_forallE_inv EQ
  obtain ⟨_, _, hQ, _, _, _, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  obtain ⟨⟨_, hA₀⟩, _, _⟩ := hQ.forallE_inv henv
  have SD' : DomainSort (proofEraseCtx Γ) ((proofErase Γ A₀).liftN 0 0) u := by
    simpa only [ProofShape.liftN_zero, EΓ, EA] using SD
  have hA := SD'.descend hΓ hΓ (Ctx.LiftN.zero []) hA₀
  have hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w (.forallE A₀ B₀) a₀ M₀ m₀ b₀) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at Ee
    cases Ee
  have H := first_stage_eq_prefix_of_function_body_exposure heq hs hΓ ht hn hA
    (by simpa only [EΓ, EA, EB] using RC)
    (by simpa only [EΓ, EA, Ea] using Ra)
    (by simpa only [EΓ, EA, Eb] using Rb)
    (by simpa only [EΓ, EA] using HG)
  simpa only [EΓ, Ee, EQ, Ea, Eb, Em] using H

/-- A typed raw canonical prefix can preserve its original proof-domain
annotation around any stage-one computation to a constant lambda. The minor
is fixed; the intermediate lambda annotation is arbitrary. -/
theorem first_stage_typed_eq_prefix_retains_annotation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.eqRecBeforeMajor v w α a M m b))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (ProofShape.eqRecBeforeMajor v w α a M m b) (.lam L (m.liftN 1))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (ProofShape.eqRecBeforeMajor v w α a M m b) (.lam (eqProofType w α a b) (m.liftN 1)) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Eα, Ea, EM, Em, Eb⟩ := proofErase_eqRecBeforeMajor_inv Ee
  have hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at Ee
    cases Ee
  obtain ⟨body, RN, SD⟩ := eq_prefix_literal_native_guard
    (Step := ErasedStaticStructureEtaExpansionStage D 0) heq hΓ ht hn
  have H := staged_eta_retains_constant_domain heq hs RN SD
    (by simpa only [EΓ, Ee] using R)
  simpa only [EΓ, Ee, Eα, Ea, Eb] using H

/-- A carrier computation exposing a Pi can precede the function-body case.
The whole prefix is replayed to supply its new typed realization; the original
prefix frame restores its old domain afterward. The carrier need not be a
literal Pi initially, and its endpoint functions need no native certificates. -/
theorem first_stage_typed_eq_prefix_of_computed_function_body_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.eqRecBeforeMajor v w α a M m b))
    (RQ : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ α (.forallE A B))
    (SD : DomainSort Δ A u)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (A :: Δ) B C')
    (Ra : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (A :: Δ)
      (.app (a.liftN 1) (etaArgument u)) a')
    (Rb : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (A :: Δ)
      (.app (b.liftN 1) (etaArgument u)) b')
    (HG : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0) (A :: Δ) C' a' b') :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (ProofShape.eqRecBeforeMajor v w α a M m b) (.lam (eqProofType w α a b) (m.liftN 1)) := by
  have RP : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (ProofShape.eqRecBeforeMajor v w α a M m b)
      (ProofShape.eqRecBeforeMajor v w (.forallE A B) a M m b) :=
    .app (.app (.app (.app (.app .refl RQ) .refl) .refl) .refl) .refl
  have HT' : TypedSource Δ (ProofShape.eqRecBeforeMajor v w (.forallE A B) a M m b) := by
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize
      (erased_static_structure_eta_expansion_stage_descent heq hs 1) hΓ ht EΓ Ee RP
    exact ⟨Γ, e', T, hΓ, EΓ, HE.hasType.2, EE⟩
  exact first_stage_typed_eq_prefix_retains_annotation heq hs HT
    (RP.trans (first_stage_typed_eq_prefix_of_function_body_exposure heq hs HT' SD RC Ra Rb HG))

end Lean4Lean.VEnv.Strengthening
