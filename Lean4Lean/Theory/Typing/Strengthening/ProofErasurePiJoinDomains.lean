import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFamilyCast

/-! # Domain evidence extracted from joins of whole Pi computations

The shared output may contain arbitrary typed control wrappers. Beta confluence
aligns its two Pi readouts, retaining domain paths in the original context.
Core-stable computation certificates then supply this evidence at every pair
of domain residuals. This handles the join constructor, not arbitrary comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
variable [Params] {D : Definitions}

omit [Params] in
/-- Two readings of one output give a domain join without requiring either
selected Pi, or either component, to be normal. Codomain scopes may differ. -/
theorem ProofShape.PiReadout.domain_join
    (HA : PiReadout Step Δ A B out) (HC : PiReadout Step Δ C E out) :
    ∃ shared, ScopedCompute Step Δ A shared ∧ ScopedCompute Step Δ C shared := by
  obtain ⟨X, Y, RA, _, RX⟩ := HA
  obtain ⟨Z, W, RC, _, RZ⟩ := HC
  obtain ⟨joined, RJX, RJZ⟩ := RX.raw_confluent RZ
  obtain ⟨K, L, rfl, RK, _⟩ := beta_forallE_parts RJX
  obtain ⟨K', L', EQ, RK', _⟩ := beta_forallE_parts RJZ
  cases EQ
  exact ⟨K, RA.trans (.beta RK), RC.trans (.beta RK')⟩

/-- Whole Pi computations to a common, possibly wrapped output retain a
common computation of the original domains across all finite guard stages. -/
theorem static_structure_pi_join_domains
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort w)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ C) (proofErase (C :: Γ) E)) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ C) shared :=
  (proofErase_static_structure_union_pi_readout heq hs hΓ hA hB RA).domain_join
    (proofErase_static_structure_union_pi_readout heq hs hΓ hC hE RC)

/-- A domain core path is a whole Pi core path with unchanged raw codomain.
Its actual codomain typing transports to the evolved domain; erasure agrees. -/
theorem proofErase_core_pi_domain_residual (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (RA : Compute (ErasedLevelCore D) (proofErase Γ A) X) :
    ∃ A', env.HasType univs Γ A' (.sort u) ∧
      env.HasType univs (A' :: Γ) B (.sort v) ∧ proofErase Γ A' = X ∧
      Compute (ErasedLevelCore D) (proofErase Γ (.forallE A B))
        (proofErase Γ (.forallE A' B)) := by
  obtain ⟨A', HA, EA⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hA rfl rfl (RA.scoped (fun H => .base H))
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (A' :: Γ) := .succ .zero HA
  have hB' := hB.defeqDFC henv HC
  have EB := proofErase_defeqCtx (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, u, hA⟩) HC hB
  refine ⟨A', HA.hasType.2, hB', EA, ?_⟩
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB)),
    show proofErase Γ (.forallE A' B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (HasType.forallE HA.hasType.2 hB')), EA, ← EB]
  exact .forallE RA .refl

/-- Joining computation certificates for whole Pi types supplies a domain
join after every pair of independent core paths. Each resulting union path
has a finite stage; no uniform stage bound or general comparison extraction is
assumed. The certificates may contain casts and sequential computations. -/
theorem CoreFamilyCast.pi_join_domain_residuals
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort w)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (HA : CoreFamilyCast D stage .compute (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) out)
    (HC : CoreFamilyCast D stage .compute (proofEraseCtx Γ) (proofErase Γ (.forallE C E)) out)
    (RA : Compute (ErasedLevelCore D) (proofErase Γ A) X)
    (RC : Compute (ErasedLevelCore D) (proofErase Γ C) Y) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) X shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) Y shared := by
  obtain ⟨A', hA', hB', EA, RPiA⟩ := proofErase_core_pi_domain_residual hs hΓ hA hB RA
  obtain ⟨C', hC', hE', EC, RPiC⟩ := proofErase_core_pi_domain_residual hs hΓ hC hE RC
  have IA := HA.interpret heq hs hl hcon hc hreg hoff hD
  have IC := HC.interpret heq hs hl hcon hc hreg hoff hD
  obtain ⟨left, RL, CL⟩ := IA.2 RPiA
  obtain ⟨right, RR, CR⟩ := IC.2 RPiC
  obtain ⟨Γ₀, e, T, hΓ₀, _, ht, EE⟩ := IA.1
  obtain ⟨joined, JL, JR⟩ := hc hΓ₀ ht (EE ▸ CL) (EE ▸ CR)
  have RL := RL.trans JL.in_static_stage
  have RR := RR.trans JR.in_static_stage
  rw [show proofErase Γ (.forallE A' B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA' hB'))] at RL
  rw [show proofErase Γ (.forallE C' E) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hC' hE'))] at RR
  simpa only [EA, EC] using static_structure_pi_join_domains heq hs hΓ hA' hB' hC' hE'
    (RL.mono (fun H => ⟨stage, H⟩)) (RR.mono (fun H => ⟨stage, H⟩))

end Lean4Lean.VEnv.Strengthening
