import Lean4Lean.Theory.Typing.Strengthening.RecursiveDataTyping
import Lean4Lean.Theory.Typing.Strengthening.RecursiveTypeInhabitants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureSingletonStages

/-! # Carrier-aware comparison of fixed-data recursive loops

Returning an empty structure makes the loop's function result structurally
subsingleton. Such outputs compare without any relation between their recursive
domain annotations. A rigid data result also blocks the literal proposition
formation used in the earlier Curry construction; this is not a consistency
proof or a proof of the proposition front for the new environment.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private not_proof_at_positive_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]
namespace RecursiveData

/-- A function returning a registered empty structure has a substitution-stable
subsingleton carrier certificate, regardless of its proposition domain. -/
theorem result_subsingleton
    (hd : env.constants d = some ⟨0, .sort (.succ .zero)⟩)
    (hi : env.projections d info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero)) :
    ProofShape.SubsingletonCarrier (proofErase Γ (result d P)) := by
  have hT := result_typed hd hP
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  rw [show proofErase Γ (result d P) =
    .forallE (proofErase Γ P) (proofErase (P :: Γ) (.const d [])) from
    if_neg (not_isProof_of_sort hΓ hT),
    show proofErase (P :: Γ) (.const d []) = .const d [] from
      if_neg (not_isProof_of_sort hΓP (data_typed hd univs (P :: Γ)))]
  exact .forallE (.unit hi hx hf (ps := []) hp.symm)

/-- Fixed-data self-application outputs retain their syntax under proof erasure.
The positive result sort, rather than a universe-valued codomain, proves this. -/
theorem loop_not_proof
    (hd : env.constants d = some ⟨0, .sort (.succ .zero)⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (Hrec : env.IsDefEq univs Γ D (.forallE D (result d P).lift) (.sort u)) :
    ¬ IsProof Γ (RecursiveDomain.omegaTerm D) :=
  not_proof_at_positive_type hΓ (result_typed hd hP) (RecursiveType.inhabit_result Hrec)

/-- Two recursive loops returning the same empty-structure function type have a
carrier certificate without any assumed equality of their domain annotations.
This bypasses annotation readout for these outputs; it asserts no inequivalence
of the annotations and no general paired-substitution theorem. -/
theorem loop_carrier_compare
    (hd : env.constants d = some ⟨0, .sort (.succ .zero)⟩)
    (hi : env.projections d info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (Hrec : env.IsDefEq univs Γ D (.forallE D (result d P).lift) (.sort u))
    (Hrec' : env.IsDefEq univs Γ D' (.forallE D' (result d P).lift) (.sort u')) :
    env.IsDefEq univs Γ (RecursiveDomain.omegaTerm D) (RecursiveDomain.omegaTerm D') (result d P) ∧
      ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ (result d P))
        (proofErase Γ (RecursiveDomain.omegaTerm D)) (proofErase Γ (RecursiveDomain.omegaTerm D')) := by
  have HS := result_subsingleton hd hi hp hx hf hΓ hP
  refine ⟨?_, .subsingleton HS⟩
  apply proofErase_subsingleton_carrier_descend hΓ
    (RecursiveType.inhabit_result Hrec) (RecursiveType.inhabit_result Hrec')
    (n := 0) (k := 0)
  simpa only [ProofShape.liftN_zero] using HS

/-- A Pi expression cannot be assigned a rigid data carrier. In particular the
proposition-producing body of the earlier Curry diagonal cannot inhabit a
registered fixed data result. Other possible collapse arguments remain open. -/
theorem no_pi_at_data
    (hi : env.projections d info) (hd : env.constants d = some ⟨0, .sort (.succ .zero)⟩)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ env.HasType univs Γ (.forallE A B) (.const d []) := by
  intro H
  obtain ⟨⟨u, hA⟩, ⟨v, hB⟩⟩ := HasType.forallE_inv henv.ordered H
  have Htype := H.uniqU henv hΓ (HasType.forallE hA hB)
  have HC := Htype.typeChain henv hΓ (data_typed hd univs Γ)
  exact henv.headInversion.sort_rigid (args := []) (ls := []) hΓ (henv.projectionRigid hi) HC.symm

end RecursiveData
end Lean4Lean.VEnv.Strengthening
