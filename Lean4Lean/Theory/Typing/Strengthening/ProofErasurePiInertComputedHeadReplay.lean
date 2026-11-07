import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertFreshFieldRetainedProgress

/-! # Restore the original typed head before a computed-function observation

A source-typed function computation gives an ordinary equality of its actual
representatives. Applying that equality backwards to a typed endpoint spine
recovers typing of the original head with exactly the same erased arguments.
The forward guarded computation stays in its original scope.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_spine_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertRetainedEtaContinuation
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Restore a computed head in the actual typed endpoint spine. The result
has the exact original erased head and argument vector and the SAME result
type as that endpoint. Only ordinary equality is reversed; the native guarded
computation remains directed and is never substituted. -/
theorem pi_inert_computed_head_spine_preimage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ f) (hf : f ≠ .proof)
    (RF : ScopedCompute (PiInertStage D n) Δ f short)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ)
    (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = ProofShape.mkApps short args) :
    ∃ original, env.IsDefEq univs Γ e original T ∧
      proofErase Γ original = ProofShape.mkApps f args := by
  obtain ⟨actual, actualArgs, rfl, Eactual, Eargs⟩ := erase_spine_inv Ee
  obtain ⟨Ω, g, S, hΩ, EΩ, hg, Eg⟩ := HT
  have W := proofEraseCtx_defeq hΩ hΓ (EΩ.trans EΓ.symm)
  have hg' := hg.defeqDFC henv W
  have Eg' : proofErase Γ g = f := (proofErase_defeqCtx hΩ W hg).symm.trans Eg
  obtain ⟨g', HG, Eg'out⟩ := proofErase_scoped_compute_realize
    (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
    hΓ hg' EΓ Eg' RF
  have hng : ¬ IsProof Γ g := fun hp => hf (Eg'.symm.trans (proofErase_eq_proof.2 hp))
  have hng' : ¬ IsProof Γ g' := fun hp => hng ((isProof_congr hΓ HG).2 hp)
  obtain ⟨S', hactual⟩ := VExpr.WF.of_mkApps henv hΓ ⟨_, ht⟩
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ HG.hasType.2 hactual
    (Eg'out.trans Eactual.symm)).2 hng'
  have HC := (HE.defeq hΓ).symm.trans henv hΓ HG.symm.toU
  have HH := (HC.mkApps_congr_left henv hΓ ⟨_, ht⟩).of_l henv hΓ ht
  have hshort : short ≠ .proof := fun E => hng' (proofErase_eq_proof.1 (Eg'out.trans E))
  have hp : ¬ IsProof Γ (VExpr.mkApps actual actualArgs) := by
    intro hp
    have E := Ee.symm.trans (proofErase_eq_proof.2 hp)
    cases args using List.snoc_induction with
    | nil => exact hshort E
    | snoc args a => rw [ProofShape.mkApps_snoc] at E; cases E
  have hp' := mt (isProof_congr hΓ HH).2 hp
  refine ⟨VExpr.mkApps g actualArgs, HH, ?_⟩
  rw [proofErase_mkApps hΓ HH.hasType.2 hp', Eg', Eargs]

/-- A typed application of the computed function therefore supplies typing
for the original function applied to the identical arguments, without any
native recovery certificate for those arguments. -/
theorem TypedSource.pi_inert_head_preimage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ f) (hf : f ≠ .proof)
    (RF : ScopedCompute (PiInertStage D n) Δ f short)
    (HNext : TypedSource Δ (ProofShape.mkApps short args)) :
    TypedSource Δ (ProofShape.mkApps f args) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HNext
  obtain ⟨original, HE, EO⟩ := pi_inert_computed_head_spine_preimage heq hs HT hf RF hΓ EΓ ht Ee
  exact ⟨Γ, original, T, hΓ, EΓ, HE.hasType.2, EO⟩

end Lean4Lean.VEnv.Strengthening
