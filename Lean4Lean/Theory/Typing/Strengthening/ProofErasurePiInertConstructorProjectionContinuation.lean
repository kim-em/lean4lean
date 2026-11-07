import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstructorEtaBody
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertProjectionContinuation

/-! # Pair projection minima retain the observer through eta descent

The function-eta alternative now supplies a strictly smaller typed body minimum
whose continuation still ends at the original selected field output. Its
competitors can change body endpoints and majors, including finite stages.
This does not yet prove readout through the resulting frames.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A reachable pair and its actual constructor-prefix eta body, with a smaller
minimum including the final projection observer. The original two argument
origins and native type recovery are retained. Readout through arbitrary
application/retained frames, including nested structure eta, remains open. -/
def PairProjectionEtaMinimum (D : Definitions) (Γ : List VExpr)
    (family : Name) (info : VProjectionInfo) (source out : ProofShape) : Prop :=
  ∃ m field value pre pending A B u stage before cost smaller,
    env.HasType univs Γ m (.const family []) ∧
    (∃ reachStage, ScopedCompute (PiInertStage D reachStage) (proofEraseCtx Γ) source (proofErase Γ m)) ∧
    proofErase Γ m = ProofShape.mkApps (.const info.ctorName []) [field, value] ∧
    pre.length < 2 ∧ pending ≠ [] ∧ (∀ rest, pending ≠ .proof :: rest) ∧
    List.Forall₂ (ScopedCompute (PiInertStage D stage) (proofEraseCtx Γ))
      [field, value] (pre ++ pending) ∧
    ScopedComputeCount (PiInertStage D stage) before (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value])
      (ProofShape.mkApps (.const info.ctorName []) (pre ++ pending)) ∧
    (∃ k, k < stage ∧ ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k)
      (proofEraseCtx Γ) (ProofShape.mkApps (.const info.ctorName []) pre) (.forallE A B)) ∧
    DomainSort (proofEraseCtx Γ) A u ∧
    ScopedComputeCount (PiInertStage D stage) cost (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ m)) out ∧
    (∀ later j, ScopedComputeCount (PiInertStage D later) j (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ m)) out → cost ≤ j) ∧
    smaller < cost ∧
    PiInertProjectionContinuationMinimum D (proofEraseCtx Γ) family 0 out
      (A :: proofEraseCtx Γ)
      (.app ((ProofShape.mkApps (.const info.ctorName []) pre).liftN 1) (etaArgument u)) smaller

/-- Transfer the full projection minimum through the exact selected constructor
eta. The major and field tail together are globally minimal, so competitors
may change the major while preserving its final observed output. The actual
projection typing is derived from the original pair, not assumed at later
endpoints. -/
theorem GlobalPairFunctionEtaProjection.observed_body_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : GlobalPairFunctionEtaProjection D Γ family info source out) :
    PairProjectionEtaMinimum D Γ family info source out := by
  obtain ⟨m, field, value, major, result, stage, hm, Rreach, EM, HC,
    ⟨globalCost, RG, _, tailCost, RF, Hfull⟩, RI, _⟩ := H
  obtain ⟨cost, levels, pre, pending, target, before, after,
    _, Hmin, HB, HL, HA, RP, _, HR, RT, k, hk, HE, hpre, hne, hproof⟩ := HC
  cases HL
  have hcost := Hmin _ (EM ▸ RG)
  have HT : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (.const info.ctorName []) [field, value]) := ⟨Γ, m, _, hΓ, rfl, hm, EM⟩
  have HTwhole : TypedSource (proofEraseCtx Γ)
      (ProofShape.mkApps (ProofShape.mkApps (.const info.ctorName []) pre) pending) := by
    simpa only [ProofShape.mkApps_append] using HT.pi_inert_compute heq hs RP.forget
  have ht := (dependent_pair_projections_typed hi hp hf hz hadm hshape hΓ hm).1
  have HTproj : TypedSource (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) :=
    ⟨Γ, .proj family 0 m, _, hΓ, rfl, ht, if_neg (not_isProof_of_sort hΓ ht)⟩
  have Rtail : ScopedComputeCount (PiInertStage D stage) (1 + tailCost) (proofEraseCtx Γ)
      (.proj family 0 major) out :=
    (ScopedComputeCount.base (pi_inert_stage_core (.inl (.inl (.inl RI))))).trans RF
  have Rfull : ScopedComputeCount (PiInertStage D stage) (globalCost + 1 + tailCost)
      (proofEraseCtx Γ) (.proj family 0 (proofErase Γ m)) out := by
    simpa only [Nat.add_assoc] using RG.proj.trans Rtail
  cases HE with
  | intro RN SD =>
    rename_i A B u
    obtain ⟨smaller, hsmall, HM⟩ := pi_inert_eta_projected_minimum heq hs
      (erased_static_structure_eta_expansion_stage_descent heq hs k) HTwhole HTproj RN SD
      (by simpa only [EM, ProofShape.mkApps_append] using RP) HR RT Rtail
      (cost := globalCost + 1 + tailCost) (by omega) Hfull
    exact ⟨m, field, value, pre, pending, A, B, u, stage, before, globalCost + 1 + tailCost,
      smaller, hm, Rreach, EM, hpre, hne, hproof, HA, RP, ⟨k, hk, RN⟩, SD, Rfull, Hfull, hsmall, HM⟩

/-- Every exposed pair type-projection path either reads its original field or
constructs a smaller typed eta-body minimum retaining the final projection.
Both global minima and all actual continuation typings are derived here.
Closing readout for this invariant remains a separate unproved task. -/
theorem proofErase_pi_inert_pair_projection_readout_or_observed_eta_minimum
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hm : env.HasType univs Γ m (.const family []))
    (RI : Primitive D (.proj family 0 (proofErase Γ m)) field)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (R : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (.proj family 0 (proofErase Γ m)) out) :
    (∃ later, ScopedCompute (PiInertStage D later) (proofEraseCtx Γ) field out) ∨
    PairProjectionEtaMinimum D Γ family info (proofErase Γ m) out := by
  obtain ⟨bound, RC⟩ := R.count
  rcases proofErase_pi_inert_pair_projection_global_count_readout_or_function_eta
      heq hs hi hp hf hz hadm hshape hD hΓ hm RI hout hproj RC with ⟨later, j, _, RJ⟩ | H
  · exact .inl ⟨later, RJ.forget⟩
  · exact .inr (H.observed_body_minimum heq hs hi hp hf hz hadm hshape hΓ)

end Lean4Lean.VEnv.Strengthening
