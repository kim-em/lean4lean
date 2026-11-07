import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStructureProjectionSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCountedSubstitution

/-! # Positive-cost body tails in consumed structure projection minima

Stage-zero tails need only actual typing of the consumed argument. Arbitrary
finite guarded tails use exact native recovery of that argument at the eta
domain. Both preserve counts while permitting a larger finite guard stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Every stage-zero body tail, including positive-cost core and constant
expansions under compatible nodes, can cross the actual consuming argument.
The outer eta, body prefix, and later suffix may use arbitrary finite stages.
No native recovery of the argument is assumed. -/
theorem pi_inert_consumed_structure_zero_tail_minimum_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = A :: Δ)
    (hm : env.HasType univs Γ m (.const family []))
    (RB : ScopedComputeCount (PiInertStage D bodyStage) pb (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) (proofErase Γ m))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (RTail : ScopedComputeCount (PiInertStage D 0) tailCost (A :: Δ) target body')
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') xs') major)
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ (.proj family 0 major) out)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (hcost : cp + 1 + cd + pb + 1 + tailCost + ca + cs + cf ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.proj family 0 original) out → cost ≤ j) :
    ∃ Γ₀, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ ∧
      GlobalPairFunctionEtaProjection D Γ₀ family info (target.inst x') out := by
  obtain ⟨_, WI⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  obtain ⟨expanded, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_nativeMaskedStructureExpansion_descent hstep) hΓ hm rfl rfl (.base H)
  have HTtarget : TypedSource (A :: Δ) target :=
    ⟨Γ, expanded, _, hΓ, EΓ, HE.hasType.2, EE⟩
  have RT := pi_inert_zero_compute_count_substitution heq hs RTail HTtarget WI
  have RT' : ScopedComputeCount (PiInertStage D 0) tailCost Δ
      (target.inst x') (body'.inst x') := by
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RT
  exact pi_inert_consumed_structure_projection_minimum_function_eta_of_tail
    heq hs hguard hstep hi hp hf hz hadm hshape hD HT RN SD RP HR RD hΓ EΓ hm RB H
    RT' RX RS RF hout hproj hcost hmin

/-- An arbitrary finite-stage body tail crosses consumption at unchanged cost
when the actual computed argument recovers the exact eta domain. Only the
stage increases; global projected-path minimality still excludes the cheaper
structure-readout branch. This theorem explicitly retains the native recovery
premise and does not infer it from the argument's ordinary typing. -/
theorem pi_inert_consumed_structure_native_tail_minimum_function_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hi : env.projections family info) (hp : info.nparams = 0) (hf : info.numFields = 2)
    (hz : info.nindices = 0) (hadm : (info.resultLevel.inst []).IsNeverZero)
    (hshape : info.ctorType.instL [] = .forallE (.sort (.succ .zero))
      (.forallE (.bvar 0) (.const family [])))
    (hD : ∀ levels rhs, ¬ D.unfolds info.ctorName levels rhs)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RP : ScopedComputeCount (PiInertStage D n) cp Δ original (ProofShape.mkApps f args))
    (HR : PiInertStage D n Δ f (.lam A (.app (f.liftN 1) (etaArgument u))))
    (RD : ScopedComputeCount (PiInertStage D n) cd Δ A A')
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = A :: Δ)
    (hm : env.HasType univs Γ m (.const family []))
    (RB : ScopedComputeCount (PiInertStage D bodyStage) pb (A :: Δ)
      (.app (f.liftN 1) (etaArgument u)) (proofErase Γ m))
    (H : NativeMaskedStructureExpansion Step (proofEraseCtx Γ) (proofErase Γ m) target)
    (RTail : ScopedComputeCount (PiInertStage D tailStage) tailCost (A :: Δ) target body')
    (RArg : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D imageStage) Δ x' A)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ (ProofShape.mkApps (body'.inst x') xs') major)
    (RF : ScopedComputeCount (PiInertStage D n) cf Δ (.proj family 0 major) out)
    (hout : ∀ A b rest, out ≠ ProofShape.mkApps (.lam A b) rest)
    (hproj : ∀ major, out ≠ .proj family 0 major)
    (hcost : cp + 1 + cd + pb + 1 + tailCost + ca + cs + cf ≤ cost)
    (hmin : ∀ later j, ScopedComputeCount (PiInertStage D later) j Δ
      (.proj family 0 original) out → cost ≤ j) :
    ∃ Γ₀, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ ∧
      GlobalPairFunctionEtaProjection D Γ₀ family info (target.inst x') out := by
  obtain ⟨_, WI⟩ := pi_inert_eta_body_interpretation heq hs hguard HT RN SD RX
  obtain ⟨expanded, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_nativeMaskedStructureExpansion_descent hstep) hΓ hm rfl rfl (.base H)
  have HTtarget : TypedSource (A :: Δ) target :=
    ⟨Γ, expanded, _, hΓ, EΓ, HE.hasType.2, EE⟩
  have RT := pi_inert_compute_count_native_inst heq hs RTail HTtarget WI RArg
  exact pi_inert_consumed_structure_projection_minimum_function_eta_of_tail
    heq hs hguard hstep hi hp hf hz hadm hshape hD HT RN SD RP HR RD hΓ EΓ hm RB H
    RT RX RS RF hout hproj hcost hmin

end Lean4Lean.VEnv.Strengthening
