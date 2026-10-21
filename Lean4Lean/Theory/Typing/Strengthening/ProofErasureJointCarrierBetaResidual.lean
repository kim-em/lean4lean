import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointStageBetaCommutation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryJoinBoundary

/-! # Carrier-preserving beta residuals for the comparison induction

Ordinary terms retain a carrier guard instead of the false general common-mode
conclusion. At a literal sort this recovers ordinary comparison. Finite
computation prefixes use lower-stage commutation; application and the remaining
comparison/carrier constructors still need a simultaneous proof.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Endpoint beta residuals retain a guard at the original supplied carrier.
This is a property of a particular pair, not a closure law for all guards. -/
def JointCarrierBetaResidual
    (Target : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (A a b : ProofShape) : Prop :=
  ∀ {p q}, ProofShape.BetaRed a p → ProofShape.BetaRed b q →
    JointCarrierGuard Target Δ A p q

/-- Missing simultaneous carrier transport law at typed endpoints. In
particular it includes ordinary comparison via carrierChecked, but its output
retains the supplied carrier instead of asserting the refuted general common
comparison law. This is not established for the stages or their union and is
not claimed to be a smaller sufficient strengthening front. -/
def JointCarrierBetaTransport
    (Step Target : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ a b T}, OnCtx Γ (env.IsType univs) →
    env.HasType univs Γ a T → env.HasType univs Γ b T →
    JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ T) (proofErase Γ a) (proofErase Γ b) →
    JointCarrierBetaResidual Target (proofEraseCtx Γ) (proofErase Γ T) (proofErase Γ a) (proofErase Γ b)

/-- At Prop, retaining the carrier gives exactly the required proposition
comparison after both endpoint beta paths. No general carrier decoder is used. -/
theorem JointCarrierBetaTransport.proposition_transport
    (H : JointCarrierBetaTransport Step Target)
    (hhead : ∀ {Δ a b}, Target Δ a b → PrimitiveHead a) :
    JointPropBetaTransport Step Target := by
  intro Γ P Q p q hΓ hP hQ HC RP RQ
  have HG := H hΓ hP hQ (.carrierChecked HC) RP RQ
  rw [show proofErase Γ (.sort .zero) = .sort .zero from
    if_neg (not_isProof_of_sort hΓ (HasType.sort (by trivial)))] at HG
  exact HG.sort_checked hhead

/-- Restricting source computation restricts the input guards while retaining
the same carrier-residual conclusion. -/
theorem JointCarrierBetaTransport.source_mono
    (H : JointCarrierBetaTransport Step Target)
    (hinc : ∀ {Δ a b}, Step' Δ a b → Step Δ a b) : JointCarrierBetaTransport Step' Target :=
  fun hΓ ha hb HC => H hΓ ha hb (HC.mono hinc)

/-- A subsingleton carrier handles all endpoint beta residuals directly. This
includes the positive empty-structure identity peak that refutes common-mode
transport: its distinct variable reducts remain related at their carrier. -/
theorem JointCarrierBetaResidual.subsingleton (H : SubsingletonCarrier A) :
    JointCarrierBetaResidual Target Δ A a b := fun _ _ => .carrierSubsingleton H

/-- Symmetry preserves the supplied carrier and swaps the two future paths. -/
theorem JointCarrierBetaResidual.symm (H : JointCarrierBetaResidual Target Δ A a b) :
    JointCarrierBetaResidual Target Δ A b a := fun RP RQ => .carrierSymm (H RQ RP)

/-- A function carrier preserves all endpoint beta residuals when its body
check does. Lift the two beta paths and apply the unchanged eta argument; the
supplied domain sort and carrier telescope remain available in the result. -/
theorem JointCarrierBetaResidual.function
    (S : DomainSort Δ A u)
    (H : JointCarrierBetaResidual Target (A :: Δ) B
      (.app (a.liftN 1) (etaArgument u)) (.app (b.liftN 1) (etaArgument u))) :
    JointCarrierBetaResidual Target Δ (.forallE A B) a b :=
  fun RA RB => .carrierFunction S (H (.app RA.liftN .refl) (.app RB.liftN .refl))

/-- A target computation of the supplied carrier wraps every endpoint residual.
The carrier computation itself is not changed by endpoint beta reduction. -/
theorem JointCarrierBetaResidual.carrier_compute
    (R : ScopedCompute Target Δ A A') (H : JointCarrierBetaResidual Target Δ A' a b) :
    JointCarrierBetaResidual Target Δ A a b := fun RP RQ => .carrierCompute R (H RP RQ)

/-- Two source computation prefixes transport a residual certificate at their
outputs back to their inputs, using typed computation/beta commutation only.
The residual's supplied carrier is preserved exactly. -/
theorem JointCarrierBetaResidual.compute_typed
    (commute : ∀ {e T out reduced}, env.HasType univs Γ e T →
      ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e) out →
      ProofShape.BetaRed (proofErase Γ e) reduced →
      ∃ shared, ProofShape.BetaRed out shared ∧ ScopedCompute Target (proofEraseCtx Γ) reduced shared)
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (RA : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ a) a')
    (RB : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ b) b')
    (H : JointCarrierBetaResidual Target (proofEraseCtx Γ) A a' b') :
    JointCarrierBetaResidual Target (proofEraseCtx Γ) A (proofErase Γ a) (proofErase Γ b) := by
  intro p q PA PB
  obtain ⟨pa, BA, CA⟩ := commute ha RA PA
  obtain ⟨pb, BB, CB⟩ := commute hb RB PB
  exact .carrierReduce CA CB (H BA BB)

/-- Computation prefixes at stage n+1 need only stage-n proposition transport.
The inner residual certificate is required only at the two original prefix
outputs, not at arbitrary enlarged-stage guards. This handles the finite
prefixes in compute and carrierReduce once their recursive case is supplied. -/
theorem JointCarrierBetaResidual.stage_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (RA : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ a) a')
    (RB : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ b) b')
    (H : JointCarrierBetaResidual (ErasedJointUnion D) (proofEraseCtx Γ) A a' b') :
    JointCarrierBetaResidual (ErasedJointUnion D) (proofEraseCtx Γ) A (proofErase Γ a) (proofErase Γ b) := by
  intro p q PA PB
  apply H.compute_typed (fun ht R B => ?_) ha hb RA RB PA PB
  obtain ⟨shared, BS, RS⟩ := proofErase_joint_stage_beta_commute_of_lower_beta heq hs hregistry Hbeta hΓ ht R B
  exact ⟨shared, BS, RS.mono erased_beta_stable_joint_into_union⟩

/-- Core computation prefixes need no proposition-transport premise. This
closes the computation-prefix part of the stage-zero carrier induction, given
the recursive residual certificate at the original prefix outputs. -/
theorem JointCarrierBetaResidual.zero_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (RA : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ a) a')
    (RB : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ b) b')
    (H : JointCarrierBetaResidual (ErasedJointUnion D) (proofEraseCtx Γ) A a' b') :
    JointCarrierBetaResidual (ErasedJointUnion D) (proofEraseCtx Γ) A (proofErase Γ a) (proofErase Γ b) := by
  intro p q PA PB
  apply H.compute_typed (fun ht R B => ?_) ha hb RA RB PA PB
  obtain ⟨shared, BS, RS⟩ := proofErase_joint_zero_beta_commute heq hs hΓ ht R B
  exact ⟨shared, BS, RS.mono erased_beta_stable_joint_into_union⟩

/-- Reflexive typed comparison has carrier residuals at any supplied carrier:
the two beta paths commute through the already proved core computation case.
The output carrier need not have a separately recovered type. -/
theorem joint_carrier_beta_residual_refl
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    JointCarrierBetaResidual (ErasedJointUnion D) (proofEraseCtx Γ) A (proofErase Γ e) (proofErase Γ e) := by
  intro p q RP RQ
  obtain ⟨shared, BP, CQ⟩ := proofErase_joint_zero_beta_commute heq hs hΓ ht (.beta RP) RQ
  exact .carrierReduce (.beta BP) (CQ.mono erased_beta_stable_joint_into_union) (.carrierChecked (.leaf .refl))

end Lean4Lean.VEnv.Strengthening
