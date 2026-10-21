import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierBetaResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin

/-! # Beta residuals of dependent carrier recipes

A dependent field's carrier changes when its parameters or left major reduce.
Retaining beta transport of the carrier itself gives the recursive premise
needed by carrierNested. Computation of the carrier is handled by the same
lower-stage commutation theorem as computation of the endpoints.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private beta_images from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointPropBeta
variable [Params]

private theorem instOuter_beta (H : List.Forall₂ ProofShape.BetaRed args args') (body : ProofShape) :
    ProofShape.BetaRed (body.instOuter args) (body.instOuter args') := by
  apply beta_images
  intro i
  unfold ProofShape.Subst.ofList
  have hlen := H.length_eq
  by_cases hi : i < args.length
  · simp only [← hlen, dif_pos hi]
    exact H.getElem_of _ (by omega) (by omega)
  · simp only [← hlen, dif_neg hi]
    exact .refl

/-- Reducing parameters and the major reduces the exact dependent projection
carrier, including every preceding-field occurrence in its template. No
closure, typing or scope assumption on the template is needed for beta congruence. -/
theorem ProofShape.projectionType_beta
    (HP : List.Forall₂ ProofShape.BetaRed ps ps') (HM : ProofShape.BetaRed m m') :
    ProofShape.BetaRed (projectionType s info doms j hj ps m)
      (projectionType s info doms j hj ps' m') := by
  unfold projectionType
  apply instOuter_beta
  unfold projectionArgs
  apply List.Forall₂.append' (Lean4Lean.List.forall₂_take HP _)
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  exact Lean4Lean.List.Forall₂.rfl (fun _ _ => .proj HM)

/-- A local residual certificate allowing beta reduction of the supplied
carrier as well as both endpoints. This is stronger than endpoint-only
residuals and is not asserted for arbitrary joint guards. -/
def JointCarrierTypeBetaResidual
    (Target : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (A a b : ProofShape) : Prop :=
  ∀ {A' p q}, ProofShape.BetaRed A A' → ProofShape.BetaRed a p → ProofShape.BetaRed b q →
    JointCarrierGuard Target Δ A' p q

/-- The reflexive carrier path recovers the preceding endpoint-only property. -/
theorem JointCarrierTypeBetaResidual.endpoints
    (H : JointCarrierTypeBetaResidual Target Δ A a b) :
    JointCarrierBetaResidual Target Δ A a b := H .refl

/-- Structural subsingleton certificates survive reduction of their carrier,
so no endpoint computation or type recovery is required in this base case. -/
theorem JointCarrierTypeBetaResidual.subsingleton (H : SubsingletonCarrier A) :
    JointCarrierTypeBetaResidual Target Δ A a b :=
  fun RC _ _ => .carrierSubsingleton (H.beta RC)

/-- Carrier reduction is unchanged when the two endpoint roles are exchanged. -/
theorem JointCarrierTypeBetaResidual.symm
    (H : JointCarrierTypeBetaResidual Target Δ A a b) :
    JointCarrierTypeBetaResidual Target Δ A b a :=
  fun RC RP RQ => .carrierSymm (H RC RQ RP)

/-- Every dependent field uses the beta-reduced parameters and new left major.
The exact template congruence supplies its changed carrier to the recursive
certificate. This handles carrierNested without requiring old and new field
carriers to be syntactically equal or reversing carrier computation. -/
theorem JointCarrierTypeBetaResidual.record_nested
    (hi : env.projections family info) (hx : info.nindices = 0)
    (hp : ps.length = info.nparams)
    (hadm : (info.resultLevel.inst ls).IsNeverZero ∨ StructureReplay.ProofFields env univs info ls)
    (HT : ProjTele env univs family info ls doms result)
    (H : ∀ i (hj : i < info.numFields), ¬ StructureReplay.ProofField env univs info ls i →
      JointCarrierTypeBetaResidual Target Δ
        (projectionType family info doms i (by have := HT.numFields; omega) ps a)
        (.proj family i a) (.proj family i b)) :
    JointCarrierTypeBetaResidual Target Δ (mkApps (.const family ls) ps) a b := by
  intro A' p q RC RP RQ
  obtain ⟨ps', rfl, HP⟩ := RC.const_spine
  apply JointCheck.carrierNested hi hx (HP.length_eq.symm.trans hp) hadm HT
  intro i hj hn
  exact H i hj hn (projectionType_beta HP RP) (.proj RP) (.proj RQ)

/-- Endpoint-computation prefixes preserve the stronger certificate too. The
independent carrier beta path is passed to the recursive residual unchanged. -/
theorem JointCarrierTypeBetaResidual.compute_typed
    (commute : ∀ {e T out reduced}, env.HasType univs Γ e T →
      ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e) out →
      ProofShape.BetaRed (proofErase Γ e) reduced →
      ∃ shared, ProofShape.BetaRed out shared ∧ ScopedCompute Target (proofEraseCtx Γ) reduced shared)
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b T)
    (RA : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ a) a')
    (RB : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ b) b')
    (H : JointCarrierTypeBetaResidual Target (proofEraseCtx Γ) A a' b') :
    JointCarrierTypeBetaResidual Target (proofEraseCtx Γ) A (proofErase Γ a) (proofErase Γ b) := by
  intro A' p q RC PA PB
  obtain ⟨pa, BA, CA⟩ := commute ha RA PA
  obtain ⟨pb, BB, CB⟩ := commute hb RB PB
  exact .carrierReduce CA CB (H RC BA BB)

/-- Computation of the old supplied carrier commutes with its requested beta
path. The recursive residual is used at the shared carrier, then an actual
target carrierCompute wraps it at the requested new carrier. This gives the
needed forward change without inverting a computation path. -/
theorem JointCarrierTypeBetaResidual.carrier_compute_typed
    (commute : ∀ {e T out reduced}, env.HasType univs Γ e T →
      ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ e) out →
      ProofShape.BetaRed (proofErase Γ e) reduced →
      ∃ shared, ProofShape.BetaRed out shared ∧ ScopedCompute Target (proofEraseCtx Γ) reduced shared)
    (hA : env.HasType univs Γ A (.sort u))
    (R : ScopedCompute Source (proofEraseCtx Γ) (proofErase Γ A) B)
    (H : JointCarrierTypeBetaResidual Target (proofEraseCtx Γ) B a b) :
    JointCarrierTypeBetaResidual Target (proofEraseCtx Γ) (proofErase Γ A) a b := by
  intro A' p q RC RP RQ
  obtain ⟨C, BC, AC⟩ := commute hA R RC
  exact .carrierCompute AC (H BC RP RQ)

/-- Stage-n+1 carrier computation needs beta transport only at source stage n.
The recursive certificate stays attached to the old computation's output. -/
theorem JointCarrierTypeBetaResidual.stage_carrier_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ A) B)
    (H : JointCarrierTypeBetaResidual (ErasedJointUnion D) (proofEraseCtx Γ) B a b) :
    JointCarrierTypeBetaResidual (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) a b := by
  intro A' p q RC RP RQ
  apply H.carrier_compute_typed (fun ht R B => ?_) hA R RC RP RQ
  obtain ⟨shared, BS, RS⟩ := proofErase_joint_stage_beta_commute_of_lower_beta heq hs hregistry Hbeta hΓ ht R B
  exact ⟨shared, BS, RS.mono erased_beta_stable_joint_into_union⟩

/-- The carrier-computation base case needs no proposition beta-transport law. -/
theorem JointCarrierTypeBetaResidual.zero_carrier_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ScopedCompute (ErasedJointStage D 0) (proofEraseCtx Γ) (proofErase Γ A) B)
    (H : JointCarrierTypeBetaResidual (ErasedJointUnion D) (proofEraseCtx Γ) B a b) :
    JointCarrierTypeBetaResidual (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ A) a b := by
  intro A' p q RC RP RQ
  apply H.carrier_compute_typed (fun ht R B => ?_) hA R RC RP RQ
  obtain ⟨shared, BS, RS⟩ := proofErase_joint_zero_beta_commute heq hs hΓ ht R B
  exact ⟨shared, BS, RS.mono erased_beta_stable_joint_into_union⟩

/-- Reflexive typed endpoints retain a guard at every beta-reduced carrier.
The endpoint beta join does not depend on the supplied carrier's syntax. -/
theorem joint_carrier_type_beta_residual_refl
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T) :
    JointCarrierTypeBetaResidual (ErasedJointUnion D) (proofEraseCtx Γ) A (proofErase Γ e) (proofErase Γ e) :=
  fun _ RP RQ => joint_carrier_beta_residual_refl heq hs hΓ ht RP RQ

end Lean4Lean.VEnv.Strengthening
