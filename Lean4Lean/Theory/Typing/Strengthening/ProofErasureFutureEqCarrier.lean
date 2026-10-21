import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableEqComputation

/-! # Retained carrier certificates construct future Eq guards

Native Eq recovery selects any supplied raw carrier exactly. A future carrier
certificate can therefore check the final endpoints after independent carrier,
anchor and endpoint beta paths, including every interpreted substitution.
This constructs certified Eq steps from the existing function and structure
carrier recipes without a general forward-transport law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_eq_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqDecode
open private eq_prefix_certified_with_family
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinEqComputation
variable [Params]

private theorem eq_native_recovery (heq : env.HasCanonicalEq) (hu : u.WF univs) :
    ScopedTypeRecovery Step Δ (.app (.app (.const ``Eq [u]) A) z)
      (.forallE A (.sort .zero)) := by
  have R0 : ScopedTypeRecovery Step Δ (.const ``Eq [u])
      (.forallE (.sort u) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))) := by
    rw [← erase_eq_type hu]
    exact .const heq.1 (by simpa using hu) rfl
  have R1 : ScopedTypeRecovery Step Δ (.app (.const ``Eq [u]) A)
      (.forallE A (.forallE (A.liftN 1) (.sort .zero))) := by
    simpa [ProofShape.inst, ProofShape.liftN_zero] using ScopedTypeRecovery.app (a := A) R0
  simpa only [ProofShape.inst_eq_subst, ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.liftN,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using ScopedTypeRecovery.app (a := z) R1

private theorem eq_carrier_beta
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (HA : ∀ {A' B'}, ProofShape.BetaRed A A' → ProofShape.BetaRed B B' →
      JointCompare Step Δ true A' B')
    (HZ : ∀ {z' w'}, ProofShape.BetaRed z z' → ProofShape.BetaRed w w' →
      JointCompare Step Δ true z' w')
    (HC : JointCarrierTypeBetaResidual Step Δ A a b)
    (RP : ProofShape.BetaRed (eqProofType u A z a) p)
    (RQ : ProofShape.BetaRed (eqProofType u B w b) q) :
    JointCompare Step Δ true p q := by
  obtain ⟨left, rfl, HP⟩ := RP.const_spine (args := [A, z, a])
  obtain ⟨right, rfl, HQ⟩ := RQ.const_spine (args := [B, w, b])
  cases HP with | cons RA HP =>
  cases HP with | cons RZ HP =>
  cases HP with | cons Ra HP =>
  cases HP
  cases HQ with | cons RB HQ =>
  cases HQ with | cons RW HQ =>
  cases HQ with | cons Rb HQ =>
  cases HQ
  exact .appCarrier (eq_native_recovery heq hu)
    (.app (.app (.leaf .refl) (HA RA RB)) (HZ RZ RW)) (HC RA Ra Rb)

/-- Future carrier checking yields future Eq comparison with independently
changing carriers and anchors. Only the left carrier checks the final endpoints;
the two carrier and anchor prefixes retain their own future comparisons.
No actual typing or primitive closure is required by this raw construction. -/
theorem eq_family_of_future_carrier
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (HA : BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ A B)
    (HZ : BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ z w)
    (HC : BetaStableCarrier Step Δ A a b) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) Δ
      (eqProofType u A z a) (eqProofType u B w b) := by
  refine ⟨fun RP RQ => eq_carrier_beta heq hu HA.1 HZ.1 HC.1 RP RQ, ?_⟩
  intro Δ' τ p q W RP RQ
  simp only [eqProofType, ProofShape.subst] at RP RQ
  exact eq_carrier_beta heq hu (HA.subst W).1 (HZ.subst W).1 (HC.subst W).1 RP RQ

/-- At any typed supplied carrier and repeated anchor, a full future carrier
certificate supplies the actual future Eq family comparison. Reflexive future
certificates for the carrier and anchor follow from their typings. -/
theorem proofErase_future_carrier_eq_family
    (heq : env.HasCanonicalEq) (hu : u.WF univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α) (ha : env.HasType univs Γ a α) (hb : env.HasType univs Γ b α)
    (HC : BetaStableCarrier Step (proofEraseCtx Γ) (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (proofErase Γ (eqApp u α z a)) (proofErase Γ (eqApp u α z b)) := by
  rw [proofErase_eqProofType heq hu hΓ hα hz ha, proofErase_eqProofType heq hu hΓ hα hz hb]
  exact eq_family_of_future_carrier heq hu
    (proofErase_beta_join_family hΓ hα hα .refl .refl)
    (proofErase_beta_join_family hΓ hz hz .refl .refl) HC

/-- A full future carrier recipe in the union constructs the actual certified
Eq singleton step. This includes arbitrary supplied carrier syntax and the
existing function, structure, and computed-carrier recipes. No common index
certificate, join, or forward guard-transport law is assumed. -/
theorem proofErase_future_carrier_eq_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (eqRecBeforeMajor v w α a M m b))
    (HC : BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) :
    ErasedBetaStableJoint D (proofEraseCtx Γ)
      (proofErase Γ (eqRecBeforeMajor v w α a M m b))
      (proofErase Γ (.lam (eqApp w α a b) m.lift)) := by
  obtain ⟨_, hw, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hab := proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs) hΓ ha hb HC.base
  exact eq_prefix_certified_with_family heq hregistry hΓ ht hn hab.toU
    (proofErase_future_carrier_eq_family heq hw hΓ hα ha ha hb HC)

end Lean4Lean.VEnv.Strengthening
