import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFutureTypeComparison
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCertifiedProbe
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront

/-! # Compared carrier types without a computational join

The source is P → Unit; the target is Q → K(Unit), where K is a closed
reflexive Eq type probe and P, Q are eta-related propositions with no union
computation join. The target is not syntactically a structural subsingleton.
Certified type comparison nevertheless supplies its full future carrier guard.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private functionType function_type
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaCertifiedProbe
open private subsingleton_pi
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComparedSubsingleton
open private carrier_exposure_ne_eqRec
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypePathUnitFront
variable [Params]

private theorem subsingleton_exposure (H : SubsingletonCarrier A) : CarrierExposure A := by
  cases H with
  | unit hi hx hf hp => exact .record hi hx hp
  | forallE => exact .function

/-- Actual certified type comparison supplies a future guard at a target that
is not structurally subsingleton and has no computational join with the source
in the full union. Domain eta and explicit codomain computation are both used. -/
theorem compared_types_nonjoining_future_carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hEq : ∀ levels rhs, ¬ D.unfolds ``Eq levels rhs)
    (hD : ∀ {family info}, env.projections family info → ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hf : info.numFields = 0)
    (hS : env.HasType univs [] (.const family ls) (.sort (.succ u))) :
    ∃ Γ T U v, OnCtx Γ (env.IsType univs) ∧
      env.HasType univs Γ T (.sort v) ∧ env.HasType univs Γ U (.sort v) ∧
      JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true (proofErase Γ T) (proofErase Γ U) ∧
      SubsingletonCarrier (proofErase Γ T) ∧ ¬ SubsingletonCarrier (proofErase Γ U) ∧
      (¬ ∃ shared, ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ T) shared ∧
        ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ U) shared) ∧
      ∀ a b, BetaStableCarrier (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ U) a b := by
  obtain ⟨P, Q, q, hP, hQ, _, HF, Hno⟩ :=
    EtaCertifiedProbe.no_join_indices (Step := ErasedBetaStableJoint D) heq hEq (show OnCtx [] (env.IsType univs) from trivial)
  let Γ := [functionType]
  let S := VExpr.const family ls
  have hΓ : OnCtx Γ (env.IsType univs) := ⟨trivial, _, function_type⟩
  have hΓP : OnCtx (P :: Γ) (env.IsType univs) := ⟨hΓ, _, hP⟩
  have hSP : env.HasType univs (P :: Γ) S (.sort (.succ u)) := hS.weak0 henv.ordered
  have hSQ : env.HasType univs (Q :: Γ) S (.sort (.succ u)) := hS.weak0 henv.ordered
  let R : VExpr := .forallE (.sort .zero) (.bvar 0)
  have hR : env.HasType univs [] R (.sort .zero) :=
    (IsDefEq.sortDF (by trivial) (by trivial)
      (show VLevel.imax (.succ .zero) .zero ≈ .zero from rfl)).defeq
        (HasType.forallE (HasType.sort (by trivial)) (HasType.bvar .zero))
  let r := eqReflApp (.succ .zero) (.sort .zero) R
  have hr : env.HasType univs [] r (eqApp (.succ .zero) (.sort .zero) R R) :=
    HasType.eqReflApp heq (by trivial) (HasType.sort (by trivial)) hR
  let K := eqTypeProbe (.succ u) S R R r
  have hK := eqTypeProbe_typed heq (by trivial) hS hR hR hr
  have hKP : env.HasType univs (P :: Γ) K (.sort (.succ u)) := hK.weak0 henv.ordered
  have hKQ : env.HasType univs (Q :: Γ) K (.sort (.succ u)) := hK.weak0 henv.ordered
  have RK : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) K) (proofErase (P :: Γ) S) :=
    eqTypeProbe_compute_certified_of_beta_join heq hregistry hΓP hSP
      (hR.weak0 henv.ordered) (hR.weak0 henv.ordered) (hr.weak0 henv.ordered) .refl .refl
  have HPQ := proofErase_joint_carrier_reflect (erased_beta_stable_joint_descent heq hs)
    hΓ hP hQ (.carrierChecked HF.base)
  have W : IsDefEqCtx env univs [] (P :: Γ) (Q :: Γ) := .succ (.refl hΓ) HPQ
  have EK := proofErase_defeqCtx hΓP W hKP
  have hT := HasType.forallE hP hSP
  have hU := HasType.forallE hQ hKQ
  have ET : proofErase Γ (.forallE P S) = .forallE (proofErase Γ P) (proofErase (P :: Γ) S) :=
    if_neg (not_isProof_of_sort hΓ hT)
  have EU : proofErase Γ (.forallE Q K) = .forallE (proofErase Γ Q) (proofErase (Q :: Γ) K) :=
    if_neg (not_isProof_of_sort hΓ hU)
  have HC : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx Γ) true
      (proofErase Γ (.forallE P S)) (proofErase Γ (.forallE Q K)) := by
    rw [ET, EU, ← EK]
    apply JointCheck.forallSorted ⟨Γ, P, hΓ, rfl, hP, rfl⟩ ⟨Γ, Q, hΓ, rfl, hQ, rfl⟩ HF.base
      ⟨P :: Γ, S, hΓP, rfl, hSP, rfl⟩ ⟨P :: Γ, K, hΓP, rfl, hKP, rfl⟩
    exact .compute .refl RK (.leaf .refl)
  have HT : SubsingletonCarrier (proofErase Γ (.forallE P S)) := by
    rw [ET, show proofErase (P :: Γ) S = .const family ls from if_neg (not_isProof_of_sort hΓP hSP)]
    exact .forallE (.unit hi hx hf (ps := []) hp.symm)
  refine ⟨Γ, .forallE P S, .forallE Q K, _, hΓ, hT, hU, HC, HT, ?_, ?_, ?_⟩
  · intro HU
    rw [EU, ← EK] at HU
    have HK := subsingleton_pi HU
    have HX := subsingleton_exposure HK
    apply carrier_exposure_ne_eqRec heq HX
    rw [eqTypeProbe_erase heq hΓP hSP (hR.weak0 henv.ordered)
      (hR.weak0 henv.ordered) (hr.weak0 henv.ordered)]
    exact constHead_mkApps _ _
  · rintro ⟨shared, RT, RU⟩
    rw [ET] at RT
    rw [EU] at RU
    obtain ⟨A, B, E, RA⟩ := RT.forallE_domain_inv erased_joint_union_head
    obtain ⟨C, D, F, RC⟩ := RU.forallE_domain_inv erased_joint_union_head
    have EAC := (ProofShape.forallE.inj (E.symm.trans F)).1
    exact Hno ⟨A, RA, EAC ▸ RC⟩
  · intro a b
    exact proofErase_certified_compared_subsingleton_future heq hs hD hΓ hT hU HC HT

end Lean4Lean.VEnv.Strengthening
