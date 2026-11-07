import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertTerminalSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeExposure

/-! # Read a constant control application from its function comparison

The target application's typing and the inferred function child supply its
argument at the source's written domain. A sort assignment for the discarded
source argument makes the target argument terminal. The existing stage-zero
terminal substitution theorem then removes the source constant frame.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private erase_app_inv erase_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private source_realize
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeExposure
open private control_realize
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureConstructorTypeReadout
variable [Params] {D : Definitions}

/-- Inferred comparison of constant control functions retypes the target
application argument at the source domain. If the discarded source argument
is a type, the target argument is terminal automatically. The target body may
depend on it; neither an argument guard nor target native recovery is needed. -/
theorem proofErase_pi_inert_zero_constant_application_of_type_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort w))
    (ha : env.HasType univs Γ a T) (hna : ¬ IsProof Γ a)
    (hx : env.HasType univs Γ x A) (hxu : env.HasType univs Γ x (.sort u))
    (hgp : env.HasType univs Γ (.app g p) U)
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a.lift)) (proofErase Γ g)) :
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ a) (proofErase Γ (.app g p)) := by
  have hf : env.HasType univs Γ (.lam A a.lift) (.forallE A T.lift) :=
    .lam hA (ha.weak henv)
  have Hbeta : env.IsDefEq univs Γ (.app (.lam A a.lift) x) a T := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta (ha.weak henv (B := A)) hx
  have hnapp := mt (isProof_congr hΓ Hbeta).1 hna
  have hnf := not_isProof_fn hΓ hf hx hnapp
  have EF : proofErase Γ (.lam A a.lift) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) a.lift) := if_neg hnf
  have HR := H
  rw [EF] at HR
  obtain ⟨_, _, _, _, _, RG, _⟩ := HR.pi_inert_lambda_cut
  have hng : ¬ IsProof Γ g := by
    intro hproof
    rw [proofErase_eq_proof.2 hproof] at RG
    cases RG.pi_inert_proof_fixed
  obtain ⟨C, E, hg, hp⟩ := hgp.app_inv henv hΓ
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have HE := (proofErase_computed_joint_compare_reflect @hd hΓ hf hg H).2 rfl hnf hng
  have hgPi := (HE.of_l henv hΓ hf).hasType.2
  have hpA := argument_at_displayed_domain hΓ hg hgPi hp
  have hpu := hpA.defeqU_r henv hΓ (hx.uniqU henv hΓ hxu)
  exact proofErase_pi_inert_zero_constant_function_application heq hs hΓ hA ha hna
    hpA (.type hpu) hg H

/-- Independent computation of the source control function and the target
function before checking preserves the same application readout. The discarded
source argument needs only its actual domain and sort typings; every target
argument condition is derived from the original application and function child. -/
theorem proofErase_pi_inert_zero_computed_constant_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort w))
    (ha : env.HasType univs Γ a T) (hna : ¬ IsProof Γ a)
    (hx : env.HasType univs Γ x A) (hxu : env.HasType univs Γ x (.sort u))
    (hgp : env.HasType univs Γ (.app g p) U)
    (RF : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ)
      (proofErase Γ (.lam A a.lift)) f')
    (RG : ScopedCompute (PiInertStage D 0) (proofEraseCtx Γ) (proofErase Γ g) g')
    (H : ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false f' g') :
    ComputedJointCompare (PiInertStage D 0) (proofEraseCtx Γ) false
      (proofErase Γ a) (proofErase Γ (.app g p)) :=
  proofErase_pi_inert_zero_constant_application_of_type_argument heq hs hΓ hA ha hna hx hxu hgp
    (.compute RF RG H)

/-- An erased constant frame can be removed directly from an application
node's inferred function child. Only the erased body must omit the binder;
the actual body need not be a lift. Source application typing supplies a typed
nonproof lower payload by beta realization, and the discarded source argument
is sort-typed. No payload, target argument or target body certificate is an
additional premise. -/
theorem pi_inert_zero_constant_control_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HTX : TypedSource Δ (.app (.lam rawA (rawa.liftN 1)) rawx))
    (HTY : TypedSource Δ (.app rawg rawp))
    (HX : ControlTyping Δ rawx (.sort u))
    (HF : ComputedJointCompare (PiInertStage D 0) Δ false
      (.lam rawA (rawa.liftN 1)) rawg) :
    ComputedJointCompare (PiInertStage D 0) Δ false rawa (.app rawg rawp) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HTX
  have hd : ErasedScopedPrimitiveDescent (PiInertStage D 0) :=
    ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs 0)
  have R : ScopedCompute (PiInertStage D 0) Δ
      (.app (.lam rawA (rawa.liftN 1)) rawx) rawa :=
    .beta ConstantHeadDeletion.drop.reduce
  obtain ⟨a, HA, Ea⟩ := proofErase_scoped_compute_realize @hd hΓ ht EΓ Ee R
  have hne : ¬ IsProof Γ e := by
    intro hp
    have E := Ee.symm.trans (proofErase_eq_proof.2 hp)
    cases E
  have ha := HA.hasType.2
  have hna := mt (isProof_congr hΓ HA).2 hne
  obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
  obtain ⟨A₀, b₀, rfl, _, EA, _⟩ := erase_lam_inv Ef
  obtain ⟨P, Q, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨⟨w, hA⟩, B₀, hb⟩ := hf.lam_inv henv hΓ
  have hxA := argument_at_displayed_domain hΓ hf (HasType.lam hA hb) hx
  obtain ⟨x₁, hx₁, Ex₁⟩ := control_realize HX hΓ EΓ
  have hnx : ¬ IsProof Γ x₀ := fun hp => HX.ne_proof (Ex.symm.trans (proofErase_eq_proof.2 hp))
  obtain ⟨_, HE⟩ := (proofErase_reflect hΓ hxA hx₁ (Ex.trans Ex₁.symm)).2 hnx
  have hxSort := ((HE.defeq hΓ).of_r henv hΓ hx₁).hasType.1
  obtain ⟨e', T', ht', Ee'⟩ := source_realize HTY hΓ EΓ
  obtain ⟨g, p, rfl, _, Eg, _⟩ := erase_app_inv Ee'
  have hconst : env.HasType univs Γ (.lam A₀ a.lift) (.forallE A₀ T.lift) :=
    .lam hA (ha.weak henv)
  have Hbeta : env.IsDefEq univs Γ (.app (.lam A₀ a.lift) x₀) a T := by
    simpa only [VExpr.inst_lift] using IsDefEq.beta (ha.weak henv (B := A₀)) hxA
  have hnconst := not_isProof_fn hΓ hconst hxA (mt (isProof_congr hΓ Hbeta).1 hna)
  have hΓA : OnCtx (A₀ :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  have EF : proofErase Γ (.lam A₀ a.lift) = .lam rawA (rawa.liftN 1) := by
    rw [show proofErase Γ (.lam A₀ a.lift) =
      .lam (proofErase Γ A₀) (proofErase (A₀ :: Γ) a.lift) from if_neg hnconst]
    rw [proofErase_liftN hΓ hΓA Ctx.LiftN.one ha, EA, Ea]
  have H := proofErase_pi_inert_zero_constant_application_of_type_argument
    heq hs hΓ hA ha hna hxA hxSort ht'
      (by simpa only [EΓ, EF, Eg] using HF)
  simpa only [EΓ, Ea, Ee'] using H

end Lean4Lean.VEnv.Strengthening
