import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertificateStrengthening

/-! # Carrier applications with a displayed lambda domain

A displayed lambda already supplies its argument domain. Its application can
therefore consume a carrier guard without recovering the lambda's entire Pi
type, including its codomain. This local rule preserves exact certificates
under binder removal. It is not yet a recursively enlarged joint checker or
a proof of substitution closure for arbitrary proposition images.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_app_inv ProofShape.liftN_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params]

/-- A local application certificate reading its carrier from the left lambda
annotation. Its recursive premises use the existing joint grammar. No complete
Pi recovery of the lambda is requested; no recursive coverage is asserted. -/
inductive DisplayedLambdaApplication
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro : JointCompare Step Δ false (.lam A body) g →
      JointCarrierGuard Step Δ A x y →
      DisplayedLambdaApplication Step Δ (.app (.lam A body) x) (.app g y)

/-- The existing application rule covers this local certificate whenever full
Pi recovery at the displayed domain happens to be available. -/
theorem DisplayedLambdaApplication.joint
    (H : DisplayedLambdaApplication Step Δ (.app (.lam A body) x) (.app g y))
    (HR : ScopedTypeRecovery Step Δ (.lam A body) (.forallE A B)) :
    JointCompare Step Δ mode (.app (.lam A body) x) (.app g y) := by
  cases H with
  | intro HF HX => exact .appCarrier HR HF HX

/-- Both the local application certificate and its semantic equality descend
through arbitrary inserted binders. Independently supplied lower endpoint
typings suffice. The displayed domain is reconstructed from the lower lambda,
so no recovered codomain or recovery-completeness premise enters the proof. -/
theorem proofErase_displayed_lambda_application_descend
    (hcert : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (H : DisplayedLambdaApplication Step (proofEraseCtx Γ')
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    DisplayedLambdaApplication Target (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) ∧
      env.IsDefEqU univs Γ a b := by
  generalize Ea : (proofErase Γ a).liftN n k = sa at H
  generalize Eb : (proofErase Γ b).liftN n k = sb at H
  cases H with
  | intro HF HX =>
    obtain ⟨_, _, Eaa, Eaf, Eax⟩ := ProofShape.liftN_app_inv Ea
    obtain ⟨_, _, Ebb, Ebg, Eby⟩ := ProofShape.liftN_app_inv Eb
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Eaa
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Ebb
    rw [← Ef] at Eaf
    rw [← Ex] at Eax
    rw [← Eg] at Ebg
    rw [← Ey] at Eby
    obtain ⟨rawA, rawBody, EfLam, EA, _⟩ := ProofShape.liftN_lam_inv Eaf
    obtain ⟨A, body, rfl, hnf, EDom, EBody⟩ := erase_lam_inv EfLam
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    obtain ⟨⟨u, hA⟩, C, hbody⟩ := hf.lam_inv henv hΓ
    have hfPi := HasType.lam hA hbody
    have hng := not_isProof_fn hΓ hg hy hnb
    have HF' : JointCompare Step (proofEraseCtx Γ') false
        ((proofErase Γ (.lam A body)).liftN n k) ((proofErase Γ g).liftN n k) := by
      simpa only [Eaf, Ebg] using HF
    have Hfg := (proofErase_joint_compare_descend hcert.descent hΓ hΓ' W rfl hf hg HF').2
      rfl hnf hng
    have HfgPi := Hfg.of_l henv hΓ hfPi
    have hxA := argument_at_displayed_domain hΓ hf hfPi hx
    have hyA := argument_at_displayed_domain hΓ hg HfgPi.hasType.2 hy
    have HX' : JointCarrierGuard Step (proofEraseCtx Γ') ((proofErase Γ A).liftN n k)
        ((proofErase Γ x).liftN n k) ((proofErase Γ y).liftN n k) := by
      simpa only [EDom, EA, Eax, Eby] using HX
    have Hxy := proofErase_joint_carrier_descend hcert.descent hΓ hΓ' W hxA hyA HX'
    have CF := (proofErase_joint_compare_certificate_descend hcert hΓ hΓ' W rfl hf hg HF').2
      rfl hnf hng
    have CX := proofErase_joint_carrier_certificate_descend hcert hΓ hΓ' W hxA hyA HX'
    refine ⟨?_, _, IsDefEq.appDF HfgPi (Hxy.of_l henv hΓ hxA)⟩
    rw [show proofErase Γ (.app (.lam A body) x) = .app _ _ from if_neg hna,
      show proofErase Γ (.app g y) = .app _ _ from if_neg hnb]
    rw [EfLam, ← EDom, ← EBody] at CF ⊢
    exact .intro CF CX

/-- In the full joint union the displayed-domain rule retains its exact lower
certificate as well as semantic equality, without any arbitrary primitive
substitution assumption. -/
theorem proofErase_joint_displayed_lambda_application_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (H : DisplayedLambdaApplication (ErasedJointUnion D) (proofEraseCtx Γ')
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    DisplayedLambdaApplication (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ b) ∧ env.IsDefEqU univs Γ a b :=
  proofErase_displayed_lambda_application_descend (erased_joint_union_certificate_descent heq hs)
    hΓ hΓ' W ha hb H

end Lean4Lean.VEnv.Strengthening
