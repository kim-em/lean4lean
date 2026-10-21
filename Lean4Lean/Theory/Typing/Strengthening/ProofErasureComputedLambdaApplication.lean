import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDisplayedLambdaApplication

/-! # Reading an application domain after function computation

A function need not already display a lambda to supply its argument domain.
A computation exposing one suffices. The function comparison still concerns
the original endpoints: no forward transport of comparison through that
computation is assumed. Exact binder descent preserves all three premises.
This is a local rule, not recursive coverage or proposition beta stability.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_app_inv erase_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.liftN_app_inv ProofShape.liftN_lam_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params]

/-- Application checking using only a domain exposed by computation of the
left function. The original function endpoints must compare in inferred mode;
the computed lambda's body has no recovery requirement. -/
inductive ComputedLambdaApplication
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro : ScopedCompute Step Δ f (.lam A body) →
      JointCompare Step Δ false f g → JointCarrierGuard Step Δ A x y →
      ComputedLambdaApplication Step Δ (.app f x) (.app g y)

/-- A syntactically displayed domain is the zero-computation special case. -/
theorem DisplayedLambdaApplication.computed
    (H : DisplayedLambdaApplication Step Δ a b) :
    ComputedLambdaApplication Step Δ a b := by
  cases H with
  | intro HF HX => exact .intro .refl HF HX

/-- Exact certificate descent reconstructs the exposed lambda from the lower
function's computation. The resulting annotation types both arguments, even
when the original functions have no native Pi recovery. No comparison is
transported forward along computation. -/
theorem proofErase_computed_lambda_application_descend
    (hcert : ErasedScopedPrimitiveCertificateDescent Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (H : ComputedLambdaApplication Step (proofEraseCtx Γ')
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    ComputedLambdaApplication Target (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b) ∧
      env.IsDefEqU univs Γ a b := by
  generalize Ea : (proofErase Γ a).liftN n k = sa at H
  generalize Eb : (proofErase Γ b).liftN n k = sb at H
  cases H with
  | intro RF HF HX =>
    obtain ⟨_, _, Eaa, Eaf, Eax⟩ := ProofShape.liftN_app_inv Ea
    obtain ⟨_, _, Ebb, Ebg, Eby⟩ := ProofShape.liftN_app_inv Eb
    obtain ⟨f, x, rfl, hna, Ef, Ex⟩ := erase_app_inv Eaa
    obtain ⟨g, y, rfl, hnb, Eg, Ey⟩ := erase_app_inv Ebb
    rw [← Ef] at Eaf
    rw [← Ex] at Eax
    rw [← Eg] at Ebg
    rw [← Ey] at Eby
    obtain ⟨_, _, hf, hx⟩ := ha.app_inv henv hΓ
    obtain ⟨_, _, hg, hy⟩ := hb.app_inv henv hΓ
    have RF' := Eaf ▸ RF
    obtain ⟨f', HE, RC, EC⟩ := proofErase_scoped_compute_certificate_descend
      hcert hΓ hΓ' W hf rfl RF'
    obtain ⟨_, _, EfLam, EA, _⟩ := ProofShape.liftN_lam_inv EC
    obtain ⟨A, body, rfl, _, EDom, EBody⟩ := erase_lam_inv EfLam
    obtain ⟨⟨u, hA⟩, C, hbody⟩ := HE.hasType.2.lam_inv henv hΓ
    have hfPi := ((show env.IsDefEqU univs Γ f (.lam A body) from ⟨_, HE⟩).of_r
      henv hΓ (HasType.lam hA hbody)).hasType.1
    have hnf := not_isProof_fn hΓ hf hx hna
    have hng := not_isProof_fn hΓ hg hy hnb
    have HF' : JointCompare Step (proofEraseCtx Γ') false
        ((proofErase Γ f).liftN n k) ((proofErase Γ g).liftN n k) := by
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
    rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hna,
      show proofErase Γ (.app g y) = .app _ _ from if_neg hnb]
    rw [EfLam, ← EDom, ← EBody] at RC
    exact .intro RC CF CX

/-- The full joint union supports the computed-domain rule with exact lower
certificates, without a substitution or forward beta-stability hypothesis. -/
theorem proofErase_joint_computed_lambda_application_descend
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (H : ComputedLambdaApplication (ErasedJointUnion D) (proofEraseCtx Γ')
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k)) :
    ComputedLambdaApplication (ErasedJointUnion D) (proofEraseCtx Γ)
      (proofErase Γ a) (proofErase Γ b) ∧ env.IsDefEqU univs Γ a b :=
  proofErase_computed_lambda_application_descend (erased_joint_union_certificate_descent heq hs)
    hΓ hΓ' W ha hb H

end Lean4Lean.VEnv.Strengthening
