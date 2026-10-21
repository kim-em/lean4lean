import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedFamilyPrefixes
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Future body certificates at computationally joined arguments

A common typed realization of the argument join instantiates the stored body
certificate once. Certified image computation then transports the two actual
instantiations to those residuals, retaining every future beta/substitution
comparison. Lambda applications are handled by their displayed beta steps.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A stored future body comparison instantiates at any typed argument while
retaining all future comparisons, including beta redexes created by instantiation. -/
theorem proofErase_family_inst
    (hΓA : OnCtx (A :: Γ) (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (A :: Γ) c C)
    (H : BetaStableFamily (fun Δ => JointCompare Step Δ true)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) (proofErase (A :: Γ) c)) :
    BetaStableFamily (fun Δ => JointCompare Step Δ true) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst x)) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have HI := H.subst (ContextSubstitution.of_typed hΓA.1 W (erasedSubstAgreement_one hΓA hx))
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb, proofErase_instN hΓA hx Ctx.InstN.zero hc]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HI

/-- Certified argument computation propagates through every occurrence in a
typed body. Primitive renaming suffices, with no recovery premise on the image. -/
theorem proofErase_certified_compute_inst_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ x) out) :
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) ((proofErase (A :: Γ) b).inst out) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have H := proofErase_compute_subst_images_of_renaming
    (fun H W => erased_beta_stable_joint_subst heq hs H W.interpretation)
    hΓA.1 W hb (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one out) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

/-- Paired instantiation is constructive for future body certificates when the
arguments have a certified computational join. The resulting bodies need not
join: their future comparison is retained from the original body certificate. -/
theorem proofErase_family_inst_joined
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (A :: Γ) c C)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) (proofErase (A :: Γ) c))
    (RX : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ y) shared) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  obtain ⟨z, HZ, EZ⟩ := proofErase_scoped_compute_realize
    (erased_beta_stable_joint_descent heq hs) hΓA.1 hx rfl rfl RX
  have hz := HZ.hasType.2
  have HI := proofErase_family_inst hΓA hz hb hc H
  have RB := proofErase_certified_compute_inst_argument heq hs hΓA hb hx RX
  have RC := proofErase_certified_compute_inst_argument heq hs hΓA hc hy RY
  rw [← EZ, ← proofErase_instN hΓA hz Ctx.InstN.zero hb] at RB
  rw [← EZ, ← proofErase_instN hΓA hz Ctx.InstN.zero hc] at RC
  exact HI.certified_prefixes heq hs hΓA.1 (hb.instN henv Ctx.InstN.zero hx)
    (hc.instN henv Ctx.InstN.zero hy) RB RC

/-- Two displayed lambdas with future-related bodies apply to independently
computed arguments with a certified join. Their beta redexes contract before
the residual comparison; the output retains arbitrary future substitution and
beta paths rather than only one immediate common-mode comparison. -/
theorem proofErase_family_apply_lams_joined
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (A :: Γ) c C)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) (proofErase (A :: Γ) c))
    (RX : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ) (proofErase Γ y) shared) :
    BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) (proofErase Γ (.app (.lam A c) y)) := by
  have ha := HasType.app (HasType.lam hA hb) hx
  have hd := HasType.app (HasType.lam hA hc) hy
  exact (proofErase_family_inst_joined heq hs ⟨hΓ, u, hA⟩ hb hc hx hy H RX RY).certified_prefixes
    heq hs hΓ ha hd (.beta (proofErase_beta_forward hΓ ha .beta))
    (.beta (proofErase_beta_forward hΓ hd .beta))

end Lean4Lean.VEnv.Strengthening
