import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertConstructorFrames
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnusedBodyBeta

/-! # Retain comparison when deleting unused lambda binders

Inferred comparison of constant functions returns a comparison of their lower
payloads at the same Pi-inert stage. Both annotations may change internally.
This consumes actual terminal body certificates in their recorded contexts;
it does not infer general substitution or beta closure of the checker.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private eta_unused_body
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointUnusedBodyBeta
open private isProof_congr
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- A terminal inferred comparison of two constant lambdas descends to their
independently typed nonproof payloads. Either annotation may scope the body
child; eta instead supplies a beta path between the lower payloads. -/
theorem InferredLambdaTerminal.pi_inert_unused_payload
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b)
    (H : InferredLambdaTerminal (PiInertStage D n) (proofEraseCtx Γ)
      (proofErase Γ A) ((proofErase Γ a).liftN 1)
      (proofErase Γ B) ((proofErase Γ b).liftN 1)) :
    ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) false
      (proofErase Γ a) (proofErase Γ b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, v, hB⟩
  rcases H.body_cases with ⟨_, E⟩ | HL | HR | HE
  · have E' := ProofShape.liftN_inj.1 E
    rw [E']; exact .leaf .refl
  · exact (proofErase_computed_joint_compare_certificate_descend
      (pi_inert_stage_certificate_descent heq hs n) hΓ hΓA Ctx.LiftN.one
      rfl ha hb HL).2 rfl hna hnb
  · exact (proofErase_computed_joint_compare_certificate_descend
      (pi_inert_stage_certificate_descent heq hs n) hΓ hΓB Ctx.LiftN.one
      rfl ha hb HR).2 rfl hna hnb
  · rcases HE with HE | HE
    · exact .compute (.beta (eta_unused_body HE)) .refl (.leaf .refl)
    · exact .compute .refl (.beta (eta_unused_body HE)) (.leaf .refl)

/-- Full inferred comparison of constant functions retains an inferred
comparison of their original lower payloads at the same finite stage.
Computation, symmetry, sorted-domain rules and eta are all included. The two
written domains and payload types may differ; both payloads omit the binder. -/
theorem pi_inert_inferred_constant_lambda_payload
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b)
    (H : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) false
      (.lam (proofErase Γ A) ((proofErase Γ a).liftN 1))
      (.lam (proofErase Γ B) ((proofErase Γ b).liftN 1))) :
    ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) false
      (proofErase Γ a) (proofErase Γ b) := by
  obtain ⟨X, x, Y, y, RX, RY, HT⟩ := H.pi_inert_lambda_cut
  obtain ⟨A', a', HA, Ha, EX, RA⟩ := pi_inert_constant_lambda_readout heq hs hΓ hA ha rfl RX
  obtain ⟨B', b', HB, Hb, EY, RB⟩ := pi_inert_constant_lambda_readout heq hs hΓ hB hb rfl RY
  cases EX
  cases EY
  have HC := HT.pi_inert_unused_payload heq hs hΓ HA.hasType.2 HB.hasType.2
    Ha.hasType.2 Hb.hasType.2 (mt (isProof_congr hΓ Ha).2 hna) (mt (isProof_congr hΓ Hb).2 hnb)
  exact .compute RA RB HC

/-- The same payload comparison survives arbitrary independent function
computations before the supplied inferred check. Consequently an application
rule can consume its function child without recovering or comparing either
discarded argument. This does not contract arbitrary enclosing computations. -/
theorem pi_inert_computed_constant_functions_payload
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs Γ B (.sort v))
    (ha : env.HasType univs Γ a T) (hb : env.HasType univs Γ b U)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b)
    (RA : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (.lam (proofErase Γ A) ((proofErase Γ a).liftN 1)) f)
    (RB : ScopedCompute (PiInertStage D n) (proofEraseCtx Γ)
      (.lam (proofErase Γ B) ((proofErase Γ b).liftN 1)) g)
    (H : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) false f g) :
    ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) false
      (proofErase Γ a) (proofErase Γ b) :=
  pi_inert_inferred_constant_lambda_payload heq hs hΓ hA hB ha hb hna hnb (.compute RA RB H)

/-- Paired head beta of constant sort-valued functions preserves comparison
at every Pi-inert stage. Their actual arguments may be unrelated and need no
native recovery or carrier certificate: the erased bodies omit those arguments.
Only the inferred function comparison is consumed, as at an application node. -/
theorem proofErase_pi_inert_unused_sort_head_beta {rawa rawb : ProofShape}
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort w)) (hB : env.HasType univs Γ B (.sort z))
    (ha : env.HasType univs (A :: Γ) a (.sort u))
    (hb : env.HasType univs (B :: Γ) b (.sort v))
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y B)
    (EA : proofErase (A :: Γ) a = rawa.liftN 1)
    (EB : proofErase (B :: Γ) b = rawb.liftN 1)
    (H : ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) false
      (proofErase Γ (.lam A a)) (proofErase Γ (.lam B b))) :
    ComputedJointCompare (PiInertStage D n) (proofEraseCtx Γ) true
      (proofErase Γ (a.inst x)) (proofErase Γ (b.inst y)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, w, hA⟩
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, z, hB⟩
  have hax : env.HasType univs Γ (a.inst x) (.sort u) := by
    simpa only [VExpr.inst] using ha.instN henv Ctx.InstN.zero hx
  have hby : env.HasType univs Γ (b.inst y) (.sort v) := by
    simpa only [VExpr.inst] using hb.instN henv Ctx.InstN.zero hy
  have EX : proofErase Γ (a.inst x) = rawa := by
    rw [proofErase_instN hΓA hx Ctx.InstN.zero ha, EA]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id]
  have EY : proofErase Γ (b.inst y) = rawb := by
    rw [proofErase_instN hΓB hy Ctx.InstN.zero hb, EB]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
      ProofShape.lift_subst_cons, ProofShape.subst_id]
  have EF : proofErase Γ (.lam A a) = .lam (proofErase Γ A) (rawa.liftN 1) := by
    rw [show proofErase Γ (.lam A a) = .lam (proofErase Γ A) (proofErase (A :: Γ) a)
      from if_neg (not_isProof_function_to_sort hΓ (.lam hA ha)), EA]
  have EG : proofErase Γ (.lam B b) = .lam (proofErase Γ B) (rawb.liftN 1) := by
    rw [show proofErase Γ (.lam B b) = .lam (proofErase Γ B) (proofErase (B :: Γ) b)
      from if_neg (not_isProof_function_to_sort hΓ (.lam hB hb)), EB]
  apply ComputedJointCompare.common
  apply pi_inert_inferred_constant_lambda_payload heq hs hΓ hA hB hax hby
    (not_isProof_of_sort hΓ hax) (not_isProof_of_sort hΓ hby)
  simpa only [EF, EG, EX, EY] using H

end Lean4Lean.VEnv.Strengthening
