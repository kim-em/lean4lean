import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStableEqComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCertifiedJoinFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointImageComputation

/-! # Recursive cast computation from explicit endpoint joins

Each cast stores two smaller computations of its endpoint types to a common
shape. Structural interpretation constructs the existing certified singleton
computation and its future beta/substitution certificates. No future-transport
oracle is stored in this grammar. Typed substitution and pointwise image
computation retain the grammar and are interpreted by the same induction.
The core here is ordinary delta/iota/beta;
arbitrary level-core or singleton-stage confluence is not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- A future certificate between the actual endpoint types licenses complete
cast removal in the existing beta/substitution-stable computation relation.
Proof-valued casts are included. Semantic endpoint equality is derived. -/
theorem proofErase_typeCast_certified
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X)
    (H : BetaStableFamily (fun Δ => JointCompare (ErasedJointUnion D) Δ true)
      (proofEraseCtx Γ) (proofErase Γ X) (proofErase Γ Y)) :
    ScopedCompute (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ (typeCast u X Y q x)) (proofErase Γ x) := by
  have HXY := proofErase_joint_carrier_reflect (erased_joint_union_descent heq hs)
    hΓ hX hY (.carrierChecked H.base)
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ HXY hq hx
  by_cases hp : IsProof Γ (typeCast u X Y q x)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)]
    exact .refl
  have hxnp : ¬ IsProof Γ x := fun H => hp ((isProof_congr hΓ HC).2 H)
  obtain ⟨_, _, hprefix, hmajor⟩ := HC.hasType.1.app_inv henv hΓ
  have RP := proofErase_stable_eq_prefix heq hs hregistry hΓ hprefix
    (not_isProof_fn hΓ hprefix hmajor hp) H
  have HB := IsDefEq.beta (HC.hasType.2.weak henv (B := eqApp (.succ u) (.sort u) X Y)) hq
  simp only [VExpr.inst_lift] at HB
  have hnApp := fun H => hxnp ((isProof_congr hΓ HB).1 H)
  have RB := proofErase_beta_forward hΓ HB.hasType.1 VExpr.BetaRed.beta
  simp only [VExpr.inst_lift] at RB
  rw [show proofErase Γ (.app (.lam (eqApp (.succ u) (.sort u) X Y) x.lift) q) =
      .app (proofErase Γ (.lam (eqApp (.succ u) (.sort u) X Y) x.lift)) (proofErase Γ q)
      from if_neg hnApp] at RB
  rw [show proofErase Γ (typeCast u X Y q x) =
      .app (proofErase Γ (eqRecBeforeMajor u (.succ u) (.sort u) X (castMotive u X) x Y))
        (proofErase Γ q) from if_neg hp]
  exact ScopedCompute.trans (ScopedCompute.app (.base RP) .refl) (.beta RB)

/-- Finite computations with recursively joined cast endpoints. The two child
paths, rather than semantic conversion or a future-comparison premise, justify
each cast. Compatible contexts and sequential computation are unrestricted.
The images rule propagates child computations through an arbitrary typed
consumer; subst retains an entire computation under actual typed substitution.
Neither constructor stores a postulated transport law. -/
inductive RecursiveCastCompute (D : Definitions) :
    List ProofShape → ProofShape → ProofShape → Prop where
  | core : ProofShape.Compute (ErasedIotaPrimitive D) a b → RecursiveCastCompute D Δ a b
  | cast (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
      (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
      (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
      (hx : env.HasType univs Γ x X)
      (RX : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ X) shared)
      (RY : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ Y) shared) :
      RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ (typeCast u X Y q x)) (proofErase Γ x)
  | trans : RecursiveCastCompute D Δ a b → RecursiveCastCompute D Δ b c → RecursiveCastCompute D Δ a c
  | app : RecursiveCastCompute D Δ f f' → RecursiveCastCompute D Δ a a' →
      RecursiveCastCompute D Δ (.app f a) (.app f' a')
  | proj : RecursiveCastCompute D Δ m m' → RecursiveCastCompute D Δ (.proj s i m) (.proj s i m')
  | lam : RecursiveCastCompute D Δ A A' → RecursiveCastCompute D (A :: Δ) b b' →
      RecursiveCastCompute D Δ (.lam A b) (.lam A' b')
  | forallE : RecursiveCastCompute D Δ A A' → RecursiveCastCompute D (A :: Δ) B B' →
      RecursiveCastCompute D Δ (.forallE A B) (.forallE A' B')
  | images (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
      (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) (W' : Ctx.SubstEq env univs Γ₀ τ τ Γ)
      (ht : env.HasType univs Γ e T)
      (R : ∀ i, RecursiveCastCompute D (proofEraseCtx Γ₀)
        (proofErase Γ₀ (σ i)) (proofErase Γ₀ (τ i))) :
      RecursiveCastCompute D (proofEraseCtx Γ₀)
        (proofErase Γ₀ (e.subst σ)) (proofErase Γ₀ (e.subst τ))
  | subst (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
      (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
      (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
      (R : RecursiveCastCompute D (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
      RecursiveCastCompute D (proofEraseCtx Γ₀)
        (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ))

/-- Structural interpretation constructs a certified computation at the exact
original endpoints. A cast's two child induction hypotheses construct its
future endpoint certificate, so certification is not an additional assumption. -/
theorem RecursiveCastCompute.certified
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (R : RecursiveCastCompute D Δ a b) : ScopedCompute (ErasedBetaStableJoint D) Δ a b := by
  induction R with
  | core R => exact R.scoped (fun H => .base (.inl H))
  | cast hu hΓ hX hY hq hx _ _ ihX ihY =>
    exact proofErase_typeCast_certified heq hs hregistry hu hΓ hX hY hq hx
      (proofErase_certified_join_family heq hs hΓ hX hY ihX ihY)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂
  | @images Γ₀ σ Γ τ e T hΓ₀ W W' ht _ ih =>
    have ES : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
    have ET : ErasedSubstAgreement Γ Γ₀ τ (fun i => proofErase Γ₀ (τ i)) := fun _ _ => rfl
    have H := proofErase_compute_subst_images_of_renaming
      (fun H W => erased_beta_stable_joint_subst heq hs H W.interpretation)
      hΓ₀ W ht ES ih
    rw [← proofErase_subst_with hΓ₀ W ht ES, ← proofErase_subst_with hΓ₀ W' ht ET] at H
    exact H
  | @subst Γ₀ σ Γ a A b B hΓ₀ W ha hb _ ih =>
    have ES : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
    have H := ih.subst (erased_beta_stable_joint_subst heq hs) (ContextSubstitution.of_typed hΓ₀ W ES)
    rw [← proofErase_subst_with hΓ₀ W ha ES, ← proofErase_subst_with hΓ₀ W hb ES] at H
    exact H

/-- Every interpreted recursive computation belongs to an actual finite joint
stage. The finite bound may depend on its generated endpoint certificates. -/
theorem RecursiveCastCompute.finite_stage
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (R : RecursiveCastCompute D Δ a b) :
    ∃ n, ScopedCompute (ErasedJointStage D n) Δ a b :=
  ((R.certified heq hs hregistry).mono erased_beta_stable_joint_into_union).finite_stage erased_joint_stage_mono

end Lean4Lean.VEnv.Strengthening
