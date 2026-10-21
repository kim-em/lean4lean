import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRelatedTypes
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCertifiedChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainPullback

/-! # Typed structural conversions interleaved with beta paths

The local structural relation preserves visible heads; general type equality
need not. Finite typed paths combine that relation with beta reduction
and expansion. Full certified carrier and context checking transports along
these paths; expression endpoints remain fixed throughout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- A finite path of actual types at one sort. Structural edges carry both
actual equality and the proposed erased relation. Beta edges carry actual
endpoint typings and an erased beta path, in either direction. There is no
coverage assumption for arbitrary definitional equality. -/
inductive TypeChangePath (Rel : Nat → ProofShape → ProofShape → Prop)
    (Γ : List VExpr) (u : VLevel) : VExpr → VExpr → Prop where
  | refl : env.HasType univs Γ A (.sort u) → TypeChangePath Rel Γ u A A
  | related : env.IsDefEq univs Γ A B (.sort u) →
      Rel 0 (proofErase Γ A) (proofErase Γ B) → TypeChangePath Rel Γ u A B
  | beta : env.HasType univs Γ A (.sort u) → env.HasType univs Γ B (.sort u) →
      ProofShape.BetaRed (proofErase Γ A) (proofErase Γ B) → TypeChangePath Rel Γ u A B
  | beta_back : env.HasType univs Γ A (.sort u) → env.HasType univs Γ B (.sort u) →
      ProofShape.BetaRed (proofErase Γ B) (proofErase Γ A) → TypeChangePath Rel Γ u A B
  | trans : TypeChangePath Rel Γ u A B → TypeChangePath Rel Γ u B C → TypeChangePath Rel Γ u A C

/-- Every edge is an actual type conversion. Beta reflection constructs the
conversion for beta edges from their endpoint typings. -/
theorem TypeChangePath.defeq (H : TypeChangePath Rel Γ u A B)
    (hΓ : OnCtx Γ (env.IsType univs)) : env.IsDefEq univs Γ A B (.sort u) := by
  induction H with
  | refl hA => exact hA
  | related HE _ => exact HE
  | beta hA hB R => exact proofErase_beta_join_reflect hΓ hA hB R .refl
  | beta_back hA hB R => exact proofErase_beta_join_reflect hΓ hA hB .refl R
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A symmetric structural relation gives reversible typed paths, including
all beta expansions and reductions. -/
theorem TypeChangePath.symm (hsym : ∀ {k a b}, Rel k a b → Rel k b a)
    (H : TypeChangePath Rel Γ u A B) : TypeChangePath Rel Γ u B A := by
  induction H with
  | refl hA => exact .refl hA
  | related HE HR => exact .related HE.symm (hsym HR)
  | beta hA hB R => exact .beta_back hB hA R
  | beta_back hA hB R => exact .beta hB hA R
  | trans _ _ ih₁ ih₂ => exact ih₂.trans ih₁

/-- Under substitution-closed primitives, comparison pulls back along a
computation of the binder annotation in the same relation. Exact recovery of
the reduced annotation is obtained from the original variable declaration. -/
theorem proofErase_joint_context_compute_back
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (R : ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (B :: Γ) a T) (hb : env.HasType univs (B :: Γ) b T)
    (H : JointCompare Step (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b)) :
    JointCompare Step (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have W := RecoveringSubstitution.of_domain_compute
    (fun H W => hsubst H W.interpretation) hΓ HAB R
  have HC := H.subst_recovering hstep (fun H W => hsubst H W.interpretation)
    (fun H => H) (fun _ _ _ W H => .base (hsubst H W.interpretation))
    hΓB ha hb rfl rfl rfl W
  simp only [ProofShape.subst_id] at HC
  have WC : IsDefEqCtx env univs [] (B :: Γ) (A :: Γ) := .succ (.refl hΓ) HAB.symm
  rwa [proofErase_defeqCtx hΓB WC ha, proofErase_defeqCtx hΓB WC hb] at HC

private theorem certified_carrier_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (R : ProofShape.BetaRed (proofErase Γ A) target)
    (H : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      target (proofErase Γ a) (proofErase Γ b) := by
  have W : ContextOracleBeta (proofEraseCtx Γ) (proofEraseCtx Γ) :=
    ⟨ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ)), fun _ => .refl⟩
  exact proofErase_beta_stable_joint_oracle_beta heq hs H hΓ ha hb rfl rfl rfl rfl W target R

private theorem certified_context_beta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (R : ProofShape.BetaRed (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have WC : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have W : ContextOracleBeta (proofEraseCtx Γ) (proofEraseCtx Γ) :=
    ⟨ContextSubstitution.of_defeqCtx hΓ (.zero (Γ₀ := Γ)), fun _ => .refl⟩
  have HC := proofErase_beta_stable_joint_oracle_beta heq hs H hΓA ha hb rfl rfl rfl (W.cons R)
  rwa [proofErase_defeqCtx hΓA WC ha, proofErase_defeqCtx hΓA WC hb] at HC

/-- Full certified carrier guards transport along any finite mixture of
structural type changes, beta reductions and beta expansions. Every
intermediate guard remains certified, so the operations may be iterated. -/
theorem TypeChangePath.carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (L : TypeChangeLaws (ErasedBetaStableJoint D) Rel)
    (hΓ : OnCtx Γ (env.IsType univs)) (P : TypeChangePath Rel Γ u A B)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard (ErasedBetaStableJoint D) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ a) (proofErase Γ b) := by
  induction P with
  | refl => exact H
  | related HE HR =>
    exact proofErase_joint_related_carrier (erased_beta_stable_joint_descent heq hs)
      (erased_beta_stable_joint_subst heq hs) L hΓ ha hb HE.toU HR H
  | beta _ _ R => exact certified_carrier_beta heq hs hΓ ha hb R H
  | beta_back _ _ R => exact .carrierCompute (.beta R) H
  | trans P Q ihP ihQ =>
    exact ihQ ((P.defeq hΓ).defeq ha) ((P.defeq hΓ).defeq hb) (ihP ha hb H)

/-- Full certified body comparison survives each edge of the same typed
path. Beta expansion uses exact recovered annotations; structural edges use
the general local-law theorem. Endpoint beta stability is not a premise. -/
theorem TypeChangePath.context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (L : TypeChangeLaws (ErasedBetaStableJoint D) Rel)
    (hΓ : OnCtx Γ (env.IsType univs)) (P : TypeChangePath Rel Γ u A B)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    JointCompare (ErasedBetaStableJoint D) (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b) := by
  induction P with
  | refl => exact H
  | related HE HR =>
    exact proofErase_joint_related_context (erased_beta_stable_joint_descent heq hs)
      (erased_beta_stable_joint_subst heq hs) L hΓ HE HR ha hb H
  | beta hA hB R =>
    exact certified_context_beta heq hs hΓ (proofErase_beta_join_reflect hΓ hA hB R .refl) R ha hb H
  | beta_back hA hB R =>
    exact proofErase_joint_context_compute_back (erased_beta_stable_joint_descent heq hs)
      (erased_beta_stable_joint_subst heq hs) hΓ
      (proofErase_beta_join_reflect hΓ hB hA R .refl) (.beta R) ha hb H
  | trans P Q ihP ihQ =>
    have W := IsDefEqCtx.succ (.refl hΓ) (P.defeq hΓ)
    exact ihQ (ha.defeqDFC henv W) (hb.defeqDFC henv W) (ihP ha hb H)

end Lean4Lean.VEnv.Strengthening
