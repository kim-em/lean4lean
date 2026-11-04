import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeImages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointPrimitiveRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointTransport

/-! # Exactly recoverable images at a fixed guarded stage

The image condition is explicit and extends under typed binders. Recovery
transport uses only forward source replay and typed computation transport;
no confluence or backward recovery of a selected type is needed.
-/
namespace Lean4Lean.VEnv.Strengthening.ExactStageSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]
variable {D : PureObservation.Definitions} {k later : Nat}

/-- Every retained variable image recovers its exact substituted oracle type
at the common finite stage `k`. Proof images and absent variables are excluded. -/
def Images (D : PureObservation.Definitions) (k : Nat)
    (Γ Γ₀ : List VExpr) (τ : ProofShape.Subst) : Prop :=
  NativeImageTransport.Images (ErasedComputedJointStage D k) Γ Γ₀ τ

/-- Exact image recovery extends under a binder without increasing its stage. -/
theorem Images.cons (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (hA : env.HasType univs Γ A (.sort u)) (H : Images D k Γ Γ₀ τ) :
    Images D k (A :: Γ) (A.subst σ :: Γ₀) τ.lift :=
  NativeImageTransport.Images.cons (erased_computed_joint_stage_rename heq hs k) hΓ₀ W ES hA H

/-- One exactly recoverable argument gives the required images for instantiation. -/
theorem Images.inst
    (H : ScopedTypeRecovery (ErasedComputedJointStage D k) (proofEraseCtx Γ)
      (proofErase Γ p) (proofErase Γ T)) :
    Images D k (T :: Γ) Γ (ProofShape.Subst.one (proofErase Γ p)) :=
  NativeImageTransport.Images.inst H

/-- An interpreted substitution with exactly recovering images at a fixed finite stage in each
typed realization of its source erasure. -/
def ImageSubstitution (D : PureObservation.Definitions) (k : Nat)
    (Δ Δ' : List ProofShape) (τ : ProofShape.Subst) : Prop :=
  NativeImageTransport.ImageSubstitution (ErasedComputedJointStage D k) Δ Δ' τ

/-- Forgetting image information gives ordinary interpreted substitution. -/
theorem ImageSubstitution.interpretation (W : ImageSubstitution D k Δ Δ' τ) :
    ContextSubstitution Δ Δ' τ :=
  NativeImageTransport.ImageSubstitution.interpretation W

/-- The exact image condition extends through arbitrary typed binder realizations. -/
theorem ImageSubstitution.cons (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (W : ImageSubstitution D k Δ Δ' τ) :
    ImageSubstitution D k (A :: Δ) (A.subst τ :: Δ') τ.lift :=
  NativeImageTransport.ImageSubstitution.cons (erased_computed_joint_stage_rename heq hs k) W

/-- One actual source context suffices to certify the interpreted image
condition. Equal-erasure source realizations convert to that context. -/
theorem ImageSubstitution.of_typed
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : Images D k Γ Γ₀ τ) :
    ImageSubstitution D k (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ :=
  NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI

end Lean4Lean.VEnv.Strengthening.ExactStageSubstitution
