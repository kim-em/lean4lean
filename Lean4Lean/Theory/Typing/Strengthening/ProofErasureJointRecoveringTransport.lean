import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveringSubstitution

/-! # Joint checking under exact recoverable substitutions

Exact selected recovery replaces re-synthesis. The carrier induction hypothesis
then supplies the guard at that same substituted domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- All checking modes transport through substitutions with exactly recoverable non-proof
images, assuming only source descent and typed primitive transport. -/
theorem ProofShape.JointCheck.subst_recovering_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ContextRenaming Δ Δ' τ → Image Δ' (a.subst τ) (b.subst τ))
    (hinc : ∀ {Δ a b}, Image Δ a b → Target Δ a b)
    (htrans : RecoveringPrimitiveTransport Image Step Target)
    (H : JointCheck Step Δ kind sa sb) :
    JointTransportResult (RecoveringSubstitution Image) Target Δ kind sa sb := by
  apply H.transport (RecoveringSubstitution Image) hstep (fun W => W.cons hrename) (fun W S => W.sort S)
    (fun R hΓ ht EΓ Ee W => R.subst_recovering hstep hrename htrans hΓ ht EΓ Ee W)
  intro Γ Δ' τ f x y D C A B hΓ hf hx hy R HX W HX'
  exact ⟨A.subst τ, B.subst τ.lift, R.subst_recovering hstep hrename hinc htrans hΓ hf rfl rfl W, HX'⟩

/-- Common-typed joint comparison transports without domain re-synthesis when
all retained images recover their exact transported oracle assignments. -/
theorem ProofShape.JointCompare.subst_recovering
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ContextRenaming Δ Δ' τ → Image Δ' (a.subst τ) (b.subst τ))
    (hinc : ∀ {Δ a b}, Image Δ a b → Target Δ a b)
    (htrans : RecoveringPrimitiveTransport Image Step Target)
    (H : JointCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : RecoveringSubstitution Image Δ Δ' τ) : JointCompare Target Δ' mode (sa.subst τ) (sb.subst τ) :=
  H.subst_recovering_typed hstep hrename hinc htrans hΓ ha hb EΓ Ea Eb W

/-- Explicit carriers transport with their exact substituted syntax under the
same exact-image condition, including all nested recovered applications. -/
theorem ProofShape.JointCarrierGuard.subst_recovering
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Image Δ a b → ContextRenaming Δ Δ' τ → Image Δ' (a.subst τ) (b.subst τ))
    (hinc : ∀ {Δ a b}, Image Δ a b → Target Δ a b)
    (htrans : RecoveringPrimitiveTransport Image Step Target)
    (H : JointCarrierGuard Step Δ α sa sb)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Eα : proofErase Γ A = α)
    (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : RecoveringSubstitution Image Δ Δ' τ) :
    JointCarrierGuard Target Δ' (α.subst τ) (sa.subst τ) (sb.subst τ) :=
  H.subst_recovering_typed hstep hrename hinc htrans hΓ ha hb EΓ Eα Ea Eb W

end Lean4Lean.VEnv.Strengthening
