import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRetainedRenaming

/-! # Joint checking under retained-variable transport

Exact selected recovery replaces re-synthesis. The carrier induction hypothesis
then supplies the guard at that same substituted domain.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- All checking modes transport through substitutions that rename retained
variables, assuming only source descent and typed primitive transport. -/
theorem ProofShape.JointCheck.rename_retained_typed
    (hstep : ErasedScopedPrimitiveDescent Step) (htrans : RetainedPrimitiveTransport Step Target)
    (H : JointCheck Step Δ kind sa sb) :
    JointTransportResult RetainedRenaming Target Δ kind sa sb := by
  apply H.transport RetainedRenaming hstep (fun W => W.cons) (fun W S => W.sort S)
    (fun R hΓ ht EΓ Ee W => R.rename_retained hstep htrans hΓ ht EΓ Ee W)
  intro Γ Δ' τ f x y D C A B hΓ hf hx hy R HX W HX'
  exact ⟨A.subst τ, B.subst τ.lift, R.rename_retained hstep htrans hΓ hf rfl rfl W, HX'⟩

/-- Common-typed joint comparison transports without domain re-synthesis when
all retained variable images have their exact transported oracle assignments. -/
theorem ProofShape.JointCompare.rename_retained
    (hstep : ErasedScopedPrimitiveDescent Step) (htrans : RetainedPrimitiveTransport Step Target)
    (H : JointCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : RetainedRenaming Δ Δ' τ) : JointCompare Target Δ' mode (sa.subst τ) (sb.subst τ) :=
  H.rename_retained_typed hstep htrans hΓ ha hb EΓ Ea Eb W

/-- Explicit carriers transport with their exact substituted syntax under the
same retained-variable condition, including all nested recovered applications. -/
theorem ProofShape.JointCarrierGuard.rename_retained
    (hstep : ErasedScopedPrimitiveDescent Step) (htrans : RetainedPrimitiveTransport Step Target)
    (H : JointCarrierGuard Step Δ α sa sb)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Eα : proofErase Γ A = α)
    (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : RetainedRenaming Δ Δ' τ) :
    JointCarrierGuard Target Δ' (α.subst τ) (sa.subst τ) (sb.subst τ) :=
  H.rename_retained_typed hstep htrans hΓ ha hb EΓ Eα Ea Eb W

end Lean4Lean.VEnv.Strengthening
