import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeContext
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFamilyFramework

/-! # Joined native recovery beyond forward exact-result alignment

A generic Type parameter can be assigned a beta-expanded annotation while its
native lookup returns the parameter itself. Full checking crosses this binder
conversion, although the preceding finite alignment grammar cannot align the
native parameter to its beta expansion, for any input predicate.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative.Example
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {hq : QuotRegistered env}

/-- Beta expansion of an arbitrary type at Type. -/
def expanded (T : VExpr) : VExpr := .app (.lam (.sort (.succ .zero)) (.bvar 0)) T

/-- The expansion is ordinarily equal to its argument, with an actual typing. -/
theorem expanded_equal (hT : env.HasType univs Γ T (.sort (.succ .zero))) :
    env.IsDefEq univs Γ (expanded T) T (.sort (.succ .zero)) := by
  simpa [expanded, VExpr.inst_lift, VExpr.inst, instVar] using
    (IsDefEq.beta (show env.HasType univs (.sort (.succ .zero) :: Γ) (.bvar 0)
      (VExpr.sort (.succ .zero)).lift from .bvar .zero) hT)

/-- Erasure retains the beta redex and its arbitrary dependent argument. -/
theorem expanded_erasure (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ .zero))) :
    proofErase Γ (expanded T) = .app (.lam (.sort (.succ .zero)) (.bvar 0)) (proofErase Γ T) := by
  have hI : env.HasType univs Γ (.lam (.sort (.succ .zero)) (.bvar 0))
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) :=
    .lam (.sort (by trivial)) (.bvar .zero)
  have hS : env.HasType univs Γ (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have hΔ : OnCtx (.sort (.succ .zero) :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hx : env.HasType univs (.sort (.succ .zero) :: Γ) (.bvar 0) (.sort (.succ .zero)) :=
    .bvar .zero
  rw [show proofErase Γ (expanded T) = .app _ _ from
    if_neg (not_isProof_of_sort hΓ (expanded_equal hT).hasType.1)]
  rw [show proofErase Γ (.lam (.sort (.succ .zero)) (.bvar 0)) = .lam _ _ from
    if_neg (not_isProof_function_to_sort hΓ hI)]
  rw [show proofErase Γ (.sort (.succ .zero)) = .sort _ from if_neg (not_isProof_of_sort hΓ hS)]
  rw [show proofErase (.sort (.succ .zero) :: Γ) (.bvar 0) = .bvar 0 from
    if_neg (not_isProof_of_sort hΔ hx)]

/-- The assigned carrier computes to the native carrier, without a reverse
computation premise. -/
theorem expanded_compute (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ .zero))) :
    Compute (Step hq) (proofErase Γ (expanded T)) (proofErase Γ T) := by
  rw [expanded_erasure hΓ hT]
  simpa [ProofShape.inst, instVar, ProofShape.liftN_zero] using
    (Compute.beta (Step := Step hq) (BetaRed.beta (A := .sort (.succ .zero))
      (b := .bvar 0) (a := proofErase Γ T)))

/-- The new transport handles a beta-expanded arbitrary type annotation,
including generic type variables and all dependent checking beneath them. -/
theorem expanded_carrier_context
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort (.succ .zero)))
    (ha : env.HasType univs (expanded T :: Γ) a C) (hb : env.HasType univs (expanded T :: Γ) b C)
    (H : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx (expanded T :: Γ))
      (proofErase (expanded T :: Γ) C) (proofErase (expanded T :: Γ) a) (proofErase (expanded T :: Γ) b)) :
    ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx (T :: Γ))
      (proofErase (expanded T :: Γ) C) (proofErase (expanded T :: Γ) a) (proofErase (expanded T :: Γ) b) :=
  carrier_context hcon hΓ (expanded_equal hT) (expanded_compute hΓ hT) .refl ha hb H

/-- At a retained generic variable, no previous finite alignment certificate
can select its beta expansion, regardless of the input-family predicate. -/
theorem variable_not_aligned (D : PureObservation.Definitions)
    (F : List VExpr → VExpr → Prop) (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ (.bvar i) (.sort (.succ .zero))) :
    ¬ NativeFamilyFramework.Alignment D F Γ (.bvar i) (proofErase Γ (expanded (.bvar i))) := by
  intro H
  rcases H.shape with RC | ⟨u, E⟩ | ⟨A, B, E⟩
  · have ET : proofErase Γ (.bvar i) = .bvar i := if_neg (not_isProof_of_sort hΓ hT)
    rw [expanded_erasure hΓ hT, ET] at RC
    have EE := (RC.scoped (Δ := proofEraseCtx Γ) (fun H => .base H)).bvar_fixed
      (fun H => erased_iota_primitive_head H)
    cases EE
  · cases E
  · cases E

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative.Example
