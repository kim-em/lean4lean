import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJoinedNativeTransport

/-! # Full checking under single substitution with joined native types

A lambda argument or another non-proof value may have a native carrier that
merely joins its assigned type. Whole recursive comparison and carrier checking
survive its substitution without exact backward recovery at the assigned type.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {hq : QuotRegistered env}

/-- Both sides of a carrier join supply the single-substitution image law. -/
theorem Images.inst_join
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ p) native)
    (RA : Compute (Step hq) (proofErase Γ A) shared)
    (RN : Compute (Step hq) native shared) :
    Images hq (A :: Γ) Γ (ProofShape.Subst.one (proofErase Γ p)) :=
  Images.inst (R.convert (RN.scoped (fun H => .base H))) RA

/-- Common-typed comparisons survive single substitution at a computationally
joined native type, including recursive computed-domain applications. -/
theorem compare_inst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ p) native)
    (RA : Compute (Step hq) (proofErase Γ A) shared)
    (RN : Compute (Step hq) native shared)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (fun _ => Step hq) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    compare_subst hcon hΓ W ES (Images.inst_join R RA RN) ha hb H

/-- Carrier mode retains the exact substituted dependent carrier. Its internal
application checks may use different domains obtained through core confluence. -/
theorem carrier_inst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ p) native)
    (RA : Compute (Step hq) (proofErase Γ A) shared)
    (RN : Compute (Step hq) native shared)
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) T) (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ)
      (proofErase Γ (T.inst p)) (proofErase Γ (a.inst p)) (proofErase Γ (b.inst p)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := p) (A₀ := A)).substEq hΓA hp
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one p)
      (ProofShape.Subst.one (proofErase Γ p)) := erasedSubstAgreement_one hΓA hp
  simpa only [VExpr.inst_eq, VExpr.Subst.liftN] using
    carrier_subst hcon hΓ W ES (Images.inst_join R RA RN) ha hb H

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.JoinedNative
