import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeJoinTransport

/-! # Full checking under single substitution with combined native types

A lambda argument or another non-proof value may have a native carrier that
aligns with a reduct of its assigned type. Whole recursive comparison and carrier checking
survive its substitution without exact backward recovery at the assigned type.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {hq : QuotRegistered env} {F : List VExpr → VExpr → Prop}
variable [NativeFamilyFramework.InputLaws (definitions hq) F]

/-- Common-typed comparisons survive single substitution at a combined native type, including recursive computed-domain applications. -/
theorem compare_inst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (HR : Recovery hq F Γ p (proofErase Γ A))
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
    compare_subst hcon hΓ W ES (Images.inst HR) ha hb H

/-- Carrier mode retains the exact substituted dependent carrier. Its internal
application checks may use different domains obtained through core confluence. -/
theorem carrier_inst
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hp : env.HasType univs Γ p A)
    (HR : Recovery hq F Γ p (proofErase Γ A))
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
    carrier_subst hcon hΓ W ES (Images.inst HR) ha hb H

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
