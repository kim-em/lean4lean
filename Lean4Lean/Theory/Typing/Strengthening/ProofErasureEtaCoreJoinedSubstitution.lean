import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaJoinedGuardSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreExpansionRecovery

/-! # Impure native eta substitution through common core carriers

Mixed ordinary computation and controlled beta expansions transport their
native guards to common core reducts. The eta-aware readout theorem consumes
those reducts, yielding a whole eta substitution square on arbitrary sources.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Every native eta primitive whose type guard uses mixed core/controlled
computation transports to a common reduct under joined native images. Source
terms, contexts and images may contain arbitrary dependent binders, constants
and projections. The target residuals use the full eta-expanded union. -/
theorem native_eta_expansion_joined_subst
    (hq : QuotRegistered env) (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (hf : env.HasType univs Γ f T)
    (HI : JoinedNative.Images hq Γ Γ₀ τ)
    (R : NativeEtaExpansion (ErasedCoreExpansion (definitions hq) Recovery)
      (proofEraseCtx Γ) (proofErase Γ f) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion (definitions hq)) (proofEraseCtx Γ₀)
        ((proofErase Γ f).subst τ) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion (definitions hq)) (proofEraseCtx Γ₀)
        (out.subst τ) shared := by
  cases R with
  | intro RN SD =>
    obtain ⟨native, RI, RP⟩ := expansion_recovery_joined_subst hq hcon hr hΓ₀ W ES hf HI RN
    exact proofErase_native_eta_subst_of_joined_guard heq (sound hq)
      (erased_core_expansion_descent (sound hq) hr) hΓ₀ W ES hf RN SD
      (RI.mono (fun H => ⟨0, .inl (.inl H)⟩))
      (RP.scoped (fun H => .base ⟨0, .inl (.inl H)⟩)) .refl

/-- At a beta cut, an argument's common native carrier suffices for the
entire native eta body step. The body guard may use arbitrary mixed core
computation. Both branches start at exact erased beta-instantiated shapes. -/
theorem native_eta_body_joined_inst
    (hq : QuotRegistered env) (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hp : env.HasType univs Γ p A) (hb : env.HasType univs (A :: Γ) b B)
    (RI : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ p) native)
    (RC : Compute (Step hq) (proofErase Γ A) native)
    (R : NativeEtaExpansion (ErasedCoreExpansion (definitions hq) Recovery)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion (definitions hq)) (proofEraseCtx Γ)
        (proofErase Γ (b.inst p)) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion (definitions hq)) (proofEraseCtx Γ)
        (out.inst (proofErase Γ p)) shared := by
  obtain ⟨shared, RS, RL⟩ := native_eta_expansion_joined_subst hq heq hcon hr hΓA.1
    (Ctx.InstN.zero.substEq hΓA hp) (erasedSubstAgreement_one hΓA hp) hb
    (JoinedNative.Images.inst RI RC) R
  refine ⟨shared, ?_, ?_⟩
  · rw [proofErase_instN hΓA hp Ctx.InstN.zero hb]
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
  · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RL

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore
