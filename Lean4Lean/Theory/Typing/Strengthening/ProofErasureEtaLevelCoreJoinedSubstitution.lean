import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaJoinedGuardSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreGuardPrimitives

/-! # Native eta substitution through universe-core common carriers

Mixed ordinary computation, explicit universe conversion and controlled beta expansions transport their
native guards to common core reducts. The eta-aware readout theorem consumes
those reducts, yielding a whole eta substitution square on arbitrary sources.
-/
namespace Lean4Lean.VEnv.Strengthening.LevelCoreNative
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {Defs : Definitions}

/-- Every native eta primitive whose type guard uses mixed core/controlled
computation transports to a common reduct under joined native images. Source
terms, contexts and images may contain arbitrary dependent binders, constants
and projections. The target residuals use the full eta-expanded union. -/
theorem native_eta_expansion_joined_subst
    (heq : env.HasCanonicalEq)
    (hs : Defs.Sound env univs) (hlevels : Defs.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ Defs.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive Defs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (hf : env.HasType univs Γ f T)
    (HI : Images Defs Γ Γ₀ τ)
    (R : NativeEtaExpansion (ErasedLevelCoreExpansion Defs Recovery)
      (proofEraseCtx Γ) (proofErase Γ f) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion Defs) (proofEraseCtx Γ₀)
        ((proofErase Γ f).subst τ) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion Defs) (proofEraseCtx Γ₀)
        (out.subst τ) shared := by
  cases R with
  | intro RN SD =>
    obtain ⟨native, RI, RP⟩ := expansion_recovery_joined_subst hs hlevels hcon hRigid hc hr hΓ₀ W ES hf HI RN
    exact proofErase_native_eta_subst_of_joined_guard heq hs
      (erased_level_core_expansion_descent hs hr) hΓ₀ W ES hf RN SD
      (RI.mono (fun H => ⟨0, .inl H⟩))
      (RP.scoped (fun H => .base ⟨0, .inl (.inl H)⟩)) .refl

/-- At a beta cut, an argument's common native carrier suffices for the
entire native eta body step. The body guard may use arbitrary mixed core
computation. Both branches start at exact erased beta-instantiated shapes. -/
theorem native_eta_body_joined_inst
    (heq : env.HasCanonicalEq)
    (hs : Defs.Sound env univs) (hlevels : Defs.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ Defs.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive Defs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hp : env.HasType univs Γ p A) (hb : env.HasType univs (A :: Γ) b B)
    (RI : ScopedTypeRecovery (fun _ => ErasedLevelCore Defs) (proofEraseCtx Γ) (proofErase Γ p) native)
    (RC : Compute (ErasedIotaPrimitive Defs) (proofErase Γ A) native)
    (R : NativeEtaExpansion (ErasedLevelCoreExpansion Defs Recovery)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion Defs) (proofEraseCtx Γ)
        (proofErase Γ (b.inst p)) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion Defs) (proofEraseCtx Γ)
        (out.inst (proofErase Γ p)) shared := by
  obtain ⟨shared, RS, RL⟩ := native_eta_expansion_joined_subst heq hs hlevels hRigid hc hcon hr hΓA.1
    (Ctx.InstN.zero.substEq hΓA hp) (erasedSubstAgreement_one hΓA hp) hb
    (Images.inst RI RC) R
  refine ⟨shared, ?_, ?_⟩
  · rw [proofErase_instN hΓA hp Ctx.InstN.zero hb]
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RS
  · simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using RL

/-- The original beta argument may recover through mixed level-core expansion
and have only a common level reduct with its assigned carrier. This supplies
the eta-body substitution square without exact recovery of that carrier. -/
theorem native_eta_body_mixed_inst
    (heq : env.HasCanonicalEq)
    (hs : Defs.Sound env univs) (hlevels : Defs.LevelCompatible univs)
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ Defs.unfolds c levels rhs)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive Defs))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hr : ErasedScopedPrimitiveDescent Recovery) (hr' : ErasedScopedPrimitiveDescent Recovery')
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hp : env.HasType univs Γ p A) (hb : env.HasType univs (A :: Γ) b B)
    (RI : ScopedTypeRecovery (ErasedLevelCoreExpansion Defs Recovery')
      (proofEraseCtx Γ) (proofErase Γ p) native)
    (HJ : ComputeJoin (ErasedLevelCore Defs) (proofErase Γ A) native)
    (R : NativeEtaExpansion (ErasedLevelCoreExpansion Defs Recovery)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion Defs) (proofEraseCtx Γ)
        (proofErase Γ (b.inst p)) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion Defs) (proofEraseCtx Γ)
        (out.inst (proofErase Γ p)) shared := by
  obtain ⟨native', RN, RC⟩ := expansion_recovery_align hs hlevels hcon hRigid hc hr' hΓA.1 hp RI HJ
  exact native_eta_body_joined_inst heq hs hlevels hRigid hc hcon hr hΓA hp hb RN RC R

end Lean4Lean.VEnv.Strengthening.LevelCoreNative

namespace Lean4Lean.VEnv.Strengthening.StoredCore
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Actual stored definitions discharge the core interfaces for eta-body
substitution. Both the original argument's native guard and the body eta guard
may use arbitrary mixed universe/core/expansion paths with full-union native
guards. The argument needs only a common level reduct with its assigned type. -/
theorem native_eta_body_level_mixed_inst (heq : env.HasCanonicalEq)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hp : env.HasType univs Γ p A) (hb : env.HasType univs (A :: Γ) b B)
    (RI : ScopedTypeRecovery (ErasedLevelCoreExpansion (Definitions.ofEnv env univs henv)
        (ErasedExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx Γ) (proofErase Γ p) native)
    (HJ : ComputeJoin (ErasedLevelCore (Definitions.ofEnv env univs henv)) (proofErase Γ A) native)
    (R : NativeEtaExpansion (ErasedLevelCoreExpansion (Definitions.ofEnv env univs henv)
        (ErasedExpansionUnion (Definitions.ofEnv env univs henv)))
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) out) :
    ∃ shared, ScopedCompute (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ)
        (proofErase Γ (b.inst p)) shared ∧
      ScopedCompute (ErasedEtaExpansionUnion (Definitions.ofEnv env univs henv)) (proofEraseCtx Γ)
        (out.inst (proofErase Γ p)) shared :=
  LevelCoreNative.native_eta_body_mixed_inst heq (Definitions.ofEnv_sound henv)
    (Definitions.ofEnv_levelCompatible henv) (fun hr _ _ => Definitions.ofEnv_no_rigid henv hr)
    (typed_core_confluence hcon) hcon
    (erased_expansion_union_descent heq (Definitions.ofEnv_sound henv))
    (erased_expansion_union_descent heq (Definitions.ofEnv_sound henv)) hΓA hp hb RI HJ R

end Lean4Lean.VEnv.Strengthening.StoredCore
