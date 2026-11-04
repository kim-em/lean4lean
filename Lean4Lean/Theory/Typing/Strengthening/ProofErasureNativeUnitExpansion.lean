import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativeEtaExpansion
import Lean4Lean.Theory.Typing.UnitLikeConstructor

/-! # Native eta expansion of unit-like structures

Recover the actual family and its parameters from the retained source, then
expand to the registered empty constructor. Parameters may be dependent, open,
and computed; no closed-unit restriction is imposed. Native recovery brings
all retained parameters below inserted binders, so expansion descends at the
source's original assigned type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- An unindexed empty structure expands at its natively recovered family
instance. Saturation retains exactly the recovered parameter spine. -/
inductive ProofShape.NativeUnitExpansion
    (Step : List ProofShape → ProofShape → ProofShape → Prop) (Δ : List ProofShape) :
    ProofShape → ProofShape → Prop where
  | intro (hi : env.projections family info) (hx : info.nindices = 0)
      (hf : info.numFields = 0) (hp : ps.length = info.nparams) :
      ScopedTypeRecovery Step Δ source (mkApps (.const family ls) ps) →
      NativeUnitExpansion Step Δ source (mkApps (.const info.ctorName ls) ps)

/-- Enlarging the guard computation preserves unit expansion. -/
theorem ProofShape.NativeUnitExpansion.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (R : NativeUnitExpansion Step Δ a b) : NativeUnitExpansion Step' Δ a b := by
  cases R with
  | intro hi hx hf hp RN => exact .intro hi hx hf hp (RN.mono hstep)

/-- Native family recovery reconstructs the constructor and every parameter
below arbitrary block insertion. The original assigned type is preserved,
even when it differs from the natively selected family. -/
theorem erased_nativeUnitExpansion_descent (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (NativeUnitExpansion Step) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro hi hx hf hp RN =>
    rename_i family info ls rawPs
    obtain ⟨A, heA, EA⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ' W ht rfl RN
    obtain ⟨rawPs, Es, Eps⟩ := ProofShape.liftN_const_spine_inv EA
    obtain ⟨ps, rfl, rfl⟩ := proofErase_const_spine_inv Es
    have hps : ps.length = info.nparams := by
      have H := congrArg List.length Eps
      simp only [List.length_map] at H
      omega
    have hc := heA.unitLike_constructor henv hΓ hi hps hx hf
    have HE := IsDefEq.unitLike hi hps hx hf heA hc
    have hn : ¬ IsProof Γ e := by
      intro H
      exact RN.ne_proof (by rw [proofErase_eq_proof.2 H]; rfl)
    have hnc : ¬ IsProof Γ _ := fun H => hn ((isProof_congr hΓ HE).2 H)
    refine ⟨_, HE.toU.of_l henv hΓ ht, ?_⟩
    rw [proofErase_const_spine hΓ hc hnc, ProofShape.liftN_mkApps]
    simpa only [ProofShape.liftN] using congrArg (ProofShape.mkApps (.const info.ctorName ls)) Eps.symm

/-- Interpreted renaming preserves the exact recovered parameter spine. -/
theorem ProofShape.NativeUnitExpansion.rename
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step' Δ' (a.subst τ) (b.subst τ))
    (R : NativeUnitExpansion Step Δ a b) (W : ContextRenaming Δ Δ' τ) :
    NativeUnitExpansion Step' Δ' (a.subst τ) (b.subst τ) := by
  cases R with
  | intro hi hx hf hp RN =>
    have RN' := RN.rename hrename W
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at RN' ⊢
    exact .intro hi hx hf (by simpa only [List.length_map] using hp) RN'

/-- Native-image transport substitutes the complete parameter spine and the
source's family guard. It assumes no universal coverage of such images. -/
theorem ProofShape.NativeUnitExpansion.subst_typed
    (hrename : ∀ {Δ Δ' a b τ}, ImageStep Δ a b → ContextRenaming Δ Δ' τ →
      ImageStep Δ' (a.subst τ) (b.subst τ))
    (hstep : ErasedScopedPrimitiveDescent Source)
    (hinclude : ∀ {Δ a b}, ImageStep Δ a b → Target Δ a b)
    (hcompute : ∀ {Γ Δ Δ' τ e T source out}, ScopedCompute Source Δ source out →
      OnCtx Γ (env.IsType univs) → env.HasType univs Γ e T →
      proofEraseCtx Γ = Δ → proofErase Γ e = source →
      NativeImageTransport.ImageSubstitution ImageStep Δ Δ' τ →
      ScopedCompute Target Δ' (source.subst τ) (out.subst τ))
    (R : NativeUnitExpansion Source Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (EΓ : proofEraseCtx Γ = Δ) (Ee : proofErase Γ e = source)
    (W : NativeImageTransport.ImageSubstitution ImageStep Δ Δ' τ) :
    NativeUnitExpansion Target Δ' (source.subst τ) (out.subst τ) := by
  cases R with
  | intro hi hx hf hp RN =>
    have RN' := NativeImageTransport.recovery_of_compute hrename hstep hinclude hcompute RN hΓ ht EΓ Ee W
    simp only [ProofShape.subst_mkApps, ProofShape.subst] at RN' ⊢
    exact .intro hi hx hf (by simpa only [List.length_map] using hp) RN'

end Lean4Lean.VEnv.Strengthening
