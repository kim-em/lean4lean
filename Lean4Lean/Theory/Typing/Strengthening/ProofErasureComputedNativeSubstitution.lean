import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeHeadSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextJoin

/-! # Simultaneous substitution repairs dependent computations

Computing all images can change dependent assigned types as well as arguments.
Only the final simultaneous images must recover their substituted oracle types;
no image must recover its type under the original substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

/-- Full computation transports through simultaneous native images. Each
image may have its own finite guard bound; the context collects them. -/
theorem static_structure_union_compute_subst_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ)
    (HI : NativeImageTransport.Images (ErasedStaticStructureEtaExpansionUnion D) Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  obtain ⟨k, HI⟩ := HI.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m Δ a b} hle H => erased_static_structure_eta_expansion_stage_mono hle H)
  obtain ⟨n, R⟩ := R.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  have R := StaticStructureEtaNativeSubstitution.compute heq hs R W.wf ht rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ₀ W ES HI)
  rw [← proofErase_subst_with hΓ₀ W ht ES] at R
  exact R.mono (fun H => ⟨n+k, H⟩)

/-- A complete generic computation joins its instantiated output after all
substitution images compute to simultaneously native images. Dependent types
are substituted by the final map as well. Original images need no native
recovery, and final images need not recover the original substituted types.
The body has arbitrary dependent type; no global joining premise is used. -/
theorem static_structure_subst_join_computed_native_images
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W₁ : Ctx.SubstEq env univs Γ₀ σ₁ σ₁ Γ)
    (E₁ : ErasedSubstAgreement Γ Γ₀ σ₁ ρ)
    (W₂ : Ctx.SubstEq env univs Γ₀ σ₂ σ₂ Γ)
    (E₂ : ErasedSubstAgreement Γ Γ₀ σ₂ τ)
    (HI : NativeImageTransport.Images (ErasedStaticStructureEtaExpansionUnion D) Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ e) out)
    (RI : ∀ i, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₀) (ρ i) (τ i)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₀)
        (proofErase Γ₀ (e.subst σ₁)) (out.subst τ) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ₀)
        (out.subst ρ) (out.subst τ) := by
  have hrename : ∀ {Δ Δ' a b σ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' σ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst σ) (b.subst σ) := by
    intro Δ Δ' a b σ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have RF := proofErase_compute_subst_images_of_renaming hrename hΓ₀ W₁ ht E₁ RI
  rw [← proofErase_subst_with hΓ₀ W₁ ht E₁,
    ← proofErase_subst_with hΓ₀ W₂ ht E₂] at RF
  obtain ⟨e', HE, Ee⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) W₁.wf ht rfl rfl R
  have RR := proofErase_compute_subst_images_of_renaming hrename hΓ₀ W₁ HE.hasType.2 E₁ RI
  rw [Ee] at RR
  exact ⟨RF.trans (static_structure_union_compute_subst_native heq hs hΓ₀ W₂ E₂ HI ht R), RR⟩

end Lean4Lean.VEnv.Strengthening
