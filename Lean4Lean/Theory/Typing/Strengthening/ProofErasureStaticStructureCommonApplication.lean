import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureSortRecovery
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeRetainedInstantiation

/-! # Common native application through full structure eta

Pi readout retains the original codomain history. Exact retained argument
images can instantiate that history; proof arguments need no image, and
common certificates suffice for arguments assigned a universe.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Full structure/function-eta computation instantiates at a retained native
argument. Finiteness supplies independent body and image stage bounds; proof
arguments impose no native obligation. -/
theorem static_structure_union_compute_inst
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (hb : env.HasType univs (A :: Γ) b B)
    (RN : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) b) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.inst (proofErase Γ x)) := by
  classical
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨n, RN⟩ := RN.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
    (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
  have HI : ∃ k, ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D k)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A) := by
    by_cases hp : IsProof Γ x
    · exact ⟨0, fun hn => (hn hp).elim⟩
    · obtain ⟨k, R⟩ := (HR hp).finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
        (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
      exact ⟨k, fun _ => R⟩
  obtain ⟨k, HI⟩ := HI
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have ES : ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one x)
      (ProofShape.Subst.one (proofErase Γ x)) := erasedSubstAgreement_one hΓA hx
  have R := StaticStructureEtaNativeSubstitution.compute heq hs RN hΓA hb rfl rfl
    (NativeImageTransport.ImageSubstitution.of_typed hΓ W ES
      (NativeImageTransport.Images.inst_retained hΓ hx HI))
  rw [← proofErase_subst_with hΓ W hb ES] at R
  have R' : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n+k)) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (out.inst (proofErase Γ x)) := by
    simpa only [VExpr.inst_eq, VExpr.Subst.liftN, ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using R
  exact R'.mono (fun H => ⟨n+k, H⟩)

/-- A common native function certificate yields a common native application
certificate. Only a retained argument needs exact native recovery at its written
domain. The selected native Pi can have different computed components. -/
theorem static_structure_common_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.app f x))
    (HR : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) shared) :
    ∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (.app f x)) out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (B.inst x)) out := by
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, v, hB⟩ := hPi.forallE_inv henv
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hPi)] at RC
  obtain ⟨X, Y, ⟨A', B', _, _, _, _, _, RB⟩, Rβ⟩ :=
    proofErase_static_structure_union_pi_origin heq hs hΓ hA hB RC
  have RF := RN.convert (.beta Rβ)
  have RX := static_structure_union_compute_inst heq hs hΓ hx HR hB RB
  refine ⟨Y.inst (proofErase Γ x), ?_, RX⟩
  rw [show proofErase Γ (.app f x) = .app _ _ from if_neg hn]
  exact .app RF

/-- Applying a commonly recovered function to a proof needs no native
certificate for the argument. The dependent result retains a common output. -/
theorem static_structure_common_proof_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hx : env.HasType univs Γ x A)
    (hp : IsProof Γ x) (hn : ¬ IsProof Γ (.app f x))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) shared) :
    ∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (.app f x)) out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (B.inst x)) out :=
  static_structure_common_application heq hs hΓ hf hx hn (fun h => (h hp).elim) RN RC

/-- Type application needs only common native certificates for the function
and its type argument. Sort readout discharges the argument's exact demand;
no exact coverage of arbitrary retained data arguments is asserted. -/
theorem static_structure_common_type_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE (.sort u) B))
    (hx : env.HasType univs Γ x (.sort u)) (hn : ¬ IsProof Γ (.app f x))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) shared)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ (.forallE (.sort u) B)) shared)
    (RNx : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) sharedX)
    (RCx : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (.sort u) sharedX) :
    ∃ out, ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (.app f x)) out ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
        (proofEraseCtx Γ) (proofErase Γ (B.inst x)) out := by
  have RX := static_structure_exact_sort_of_common heq hs hΓ hx RNx RCx
  obtain ⟨_, hU⟩ := hx.isType henv hΓ
  have E : proofErase Γ (.sort u) = .sort u := if_neg (not_isProof_of_sort hΓ hU)
  exact static_structure_common_application heq hs hΓ hf hx hn (fun _ => E ▸ RX) RN RC

end Lean4Lean.VEnv.Strengthening
