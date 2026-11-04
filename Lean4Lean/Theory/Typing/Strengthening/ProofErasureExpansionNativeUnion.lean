import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionNativeInstantiation

/-! # Substitution with native images recovered over the finite-stage union

Each image and each source derivation may initially use its own finite bound.
Finiteness of the source context collects image bounds before transport.
-/
namespace Lean4Lean.VEnv.Strengthening.ExpansionNativeSubstitution
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private finite_uniform_bound from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageUnion
variable [Params] {D : PureObservation.Definitions}

/-- Union recovery is required only for the finitely many retained variables. -/
def UnionImages (D : PureObservation.Definitions)
    (Γ Γ₀ : List VExpr) (τ : ProofShape.Subst) : Prop :=
  ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ)

/-- All retained images in a finite source context have a common finite stage. -/
theorem UnionImages.finite_stage (H : UnionImages D Γ Γ₀ τ) :
    ∃ k, Images D k Γ Γ₀ τ := by
  classical
  let P (i k : Nat) := ¬ IsProof Γ (.bvar i) →
    ScopedTypeRecovery (ErasedExpansionStage D k) (proofEraseCtx Γ₀) (τ i)
      ((contextOracle (proofEraseCtx Γ) i).subst τ)
  have HM : ∀ {i n m}, n ≤ m → P i n → P i m := by
    intro i n m hle H hn
    exact (H hn).mono (fun H => erased_expansion_stage_mono hle H)
  have HB : ∀ i, i < Γ.length → ∃ k, P i k := by
    intro i hi
    by_cases hn : IsProof Γ (.bvar i)
    · exact ⟨0, fun H => (H hn).elim⟩
    · obtain ⟨k, HR⟩ := (H (Lookup.ofLt hi).2 hn).finite_stage (Stages := ErasedExpansionStage D)
        (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
      exact ⟨k, fun _ => HR⟩
  obtain ⟨k, HK⟩ := finite_uniform_bound (P := P) (count := Γ.length) (fun hle H => HM hle H) HB
  exact ⟨k, fun hl hn => HK _ hl.lt hn⟩

/-- Finite-stage images embed in the union without any new recovery rule. -/
theorem Images.union (H : Images D k Γ Γ₀ τ) : UnionImages D Γ Γ₀ τ :=
  fun hl hn => (H hl hn).mono (fun H => ⟨k, H⟩)

/-- Exact union recovery and a common finite image bound are equivalent. -/
theorem union_images_iff : UnionImages D Γ Γ₀ τ ↔ ∃ k, Images D k Γ Γ₀ τ :=
  ⟨UnionImages.finite_stage, fun ⟨_, H⟩ => H.union⟩

/-- The union image class is closed under composition of actual typed maps. -/
theorem UnionImages.compose (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₂ : OnCtx Γ₂ (env.IsType univs))
    (W₁ : Ctx.SubstEq env univs Γ₁ σ₁ σ₁ Γ)
    (W₂ : Ctx.SubstEq env univs Γ₂ σ₂ σ₂ Γ₁)
    (E₁ : ErasedSubstAgreement Γ Γ₁ σ₁ τ₁)
    (E₂ : ErasedSubstAgreement Γ₁ Γ₂ σ₂ τ₂)
    (H₁ : UnionImages D Γ Γ₁ τ₁) (H₂ : UnionImages D Γ₁ Γ₂ τ₂) :
    UnionImages D Γ Γ₂ (τ₁.comp τ₂) := by
  obtain ⟨n, H₁⟩ := H₁.finite_stage
  obtain ⟨k, H₂⟩ := H₂.finite_stage
  exact Images.union (H₁.compose heq hs hΓ₂ W₁ W₂ E₁ E₂ H₂)

/-- Union computations substitute when each retained image has exact union recovery. -/
theorem compute_union_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : UnionImages D Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  obtain ⟨k, HI⟩ := HI.finite_stage
  obtain ⟨n, R⟩ := R.finite_stage (Stages := ErasedExpansionStage D) (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  exact (compute_subst heq hs hΓ₀ W ES HI ht R).mono (fun H => ⟨n + k, H⟩)

/-- Native selected types substitute exactly over the union. -/
theorem recovery_union_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : UnionImages D Γ Γ₀ τ)
    (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedTypeRecovery (ErasedExpansionUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (e.subst σ)) (out.subst τ) := by
  obtain ⟨k, HI⟩ := HI.finite_stage
  obtain ⟨n, R⟩ := R.finite_stage (Stages := ErasedExpansionStage D) (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  exact (recovery_subst heq hs hΓ₀ W ES HI ht R).mono (fun H => ⟨n + k, H⟩)

/-- Full common-typed union comparison substitutes, with all recursive guards. -/
theorem compare_union_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : UnionImages D Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCompare (ErasedExpansionUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare (ErasedExpansionUnion D) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  obtain ⟨k, HI⟩ := HI.finite_stage
  obtain ⟨n, H⟩ := H.finite_stage (Stages := ErasedExpansionStage D) (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  exact (compare_subst heq hs hΓ₀ W ES HI ha hb H).mono (fun H => ⟨n + k, H⟩)

/-- Full carrier checking substitutes over the union at the exact dependent carrier. -/
theorem carrier_union_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : UnionImages D Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCarrierGuard (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCarrierGuard (ErasedExpansionUnion D) (proofEraseCtx Γ₀)
      (proofErase Γ₀ (A.subst σ)) (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  obtain ⟨k, HI⟩ := HI.finite_stage
  obtain ⟨n, H⟩ := H.finite_stage (Stages := ErasedExpansionStage D) (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  exact (carrier_subst heq hs hΓ₀ W ES HI ha hb H).mono (fun H => ⟨n + k, H⟩)

/-- Recovered-family comparison substitutes over the entire union. -/
theorem recovered_union_subst (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ES : ErasedSubstAgreement Γ Γ₀ σ τ) (HI : UnionImages D Γ Γ₀ τ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : CarrierRecoveredCompare (ErasedExpansionUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    CarrierRecoveredCompare (ErasedExpansionUnion D) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  obtain ⟨k, HI⟩ := HI.finite_stage
  obtain ⟨n, H⟩ := H.finite_stage (Stages := ErasedExpansionStage D) (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  exact (recovered_subst heq hs hΓ₀ W ES HI ha hb H).mono (fun H => ⟨n + k, H⟩)

end Lean4Lean.VEnv.Strengthening.ExpansionNativeSubstitution
