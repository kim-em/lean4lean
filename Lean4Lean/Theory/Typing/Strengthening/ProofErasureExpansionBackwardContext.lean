import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionNativeInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativeImages

/-! # Pulling computation back across a computed binder

If A computes to B, a variable under A can recover the exact lookup type used
under B. This gives native identity images from the B context back to the A
context, without a purity or finite-family restriction on either annotation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Computing the target binder to the source binder supplies all exact native
identity images. The newest lookup uses the weakened computation; older lookup
types agree already. No classification of the binder's shape is required. -/
theorem expansion_native_backward_context_images
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (RA : ScopedCompute (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B)) :
    ExpansionNativeSubstitution.Images D k (B :: Γ) (A :: Γ) ProofShape.Subst.id := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have RL := RA.rename (erased_expansion_stage_rename heq hs k)
    (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
  simp only [subst_bvar_liftN] at RL
  intro i T hl _
  cases hl with
  | zero =>
    simp only [ProofShape.subst_id, proofEraseCtx, contextOracle, TypeOracle.cons]
    exact ScopedTypeRecovery.convert (T := (proofErase Γ A).liftN 1) .bvar RL
  | succ hl =>
    simp only [ProofShape.subst_id, proofEraseCtx, contextOracle, TypeOracle.cons]
    exact .bvar

/-- Actual domain equality interprets those native images as an identity
substitution, from the computed binder back to its predecessor. -/
theorem expansion_native_backward_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B)) :
    ExpansionNativeSubstitution.ImageSubstitution D k
      (proofEraseCtx (B :: Γ)) (proofEraseCtx (A :: Γ)) ProofShape.Subst.id := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have HC : IsDefEqCtx env univs [] (A :: Γ) (B :: Γ) := .succ (.refl hΓ) HAB
  have W : Ctx.SubstEq env univs (A :: Γ) VExpr.Subst.id VExpr.Subst.id (B :: Γ) :=
    substEq_source_convert hΓA HC (Ctx.SubstEq.id henv.ordered hΓA)
  have ES : ErasedSubstAgreement (B :: Γ) (A :: Γ) VExpr.Subst.id ProofShape.Subst.id := by
    intro i T hl hn
    have hn' : ¬ IsProof (A :: Γ) (.bvar i) := fun hp => hn ((isProof_defeqCtx HC).1 hp)
    simp only [VExpr.Subst.id, proofErase, if_neg hn', ProofShape.Subst.id]
  intro Γ' hΓ' EΓ'
  exact NativeImageTransport.ImageSubstitution.of_typed hΓA W ES
    (expansion_native_backward_context_images heq hs hΓ HAB.hasType.1 RA) hΓ' EΓ'

/-- A computation under the computed binder pulls back to its predecessor
with exact raw endpoints and the additive native-image stage bound. -/
theorem proofErase_expansion_compute_backward_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (ht : env.HasType univs (B :: Γ) e T)
    (R : ScopedCompute (ErasedExpansionStage D n) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out) :
    ScopedCompute (ErasedExpansionStage D (n + k)) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HR := ExpansionNativeSubstitution.compute heq hs R hΓB ht rfl rfl
    (expansion_native_backward_context heq hs hΓ HAB RA)
  simp only [ProofShape.subst_id] at HR
  have EE := proofErase_defeqCtx hΓB (IsDefEqCtx.succ .zero HAB.symm) ht
  simpa only [EE] using HR

/-- Native recovery likewise pulls back with the exact selected output; it
need not be replaced by an output joined only up to beta or universe changes. -/
theorem proofErase_expansion_recovery_backward_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (ht : env.HasType univs (B :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedExpansionStage D n) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out) :
    ScopedTypeRecovery (ErasedExpansionStage D (n + k)) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HR := ExpansionNativeSubstitution.recovery heq hs R hΓB ht rfl rfl
    (expansion_native_backward_context heq hs hΓ HAB RA)
  simp only [ProofShape.subst_id] at HR
  have EE := proofErase_defeqCtx hΓB (IsDefEqCtx.succ .zero HAB.symm) ht
  simpa only [EE] using HR

/-- The full recursive computed checker pulls back across a computed binder,
retaining the mode and both actual endpoint erasures. -/
theorem proofErase_expansion_compare_backward_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (B :: Γ) a T) (hb : env.HasType univs (B :: Γ) b T)
    (H : ComputedJointCompare (ErasedExpansionStage D n) (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b)) :
    ComputedJointCompare (ErasedExpansionStage D (n + k)) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HR := ExpansionNativeSubstitution.check heq hs H hΓB ha hb rfl rfl rfl
    (expansion_native_backward_context heq hs hΓ HAB RA)
  have HC := IsDefEqCtx.succ IsDefEqCtx.zero HAB.symm
  simpa only [ProofShape.subst_id, proofErase_defeqCtx hΓB HC ha,
    proofErase_defeqCtx hΓB HC hb] using HR

/-- Recursive alignment of native types, common-carrier promotions and fresh
eta binders all pull back using the same exact native identity images. -/
theorem proofErase_expansion_aligned_backward_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute (ErasedExpansionStage D k) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (B :: Γ) a T) (hb : env.HasType univs (B :: Γ) b T)
    (H : CarrierAlignedCompare (ErasedExpansionStage D n) (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b)) :
    CarrierAlignedCompare (ErasedExpansionStage D (n + k)) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b) := by
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have HR := NativeImageTransport.aligned_of_compute
    (erased_expansion_stage_rename heq hs k) (erased_expansion_stage_descent heq hs n)
    (fun H => erased_expansion_stage_mono (Nat.le_add_left k n) H)
    (fun R => ExpansionNativeSubstitution.compute heq hs R)
    H hΓB ha hb rfl rfl rfl (expansion_native_backward_context heq hs hΓ HAB RA)
  have HC := IsDefEqCtx.succ IsDefEqCtx.zero HAB.symm
  simpa only [ProofShape.subst_id, proofErase_defeqCtx hΓB HC ha,
    proofErase_defeqCtx hΓB HC hb] using HR

/-- Full-union computation has the same backward context transport, with
independent finite bounds for the domain and body paths. -/
theorem proofErase_expansion_union_compute_backward_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (ht : env.HasType univs (B :: Γ) e T)
    (R : ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx (B :: Γ))
      (proofErase (B :: Γ) e) out) :
    ScopedCompute (ErasedExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) e) out := by
  obtain ⟨k, RA⟩ := RA.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  obtain ⟨n, R⟩ := R.finite_stage (Stages := ErasedExpansionStage D)
    (fun {stage later} hle {Δ a b} H => erased_expansion_stage_mono hle H)
  exact (proofErase_expansion_compute_backward_context heq hs hΓ HAB RA ht R).mono
    (fun H => ⟨n + k, H⟩)

end Lean4Lean.VEnv.Strengthening
