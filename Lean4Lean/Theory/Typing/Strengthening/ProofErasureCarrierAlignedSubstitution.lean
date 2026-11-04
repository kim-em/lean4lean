import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCongruence

/-! # Two interpreted substitutions with inferred-related erased images

Both maps are typed in one target context. Under a binder the right map is
converted to the left substituted domain using the already proved typed image
congruence. No exact native recovery at that domain is asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Erasure agreement lifts into any actually typed target binder for the map.
The target annotation need not be the literal substitution of the source one. -/
theorem ErasedSubstAgreement.lift_to
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (hΓX : OnCtx (X :: Γ₀) (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (WL : Ctx.SubstEq env univs (X :: Γ₀) σ.lift σ.lift (A :: Γ))
    (H : ErasedSubstAgreement Γ Γ₀ σ τ) :
    ErasedSubstAgreement (A :: Γ) (X :: Γ₀) σ.lift τ.lift := by
  intro i B hl hn
  cases hl with
  | zero =>
    have hn' : ¬ IsProof (X :: Γ₀) (.bvar 0) :=
      fun hp => hn ((isProof_subst hΓX WL (.bvar .zero)).1 hp)
    simp only [VExpr.Subst.lift, ProofShape.Subst.lift, proofErase, if_neg hn']
  | @succ _ i B _ hl =>
    have hn₀ : ¬ IsProof Γ (.bvar i) := fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
    have hx := (W.lookup hl).hasType.1
    have HE := proofErase_liftN hΓ₀ hΓX Ctx.LiftN.one hx
    simpa only [VExpr.Subst.lift, ProofShape.Subst.lift, H hl hn₀] using HE

/-- Actual interpretations of two image maps together with pointwise inferred
comparison. This is a finite typed substitution certificate, not a substitution
or beta-stability oracle for an arbitrary comparison language. -/
structure CarrierAlignedSubstitution
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Γ Γ₀ : List VExpr) (σ φ : VExpr.Subst) (ρ τ : ProofShape.Subst) : Prop where
  target_wf : OnCtx Γ₀ (env.IsType univs)
  left : Ctx.SubstEq env univs Γ₀ σ σ Γ
  right : Ctx.SubstEq env univs Γ₀ φ φ Γ
  left_erasure : ErasedSubstAgreement Γ Γ₀ σ ρ
  right_erasure : ErasedSubstAgreement Γ Γ₀ φ τ
  images : ∀ i, CarrierAlignedCompare Step (proofEraseCtx Γ₀) false (ρ i) (τ i)

/-- Swapping the maps reverses each inferred image comparison. -/
theorem CarrierAlignedSubstitution.symm (W : CarrierAlignedSubstitution Step Γ Γ₀ σ φ ρ τ) :
    CarrierAlignedSubstitution Step Γ Γ₀ φ σ τ ρ :=
  ⟨W.target_wf, W.right, W.left, W.right_erasure, W.left_erasure, fun i => (W.images i).symm⟩

/-- Both typed image maps lift into the left substituted domain. The domain
equality is proved from typed template congruence and semantic descent, while
the target image certificates are weakened by interpreted renaming. -/
theorem CarrierAlignedSubstitution.cons
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (W : CarrierAlignedSubstitution Step Γ Γ₀ σ φ ρ τ)
    (hA : env.HasType univs Γ A (.sort u)) :
    CarrierAlignedSubstitution Step (A :: Γ) (A.subst σ :: Γ₀) σ.lift φ.lift ρ.lift τ.lift := by
  have hAσ := hA.subst henv.orderedStrong W.left W.target_wf
  have hAφ := hA.subst henv.orderedStrong W.right W.target_wf
  have hΓA : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨W.target_wf, u, hAσ⟩
  have HC := proofErase_carrier_aligned_subst_images hrename W.target_wf W.left hA W.left_erasure W.images
  rw [← proofErase_subst_with W.target_wf W.left hA W.left_erasure,
    ← proofErase_subst_with W.target_wf W.right hA W.right_erasure] at HC
  have HE := ((proofErase_carrier_aligned_compare_descend hstep W.target_wf W.target_wf
      (Ctx.LiftN.zero []) rfl hAσ hAφ (by simpa only [List.length_nil, ProofShape.liftN_zero] using HC)).2 rfl
    (not_isProof_of_sort W.target_wf hAσ) (not_isProof_of_sort W.target_wf hAφ)).of_l henv W.target_wf hAσ
  have WR := W.right.lift_at henv.ordered hA HE.symm
  refine ⟨hΓA, W.left.lift henv.ordered hA, WR, ErasedSubstAgreement.lift W.target_wf W.left hA W.left_erasure,
    ErasedSubstAgreement.lift_to W.target_wf hΓA W.right WR W.right_erasure, ?_⟩
  intro i
  cases i with
  | zero => exact .computed (.leaf .refl)
  | succ i =>
    have HR := (W.images i).rename hrename (ContextRenaming.of_liftN W.target_wf hΓA Ctx.LiftN.one)
    simpa only [subst_bvar_liftN, ProofShape.Subst.lift] using HR

/-- Eta on the right uses the right substituted binder; both maps can also
be lifted into that context without changing their order. -/
theorem CarrierAlignedSubstitution.cons_right
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (W : CarrierAlignedSubstitution Step Γ Γ₀ σ φ ρ τ)
    (hA : env.HasType univs Γ A (.sort u)) :
    CarrierAlignedSubstitution Step (A :: Γ) (A.subst φ :: Γ₀) σ.lift φ.lift ρ.lift τ.lift :=
  (W.symm.cons hstep hrename hA).symm

end Lean4Lean.VEnv.Strengthening
