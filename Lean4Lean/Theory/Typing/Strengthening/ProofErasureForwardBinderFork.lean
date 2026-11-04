import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeBinder

/-! # Forward binder transport requires type-fork joining

The variable case of forward binder transport already joins competing domain
computations. A function-to-sort wrapper removes the restriction that the
generic variable be retained by erasure. These are necessary consequences of
the still-open transport obligation, not a confluence proof.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- The generic retained variable tests every fork at its declared type.
Both paths to the common result descend back through the test binder. -/
theorem NativeForwardBinder.retained_type_fork
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : NativeForwardBinder D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (HAB : env.IsDefEq univs Γ A B (.sort u))
    (HAC : env.IsDefEq univs Γ A C (.sort u))
    (hn : ¬ IsProof (A :: Γ) (.bvar 0))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C)) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ B) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ C) shared := by
  have hA := HAB.hasType.1
  have hB := HAB.hasType.2
  have hC := HAC.hasType.2
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have HC : IsDefEqCtx env univs Γ (A :: Γ) (C :: Γ) := .succ .zero HAC
  have hnC : ¬ IsProof (C :: Γ) (.bvar 0) := mt (isProof_defeqCtx HC).2 hn
  have hrename : ∀ {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' τ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst τ) (b.subst τ) := by
    intro Δ Δ' a b τ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have RBL := RB.rename hrename (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
  simp only [subst_bvar_liftN] at RBL
  rw [← proofErase_liftN hΓ hΓA Ctx.LiftN.one hA] at RBL
  have RN := proofErase_scoped_lookup_recovery hΓA Lookup.zero hn RBL
  obtain ⟨shared, RN, RT⟩ := HF hΓ HAC RC (HasType.bvar Lookup.zero) RN
  rw [show proofErase (C :: Γ) (.bvar 0) = .bvar 0 from if_neg hnC] at RN
  have RCT : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
      ((proofErase Γ C).liftN 1) shared := RN.bvar_compute
  obtain ⟨B', _, RB', EB⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓC Ctx.LiftN.one hB rfl RT
  obtain ⟨C', _, RC', EC⟩ := proofErase_scoped_compute_certificate_descend
    (erased_static_structure_eta_expansion_union_certificate_descent heq hs)
    hΓ hΓC Ctx.LiftN.one hC rfl RCT
  have E := ProofShape.liftN_inj.mp (EB.trans EC.symm)
  exact ⟨proofErase Γ B', RB', E ▸ RC'⟩

/-- Forward binder transport forces joining of every computational fork
starting at a typed type, including propositions. Wrapping the type as the
domain of a function returning a sort retains the test variable; marked Pi
readout then extracts the common domain. Thus the open transport problem
already contains full type-level fork joining in this computation language. -/
theorem NativeForwardBinder.type_fork
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : NativeForwardBinder D)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) b)
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) c) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) b shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) c shared := by
  obtain ⟨B, HAB, rfl⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hA rfl rfl RB
  obtain ⟨C, HAC, rfl⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hA rfl rfl RC
  have hB := HAB.hasType.2
  have hC := HAC.hasType.2
  have E (X : VExpr) (hX : env.HasType univs Γ X (.sort u)) :
      proofErase Γ (.forallE X (.sort .zero)) = .forallE (proofErase Γ X) (.sort .zero) := by
    have hΓX : OnCtx (X :: Γ) (env.IsType univs) := ⟨hΓ, u, hX⟩
    rw [show proofErase Γ (.forallE X (.sort .zero)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (HasType.forallE hX (HasType.sort (by trivial))))]
    rw [show proofErase (X :: Γ) (.sort .zero) = .sort .zero from
      if_neg (not_isProof_of_sort hΓX (HasType.sort (by trivial)))]
  have HFB := IsDefEq.forallEDF HAB (HasType.sort (l := .zero) (by trivial))
  have HFC := IsDefEq.forallEDF HAC (HasType.sort (l := .zero) (by trivial))
  have hΓF : OnCtx (.forallE A (.sort .zero) :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HFB.hasType.1⟩
  have hn : ¬ IsProof (.forallE A (.sort .zero) :: Γ) (.bvar 0) :=
    not_isProof_function_to_sort hΓF (show env.HasType univs
      (.forallE A (.sort .zero) :: Γ) (.bvar 0) (.forallE A.lift (.sort .zero)) from .bvar .zero)
  have RFB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A (.sort .zero))) (proofErase Γ (.forallE B (.sort .zero))) := by
    rw [E A hA, E B hB]
    exact .forallE RB .refl
  have RFC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A (.sort .zero))) (proofErase Γ (.forallE C (.sort .zero))) := by
    rw [E A hA, E C hC]
    exact .forallE RC .refl
  obtain ⟨shared, RB', RC'⟩ := HF.retained_type_fork heq hs hΓ HFB HFC hn RFB RFC
  rw [E B hB] at RB'
  rw [E C hC] at RC'
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, hB⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have ESB : proofErase (B :: Γ) (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓB (HasType.sort (by trivial)))
  have ESC : proofErase (C :: Γ) (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΓC (HasType.sort (by trivial)))
  rw [← ESB] at RB'
  rw [← ESC] at RC'
  obtain ⟨X, Y, HO, Rbeta⟩ := proofErase_static_structure_union_pi_origin heq hs hΓ hB
    (HasType.sort (by trivial)) RB'
  have HC := proofErase_static_structure_union_pi_components heq hs hΓ hC
    (HasType.sort (by trivial)) (RC'.trans (.beta Rbeta))
  obtain ⟨_, _, _, _, _, _, RBX, _⟩ := HO
  obtain ⟨_, _, _, _, _, _, RCX, _⟩ := HC
  exact ⟨X, RBX, RCX⟩

end Lean4Lean.VEnv.Strengthening
