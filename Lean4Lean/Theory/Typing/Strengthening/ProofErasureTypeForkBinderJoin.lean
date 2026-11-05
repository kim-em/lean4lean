import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeContextLambdaAnnotation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructurePiOrigin

/-! # Forward binder transport of type computations up to joining

A domain computation and a computation of a type below that domain form a fork
at a typed Pi. Type-only fork joining, followed by exact Pi readout, gives a join
of the original body computation's endpoints under the computed domain. This is
conditional joining, not exact primitive or native-certificate transport.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Type-only fork joining transports a type computation forward across a
computed binder up to a common reduct. The output may be raw, with no native
certificate. The fork used is rooted at Pi A C; Pi readout extracts the resulting
codomain join in the new context B. The premise TypeForkJoin remains open. -/
theorem TypeForkJoin.type_compute_forward_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (hC : env.HasType univs (A :: Γ) C (.sort v))
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) C) out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (B :: Γ))
        (proofErase (B :: Γ) C) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (B :: Γ)) out shared := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have W : IsDefEqCtx env univs Γ (A :: Γ) (B :: Γ) := .succ .zero HAB
  have hCB := hC.defeqDFC henv W
  have EC := proofErase_defeqCtx hΓA W hC
  obtain ⟨C', HC', EC'⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hC rfl rfl RC
  have hC'B := HC'.hasType.2.defeqDFC henv W
  have EC'B : proofErase (B :: Γ) C' = out :=
    (proofErase_defeqCtx hΓA W HC'.hasType.2).symm.trans EC'
  have hPi := HasType.forallE HAB.hasType.1 hC
  have EP : proofErase Γ (.forallE A C) = .forallE (proofErase Γ A) (proofErase (A :: Γ) C) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have RL : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A C)) (.forallE (proofErase Γ B) (proofErase (B :: Γ) C)) := by
    rw [EP, ← EC]
    exact .forallE RA .refl
  have RR : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A C)) (.forallE (proofErase Γ B) (proofErase (B :: Γ) C')) := by
    rw [EP, EC'B]
    exact .forallE RA (by simpa only [proofEraseCtx] using RC)
  obtain ⟨joint, RJL, RJR⟩ := HF hΓ hPi RL RR
  obtain ⟨X, Y, HL, Rβ⟩ := proofErase_static_structure_union_pi_origin heq hs hΓ HAB.hasType.2 hCB RJL
  have HR := proofErase_static_structure_union_pi_components heq hs hΓ HAB.hasType.2 hC'B
    (RJR.trans (.beta Rβ))
  obtain ⟨_, _, _, _, _, _, _, RCL⟩ := HL
  obtain ⟨_, _, _, _, _, _, _, RCR⟩ := HR
  rw [EC'B] at RCR
  exact ⟨Y, RCL, RCR⟩

/-- A common reduct of two types under A remains a common-reduct relation
under a computed binder B. The middle raw endpoint is realized as a typed type
before type-only fork joining composes the two transported joins. -/
theorem TypeForkJoin.type_join_forward_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (HF : TypeForkJoin D)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAB : env.IsDefEq univs Γ A B (.sort u))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ B))
    (hC : env.HasType univs (A :: Γ) C (.sort v))
    (hC' : env.HasType univs (A :: Γ) C' (.sort w))
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) C) out)
    (RC' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) C') out) :
    ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (B :: Γ))
        (proofErase (B :: Γ) C) shared ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (B :: Γ))
        (proofErase (B :: Γ) C') shared := by
  obtain ⟨s, LC, LO⟩ := HF.type_compute_forward_context heq hs hΓ HAB RA hC RC
  obtain ⟨t, RC', RO⟩ := HF.type_compute_forward_context heq hs hΓ HAB RA hC' RC'
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.1⟩
  have hΓB : OnCtx (B :: Γ) (env.IsType univs) := ⟨hΓ, u, HAB.hasType.2⟩
  have W : IsDefEqCtx env univs Γ (A :: Γ) (B :: Γ) := .succ .zero HAB
  obtain ⟨C₀, HC₀, EC₀⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hC rfl rfl RC
  have hC₀ := HC₀.hasType.2.defeqDFC henv W
  have E : proofErase (B :: Γ) C₀ = out :=
    (proofErase_defeqCtx hΓA W HC₀.hasType.2).symm.trans EC₀
  obtain ⟨r, L, R⟩ := HF hΓB hC₀ (E ▸ LO) (E ▸ RO)
  exact ⟨r, LC.trans L, RC'.trans R⟩

end Lean4Lean.VEnv.Strengthening
