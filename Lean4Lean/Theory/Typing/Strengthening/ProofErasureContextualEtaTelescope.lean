import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeEtaTelescope

/-! # Contextual eta at arbitrary dependent binder depth

A generic function's full telescope supplies all native guards before
substitution. Only administrative beta redexes are contracted afterward.
The sole joining premise is confluence of forks at typed types; it remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : PureObservation.Definitions}

/-- Every finite dependent eta expansion is contextually joined under the
explicit type-fork premise. The actual function needs no native certificate. -/
theorem type_forks_contextual_eta_telescope
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : ∀ {Γ T u left right}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ T (.sort u) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds T)) :
    TypeContextJoin D Γ (VExpr.wrapForalls ds T) f
      (VExpr.wrapLams ds (etaOpen ds.length f)) := by
  intro K z hK
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have hΓT : OnCtx (VExpr.wrapForalls ds T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have HE := hf.etaOpen_defeq henv hΓ
  classical
  by_cases hp : IsProof Γ f
  · exact TypeContextJoin.of_erasure_eq hΓT hf HE.hasType.2
      ((proofErase_eq_proof.2 hp).trans (proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)).symm) hK
  have hu : ¬ u ≈ .zero := by
    intro hu
    exact hp ⟨_, hf, (IsDefEq.sortDF (hT.sort_r henv hΓ) (by trivial) hu).defeq hT⟩
  have hn : ¬ IsProof (VExpr.wrapForalls ds T :: Γ) (.bvar 0) :=
    fun hp => hu ((isProof_fresh_iff hΓ hT).1 hp)
  have RG := static_structure_generic_eta_telescope heq hs hΓ hT
  rw [show proofErase (VExpr.wrapForalls ds T :: Γ) (.bvar 0) = .bvar 0 from if_neg hn] at RG
  exact type_forks_generic_context_beta heq hs HF hΓ hT hf
    (generic_eta_telescope_typing hΓ hT) RG
    (by rw [EtaTelescope.generic_inst]; exact .refl) hK

/-- Function eta below an arbitrary finite dependent lambda prefix is joined
in every enclosing typed type context. No native recovery of the original body
or its enclosing abstraction is assumed. This handles arbitrary binder depth
for eta, while general lambda-body congruence and type-fork joining stay open. -/
theorem type_forks_contextual_eta_under_telescope
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HF : ∀ {Γ T u left right}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ T (.sort u) →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) left →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) (proofErase Γ T) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) right shared)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hctx : OnCtx (ds.reverse ++ Γ) (env.IsType univs))
    (hf : env.HasType univs (ds.reverse ++ Γ) f (.forallE A B)) :
    TypeContextJoin D Γ (VExpr.wrapForalls (ds ++ [A]) B)
      (VExpr.wrapLams ds f) (VExpr.wrapLams ds (.lam A (.app f.lift (.bvar 0)))) := by
  intro K z hK
  have hLam : env.HasType univs Γ (VExpr.wrapLams ds f) (VExpr.wrapForalls (ds ++ [A]) B) := by
    simpa only [EtaTelescope.wrapForalls_append_one] using (IsDefEq.etaOpen_wrapLams hΓ hctx hf).hasType.1
  obtain ⟨u, hT⟩ := hLam.isType henv hΓ
  have hΓT : OnCtx (VExpr.wrapForalls (ds ++ [A]) B :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have HE : env.IsDefEq univs Γ (VExpr.wrapLams ds f)
      (VExpr.wrapLams ds (.lam A (.app f.lift (.bvar 0)))) (VExpr.wrapForalls (ds ++ [A]) B) := by
    simpa only [EtaTelescope.wrapForalls_append_one] using
      ((IsDefEq.eta hf).symm.etaOpen_wrapLams hΓ hctx)
  classical
  by_cases hp : IsProof Γ (VExpr.wrapLams ds f)
  · exact TypeContextJoin.of_erasure_eq hΓT hLam HE.hasType.2
      ((proofErase_eq_proof.2 hp).trans (proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)).symm) hK
  have hu : ¬ u ≈ .zero := by
    intro hu
    exact hp ⟨_, hLam, (IsDefEq.sortDF (hT.sort_r henv hΓ) (by trivial) hu).defeq hT⟩
  have hn : ¬ IsProof (VExpr.wrapForalls (ds ++ [A]) B :: Γ) (.bvar 0) :=
    fun hp => hu ((isProof_fresh_iff hΓ hT).1 hp)
  have RG := static_structure_generic_eta_telescope heq hs hΓ hT
  rw [show proofErase (VExpr.wrapForalls (ds ++ [A]) B :: Γ) (.bvar 0) = .bvar 0 from if_neg hn] at RG
  exact type_forks_generic_context_beta heq hs HF hΓ hT hLam
    (generic_eta_telescope_typing hΓ hT) RG (EtaTelescope.generic_inst_wrapLams_beta ds A f) hK

end Lean4Lean.VEnv.Strengthening
