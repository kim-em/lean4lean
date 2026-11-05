import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaTelescopeSyntax

/-! # Native eta through arbitrary dependent telescopes

The generic declaration supplies every application guard. Proof erasure is
classified at each dependent domain; no bound argument needs native recovery.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : PureObservation.Definitions}

/-- Exact assigned native recovery weakens beneath a fresh typed binder.
Proofness is transported by typed insertion, not by native coverage. -/
theorem static_structure_exact_native_weak
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f T)
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ T)) :
    ¬ IsProof (A :: Γ) f.lift → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) f.lift) (proofErase (A :: Γ) T.lift) := by
  intro hn
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hn₀ : ¬ IsProof Γ f := fun hp => hn ((isProof_liftN hΓ hΓA Ctx.LiftN.one hf).2 hp)
  have hrename : ∀ {Δ Δ' a b σ}, ErasedStaticStructureEtaExpansionUnion D Δ a b →
      ContextRenaming Δ Δ' σ → ErasedStaticStructureEtaExpansionUnion D Δ' (a.subst σ) (b.subst σ) := by
    intro Δ Δ' a b σ ⟨n, H⟩ W
    exact ⟨n, erased_static_structure_eta_expansion_stage_rename heq hs n H W⟩
  have R := (RF hn₀).rename hrename (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
  simp only [subst_bvar_liftN] at R
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  rw [← proofErase_liftN hΓ hΓA Ctx.LiftN.one hf,
    ← proofErase_liftN hΓ hΓA Ctx.LiftN.one hT] at R
  exact R

/-- Exact native recovery computes eta along any finite dependent telescope.
The length is unrestricted, and every fresh argument requires ordinary typing
only. Proof domains and proof-valued residual functions are included. -/
theorem static_structure_native_eta_telescope
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (VExpr.wrapForalls ds T))
    (RF : ¬ IsProof Γ f → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (VExpr.wrapForalls ds T))) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ (VExpr.wrapLams ds (etaOpen ds.length f))) := by
  induction ds generalizing Γ f with
  | nil => exact .refl
  | cons A ds ih =>
    obtain ⟨⟨u, hA⟩, _⟩ := (hf.isType henv hΓ).forallE_inv henv.ordered
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hf' := hf.weak henv (B := A)
    have hx : env.HasType univs (A :: Γ) (.bvar 0) A.lift := .bvar .zero
    have hb : env.HasType univs (A :: Γ) (.app f.lift (.bvar 0)) (VExpr.wrapForalls ds T) := by
      simpa only [VExpr.lift, VExpr.inst_liftN_bvar, VExpr.wrapForalls] using HasType.app hf' hx
    have RB := static_structure_exact_native_app hΓA hf' hx
      (static_structure_exact_native_weak heq hs hΓ hA hf RF)
    have RB' : ¬ IsProof (A :: Γ) (.app f.lift (.bvar 0)) →
        ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (A :: Γ))
          (proofErase (A :: Γ) (.app f.lift (.bvar 0))) (proofErase (A :: Γ) (VExpr.wrapForalls ds T)) := by
      simpa only [VExpr.lift, VExpr.inst_liftN_bvar, VExpr.wrapForalls] using RB
    have R₁ := static_structure_exact_native_eta hΓ hf RF
    have R₂ := proofErase_scoped_compute_lam_eq hΓ hA (hb.etaOpen_defeq henv hΓA) (ih hΓA hb RB')
    exact R₁.trans R₂

/-- A fresh generic function supplies exact native recovery at every depth of
its declared telescope, so its full eta opening computes without assumptions
about the actual function later substituted for it. -/
theorem static_structure_generic_eta_telescope
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ (VExpr.wrapForalls ds T) (.sort u)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx (VExpr.wrapForalls ds T :: Γ))
      (proofErase (VExpr.wrapForalls ds T :: Γ) (.bvar 0))
      (proofErase (VExpr.wrapForalls ds T :: Γ)
        (VExpr.wrapLams (EtaTelescope.liftDomains ds 0) (etaOpen ds.length (.bvar 0)))) := by
  have hΓT : OnCtx (VExpr.wrapForalls ds T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hg : env.HasType univs (VExpr.wrapForalls ds T :: Γ) (.bvar 0)
      (VExpr.wrapForalls ds T).lift := .bvar .zero
  have ET := EtaTelescope.wrapForalls_lift (ds := ds) (T := T) (k := 0)
  have hg' := hg
  rw [VExpr.lift, ET] at hg'
  have R := static_structure_native_eta_telescope heq hs hΓT hg'
    (fun hn => by
      have R := proofErase_scoped_lookup_recovery (Step := ErasedStaticStructureEtaExpansionUnion D)
        hΓT .zero hn ScopedCompute.refl
      rw [VExpr.lift, ET] at R
      exact R)
  simpa only [EtaTelescope.liftDomains_length] using R

/-- The full generic eta telescope is typed at the original generic assignment. -/
theorem generic_eta_telescope_typing
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ (VExpr.wrapForalls ds T) (.sort u)) :
    env.HasType univs (VExpr.wrapForalls ds T :: Γ)
      (VExpr.wrapLams (EtaTelescope.liftDomains ds 0) (etaOpen ds.length (.bvar 0)))
      (VExpr.wrapForalls ds T).lift := by
  have hΓT : OnCtx (VExpr.wrapForalls ds T :: Γ) (env.IsType univs) := ⟨hΓ, u, hT⟩
  have hg : env.HasType univs (VExpr.wrapForalls ds T :: Γ) (.bvar 0)
      (VExpr.wrapForalls ds T).lift := .bvar .zero
  have ET := EtaTelescope.wrapForalls_lift (ds := ds) (T := T) (k := 0)
  have hg' := hg
  rw [VExpr.lift, ET] at hg'
  have H := hg'.etaOpen_defeq henv hΓT
  rw [← ET] at H
  simpa only [EtaTelescope.liftDomains_length] using H.hasType.2

end Lean4Lean.VEnv.Strengthening
