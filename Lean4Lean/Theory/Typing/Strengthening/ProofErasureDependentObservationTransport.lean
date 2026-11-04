import Lean4Lean.Theory.Typing.Strengthening.ProofErasureDependentControlObservation

/-! # Dependent-profile observations through full structure/function eta -/
namespace Lean4Lean.VEnv.Strengthening.DemandProfile
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Primitive observation preservation extends to all compatible paths. Node
typings supply the ordinary context interpretations needed at changed binders. -/
theorem Obs.compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hroot : ∀ {Δ a b S t o}, Step Δ a b → Obs Δ S a t o → Obs Δ S b t o)
    (R : ScopedCompute Step Δ source out) (HS : S.Typed Δ) (H : Obs Δ S source t o) :
    Obs Δ S out t o := by
  induction R using ScopedCompute.rootBeta_induction generalizing S t o with
  | refl => exact H
  | base R => exact hroot R H
  | beta => exact H.beta_forward HS
  | trans _ _ ih₁ ih₂ => exact ih₂ HS (ih₁ HS H)
  | app RF RX ihf ihx =>
    have HT := H.typing.compute hstep (.app RF RX)
    cases H with
    | app _ HF HX => exact .app HT (ihf HS HF) (fun key hk => ihx HS (HX key hk))
  | proj => exact H.not_proj.elim
  | forallE => exact H.not_pi.elim
  | @lam Δ D D' b b' RA RB ihA ihb =>
    have HT := H.typing.compute hstep (.lam RA RB)
    obtain ⟨Γ, f, T, hΓ, EΓ, hf, HP, Ef⟩ := H.typing
    obtain ⟨A, body, rfl, _, EA, Eb⟩ := erase_lam_inv Ef
    obtain ⟨⟨u, hA⟩, C, hb⟩ := hf.lam_inv henv hΓ
    have EΓA : proofEraseCtx (A :: Γ) = D :: Δ := by simp only [proofEraseCtx, EA, EΓ]
    have SD : DomainSort Δ D u := ⟨Γ, A, hΓ, EΓ, hA, EA⟩
    obtain ⟨A', HA', EA'⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ EA RA
    have HC : IsDefEqCtx env univs [] (A :: Γ) (A' :: Γ) := .succ (.refl hΓ) HA'
    have WC : ContextSubstitution (D :: Δ) (D' :: Δ) ProofShape.Subst.id := by
      intro Γ₀ hΓ₀ EΓ₀
      have HH := control_context_substitution HC hΓ₀ (EΓA.trans EΓ₀.symm).symm
      simpa only [proofEraseCtx, EA', EΓ] using HH
    cases H with
    | lam HL HK HB =>
      exact .lam HT HK ((ihb (HS.cons HL.lam_parts.2 HK SD) HB).context WC)

/-- Every finite enriched stage preserves dependent neutral demands.
Visible profiles exclude structure majors even with arbitrary ignored domains. -/
theorem static_structure_stage_observation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage {Δ a b S t o}, ErasedStaticStructureEtaExpansionStage D stage Δ a b →
      Obs Δ S a t o → Obs Δ S b t o := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b S t o R H
    rcases R with (R | R) | R
    · exact (H.not_primitiveHead (erased_iota_primitive_head R)).elim
    · cases R with
      | sort => exact H.not_sort.elim
      | const => exact (H.not_primitiveHead trivial).elim
    · cases R; exact H.constant_expansion
  | succ stage ih =>
    intro Δ a b S t o R H
    rcases R with R | R | R | R | R | R
    · exact ih R H
    · exact (H.not_primitiveHead R.2.head).elim
    · exact (H.not_primitiveHead R.head).elim
    · exact H.native_identity (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact H.native_eta (erased_static_structure_eta_expansion_stage_descent heq hs stage) R
    · exact (H.typing.no_masked_structure
        (erased_static_structure_eta_expansion_stage_descent heq hs stage) H.demand.visible R).elim

/-- Full-union compatible computation preserves the dependent observation.
Native images are not required to transport these ordinary typing witnesses. -/
theorem Obs.static_structure_union
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) Δ source out)
    (HS : S.Typed Δ) (H : Obs Δ S source t o) : Obs Δ S out t o :=
  H.compute (erased_static_structure_eta_expansion_union_descent heq hs)
    (fun ⟨stage, R⟩ H => static_structure_stage_observation heq hs stage R H) R HS

end Lean4Lean.VEnv.Strengthening.DemandProfile
