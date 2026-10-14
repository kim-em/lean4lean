import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryThinning

/-! # Projection recovery from retained variable families

A lookup supplies the major family, including parameters and indices. Registration
then supplies its closed field template. The resulting exact recovered type can
be reconstructed below every well-formed thinning.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedProjectionExamples
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A retained projection of a variable synthesizes from the variable's family
lookup, with no chosen field-type recovery certificate. -/
theorem lookup_field_recovery (hΓ : OnCtx Γ (env.IsType univs))
    (hi : env.projections s info) (hl : Lookup Γ i (mkApps (.const s ls) args))
    (ht : env.HasType univs Γ (.proj s j (.bvar i)) T)
    (hn : ¬ IsProof Γ (.proj s j (.bvar i))) :
    ∃ F, env.HasType univs Γ (.proj s j (.bvar i)) F ∧
      ProofShape.TypeRecovery Step (erasedTypeOracle Γ)
        (proofErase Γ (.proj s j (.bvar i))) (proofErase Γ F) := by
  have hnm := not_isProof_major hΓ ht hn
  apply proofErase_projection_recovery_from_family hΓ hi ht hn (HasType.bvar hl)
  rw [show proofErase Γ (.bvar i) = .bvar i from if_neg hnm,
    ← erasedTypeOracle_valid hΓ hl]
  exact .bvar

/-- Synthesizing the projection after an arbitrary thinning still produces the
exact lifted erasure of a lower original field type. This exercises the new
projection branch of recovery descent with the actual canonical upper oracle. -/
theorem lookup_field_thinning (stage : Nat) (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ')
    (hi : env.projections s info) (hl : Lookup Γ i (mkApps (.const s ls) args))
    (ht : env.HasType univs Γ (.proj s j (.bvar i)) T)
    (hn : ¬ IsProof Γ (.proj s j (.bvar i))) :
    ∃ F F₀,
      ProofShape.TypeRecovery (ErasedComparedKStage D stage) (erasedTypeOracle Γ')
        (proofErase Γ' ((VExpr.proj s j (.bvar i)).lift' ρ)) (proofErase Γ' F) ∧
      env.HasType univs Γ (.proj s j (.bvar i)) F₀ ∧
      (proofErase Γ F₀).lift' ρ = proofErase Γ' F := by
  have hl' : Lookup Γ' (ρ.liftVar i) (mkApps (.const s ls) (args.map (·.lift' ρ))) := by
    simpa only [VExpr.lift'_mkApps, VExpr.lift'] using hl.weak' W
  have ht' := ht.weak' henv.ordered W
  have hn' := mt (isProof_lift' hΓ hΓ' W ht).1 hn
  obtain ⟨F, _, R⟩ := lookup_field_recovery (Step := ErasedComparedKStage D stage) hΓ' hi hl' ht' hn'
  obtain ⟨F₀, hF₀, EF⟩ := proofErase_context_typeRecovery_thinning
    (proofErase_compared_K_compute_thinning heq hs stage) hΓ hΓ' W ht R
  exact ⟨F, F₀, R, hF₀, EF⟩

end Lean4Lean.VEnv.Strengthening.ErasedProjectionExamples
