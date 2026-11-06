import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqRetractionComposition

/-! # Replay annotations through constructed context embeddings

Retain how a reverse map inserts binders, extends under a displayed binder,
and composes. Annotation changes can then be replayed at the corresponding
target location, including below any inserted declarations.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Constructed context embeddings, retaining every inserted domain's sort
witness. Binder extension and composition allow arbitrarily many insertions
at different depths without identifying distinct source variables. -/
inductive ContextEmbedding : List ProofShape → List ProofShape → ProofShape.Subst → Prop where
  | identity : ContextEmbedding Ξ Ξ ProofShape.Subst.id
  | insert : ContextEmbedding Ξ Θ κ → DomainSort Θ B u →
      ContextEmbedding Ξ (B :: Θ) (κ.comp (fun i => .bvar (liftVar 1 i 0)))
  | binder : ContextEmbedding Ξ Θ κ →
      ContextEmbedding (A :: Ξ) (A.subst κ :: Θ) κ.lift
  | compose : ContextEmbedding Ξ Θ κ → ContextEmbedding Θ Ω ρ →
      ContextEmbedding Ξ Ω (κ.comp ρ)

/-- Every constructed embedding has the exact interpretation and oracle
transport required by native certificate renaming. -/
theorem ContextEmbedding.renaming (W : ContextEmbedding Ξ Θ κ) : ContextRenaming Ξ Θ κ := by
  induction W with
  | identity => exact ContextRenaming.identity
  | insert _ SD ih =>
    obtain ⟨Γ, B, hΓ, EΓ, hB, EB⟩ := SD
    have WI := ContextRenaming.of_liftN hΓ
      (show OnCtx (B :: Γ) (env.IsType univs) from ⟨hΓ, _, hB⟩) Ctx.LiftN.one
    exact ih.compose (by simpa only [proofEraseCtx, EB, EΓ] using WI)
  | binder _ ih => exact ih.cons
  | compose _ _ ih₁ ih₂ => exact ih₁.compose ih₂

/-- A recorded annotation computation transports an existing domain-sort
witness without changing that domain's raw syntax. Semantic context conversion
supplies the new typing; no strengthening is used. -/
theorem ProofShape.DomainSort.compute_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (SD : DomainSort Ξ A u) (R : AnnotationContextCompute Step Ξ Ξ') :
    DomainSort Ξ' A u := by
  obtain ⟨Γ, B, hΓ, EΓ, hB, EB⟩ := SD
  obtain ⟨Γ', hΓ', C, EΓ'⟩ := R.realize hstep hΓ EΓ
  exact ⟨Γ', B, hΓ', EΓ', hB.defeqDFC henv C,
    (proofErase_defeqCtx hΓ C hB).symm.trans EB⟩

/-- Replay one source annotation change through the actual embedding.
Inserted declarations retain their raw annotations with converted sort
witnesses. The map is unchanged and the target change is a single recorded
annotation computation, so this construction can be iterated. -/
theorem ContextEmbedding.compute_context
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hrename : ∀ {Ξ Θ a b κ}, Step Ξ a b → ContextRenaming Ξ Θ κ →
      Step Θ (a.subst κ) (b.subst κ))
    (W : ContextEmbedding Ξ Θ κ) (R : AnnotationContextCompute Step Ξ Ξ') :
    ∃ Θ', ContextEmbedding Ξ' Θ' κ ∧ AnnotationContextCompute Step Θ Θ' := by
  induction W generalizing Ξ' with
  | identity => exact ⟨Ξ', .identity, R⟩
  | insert W SD ih =>
    obtain ⟨Θ', W', R'⟩ := ih R
    exact ⟨_, .insert W' (SD.compute_context hstep R'), .tail R'⟩
  | binder W ih =>
    cases R with
    | refl => exact ⟨_, .binder W, .refl⟩
    | head RD => exact ⟨_, .binder W, .head (RD.rename hrename W.renaming)⟩
    | tail R =>
      obtain ⟨Θ', W', R'⟩ := ih R
      exact ⟨_, .binder W', .tail R'⟩
  | compose W₁ W₂ ih₁ ih₂ =>
    obtain ⟨Θ', W₁', R₁⟩ := ih₁ R
    obtain ⟨Ω', W₂', R₂⟩ := ih₂ R₁
    exact ⟨Ω', W₁'.compose W₂', R₂⟩

/-- Any finite retained annotation history transports the constructed
embedding, preserving its exact map and every stage of the target history. -/
theorem ContextEmbedding.context_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (W : ContextEmbedding Ξ Θ κ) (R : PiInertContextHistory D Ξ Ξ') :
    ∃ Θ', ContextEmbedding Ξ' Θ' κ ∧ PiInertContextHistory D Θ Θ' := by
  induction R generalizing Θ with
  | refl => exact ⟨Θ, W, .refl⟩
  | step RD _ ih =>
    obtain ⟨Θ', W', RD'⟩ := W.compute_context
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs _))
      (pi_inert_stage_rename heq hs _) RD
    obtain ⟨Ω, W'', RH⟩ := ih W'
    exact ⟨Ω, W'', .step RD' RH⟩

end Lean4Lean.VEnv.Strengthening
