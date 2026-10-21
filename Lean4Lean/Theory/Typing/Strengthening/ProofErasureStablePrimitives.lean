import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointStageSubstitution

/-! # Primitive certificates stable under typed substitutions

Retain an actual primitive and its transport under every interpreted context
substitution. Composition makes the enriched relation substitution closed,
without assuming beta stability or substitution closure of all target steps.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem typed_comp
    (hΓ₂ : OnCtx Γ₂ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₁ σ σ Γ)
    (V : Ctx.SubstEq env univs Γ₂ ρ ρ Γ₁) :
    Ctx.SubstEq env univs Γ₂ (σ.comp ρ) (σ.comp ρ) Γ := by
  induction Γ generalizing σ with
  | nil => exact .nil
  | cons A Γ ih =>
    cases W with
    | cons W hA hx =>
      refine .cons (ih W) hA ?_
      change env.IsDefEq univs Γ₂ (σ.head.subst ρ) (σ.head.subst ρ) (A.subst (σ.tail.comp ρ))
      rw [← VExpr.subst_subst]
      exact hx.subst henv.orderedStrong V hΓ₂

/-- Interpreted raw substitutions compose. Each target realization is chosen
by the preceding interpretation; retained-variable erasure agreement follows
ordinary forward substitution at that realization. -/
theorem ProofShape.ContextSubstitution.comp
    (W : ContextSubstitution Δ Δ₁ τ) (V : ContextSubstitution Δ₁ Δ₂ υ) :
    ContextSubstitution Δ Δ₂ (fun i => (τ i).subst υ) := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₁, σ, hΓ₁, EΓ₁, WS, ES⟩ := W hΓ EΓ
  obtain ⟨Γ₂, ρ, hΓ₂, EΓ₂, VS, EV⟩ := V hΓ₁ EΓ₁
  refine ⟨Γ₂, σ.comp ρ, hΓ₂, EΓ₂, typed_comp hΓ₂ WS VS, ?_⟩
  intro i A hl hn
  change proofErase Γ₂ ((σ i).subst ρ) = (τ i).subst υ
  rw [proofErase_subst_with hΓ₂ VS (WS.lookup hl).hasType.1 EV, ES hl hn]

/-- An actual primitive with an actual primitive residual under every typed
substitution. This is a subtype of the specified primitive relation, not an
assumption that every primitive of that relation has this property. -/
def SubstitutionStablePrimitive
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  Step Δ a b ∧ ∀ {Δ' τ}, ContextSubstitution Δ Δ' τ → Step Δ' (a.subst τ) (b.subst τ)

/-- Substitution preserves the enriched certificate by composing all future
substitutions with the one just applied. No stability law for arbitrary target
certificates is invoked. -/
theorem SubstitutionStablePrimitive.subst
    (H : SubstitutionStablePrimitive Step Δ a b) (W : ContextSubstitution Δ Δ' τ) :
    SubstitutionStablePrimitive Step Δ' (a.subst τ) (b.subst τ) := by
  refine ⟨H.2 W, ?_⟩
  intro Δ'' υ V
  rw [ProofShape.subst_subst, ProofShape.subst_subst]
  exact H.2 (W.comp V)

/-- The enriched relation inherits typed descent from its underlying actual
primitive relation. In particular its extra certificate adds no new equality. -/
theorem substitution_stable_primitive_descent
    (hstep : ErasedScopedPrimitiveDescent Step) :
    ErasedScopedPrimitiveDescent (SubstitutionStablePrimitive Step) :=
  fun hΓ hΓ' W ht H => hstep hΓ hΓ' W ht H.1

/-- Lower-stage beta transport equips each typed stage-n+1 source primitive
with a substitution-stable union certificate. The certificate retains one
actual primitive under every subsequent interpreted substitution. -/
theorem erased_joint_stage_substitution_stable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (H : ErasedJointStage D (stage + 1) (proofEraseCtx Γ) (proofErase Γ e) out) :
    SubstitutionStablePrimitive (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ e) out := by
  refine ⟨⟨stage + 1, H⟩, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  have HR := erased_joint_stage_primitive_subst_of_lower_beta heq hs hregistry Hbeta hΓ₀ WS ES ht H
  rwa [proofErase_subst_with hΓ₀ WS ht ES, EΓ₀] at HR

/-- Every typed stage-n+1 path embeds into computation whose primitives retain
substitution certificates, given stage-n proposition beta transport. This
constructs the enriched target for source paths; beta residual certification
is a separate obligation. -/
theorem proofErase_joint_stage_compute_substitution_stable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hregistry : recursorData ``Eq.rec = env.recursorRegistry ``Eq.rec)
    (Hbeta : JointPropBetaTransport (ErasedJointStage D stage) (ErasedJointUnion D))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (ErasedJointStage D (stage + 1)) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ScopedCompute (SubstitutionStablePrimitive (ErasedJointUnion D))
      (proofEraseCtx Γ) (proofErase Γ e) out := by
  have HS : ErasedPrimitiveSubstitutionTo (ErasedJointStage D (stage + 1))
      (SubstitutionStablePrimitive (ErasedJointUnion D)) := by
    intro Γ Γ₀ σ τ e T out hΓ₀ W E ht H
    rw [proofErase_subst_with hΓ₀ W ht E]
    exact .base ((erased_joint_stage_substitution_stable heq hs hregistry Hbeta W.wf ht H).subst
      (ContextSubstitution.of_typed hΓ₀ W E))
  have HR := R.subst_typed (erased_joint_stage_descent heq hs (stage + 1)) HS hΓ ht rfl rfl
    (ContextSubstitution.of_defeqCtx hΓ (IsDefEqCtx.zero (env := env) (U := univs)))
  simpa only [ProofShape.subst_id] using HR

end Lean4Lean.VEnv.Strengthening
