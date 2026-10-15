import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStageUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedCarrierResynthesis

/-! # Joint re-synthesis without explicit stage bounds

For monotone families, finite joint re-synthesis is equivalent to joint
re-synthesis over their unions. Thus stage alignment is not an additional
semantic obligation. Neither version of re-synthesis is proved here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

/-- Missing joint re-synthesis at a pair of fixed contextual relations.
Typed substitution may change the recovered Pi, but the new argument guard
must use its new domain. This is an open property, not a completeness theorem. -/
def ScopedCarrierDomainResynthesis
    (Recovery Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ₀ σ f x y D C A B}, OnCtx Γ₀ (env.IsType univs) →
    Ctx.SubstEq env univs Γ₀ σ σ Γ →
    env.HasType univs Γ f (.forallE D C) →
    env.HasType univs Γ x D → env.HasType univs Γ y D →
    ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B) →
    StructureCarrierGuard Step (proofEraseCtx Γ) A (proofErase Γ x) (proofErase Γ y) →
    ∃ A' B', ScopedTypeRecovery Recovery (proofEraseCtx Γ₀)
        (proofErase Γ₀ (f.subst σ)) (.forallE A' B') ∧
      StructureCarrierGuard Step (proofEraseCtx Γ₀) A'
        (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (y.subst σ))

/-- The two input certificates may initially have different bounds. Taking
their maximum lets finite joint re-synthesis act on both simultaneously. -/
theorem ScopedFiniteCarrierDomainResynthesis.union
    (H : ScopedFiniteCarrierDomainResynthesis Recoveries Stages)
    (hrec : ScopedStagesMonotone Recoveries) (hstep : ScopedStagesMonotone Stages) :
    ScopedCarrierDomainResynthesis (ScopedStageUnion Recoveries) (ScopedStageUnion Stages) := by
  intro Γ Γ₀ σ f x y D C A B hΓ₀ W hf hx hy R G
  obtain ⟨n, R⟩ := R.finite_stage hrec
  obtain ⟨m, G⟩ := G.finite_stage hstep
  obtain ⟨later, A', B', _, R', G'⟩ := H hΓ₀ W hf hx hy
    (R.mono (hrec (Nat.le_max_left n m))) (G.mono (hstep (Nat.le_max_right n m)))
  exact ⟨A', B', R'.mono (fun H => ⟨later, H⟩), G'.mono (fun H => ⟨later, H⟩)⟩

/-- Union re-synthesis returns finite certificates. Their bounds can be raised
together above the original stage, preserving the newly chosen common domain. -/
theorem ScopedCarrierDomainResynthesis.finite
    (H : ScopedCarrierDomainResynthesis (ScopedStageUnion Recoveries) (ScopedStageUnion Stages))
    (hrec : ScopedStagesMonotone Recoveries) (hstep : ScopedStagesMonotone Stages) :
    ScopedFiniteCarrierDomainResynthesis Recoveries Stages := by
  intro stage Γ Γ₀ σ f x y D C A B hΓ₀ W hf hx hy R G
  obtain ⟨A', B', R', G'⟩ := H hΓ₀ W hf hx hy
    (R.mono (fun H => ⟨stage, H⟩)) (G.mono (fun H => ⟨stage, H⟩))
  obtain ⟨n, R'⟩ := R'.finite_stage hrec
  obtain ⟨m, G'⟩ := G'.finite_stage hstep
  refine ⟨max stage (max n m), A', B', Nat.le_max_left _ _,
    R'.mono (hrec ?_), G'.mono (hstep ?_)⟩ <;> omega

/-- For monotone recovery and computation families, stage alignment adds no
strength to joint re-synthesis. This equivalence proves neither side. -/
theorem scoped_finite_resynthesis_iff_union
    (hrec : ScopedStagesMonotone Recoveries) (hstep : ScopedStagesMonotone Stages) :
    ScopedFiniteCarrierDomainResynthesis Recoveries Stages ↔
      ScopedCarrierDomainResynthesis (ScopedStageUnion Recoveries) (ScopedStageUnion Stages) :=
  ⟨fun H => H.union hrec hstep, fun H => H.finite hrec hstep⟩

end Lean4Lean.VEnv.Strengthening
