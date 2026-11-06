import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEqTargetPrefix

/-! # Computed annotations at arbitrary retained-binder depths

Record the scope of each annotation computation. Semantic context conversion
reifies the change, while certificate descent preserves unused insertions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation

/-- One annotation computation at any binder depth, or no change. Newer
annotations retain their literal raw syntax. This records actual computation
in the original tail scope, not arbitrary identity context interpretation. -/
inductive AnnotationContextCompute (Step : List ProofShape → ProofShape → ProofShape → Prop) :
    List ProofShape → List ProofShape → Prop where
  | refl : AnnotationContextCompute Step Ξ Ξ
  | head : ScopedCompute Step Ξ A A' → AnnotationContextCompute Step (A :: Ξ) (A' :: Ξ)
  | tail : AnnotationContextCompute Step Ξ Ξ' →
      AnnotationContextCompute Step (A :: Ξ) (A :: Ξ')

variable [Params]

/-- Reify the recorded annotation change in any actual source realization.
All unchanged annotations and terms keep their erasures by semantic context
conversion. No native guard is moved to the new context. -/
theorem AnnotationContextCompute.realize
    (hstep : ErasedScopedPrimitiveDescent Step)
    (R : AnnotationContextCompute Step Ξ Ξ')
    (hΓ : OnCtx Γ (env.IsType univs)) (E : proofEraseCtx Γ = Ξ) :
    ∃ Γ', OnCtx Γ' (env.IsType univs) ∧ IsDefEqCtx env univs [] Γ Γ' ∧
      proofEraseCtx Γ' = Ξ' := by
  induction R generalizing Γ with
  | refl => exact ⟨Γ, hΓ, .refl hΓ, E⟩
  | head RD =>
    cases Γ with
    | nil => cases E
    | cons A Γ =>
      obtain ⟨hΓ, u, hA⟩ := hΓ
      obtain ⟨EA, EΓ⟩ := List.cons.inj E
      obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize hstep hΓ hA EΓ EA RD
      exact ⟨A' :: Γ, ⟨hΓ, u, HA.hasType.2⟩, .succ (.refl hΓ) HA,
        by simp only [proofEraseCtx, EA', EΓ]⟩
  | tail R ih =>
    cases Γ with
    | nil => cases E
    | cons A Γ =>
      obtain ⟨hΓ, u, hA⟩ := hΓ
      obtain ⟨EA, EΓ⟩ := List.cons.inj E
      obtain ⟨Γ', hΓ', C, EΓ'⟩ := ih hΓ EΓ
      refine ⟨A :: Γ', ⟨hΓ', u, hA.defeqDFC henv C⟩, .succ C hA, ?_⟩
      simp only [proofEraseCtx, ← proofErase_defeqCtx hΓ C hA, EA, EΓ']

/-- Descend an annotation change through an unused insertion. A change inside
that inserted block leaves the lower context fixed; any other change retains
its lower computation certificate. Both actual context conversions and the
rebuilt insertion are returned, so the result can be iterated. -/
theorem AnnotationContextCompute.descend_insertion
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (R : AnnotationContextCompute Step Ξ Ξ')
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN count offset Γ Γ') (E : proofEraseCtx Γ' = Ξ) :
    ∃ Γ₁ Γ₁', OnCtx Γ₁ (env.IsType univs) ∧ OnCtx Γ₁' (env.IsType univs) ∧
      Ctx.LiftN count offset Γ₁ Γ₁' ∧ IsDefEqCtx env univs [] Γ Γ₁ ∧
      IsDefEqCtx env univs [] Γ' Γ₁' ∧ proofEraseCtx Γ₁' = Ξ' ∧
      AnnotationContextCompute Step (proofEraseCtx Γ) (proofEraseCtx Γ₁) := by
  induction R generalizing Γ Γ' count offset with
  | refl => exact ⟨Γ, Γ', hΓ, hΓ', W, .refl hΓ, .refl hΓ', E, .refl⟩
  | head RD =>
    cases W with
    | zero As hlen =>
      cases As with
      | nil =>
        simp only [List.nil_append] at E
        obtain ⟨Γ₁, hΓ₁, C, E₁⟩ := (AnnotationContextCompute.head RD).realize hstep.descent hΓ E
        exact ⟨Γ₁, Γ₁, hΓ₁, hΓ₁, .zero [] hlen, C, C, E₁,
          by simpa only [E, E₁] using AnnotationContextCompute.head RD⟩
      | cons A As =>
        obtain ⟨hTail, u, hA⟩ := hΓ'
        obtain ⟨EA, EΞ⟩ := List.cons.inj E
        obtain ⟨A', HA, EA'⟩ := proofErase_scoped_compute_realize hstep.descent hTail hA EΞ EA RD
        change proofErase (As ++ Γ) A' = _ at EA'
        change proofEraseCtx (As ++ Γ) = _ at EΞ
        exact ⟨Γ, A' :: (As ++ Γ), hΓ, ⟨hTail, u, HA.hasType.2⟩,
          .zero (A' :: As) hlen, .refl hΓ, .succ (.refl hTail) HA,
          by simp only [proofEraseCtx, EA', EΞ], .refl⟩
    | @succ offset Γ₀ Γ₀' A W =>
      obtain ⟨hΓ₀, u, hA⟩ := hΓ
      obtain ⟨hΓ₀', _, _⟩ := hΓ'
      obtain ⟨EA, EΞ⟩ := List.cons.inj E
      have EA₀ := (proofErase_liftN hΓ₀ hΓ₀' W hA).symm.trans EA
      obtain ⟨A', HA, RA, EA'⟩ := proofErase_scoped_compute_certificate_descend
        hstep hΓ₀ hΓ₀' W hA EΞ (EA₀.symm ▸ RD)
      refine ⟨A' :: Γ₀, A'.liftN count offset :: Γ₀',
        ⟨hΓ₀, u, HA.hasType.2⟩, ⟨hΓ₀', u, HA.hasType.2.weakN henv W⟩,
        W.succ, .succ (.refl hΓ₀) HA, .succ (.refl hΓ₀') (HA.weakN henv W), ?_, .head RA⟩
      simp only [proofEraseCtx, proofErase_liftN hΓ₀ hΓ₀' W HA.hasType.2, EA', EΞ]
  | tail R ih =>
    cases W with
    | zero As hlen =>
      cases As with
      | nil =>
        simp only [List.nil_append] at E
        obtain ⟨Γ₁, hΓ₁, C, E₁⟩ := (AnnotationContextCompute.tail R).realize hstep.descent hΓ E
        exact ⟨Γ₁, Γ₁, hΓ₁, hΓ₁, .zero [] hlen, C, C, E₁,
          by simpa only [E, E₁] using AnnotationContextCompute.tail R⟩
      | cons A As =>
        obtain ⟨hTail, u, hA⟩ := hΓ'
        obtain ⟨EA, EΞ⟩ := List.cons.inj E
        obtain ⟨Γ₁, Γ₁', hΓ₁, hΓ₁', W₁, C, C', E₁, R₁⟩ :=
          ih hΓ hTail (Ctx.LiftN.zero As rfl) EΞ
        cases W₁ with
        | zero As' hlen' =>
          refine ⟨Γ₁, A :: (As' ++ Γ₁), hΓ₁,
            ⟨hΓ₁', u, hA.defeqDFC henv C'⟩,
            .zero (A :: As') (by simpa only [List.length_cons, hlen'] using hlen),
            C, .succ C' hA, ?_, R₁⟩
          simp only [proofEraseCtx, ← proofErase_defeqCtx hTail C' hA, EA, E₁]
    | @succ offset Γ₀ Γ₀' A W =>
      obtain ⟨hΓ₀, u, hA⟩ := hΓ
      obtain ⟨hΓ₀', _, _⟩ := hΓ'
      obtain ⟨EA, EΞ⟩ := List.cons.inj E
      obtain ⟨Γ₁, Γ₁', hΓ₁, hΓ₁', W₁, C, C', E₁, R₁⟩ := ih hΓ₀ hΓ₀' W EΞ
      have hAw := hA.weakN henv W
      refine ⟨A :: Γ₁, A.liftN count offset :: Γ₁',
        ⟨hΓ₁, u, hA.defeqDFC henv C⟩, ⟨hΓ₁', u, hAw.defeqDFC henv C'⟩,
        W₁.succ, .succ C hA, .succ C' hAw, ?_, ?_⟩
      · simp only [proofEraseCtx, ← proofErase_defeqCtx hΓ₀' C' hAw, EA, E₁]
      · simpa only [proofEraseCtx, ← proofErase_defeqCtx hΓ₀ C hA] using
          AnnotationContextCompute.tail (A := proofErase Γ₀ A) R₁

/-- Completion survives a recorded annotation change at any binder depth.
Every unused insertion is rebuilt after descending the annotation certificate;
the base completion keeps the original chosen target assignment. -/
theorem IteratedAmbientEqCompletion.compute_context
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (HP : IteratedAmbientEqCompletion Δ v w original Ξ source)
    (R : AnnotationContextCompute Step Ξ Ξ') :
    IteratedAmbientEqCompletion Δ v w original Ξ' source := by
  induction HP generalizing Ξ' with
  | base H =>
    obtain ⟨Γ, Γ', count, offset, v', w', pre, F, hΓ, hΓ', W, EΓ, hf, hn, HS, ES⟩ := H
    obtain ⟨Γ₁, Γ₁', hΓ₁, hΓ₁', W₁, C, _, E₁, _⟩ :=
      R.descend_insertion hstep hΓ hΓ' W EΓ
    obtain ⟨σ, pending, HS⟩ := HS
    refine .base ⟨Γ₁, Γ₁', count, offset, v', w', pre, F, hΓ₁, hΓ₁', W₁, E₁,
      hf.defeqDFC henv C, (fun hp => hn ((isProof_defeqCtx C).2 hp)),
      (HS.source_convert hΔ C).forget, ?_⟩
    simpa only [← proofErase_defeqCtx hΓ C hf] using ES
  | @insert Γ Γ' count offset f T hΓ hΓ' W hf HP ih =>
    obtain ⟨Γ₁, Γ₁', hΓ₁, hΓ₁', W₁, C, _, E₁, R₁⟩ :=
      R.descend_insertion hstep hΓ hΓ' W rfl
    have HP₁ : IteratedAmbientEqCompletion Δ v w original (proofEraseCtx Γ₁)
        (proofErase Γ₁ f) := by
      simpa only [proofErase_defeqCtx hΓ C hf] using ih R₁
    have HH := IteratedAmbientEqCompletion.insert hΓ₁ hΓ₁' W₁ (hf.defeqDFC henv C) HP₁
    simpa only [E₁, ← proofErase_defeqCtx hΓ C hf] using HH

/-- The bounded target prefix inherits completion through the same concrete
context change, independently of any extra source arguments. -/
theorem EqTargetPrefixCompletion.compute_context
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Step)
    (hΔ : OnCtx Δ (env.IsType univs))
    (HP : EqTargetPrefixCompletion Δ v w original Ξ source)
    (R : AnnotationContextCompute Step Ξ Ξ') :
    EqTargetPrefixCompletion Δ v w original Ξ' source := by
  obtain ⟨ls, args, E, HP⟩ := HP
  exact ⟨ls, args, E, HP.compute_context hstep hΔ R⟩

/-- A finite sequence of actual annotation computations, retaining each
computation's own finite stage and original tail scope. -/
inductive PiInertContextHistory (D : Definitions) : List ProofShape → List ProofShape → Prop where
  | refl : PiInertContextHistory D Ξ Ξ
  | step : AnnotationContextCompute (PiInertStage D n) Ξ Θ → PiInertContextHistory D Θ Ξ' →
      PiInertContextHistory D Ξ Ξ'

/-- A newer unchanged annotation may be retained over the entire history. -/
theorem PiInertContextHistory.tail (H : PiInertContextHistory D Ξ Ξ') :
    PiInertContextHistory D (A :: Ξ) (A :: Ξ') := by
  induction H with
  | refl => exact .refl
  | step R _ ih => exact .step (.tail R) ih

/-- Replay the recorded context history while preserving target completion
through all ambient unused insertions. -/
theorem EqTargetPrefixCompletion.context_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΔ : OnCtx Δ (env.IsType univs))
    (HP : EqTargetPrefixCompletion Δ v w original Ξ source)
    (H : PiInertContextHistory D Ξ Ξ') :
    EqTargetPrefixCompletion Δ v w original Ξ' source := by
  induction H with
  | refl => exact HP
  | step R _ ih => exact ih (HP.compute_context (pi_inert_stage_certificate_descent heq hs _) hΔ R)

/-- The actual context change at the focused endpoint. The base records
identity or one consumed binder; each retained binder keeps its original
annotation computation before the later map is lifted beneath it. -/
inductive PiInertEndpointContext (D : Definitions) :
    List ProofShape → List ProofShape → ProofShape.Subst → Prop where
  | base : PiInertEndpointMap Ξ Ξ' σ → PiInertEndpointContext D Ξ Ξ' σ
  | binder : ScopedCompute (PiInertStage D n) Ξ A A' → PiInertEndpointContext D Ξ Ξ' σ →
      PiInertEndpointContext D (A :: Ξ) (A'.subst σ :: Ξ') σ.lift

/-- Identity maps carry the actual annotation history needed for completion.
The alternative is one consumed binder beneath the retained prefix. Its
argument still needs agreement with the previously chosen target image. -/
theorem PiInertEndpointContext.ancestry (H : PiInertEndpointContext D Ξ Ξ' σ) :
    (σ = ProofShape.Subst.id ∧ PiInertContextHistory D Ξ Ξ') ∨
      ∃ x depth, σ = (ProofShape.Subst.one x).liftN depth := by
  induction H with
  | base H =>
    cases H with
    | identity => exact .inl ⟨rfl, .refl⟩
    | inst => exact .inr ⟨_, 0, rfl⟩
  | binder RD _ ih =>
    rcases ih with ⟨rfl, Hctx⟩ | ⟨x, depth, rfl⟩
    · exact .inl ⟨ProofShape.Subst.id_lift,
        by simpa only [ProofShape.subst_id] using PiInertContextHistory.step (.head RD) Hctx.tail⟩
    · exact .inr ⟨x, depth+1, rfl⟩

/-- Forgetting the precise annotation history retains the earlier syntactic
single-consumption restriction. -/
theorem PiInertEndpointContext.single (H : PiInertEndpointContext D Ξ Ξ' σ) :
    SingleEndpointSubstitution σ := by
  rcases H.ancestry with ⟨E, _⟩ | H
  · exact .inl E
  · exact .inr H

end Lean4Lean.VEnv.Strengthening
