import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRetraction

/-! # Typed erased computation through arbitrary thinning

Single-block typed replay and raw substitution stability suffice for arbitrary
thinning. The intermediate contexts are built by weakening types from the lower
context; their well-formedness does not use context strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

variable [Params]

/-- Split one insertion from a thinning while retaining a well-formed middle
context. Its retained declarations are weakened from the lower context. -/
theorem thinning_split_wf
    (W : Ctx.Lift' (Lift.consN (.skip ρ) k) Γ₁ Γ₃)
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hΓ₃ : OnCtx Γ₃ (env.IsType univs)) :
    ∃ Γ₂, Ctx.Lift' (Lift.consN ρ k) Γ₁ Γ₂ ∧ Ctx.LiftN 1 k Γ₂ Γ₃ ∧
      OnCtx Γ₂ (env.IsType univs) := by
  induction k generalizing Γ₁ Γ₃ with
  | zero => let .skip W := W; exact ⟨_, W, .one, hΓ₃.1⟩
  | succ k ih =>
    let .cons (A := A) W := W
    obtain ⟨Γ₂, W₁, W₂, hΓ₂⟩ := ih W hΓ₁.1 hΓ₃.1
    refine ⟨A.lift' (.consN ρ k) :: Γ₂, .cons W₁, ?_, ?_⟩
    · simp only [Ctx.liftN_iff_lift'] at W₂ ⊢
      simpa [← VExpr.lift'_comp, ← Lift.consN_comp] using
        W₂.cons (A := A.lift' (.consN ρ k))
    · obtain ⟨u, hA⟩ := hΓ₁.2
      exact ⟨hΓ₂, u, hA.weak' henv.ordered W₁⟩

/-- Typed primitive replay below every thinning, with an exact erased target. -/
def ErasedPrimitiveThinning (Step : ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ' ρ e T out}, OnCtx Γ (env.IsType univs) → OnCtx Γ' (env.IsType univs) →
    Ctx.Lift' ρ Γ Γ' → env.HasType univs Γ e T →
    Step ((proofErase Γ e).lift' ρ) out →
    ∃ e', env.IsDefEq univs Γ e e' T ∧ (proofErase Γ e').lift' ρ = out

/-- Raw substitution retracts each single insertion after typed replay has
reconstructed its target. Iteration gives replay through arbitrary thinning. -/
theorem ErasedPrimitiveDescent.thinning (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} (σ : ProofShape.Subst), Step a b → Step (a.subst σ) (b.subst σ)) :
    ErasedPrimitiveThinning Step := by
  intro Γ Γ' ρ e T out hΓ hΓ' W ht R
  generalize hd : ρ.depth = d
  induction d generalizing ρ Γ' out with
  | zero =>
    rw [ProofShape.lift'_depth_zero _ hd] at R
    have R₀ : Step ((proofErase Γ e).liftN 0 0) out := by simpa only [ProofShape.liftN_zero] using R
    obtain ⟨e', HE, EE⟩ := hstep hΓ hΓ (Ctx.LiftN.zero []) ht R₀
    exact ⟨e', HE, by simpa only [ProofShape.liftN_zero, ProofShape.lift'_depth_zero _ hd] using EE⟩
  | succ d ih =>
    obtain ⟨ρ₀, k, hd₀, rfl⟩ := Lift.depth_succ hd
    obtain ⟨Γ₂, W₁, W₂, hΓ₂⟩ := thinning_split_wf W hΓ hΓ'
    have E (a : ProofShape) : a.lift' (.consN (.skip ρ₀) k) =
        (a.lift' (.consN ρ₀ k)).liftN 1 k := by
      rw [Lift.consN_skip_eq, ProofShape.lift'_comp]
      simpa only [Lift.skipN_one] using
        (ProofShape.lift'_consN_skipN (a.lift' (.consN ρ₀ k)) (n := 1) (k := k))
    have ht₂ := ht.weak' henv.ordered W₁
    have Esrc := proofErase_lift' hΓ hΓ₂ W₁ ht
    rw [E, ← Esrc] at R
    obtain ⟨e₂, HE₂, EE₂⟩ := hstep hΓ₂ hΓ' W₂ ht₂ R
    rw [← EE₂] at R
    have R₂ := ProofShape.relation_liftN_reflect hsubst R
    rw [Esrc] at R₂
    obtain ⟨e₀, HE₀, EE₀⟩ := ih hΓ₂ W₁ R₂ (by simpa using hd₀)
    exact ⟨e₀, HE₀, by rw [E, EE₀, EE₂]⟩

/-- Compatible computation inherits arbitrary-thinning replay from block
primitive replay and substitution stability. -/
theorem proofErase_compute_thinning (hstep : ErasedPrimitiveDescent Step)
    (hsubst : ∀ {a b} (σ : ProofShape.Subst), Step a b → Step (a.subst σ) (b.subst σ)) :
    ErasedPrimitiveThinning (ProofShape.Compute Step) :=
  ErasedPrimitiveDescent.thinning (proofErase_compute_typed_descend hstep)
    (fun _ H => H.subst (fun H => hsubst _ H))

/-- Every finite canonical-Eq comparison stage replays through arbitrary thinning. -/
theorem proofErase_compared_K_compute_thinning (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (stage : Nat) :
    ErasedPrimitiveThinning (ProofShape.Compute (ErasedComparedKStage D stage)) :=
  proofErase_compute_thinning (erased_compared_K_stage_descent heq hs stage)
    (fun _ H => erased_compared_K_stage_subst stage H)

end Lean4Lean.VEnv.Strengthening
