import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPrefixStages
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextCoverage

/-! # Typed substitution, eta, and earlier-stage coverage for scoped guards -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Scoped comparison transports along an ordinary typed substitution or
thinning, with no recovery requirement on its substitution images. -/
theorem proofErase_scoped_compare_subst
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  let τ : ProofShape.Subst := fun i => proofErase Γ₀ (σ i)
  have E : ErasedSubstAgreement Γ Γ₀ σ τ := fun _ _ => rfl
  rw [proofErase_subst_with hΓ₀ W ha E, proofErase_subst_with hΓ₀ W hb E]
  exact H.subst hsubst (ProofShape.ContextSubstitution.of_typed hΓ₀ W E)

/-- Scoped comparison transports along an ordinary typed substitution or
thinning, with no recovery requirement on its substitution images. -/
theorem proofErase_scoped_compare_instN
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ha : env.HasType univs Γ₁ a A) (hb : env.HasType univs Γ₁ b B)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ₁) mode (proofErase Γ₁ a) (proofErase Γ₁ b)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst x k)) (proofErase Γ (b.inst x k)) := by
  have hΓ := (W.wf henv hx hΓ₁).2
  simpa only [← instN_eq] using
    proofErase_scoped_compare_subst hsubst hΓ (W.substEq hΓ₁ hx) ha hb H

/-- Scoped comparison transports along an ordinary typed substitution or
thinning, with no recovery requirement on its substitution images. -/
theorem proofErase_scoped_compare_weak'
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ') mode
      (proofErase Γ' (a.lift' ρ)) (proofErase Γ' (b.lift' ρ)) := by
  simpa only [← lift'_subst, subst_id] using
    proofErase_scoped_compare_subst hsubst hΓ' (substEq_of_thinning hΓ W) ha hb H

/-- Typed recursive eta erases directly into contextual comparison. Whole-proof
functions collapse with their expansions; otherwise the domain typing supplies
the exact fresh-argument classification. -/
theorem proofErase_scoped_etaL (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hf : env.HasType univs Γ f (.forallE A B))
    (H : ProofShape.ScopedCompare Step (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) (.app f.lift (.bvar 0)))) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ (.lam A b)) (proofErase Γ f) := by
  classical
  have hl : env.HasType univs Γ (.lam A b) (.forallE A B) := .lam hA hb
  by_cases hp : IsProof Γ f
  · obtain ⟨P, hfP, hP⟩ := hp
    have hLP := hl.defeqU_r henv hΓ (hf.uniqU henv hΓ hfP)
    rw [proofErase_eq_proof.2 ⟨P, hLP, hP⟩, proofErase_eq_proof.2 ⟨P, hfP, hP⟩]
    exact .refl
  · have hnl : ¬ IsProof Γ (.lam A b) := by
      rintro ⟨P, hlP, hP⟩
      exact hp ⟨P, hf.defeqU_r henv hΓ (hl.uniqU henv hΓ hlP), hP⟩
    rw [show proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b)
      from if_neg hnl]
    rw [proofErase_eta_body hΓ hA hf hp] at H
    exact .etaBodyL (.of_typed hΓ hA) H

/-- Symmetric recursive eta has the same unconditional typed coverage. -/
theorem proofErase_scoped_etaR (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hf : env.HasType univs Γ f (.forallE A B))
    (H : ProofShape.ScopedCompare Step (proofEraseCtx (A :: Γ)) true
      (proofErase (A :: Γ) (.app f.lift (.bvar 0))) (proofErase (A :: Γ) b)) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true
      (proofErase Γ f) (proofErase Γ (.lam A b)) :=
  (proofErase_scoped_etaL hΓ hA hb hf H.symm).symm

/-- Every bidirectional normal certificate has a scoped guard in its
original mode; no computational or type-recovery premise is needed. -/
theorem BiNormal.scoped_compare (hΓ : OnCtx Γ (env.IsType univs))
    (H : BiNormal mode n Γ a b) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b) :=
  .base (H.context_compare hΓ)

/-- Full K and prefix computations from the earlier stages have scoped
simulations at the same stage. Full K uses prefix unfolding followed by beta. -/
theorem erased_prefix_K_scoped_compute (H : ErasedPrefixKStage D stage a b) :
    ProofShape.ScopedCompute (ErasedScopedPrefixStage D stage) Δ a b :=
  (erased_prefix_K_only_simulation stage H).scoped
    (fun H => .base (erased_prefix_only_scoped stage H))

/-- The scoped stages contain every earlier contextual comparison, preserving
its exact erased context, endpoints, mode, and stage bound. -/
theorem proofErase_prefix_context_scoped
    (H : ProofShape.ContextCompare (ErasedPrefixKStage D stage) Δ mode a b) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) Δ mode a b :=
  H.scoped (fun H => erased_prefix_K_scoped_compute H)

/-- Every contextual stage supports ordinary typed simultaneous substitution
of its comparison certificates at the same stage. -/
theorem proofErase_scoped_prefix_subst
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) :=
  proofErase_scoped_compare_subst (erased_scoped_prefix_stage_subst stage) hΓ₀ W ha hb H

/-- Arbitrary binder insertion preserves scoped stage certificates. -/
theorem proofErase_scoped_prefix_weak'
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ScopedCompare (ErasedScopedPrefixStage D stage) (proofEraseCtx Γ') mode
      (proofErase Γ' (a.lift' ρ)) (proofErase Γ' (b.lift' ρ)) :=
  proofErase_scoped_compare_weak' (erased_scoped_prefix_stage_subst stage) hΓ hΓ' W ha hb H

end Lean4Lean.VEnv.Strengthening
