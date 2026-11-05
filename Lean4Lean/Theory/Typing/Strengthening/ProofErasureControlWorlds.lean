import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRigidFunctionTransport

/-! # Exact context renamings and ordinary control applications

These are the world maps for a context-indexed computational interpretation.
Only exact renamings transport computation. Arbitrary typed substitutions below
are used solely to interpret ordinary control typing and lambda beta bodies.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Compose ordinary interpretations using actual typed substitutions. -/
theorem ProofShape.ContextSubstitution.compose_world
    (W : ContextSubstitution Δ Δ' σ) (W' : ContextSubstitution Δ' Δ'' τ) :
    ContextSubstitution Δ Δ'' (σ.comp τ) := by
  intro Γ hΓ EΓ
  obtain ⟨Γ₁, σ₁, hΓ₁, EΓ₁, H₁, E₁⟩ := W hΓ EΓ
  obtain ⟨Γ₂, σ₂, hΓ₂, EΓ₂, H₂, E₂⟩ := W' hΓ₁ EΓ₁
  refine ⟨Γ₂, σ₁.comp σ₂, hΓ₂, EΓ₂, ?_, ?_⟩
  · apply substEq_of_lookup H₁.wf
    intro i A hl
    simpa only [VExpr.Subst.comp, VExpr.subst_subst] using
      (H₁.lookup hl).hasType.1.subst henv.orderedStrong H₂ hΓ₂
  · intro i A hl hn
    exact (proofErase_subst_with hΓ₂ H₂ (H₁.lookup hl).hasType.1 E₂).trans
      (congrArg (·.subst τ) (E₁ hl hn))

/-- Every erased context has an identity interpretation. -/
theorem ProofShape.ContextRenaming.identity : ContextRenaming Δ Δ Subst.id := by
  refine ⟨?_, fun i => ⟨i, rfl, (ProofShape.subst_id _).symm⟩⟩
  intro Γ hΓ EΓ
  refine ⟨Γ, VExpr.Subst.id, hΓ, EΓ, Ctx.SubstEq.id henv.ordered hΓ, ?_⟩
  intro i A hl hn
  exact if_neg hn

/-- Exact oracle transport composes together with its ordinary interpretation. -/
theorem ProofShape.ContextRenaming.compose
    (W : ContextRenaming Δ Δ' σ) (W' : ContextRenaming Δ' Δ'' τ) :
    ContextRenaming Δ Δ'' (σ.comp τ) := by
  refine ⟨ContextSubstitution.compose_world W.interpretation W'.interpretation, ?_⟩
  intro i
  obtain ⟨j, Ej, ET⟩ := W.lookup i
  obtain ⟨k, Ek, EU⟩ := W'.lookup j
  refine ⟨k, ?_, ?_⟩
  · simp only [Subst.comp, Ej, ProofShape.subst, Ek]
  · rw [EU, ET, ProofShape.subst_subst]

namespace AtomicControl
variable [Atom]

/-- A control witness can be read in any actual realization of its raw context. -/
theorem ControlTyping.realize (H : ControlTyping Δ e t)
    (hΓ : OnCtx Γ (env.IsType univs)) (EΓ : proofEraseCtx Γ = Δ) :
    ∃ f, env.HasType univs Γ f t.expr ∧ proofErase Γ f = e := by
  obtain ⟨Γ', f, hΓ', EΓ', hf, Ef⟩ := H
  have W := proofEraseCtx_defeq hΓ' hΓ (EΓ'.trans EΓ.symm)
  exact ⟨f, hf.defeqDFC henv W, (proofErase_defeqCtx hΓ' W hf).symm.trans Ef⟩

/-- Matching closed control carriers suffice for ordinary application typing.
This constructs no native certificate for the argument. -/
theorem ControlTyping.apply (HF : ControlTyping Δ f (.arrow A B)) (HA : ControlTyping Δ a A) :
    ControlTyping Δ (.app f a) B := by
  obtain ⟨Γ, f₀, hΓ, EΓ, hf, Ef⟩ := HF
  obtain ⟨a₀, ha, Ea⟩ := HA.realize hΓ EΓ
  have ht : env.HasType univs Γ (.app f₀ a₀) B.expr := by
    simpa only [ControlType.expr, VExpr.inst_eq, ControlType.expr_subst] using hf.app ha
  refine ⟨Γ, _, hΓ, EΓ, ht, ?_⟩
  rw [show proofErase Γ (.app _ _) = .app _ _ from if_neg (ControlType.not_isProof hΓ ht), Ef, Ea]

/-- Whole-application typing and the function's control carrier determine the
argument carrier even when that argument has no observation demand. -/
theorem ControlTyping.argument (HT : ControlTyping Δ (.app f a) B)
    (HF : ControlTyping Δ f (.arrow A B)) : ControlTyping Δ a A := by
  obtain ⟨Γ, e, hΓ, EΓ, he, Ee⟩ := HT
  obtain ⟨f₀, a₀, rfl, hn, Ef, Ea⟩ := erase_app_inv Ee
  obtain ⟨D, C, hf, ha⟩ := he.app_inv henv hΓ
  obtain ⟨g, hg, Eg⟩ := HF.realize hΓ EΓ
  obtain ⟨_, HN⟩ := (proofErase_reflect hΓ hf hg (Ef.trans Eg.symm)).2 (not_isProof_fn hΓ hf ha hn)
  have hf' := ((HN.defeq hΓ).symm.of_l henv hΓ hg).hasType.2
  exact ⟨Γ, a₀, hΓ, EΓ, argument_at_displayed_domain hΓ hf hf' ha, Ea⟩

/-- Supplying a typed argument to a substituted lambda interprets substitution
into its ORIGINAL body. No native image condition is needed. -/
theorem ControlTyping.lambda_substitution
    (HF : ControlTyping Ω (.lam L b) (.arrow A B))
    (W : ContextSubstitution Ω Δ σ) (HA : ControlTyping Δ a A) :
    ContextSubstitution (L :: Ω) Δ (σ.cons a) := by
  have HB : ContextSubstitution (L.subst σ :: Δ) Δ (Subst.one a) :=
    ((HF.subst W).apply HA).beta_interpretation
  have HC : ContextSubstitution (L :: Ω) Δ (σ.lift.comp (Subst.one a)) :=
    ContextSubstitution.compose_world W.cons HB
  have E : σ.lift.comp (Subst.one a) = σ.cons a := by
    funext i
    cases i with
    | zero => rfl
    | succ i => simp only [Subst.comp, Subst.lift, Subst.one, Subst.cons,
        ProofShape.lift_subst_cons, ProofShape.subst_id]
  intro Γ hΓ EΓ
  simpa only [E] using HC hΓ EΓ

end AtomicControl
end Lean4Lean.VEnv.Strengthening
