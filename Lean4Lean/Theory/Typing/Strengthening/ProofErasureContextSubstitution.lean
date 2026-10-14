import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextEta
import Lean4Lean.Theory.Typing.LevelledReduction

/-! # Typed substitution of contextual erased certificates

A substitution acts on every well-formed realization of its erased source
context. Equal erased contexts permit source conversion of the original typed
substitution. This interpretation extends under arbitrary raw binders: a domain
needs a representative only when the extended source context is realized.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Convert the source context of an ordinary typed substitution. -/
theorem substEq_source_convert (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (H : IsDefEqCtx env univs [] Γ Γ') (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) :
    Ctx.SubstEq env univs Γ₀ σ σ Γ' := by
  induction H generalizing σ with
  | zero => exact W
  | succ H hA ih =>
    cases W with
    | cons W hD hx =>
      exact .cons (ih W) (hA.hasType.2.defeqDFC henv H)
        ((hA.subst henv.orderedStrong W hΓ₀).defeq hx)

/-- Retained-variable agreement survives conversion of the source context. -/
theorem ErasedSubstAgreement.source_convert
    (H : IsDefEqCtx env univs [] Γ Γ')
    (E : ErasedSubstAgreement Γ Γ₀ σ τ) : ErasedSubstAgreement Γ' Γ₀ σ τ := by
  intro i A hl hn
  have hx : env.HasType univs Γ' (.bvar i) A := .bvar hl
  have hx' := hx.defeqDFC henv (H.symm henv.ordered)
  obtain ⟨B, hl'⟩ := hx'.bvar_inv henv H.isType
  exact E hl' (fun hp => hn ((isProof_defeqCtx H).1 hp))

namespace ProofShape
/-- A raw substitution interpreted at every well-formed source realization.
Targets may choose a different realization of the same erased target context;
no arbitrary original representative of a proof marker is supplied. -/
def ContextSubstitution (Δ Δ' : List ProofShape) (τ : Subst) : Prop :=
  ∀ {Γ}, OnCtx Γ (env.IsType univs) → proofEraseCtx Γ = Δ →
    ∃ Γ₀ σ, OnCtx Γ₀ (env.IsType univs) ∧ proofEraseCtx Γ₀ = Δ' ∧
      Ctx.SubstEq env univs Γ₀ σ σ Γ ∧ ErasedSubstAgreement Γ Γ₀ σ τ

/-- Ordinary typed substitution supplies a context interpretation. Other source
realizations are converted using equality of their context erasures. -/
theorem ContextSubstitution.of_typed (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) (E : ErasedSubstAgreement Γ Γ₀ σ τ) :
    ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ₀) τ := by
  intro Γ' hΓ' EE
  have H := proofEraseCtx_defeq W.wf hΓ' EE.symm
  exact ⟨Γ₀, σ, hΓ₀, rfl, substEq_source_convert hΓ₀ H W, E.source_convert H⟩

/-- Context substitution transports every ambient domain-sort witness. -/
theorem ContextSubstitution.sort (W : ContextSubstitution Δ Δ' τ) (H : DomainSort Δ A u) :
    DomainSort Δ' (A.subst τ) u := by
  obtain ⟨Γ, e, hΓ, EΓ, he, Ee⟩ := H
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HS, ES⟩ := W hΓ EΓ
  exact ⟨Γ₀, e.subst σ, hΓ₀, EΓ₀, he.subst henv.orderedStrong HS hΓ₀,
    (proofErase_subst_with hΓ₀ HS he ES).trans (congrArg (·.subst τ) Ee)⟩

/-- The interpretation extends beneath every raw domain. Well-formed source
realizations provide its actual original domain when one is needed. -/
theorem ContextSubstitution.cons (W : ContextSubstitution Δ Δ' τ) :
    ContextSubstitution (A :: Δ) (A.subst τ :: Δ') τ.lift := by
  intro Γ hΓ EΓ
  cases Γ with
  | nil => cases EΓ
  | cons B Γ =>
    obtain ⟨hΓ, u, hB⟩ := hΓ
    obtain ⟨EB, EΓ⟩ := List.cons.inj EΓ
    obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, HS, ES⟩ := W hΓ EΓ
    have hB' := hB.subst henv.orderedStrong HS hΓ₀
    refine ⟨B.subst σ :: Γ₀, σ.lift, ⟨hΓ₀, u, hB'⟩, ?_, HS.lift henv.ordered hB,
      ES.lift hΓ₀ HS hB⟩
    simp only [proofEraseCtx, proofErase_subst_with hΓ₀ HS hB ES, EB, EΓ₀]

/-- Every contextual comparison substitutes along a typed context
interpretation. The primitive computation needs only raw substitution closure;
there is no chosen-type recovery condition on the substitution images. -/
theorem ContextCompare.subst
    (hsubst : ∀ {a b} {τ : Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (H : ContextCompare Step Δ mode a b) (W : ContextSubstitution Δ Δ' τ) :
    ContextCompare Step Δ' mode (a.subst τ) (b.subst τ) := by
  induction H generalizing Δ' τ with
  | base H => exact .base (H.subst hsubst)
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ihA ihb => exact .lam (ihA W) (ihb W.cons)
  | forallE _ _ ihA ihB => exact .forallE (ihA W) (ihB W.cons)
  | lamSorted SA SA' _ _ ihA ihb => exact .lamSorted (W.sort SA) (W.sort SA') (ihA W) (ihb W.cons)
  | forallSorted SA SA' _ SB SB' _ ihA ihB =>
    exact .forallSorted (W.sort SA) (W.sort SA') (ihA W) (ContextSubstitution.sort W.cons SB) (ContextSubstitution.sort W.cons SB') (ihB W.cons)
  | lamCommon _ ih => exact .lamCommon (ih W.cons)
  | etaBodyL S _ ih =>
    apply ContextCompare.etaBodyL (W.sort S)
    simpa only [ProofShape.subst, etaArgument_subst, lift_subst_lift] using ih W.cons
  | etaBodyR S _ ih =>
    apply ContextCompare.etaBodyR (W.sort S)
    simpa only [ProofShape.subst, etaArgument_subst, lift_subst_lift] using ih W.cons
  | compute Ra Rb _ ih => exact .compute (Ra.subst hsubst) (Rb.subst hsubst) (ih W)
  | symm _ ih => exact (ih W).symm
end ProofShape

/-- Typed simultaneous substitution preserves contextual erased comparison in
both modes, without recovering any substitution image at a preselected type. -/
theorem proofErase_context_compare_subst
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ContextCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ₀) mode
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  let τ : ProofShape.Subst := fun i => proofErase Γ₀ (σ i)
  have E : ErasedSubstAgreement Γ Γ₀ σ τ := fun _ _ => rfl
  rw [proofErase_subst_with hΓ₀ W ha E, proofErase_subst_with hΓ₀ W hb E]
  exact H.subst hsubst (ProofShape.ContextSubstitution.of_typed hΓ₀ W E)

/-- Typed replacement of a single binder preserves the same comparison mode.
The argument needs only its ordinary declared typing. -/
theorem proofErase_context_compare_instN
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ha : env.HasType univs Γ₁ a A) (hb : env.HasType univs Γ₁ b B)
    (H : ProofShape.ContextCompare Step (proofEraseCtx Γ₁) mode (proofErase Γ₁ a) (proofErase Γ₁ b)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ) mode
      (proofErase Γ (a.inst x k)) (proofErase Γ (b.inst x k)) := by
  have hΓ := (W.wf henv hx hΓ₁).2
  simpa only [← instN_eq] using
    proofErase_context_compare_subst hsubst hΓ (W.substEq hΓ₁ hx) ha hb H

/-- Pointwise lookup typings construct an ordinary diagonal substitution. -/
theorem substEq_of_lookup (hΓ : OnCtx Γ (env.IsType univs))
    (H : ∀ {i A}, Lookup Γ i A → env.HasType univs Γ₀ (σ i) (A.subst σ)) :
    Ctx.SubstEq env univs Γ₀ σ σ Γ := by
  induction Γ generalizing σ with
  | nil => exact .nil
  | cons A Γ ih =>
    obtain ⟨hΓ, u, hA⟩ := hΓ
    refine .cons (ih hΓ ?_) hA ?_
    · intro i B hl
      simpa only [lift_subst, VExpr.Subst.tail] using H (Lookup.succ hl)
    · simpa only [HasType, lift_subst, VExpr.Subst.head] using H Lookup.zero

/-- An actual context thinning is an ordinary typed renaming substitution. -/
theorem substEq_of_thinning (hΓ : OnCtx Γ (env.IsType univs)) (W : Ctx.Lift' ρ Γ Γ') :
    Ctx.SubstEq env univs Γ' (VExpr.Subst.id.lift_r ρ) (VExpr.Subst.id.lift_r ρ) Γ := by
  apply substEq_of_lookup hΓ
  intro i A hl
  have hx : env.HasType univs Γ (.bvar i) A := .bvar hl
  change env.HasType univs Γ' ((VExpr.bvar i).lift' ρ) (A.subst (VExpr.Subst.id.lift_r ρ))
  rw [← lift'_subst, subst_id]
  exact hx.weak' henv W

/-- Contextual comparison weakens through arbitrary typed context thinning.
It follows from typed substitution and needs no recovery of variable images. -/
theorem proofErase_context_compare_weak'
    (hsubst : ∀ {a b} {τ : ProofShape.Subst}, Step a b → Step (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.Lift' ρ Γ Γ') (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (H : ProofShape.ContextCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.ContextCompare Step (proofEraseCtx Γ') mode
      (proofErase Γ' (a.lift' ρ)) (proofErase Γ' (b.lift' ρ)) := by
  simpa only [← lift'_subst, subst_id] using
    proofErase_context_compare_subst hsubst hΓ' (substEq_of_thinning hΓ W) ha hb H

end Lean4Lean.VEnv.Strengthening
