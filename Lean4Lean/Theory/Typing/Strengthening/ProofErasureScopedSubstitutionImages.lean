import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedCoverage

/-! # Computing substitution images beneath typed dependent binders

The source substitution is typed; its computed raw images need no chosen
original representatives. Each binder is checked in the context obtained from
the source substitution, exactly as required by scoped computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

namespace ProofShape
/-- Insertion of a well-formed domain interprets the raw variable shift. -/
theorem ContextSubstitution.shift (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) :
    ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx (A :: Γ))
      (fun i => (ProofShape.bvar i).liftN 1) := by
  apply ContextSubstitution.of_typed (σ := VExpr.Subst.id.lift_r (.skip .refl))
    (hΓ₀ := (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, u, hA⟩))
    ((Ctx.SubstEq.id henv.ordered hΓ).skip henv.ordered)
  intro i B hl hn
  have H := proofErase_liftN hΓ (show OnCtx (A :: Γ) (env.IsType univs) from
    ⟨hΓ, u, hA⟩) Ctx.LiftN.one (show env.HasType univs Γ (.bvar i) B from .bvar hl)
  simpa only [VExpr.Subst.id, VExpr.Subst.lift_r, ← VExpr.lift_eq_lift',
    proofErase, if_neg hn] using H

/-- A raw scoped computation weakens beneath any typed domain. Its output need
not be assigned a separate typing for this transport. -/
theorem ScopedCompute.shift
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (R : ScopedCompute Step (proofEraseCtx Γ) a b) :
    ScopedCompute Step (proofEraseCtx (A :: Γ)) (a.liftN 1) (b.liftN 1) := by
  have H := R.subst hsubst (ContextSubstitution.shift hΓ hA)
  have E (e : ProofShape) : e.subst (fun i => (bvar i).liftN 1) = e.liftN 1 := by
    have H := (liftN_subst e Subst.id (n := 1) (k := 0)).symm
    rw [subst_id] at H
    exact H
  simpa only [E] using H
end ProofShape

/-- Pointwise computation of raw substitution images extends through a typed
template. Only the source substitution must be realized by original terms;
the target map may consist entirely of raw computational outputs. -/
theorem proofErase_scoped_compute_subst_images
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (he : env.HasType univs Γ e T) (E : ErasedSubstAgreement Γ Γ₀ σ ρ)
    (R : ∀ i, ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (ρ i) (τ i)) :
    ProofShape.ScopedCompute Step (proofEraseCtx Γ₀)
      ((proofErase Γ e).subst ρ) ((proofErase Γ e).subst τ) := by
  classical
  induction e generalizing Γ Γ₀ σ ρ τ T with
  | bvar i =>
    by_cases hp : IsProof Γ (.bvar i)
    · rw [proofErase_eq_proof.2 hp]; exact .refl
    simpa only [proofErase, if_neg hp, ProofShape.subst] using R i
  | sort u => simp only [proofErase]; split <;> exact .refl
  | const c ls => simp only [proofErase]; split <;> exact .refl
  | app f a ihf iha =>
    by_cases hp : IsProof Γ (.app f a)
    · rw [proofErase_eq_proof.2 hp]; exact .refl
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv W.wf
    simp only [proofErase, if_neg hp, ProofShape.subst]
    exact .app (ihf hΓ₀ W hf E R) (iha hΓ₀ W ha E R)
  | proj s i m ih =>
    by_cases hp : IsProof Γ (.proj s i m)
    · rw [proofErase_eq_proof.2 hp]; exact .refl
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv W.wf
    simp only [proofErase, if_neg hp, ProofShape.subst]
    exact .proj (ih hΓ₀ W hm.hasType.2 E R)
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [proofErase]
    split
    · exact .refl
    obtain ⟨⟨u, hA⟩, _, hb⟩ := by
      first | exact he.lam_inv henv W.wf | exact he.forallE_inv henv
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have hΓA' : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hA'⟩
    have RB : ∀ i, ProofShape.ScopedCompute Step (proofEraseCtx (A.subst σ :: Γ₀))
        (ρ.lift i) (τ.lift i) := by
      intro i
      cases i with
      | zero => exact .refl
      | succ i => exact (R i).shift hsubst hΓ₀ hA'
    have HB := ihb hΓA' (W.lift henv.ordered hA) hb (E.lift hΓ₀ W hA) RB
    rw [show proofEraseCtx (A.subst σ :: Γ₀) =
      (proofErase Γ A).subst ρ :: proofEraseCtx Γ₀ from
      congrArg (· :: proofEraseCtx Γ₀) (proofErase_subst_with hΓ₀ W hA E)] at HB
    simp only [ProofShape.subst]
    first | exact .lam (ihA hΓ₀ W hA E R) HB | exact .forallE (ihA hΓ₀ W hA E R) HB

/-- The raw single-argument substitution agrees with its typed realization on
every retained variable, even when some older variables are erased proofs. -/
theorem erasedSubstAgreement_one (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hx : env.HasType univs Γ x A) :
    ErasedSubstAgreement (A :: Γ) Γ (VExpr.Subst.one x)
      (ProofShape.Subst.one (proofErase Γ x)) := by
  intro i B hl hn
  have H := proofErase_instN hΓA hx Ctx.InstN.zero
    (show env.HasType univs (A :: Γ) (.bvar i) B from .bvar hl)
  rw [show proofErase (A :: Γ) (.bvar i) = .bvar i from if_neg hn] at H
  simpa only [instN_eq, VExpr.Subst.liftN, VExpr.subst, ProofShape.inst_eq_subst,
    ProofShape.Subst.liftN, ProofShape.subst] using H

/-- Computing one argument computes every occurrence in a typed body, including
occurrences in dependent annotations. The shared output is a raw shape. -/
theorem proofErase_scoped_compute_inst_argument
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (R : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ x) out) :
    ProofShape.ScopedCompute Step (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) ((proofErase (A :: Γ) b).inst out) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have H := proofErase_scoped_compute_subst_images hsubst hΓA.1 W hb
    (erasedSubstAgreement_one hΓA hx) (τ := ProofShape.Subst.one out) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

end Lean4Lean.VEnv.Strengthening
