import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoverableInstantiation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSubstitutionImages

/-! # Computing images using only primitive renaming

Compatible image computation needs only weakening of primitive paths beneath
binders. It does not substitute arbitrary terms into primitive certificates.
Thus this side of the substitution square holds for the full joint stages.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Pointwise image computation extends through any typed template whenever
primitive computation supports interpreted variable renamings. Only the source
image map needs an original typed realization. -/
theorem proofErase_compute_subst_images_of_renaming
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextRenaming Δ Δ' τ →
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
      | succ i =>
        have HR := (R i).rename hrename
          (ProofShape.ContextRenaming.of_liftN hΓ₀ hΓA' Ctx.LiftN.one)
        simpa only [subst_bvar_liftN, ProofShape.Subst.lift] using HR
    have HB := ihb hΓA' (W.lift henv.ordered hA) hb (E.lift hΓ₀ W hA) RB
    rw [show proofEraseCtx (A.subst σ :: Γ₀) =
      (proofErase Γ A).subst ρ :: proofEraseCtx Γ₀ from
      congrArg (· :: proofEraseCtx Γ₀) (proofErase_subst_with hΓ₀ W hA E)] at HB
    simp only [ProofShape.subst]
    first | exact .lam (ihA hΓ₀ W hA E R) HB | exact .forallE (ihA hΓ₀ W hA E R) HB


/-- Computing an argument through every occurrence in a typed body preserves
its joint stage, with no recovery premise on either the argument or its output. -/
theorem proofErase_joint_compute_inst_argument
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ) (proofErase Γ x) out) :
    ScopedCompute (ErasedJointStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) ((proofErase (A :: Γ) b).inst out) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have H := proofErase_compute_subst_images_of_renaming (erased_joint_stage_rename heq hs stage)
    hΓA.1 W hb (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one out) (fun i => by
      cases i with
      | zero => exact R
      | succ i => exact .refl)
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using H

end Lean4Lean.VEnv.Strengthening
