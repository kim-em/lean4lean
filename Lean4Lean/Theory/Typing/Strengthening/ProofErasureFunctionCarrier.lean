import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStructureSingletonStages

/-! # Recursive function carriers and lambda coverage

A common Pi carrier permits pointwise carrier comparison at a fresh argument.
The domain-sort witness chooses the exact erased argument, and endpoint
computation covers beta after eta expansion. No subsingleton result premise is
needed. General paired substitution of distinct arguments remains open.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Actual fresh applications supply the recursive function guard. Both proof
and data domains are covered, and proof-valued functions erase outright. -/
theorem proofErase_function_carrier_forward
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ g (.forallE A B))
    (H : ProofShape.StructureCarrierGuard Step (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) (.app f.lift (.bvar 0)))
      (proofErase (A :: Γ) (.app g.lift (.bvar 0)))) :
    ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ f) (proofErase Γ g) := by
  by_cases hpf : IsProof Γ f
  · have hpg := isProof_of_common_type hΓ hf hg hpf
    rw [proofErase_eq_proof.2 hpf, proofErase_eq_proof.2 hpg]
    exact .checked .refl
  have hpg : ¬ IsProof Γ g := fun hp => hpf (isProof_of_common_type hΓ hg hf hp)
  obtain ⟨_, hT⟩ := hf.isType henv hΓ
  rw [show proofErase Γ (.forallE A B) =
    .forallE (proofErase Γ A) (proofErase (A :: Γ) B) from if_neg (not_isProof_of_sort hΓ hT)]
  apply ProofShape.StructureCarrierGuard.function (.of_typed hΓ hA)
  simpa only [proofEraseCtx, proofErase_eta_body hΓ hA hf hpf,
    proofErase_eta_body hΓ hA hg hpg] using H

/-- Lambda bodies compared at a supplied common codomain produce a carrier
comparison of the abstractions. The bodies can use recursive structure or
function guards rather than ordinary scoped comparison. -/
theorem proofErase_lambda_carrier_forward
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (hb' : env.HasType univs (A :: Γ) b' B)
    (H : ProofShape.StructureCarrierGuard Step (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) b) (proofErase (A :: Γ) b')) :
    ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B))
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam A b')) := by
  apply proofErase_function_carrier_forward hΓ hA (HasType.lam hA hb) (HasType.lam hA hb')
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hl := HasType.app ((HasType.lam hA hb).weak henv (B := A)) (HasType.bvar .zero)
  have hr := HasType.app ((HasType.lam hA hb').weak henv (B := A)) (HasType.bvar .zero)
  have El := proofErase_beta_forward hΓA hl (BetaRed.beta (a := .bvar 0))
  have Er := proofErase_beta_forward hΓA hr (BetaRed.beta (a := .bvar 0))
  simp only [lift, liftN, inst_liftN_bvar] at El Er
  exact .reduce (.beta El) (.beta Er) H

/-- The complete recursive carrier guard survives ordinary typed substitution,
including its fresh function binders and endpoint computation. -/
theorem proofErase_carrier_subst
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ₀)
      (proofErase Γ₀ (A.subst σ)) (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  let τ : ProofShape.Subst := fun i => proofErase Γ₀ (σ i)
  have E : ErasedSubstAgreement Γ Γ₀ σ τ := fun _ _ => rfl
  obtain ⟨_, hA⟩ := ha.isType henv W.wf
  rw [proofErase_subst_with hΓ₀ W hA E, proofErase_subst_with hΓ₀ W ha E,
    proofErase_subst_with hΓ₀ W hb E]
  exact H.subst hsubst (ProofShape.ContextSubstitution.of_typed hΓ₀ W E)

/-- Single-argument instantiation has the full carrier guard as its output.
This is diagonal substitution, not the missing law for distinct arguments. -/
theorem proofErase_carrier_instN
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hx : env.HasType univs Γ₀ x A₀)
    (W : Ctx.InstN Γ₀ x A₀ k Γ₁ Γ)
    (ha : env.HasType univs Γ₁ a A) (hb : env.HasType univs Γ₁ b A)
    (H : ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ₁)
      (proofErase Γ₁ A) (proofErase Γ₁ a) (proofErase Γ₁ b)) :
    ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (A.inst x k)) (proofErase Γ (a.inst x k)) (proofErase Γ (b.inst x k)) := by
  have hΓ := (W.wf henv hx hΓ₁).2
  simpa only [← instN_eq] using
    proofErase_carrier_subst hsubst hΓ (W.substEq hΓ₁ hx) ha hb H

end Lean4Lean.VEnv.Strengthening
