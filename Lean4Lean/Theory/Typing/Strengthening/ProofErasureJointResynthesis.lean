import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDescent

/-! # The remaining re-synthesis obligation for joint carrier checking

The known old carrier counterexample is repaired by the joint grammar. Its
substitution law is not thereby proved. This file records the exact replacement
obligation and its necessary type-exposure consequence.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Missing typed joint re-synthesis for the mutually recursive carrier grammar.
After a diagonal typed substitution, a new recovered Pi and a guard at its new
domain must be chosen together. This is not established for the joint stages
or their union, and is not claimed a smaller sufficient strengthening front. -/
def JointCarrierDomainResynthesis
    (Recovery Step : List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {Γ Γ₀ σ f x y D C A B}, OnCtx Γ₀ (env.IsType univs) →
    Ctx.SubstEq env univs Γ₀ σ σ Γ →
    env.HasType univs Γ f (.forallE D C) →
    env.HasType univs Γ x D → env.HasType univs Γ y D →
    ProofShape.ScopedTypeRecovery Recovery (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B) →
    ProofShape.JointCarrierGuard Step (proofEraseCtx Γ) A (proofErase Γ x) (proofErase Γ y) →
    ∃ A' B', ProofShape.ScopedTypeRecovery Recovery (proofEraseCtx Γ₀)
        (proofErase Γ₀ (f.subst σ)) (.forallE A' B') ∧
      ProofShape.JointCarrierGuard Step (proofEraseCtx Γ₀) A'
        (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (y.subst σ))

/-- Re-synthesis already requires Pi recovery of every non-proof function whose
domain has an inhabitant. The input function is merely a fresh variable, and
the argument guard is reflexive; no nontrivial carrier reasoning is involved. -/
theorem JointCarrierDomainResynthesis.pi_of_inhabited
    (H : JointCarrierDomainResynthesis Recovery Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE D C)) (hx : env.HasType univs Γ x D)
    (hn : ¬ IsProof Γ f) :
    ∃ A B, ProofShape.ScopedTypeRecovery Recovery (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE A B) := by
  let F := VExpr.forallE D C
  obtain ⟨u, hF⟩ := hf.isType henv hΓ
  have hΓF : OnCtx (F :: Γ) (env.IsType univs) := ⟨hΓ, u, hF⟩
  have hv : env.HasType univs (F :: Γ) (.bvar 0) F.lift := .bvar .zero
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := f) (A₀ := F)).substEq hΓF hf
  have hvn : ¬ IsProof (F :: Γ) (.bvar 0) := fun hp => hn ((isProof_subst hΓ W hv).2 hp)
  have EPi : proofErase (F :: Γ) F.lift =
      .forallE (proofErase (F :: Γ) D.lift)
        (proofErase (D.lift :: F :: Γ) (C.liftN 1 1)) :=
    if_neg (not_isProof_of_sort hΓF (hF.weak henv))
  have R : ProofShape.ScopedTypeRecovery Recovery (proofEraseCtx (F :: Γ))
      (proofErase (F :: Γ) (.bvar 0))
      (.forallE (proofErase (F :: Γ) D.lift)
        (proofErase (D.lift :: F :: Γ) (C.liftN 1 1))) := by
    rw [show proofErase (F :: Γ) (.bvar 0) = .bvar 0 from if_neg hvn,
      ← EPi, ← erasedTypeOracle_valid hΓF (Lookup.zero (ty := F)), ← proofEraseCtx_oracle]
    exact .bvar
  obtain ⟨A, B, HR, _⟩ := H hΓ W hv (hx.weak henv) (hx.weak henv) R (.carrierChecked (.leaf .refl))
  exact ⟨A, B, HR⟩

/-- Joint re-synthesis forces Pi exposure after adding a function
variable and an argument variable. Unlike the raw-recovery version, this theorem
does not retract the contextual computation to the original context: that would
require an additional contextual transport argument, not an arbitrary raw filler. -/
theorem JointCarrierDomainResynthesis.positive_pi_exposure_above
    (H : JointCarrierDomainResynthesis Recovery Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ u)))
    (HT : env.IsDefEqU univs Γ T (.forallE A B)) :
    ∃ A' B', ProofShape.ScopedCompute Recovery (proofEraseCtx (A.lift :: T :: Γ))
      (((proofErase Γ T).liftN 1).liftN 1) (.forallE A' B') := by
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, _, hT⟩
  have hv : env.HasType univs (T :: Γ) (.bvar 0) T.lift := .bvar .zero
  have hfun := ((HT.of_l henv hΓ hT).weak henv).defeq hv
  obtain ⟨_, hPi⟩ := hfun.isType henv hΓT
  obtain ⟨⟨v, hA⟩, _, _⟩ := hPi.forallE_inv henv
  have hΓA : OnCtx (A.lift :: T :: Γ) (env.IsType univs) := ⟨hΓT, v, hA⟩
  have hfun' := hfun.weak henv (B := A.lift)
  have hx : env.HasType univs (A.lift :: T :: Γ) (.bvar 0) A.lift.lift := .bvar .zero
  have hv' : env.HasType univs (A.lift :: T :: Γ) (.bvar 1) T.lift.lift := hv.weak henv
  have hn := not_proof_at_positive_type hΓA ((hT.weak henv).weak henv) hv'
  obtain ⟨A', B', HR⟩ := H.pi_of_inhabited hΓA hfun' hx hn
  change ProofShape.ScopedTypeRecovery Recovery (proofEraseCtx (A.lift :: T :: Γ))
    (proofErase (A.lift :: T :: Γ) (.bvar 1)) (.forallE A' B') at HR
  rw [show proofErase (A.lift :: T :: Γ) (.bvar 1) = .bvar 1 from if_neg hn] at HR
  have RC := HR.bvar_compute
  exact ⟨_, _, RC⟩

end Lean4Lean.VEnv.Strengthening
