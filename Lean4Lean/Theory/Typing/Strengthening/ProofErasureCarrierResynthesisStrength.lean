import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainResynthesis
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortRecovery

/-! # Computational strength required by joint domain re-synthesis

Even reflexive argument guards force recovery of arbitrary non-proof functions
at inhabited domains. Adding fresh variables and retracting raw computation
then exposes the head of any type convertible to a Pi. This is a necessary
condition on re-synthesis, not a proof of the re-synthesis law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Re-synthesis already requires Pi recovery of every non-proof function whose
domain has an inhabitant. The input function is merely a fresh variable, and
the argument guard is reflexive; no nontrivial carrier reasoning is involved. -/
theorem CarrierDomainResynthesis.pi_of_inhabited
    (H : CarrierDomainResynthesis Recovery Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE D C)) (hx : env.HasType univs Γ x D)
    (hn : ¬ IsProof Γ f) :
    ∃ A B, ProofShape.TypeRecovery Recovery (ProofShape.contextOracle (proofEraseCtx Γ))
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
  have R : ProofShape.TypeRecovery Recovery (ProofShape.contextOracle (proofEraseCtx (F :: Γ)))
      (proofErase (F :: Γ) (.bvar 0))
      (.forallE (proofErase (F :: Γ) D.lift)
        (proofErase (D.lift :: F :: Γ) (C.liftN 1 1))) := by
    rw [show proofErase (F :: Γ) (.bvar 0) = .bvar 0 from if_neg hvn,
      ← EPi, proofEraseCtx_oracle, ← erasedTypeOracle_valid hΓF (Lookup.zero (ty := F))]
    exact .bvar
  obtain ⟨A, B, HR, _⟩ := H hΓ W hv (hx.weak henv) (hx.weak henv) R (.checked .refl)
  exact ⟨A, B, HR⟩

/-- Joint re-synthesis entails positive-universe Pi head exposure, even when
the Pi domain is empty. Fresh variables supply the function and its argument;
raw substitution retracts the resulting computation without typed inhabitants
below. The recovered domain and codomain may be different representatives. -/
theorem CarrierDomainResynthesis.positive_pi_exposure
    (hsubst : ∀ {a b} {σ : ProofShape.Subst}, Recovery a b → Recovery (a.subst σ) (b.subst σ))
    (H : CarrierDomainResynthesis Recovery Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ u)))
    (HT : env.IsDefEqU univs Γ T (.forallE A B)) :
    ∃ A' B', ProofShape.Compute Recovery (proofErase Γ T) (.forallE A' B') := by
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
  change ProofShape.TypeRecovery Recovery (ProofShape.contextOracle (proofEraseCtx (A.lift :: T :: Γ)))
    (proofErase (A.lift :: T :: Γ) (.bvar 1)) (.forallE A' B') at HR
  rw [show proofErase (A.lift :: T :: Γ) (.bvar 1) = .bvar 1 from if_neg hn,
    proofEraseCtx_oracle] at HR
  have RC := HR.bvar_compute
  change ProofShape.Compute Recovery (((proofErase Γ T).liftN 1).liftN 1) (.forallE A' B') at RC
  have RR := RC.subst hsubst (σ := (ProofShape.Subst.id.cons .proof).cons .proof)
  simp only [ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.subst] at RR
  exact ⟨_, _, RR⟩

end Lean4Lean.VEnv.Strengthening
