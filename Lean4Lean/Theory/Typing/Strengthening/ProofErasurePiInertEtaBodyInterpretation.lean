import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaSpineBypass

/-! # Actual typing for an eta body's application continuation

The recovered eta domain and the original pending argument's assigned domain
agree by type uniqueness. Reifying the computed argument therefore supplies
an ordinary context substitution below the original eta binder. This does not
assert native recovery or guarded computation closure for that argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- The original eta body is typed, and its actual computed first argument
interprets instantiation from the original binder context to the outer scope.
Changing lambda annotations do not change the domain used by this witness. -/
theorem pi_inert_eta_body_interpretation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs')) :
    TypedSource (A :: Δ) (.app (f.liftN 1) (etaArgument u)) ∧
      ContextSubstitution (A :: Δ) Δ (ProofShape.Subst.one x') := by
  cases RX with
  | cons RX _ =>
    have HTapp : TypedSource Δ (.app f _) := typed_spine_head HT
    obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HTapp
    obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨A₀, B₀, hf, hx⟩ := ht.app_inv henv hΓ
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨A₁, B₁, hf₁, EA, _⟩ := proofErase_scoped_recovered_pi_descend hguard hΓ hΓ W hf
      (by simpa only [ProofShape.liftN_zero, Ef] using RN)
    obtain ⟨_, hPi⟩ := hf₁.isType henv hΓ
    obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
    have hA := (EA ▸ SD).descend hΓ hΓ W hA
    simp only [ProofShape.liftN_zero] at EA
    have hΓA : OnCtx (A₁ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨x₁, HX, EX⟩ := proofErase_scoped_compute_realize
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
      hΓ hx rfl Ex RX.forget
    have hxA := argument_at_displayed_domain hΓ hf hf₁ HX.hasType.2
    have hnf : ¬ IsProof Γ f₀ := fun hp => RN.ne_proof (Ef.symm.trans (proofErase_eq_proof.2 hp))
    have hfw : env.HasType univs (A₁ :: Γ) f₀.lift
        (.forallE A₁.lift (B₁.liftN 1 1)) := hf₁.weak henv
    have hb : env.HasType univs (A₁ :: Γ) (.app f₀.lift (.bvar 0)) B₁ := by
      simpa only [VExpr.inst_liftN_bvar] using hfw.app (HasType.bvar .zero)
    refine ⟨⟨A₁ :: Γ, _, B₁, hΓA, ?_, hb, ?_⟩, ?_⟩
    · simp only [proofEraseCtx, EA]
    · simpa only [Ef] using proofErase_eta_body hΓ hA hf₁ hnf
    · have WI : ContextSubstitution (proofEraseCtx (A₁ :: Γ)) (proofEraseCtx Γ)
          (ProofShape.Subst.one (proofErase Γ x₁)) :=
        ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓA hxA)
          (erasedSubstAgreement_one hΓA hxA)
      rw [proofEraseCtx, EA, EX] at WI
      intro Γ' hΓ' EΓ'
      exact WI hΓ' EΓ'

end Lean4Lean.VEnv.Strengthening
