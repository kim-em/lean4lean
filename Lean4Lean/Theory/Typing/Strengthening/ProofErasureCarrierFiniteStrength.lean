import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierFiniteResynthesis

/-! # Finite re-synthesis still requires finite Pi head exposure

An existential output stage removes a fixed computational bound, not the
head-exposure obligation. These necessary conditions use only reflexive
argument guards and no typed inhabitants below the retracted binders.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Re-synthesis already requires Pi recovery of every non-proof function whose
domain has an inhabitant. The input function is merely a fresh variable, and
the argument guard is reflexive; no nontrivial carrier reasoning is involved. -/
theorem FiniteCarrierDomainResynthesis.pi_of_inhabited
    (H : FiniteCarrierDomainResynthesis Recoveries Stages)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE D C)) (hx : env.HasType univs Γ x D)
    (hn : ¬ IsProof Γ f) :
    ∃ stage A B, ProofShape.TypeRecovery (Recoveries stage) (ProofShape.contextOracle (proofEraseCtx Γ))
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
  have R : ProofShape.TypeRecovery (Recoveries 0) (ProofShape.contextOracle (proofEraseCtx (F :: Γ)))
      (proofErase (F :: Γ) (.bvar 0))
      (.forallE (proofErase (F :: Γ) D.lift)
        (proofErase (D.lift :: F :: Γ) (C.liftN 1 1))) := by
    rw [show proofErase (F :: Γ) (.bvar 0) = .bvar 0 from if_neg hvn,
      ← EPi, proofEraseCtx_oracle, ← erasedTypeOracle_valid hΓF (Lookup.zero (ty := F))]
    exact .bvar
  obtain ⟨stage, A, B, _, HR, _⟩ := H hΓ W hv (hx.weak henv) (hx.weak henv) R (.checked .refl)
  exact ⟨stage, A, B, HR⟩

/-- Joint re-synthesis entails positive-universe Pi head exposure, even when
the Pi domain is empty. Fresh variables supply the function and its argument;
raw substitution retracts the resulting computation without typed inhabitants
below. The recovered domain and codomain may be different representatives. -/
theorem FiniteCarrierDomainResynthesis.positive_pi_exposure
    (hsubst : ∀ stage {a b} {σ : ProofShape.Subst}, Recoveries stage a b →
      Recoveries stage (a.subst σ) (b.subst σ))
    (H : FiniteCarrierDomainResynthesis Recoveries Stages)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ u)))
    (HT : env.IsDefEqU univs Γ T (.forallE A B)) :
    ∃ stage A' B', ProofShape.Compute (Recoveries stage) (proofErase Γ T) (.forallE A' B') := by
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
  obtain ⟨stage, A', B', HR⟩ := H.pi_of_inhabited hΓA hfun' hx hn
  change ProofShape.TypeRecovery (Recoveries stage) (ProofShape.contextOracle (proofEraseCtx (A.lift :: T :: Γ)))
    (proofErase (A.lift :: T :: Γ) (.bvar 1)) (.forallE A' B') at HR
  rw [show proofErase (A.lift :: T :: Γ) (.bvar 1) = .bvar 1 from if_neg hn,
    proofEraseCtx_oracle] at HR
  have RC := HR.bvar_compute
  change ProofShape.Compute (Recoveries stage) (((proofErase Γ T).liftN 1).liftN 1) (.forallE A' B') at RC
  have RR := RC.subst (hsubst stage) (σ := (ProofShape.Subst.id.cons .proof).cons .proof)
  simp only [ProofShape.lift_subst_cons, ProofShape.subst_id, ProofShape.subst] at RR
  exact ⟨stage, _, _, RR⟩

omit [Params] in
/-- Growing only the comparison stages cannot repair re-synthesis while
recovery remains the ordinary core. Every candidate later stage would still
have to expose the same free-proof Pi cast by ordinary core computation. -/
theorem not_finite_carrier_domain_resynthesis_constant_core {env : VEnv} (henv : env.WF)
    (U : Nat) (heq : env.HasCanonicalEq)
    (Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop) :
    letI := henv.params U
    ¬ FiniteCarrierDomainResynthesis (fun _ => ErasedCore.Step) Stages := by
  letI := henv.params U
  intro H
  let u : VLevel := .succ (.succ (.succ .zero))
  let X : VExpr := .sort (.succ (.succ .zero))
  let F : VExpr := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  let Q := eqApp (.succ u) (.sort u) X X
  have hu : u.WF U := by trivial
  have hX : env.HasType U [] X (.sort u) := .sort (by trivial)
  have hF : env.HasType U [] F X :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  have hQ : env.HasType U [] Q (.sort .zero) :=
    HasType.eqApp heq hu (HasType.sort hu) hX hX
  have hΓ : OnCtx [Q] (env.IsType U) := ⟨trivial, _, hQ⟩
  have hXΓ : env.HasType U [Q] X (.sort u) := hX.weak0 henv.ordered
  have hFΓ : env.HasType U [Q] F X := hF.weak0 henv.ordered
  have hq : env.HasType U [Q] (.bvar 0) Q := by
    have HH : env.HasType U [Q] (.bvar 0) Q.lift := .bvar .zero
    simpa [Q, X, eqApp, VExpr.lift, liftN] using HH
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hXΓ hq hFΓ
  obtain ⟨stage, A', B', R⟩ := H.positive_pi_exposure
    (by intro stage a b σ HR; exact erased_iota_primitive_subst HR) hΓ HC.hasType.1 ⟨_, HC⟩
  exact ErasedCore.cast_no_pi henv U heq hu hΓ hXΓ hq hFΓ
    (R.scoped (fun H => .base H))

end Lean4Lean.VEnv.Strengthening
