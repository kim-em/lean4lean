import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedCarrierApplication

/-! # Joint re-synthesis with contextual recovery

The old compared-K recovery family is refuted. This interface allows conversion
in the actual context at every recovery node, while retaining the simultaneous
choice of a recovered domain and its argument guard. Its concrete realization
remains open; the conditional application theorem records precisely its use.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private not_proof_at_positive_type from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedUnitBoundary
variable [Params]

/-- Missing finite-stage joint re-synthesis. Both the recovered Pi and the
argument carrier guard may move to a common later stage, with no prescribed
domain or codomain syntax. This is unproved for the concrete stage families
and is not claimed a strictly smaller or sufficient strengthening front. -/
def ScopedFiniteCarrierDomainResynthesis
    (Recoveries : Nat → List ProofShape → ProofShape → ProofShape → Prop)
    (Stages : Nat → List ProofShape → ProofShape → ProofShape → Prop) : Prop :=
  ∀ {stage Γ Γ₀ σ f x y D C A B}, OnCtx Γ₀ (env.IsType univs) →
    Ctx.SubstEq env univs Γ₀ σ σ Γ →
    env.HasType univs Γ f (.forallE D C) →
    env.HasType univs Γ x D → env.HasType univs Γ y D →
    ProofShape.ScopedTypeRecovery (Recoveries stage) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE A B) →
    ProofShape.StructureCarrierGuard (Stages stage) (proofEraseCtx Γ) A
      (proofErase Γ x) (proofErase Γ y) →
    ∃ later A' B', stage ≤ later ∧
      ProofShape.ScopedTypeRecovery (Recoveries later) (proofEraseCtx Γ₀)
        (proofErase Γ₀ (f.subst σ)) (.forallE A' B') ∧
      ProofShape.StructureCarrierGuard (Stages later) (proofEraseCtx Γ₀) A'
        (proofErase Γ₀ (x.subst σ)) (proofErase Γ₀ (y.subst σ))

/-- The finite-stage law transports recovered application roots after typed
substitution. Monotonicity moves the independently substituted function
comparison to the stage chosen by joint re-synthesis. -/
theorem proofErase_scoped_carrier_application_subst_of_finite_resynthesis
    (hres : ScopedFiniteCarrierDomainResynthesis Recoveries Stages)
    (hsubst : ∀ stage {Δ Δ' a b τ}, Stages stage Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Stages stage Δ' (a.subst τ) (b.subst τ))
    (hmono : ∀ {stage later}, stage ≤ later → ∀ {Δ a b}, Stages stage Δ a b → Stages later Δ a b)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (hf : env.HasType univs Γ f (.forallE D C)) (hg : env.HasType univs Γ g (.forallE D C))
    (hx : env.HasType univs Γ x D) (hy : env.HasType univs Γ y D)
    (hnl : ¬ IsProof Γ (.app f x)) (hnr : ¬ IsProof Γ (.app g y))
    (R : ProofShape.ScopedTypeRecovery (Recoveries stage) (proofEraseCtx Γ)
      (proofErase Γ f) (.forallE A B))
    (HF : ProofShape.ScopedCompare (Stages stage) (proofEraseCtx Γ) false
      (proofErase Γ f) (proofErase Γ g))
    (HX : ProofShape.StructureCarrierGuard (Stages stage) (proofEraseCtx Γ) A
      (proofErase Γ x) (proofErase Γ y)) :
    ∃ later, stage ≤ later ∧
      ProofShape.ScopedRecoveredCarrierApplication (Recoveries later) (Stages later) (proofEraseCtx Γ₀)
        (proofErase Γ₀ ((VExpr.app f x).subst σ)) (proofErase Γ₀ ((VExpr.app g y).subst σ)) := by
  obtain ⟨later, A', B', hle, R', HX'⟩ := hres hΓ₀ W hf hx hy R HX
  have HF' := proofErase_scoped_compare_subst (hsubst stage) hΓ₀ W hf hg HF
  have hnl' := mt (isProof_subst hΓ₀ W (hf.app hx)).1 hnl
  have hnr' := mt (isProof_subst hΓ₀ W (hg.app hy)).1 hnr
  refine ⟨later, hle, ?_⟩
  rw [show proofErase Γ₀ ((VExpr.app f x).subst σ) = .app _ _ from if_neg hnl',
    show proofErase Γ₀ ((VExpr.app g y).subst σ) = .app _ _ from if_neg hnr']
  exact .app R' (HF'.mono (hmono hle)) HX'

/-- Re-synthesis already requires Pi recovery of every non-proof function whose
domain has an inhabitant. The input function is merely a fresh variable, and
the argument guard is reflexive; no nontrivial carrier reasoning is involved. -/
theorem ScopedFiniteCarrierDomainResynthesis.pi_of_inhabited
    (H : ScopedFiniteCarrierDomainResynthesis Recoveries Stages)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE D C)) (hx : env.HasType univs Γ x D)
    (hn : ¬ IsProof Γ f) :
    ∃ stage A B, ProofShape.ScopedTypeRecovery (Recoveries stage) (proofEraseCtx Γ)
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
  have R : ProofShape.ScopedTypeRecovery (Recoveries 0) (proofEraseCtx (F :: Γ))
      (proofErase (F :: Γ) (.bvar 0))
      (.forallE (proofErase (F :: Γ) D.lift)
        (proofErase (D.lift :: F :: Γ) (C.liftN 1 1))) := by
    rw [show proofErase (F :: Γ) (.bvar 0) = .bvar 0 from if_neg hvn,
      ← EPi, ← erasedTypeOracle_valid hΓF (Lookup.zero (ty := F)), ← proofEraseCtx_oracle]
    exact .bvar
  obtain ⟨stage, A, B, _, HR, _⟩ := H hΓ W hv (hx.weak henv) (hx.weak henv) R (.checked .refl)
  exact ⟨stage, A, B, HR⟩

/-- Joint re-synthesis forces finite Pi exposure after adding a function
variable and an argument variable. Unlike the raw-recovery version, this theorem
does not retract the contextual computation to the original context: that would
require an additional contextual transport argument, not an arbitrary raw filler. -/
theorem ScopedFiniteCarrierDomainResynthesis.positive_pi_exposure_above
    (H : ScopedFiniteCarrierDomainResynthesis Recoveries Stages)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hT : env.HasType univs Γ T (.sort (.succ u)))
    (HT : env.IsDefEqU univs Γ T (.forallE A B)) :
    ∃ stage A' B', ProofShape.ScopedCompute (Recoveries stage) (proofEraseCtx (A.lift :: T :: Γ))
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
  obtain ⟨stage, A', B', HR⟩ := H.pi_of_inhabited hΓA hfun' hx hn
  change ProofShape.ScopedTypeRecovery (Recoveries stage) (proofEraseCtx (A.lift :: T :: Γ))
    (proofErase (A.lift :: T :: Γ) (.bvar 1)) (.forallE A' B') at HR
  rw [show proofErase (A.lift :: T :: Γ) (.bvar 1) = .bvar 1 from if_neg hn] at HR
  have RC := HR.bvar_compute
  exact ⟨stage, _, _, RC⟩

end Lean4Lean.VEnv.Strengthening
