import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecoveryThinning
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEta
import Lean4Lean.Theory.Typing.Strengthening.RecoverySubstitutionBoundary

/-! # Exact recovery substitution still fails after proof erasure

The captured variable is a proposition, rather than a proof, so erasure retains
it. A typed identity may be assigned the captured Pi by conversion, but no finite
erased recovery stage can recover its exact erasure from that scoped identity.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedRecoverySubstitutionBoundary
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments EtaScope

/-- The captured proposition remains visible inside a beta-redex annotation. -/
def captured : ProofShape :=
  .forallE (.app (.lam (.sort .zero) (.sort .zero)) (.bvar 0)) (.sort .zero)

/-- This raw type cannot be the image of any shape under one fresh insertion. -/
theorem captured_not_thinned (a : ProofShape) : a.lift' (.skip .refl) ≠ captured := by
  intro H
  obtain ⟨_, _, _, HD, _⟩ := ProofShape.lift'_forallE_inv H
  obtain ⟨_, x, _, _, Hx⟩ := ProofShape.lift'_app_inv HD
  cases x <;> simp_all [ProofShape.lift', Lift.liftVar]

variable [Params]

/-- Proof erasure retains the extra proposition variable in the chosen type. -/
theorem captured_erasure (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase (.sort .zero :: Γ) (capturedPi (.sort .zero)) = captured := by
  have hS : env.HasType univs Γ (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) := ⟨hΓ, _, hS⟩
  have hS' : env.HasType univs (.sort .zero :: Γ) (.sort .zero) (.sort (.succ .zero)) := .sort (by trivial)
  have hΓSS : OnCtx (.sort .zero :: .sort .zero :: Γ) (env.IsType univs) := ⟨hΓS, _, hS'⟩
  have hL : env.HasType univs (.sort .zero :: Γ) (.lam (.sort .zero) (.sort .zero))
      (.forallE (.sort .zero) (.sort (.succ .zero))) := .lam hS' (.sort (by trivial))
  have hx : env.HasType univs (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have hD : env.HasType univs (.sort .zero :: Γ) (capturedDomain (.sort .zero))
      (.sort (.succ .zero)) := .app hL hx
  have hΓD : OnCtx (capturedDomain (.sort .zero) :: .sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓS, _, hD⟩
  have hPi : env.HasType univs (.sort .zero :: Γ) (capturedPi (.sort .zero))
      (.sort (.imax (.succ .zero) (.succ .zero))) := .forallE hD (.sort (by trivial))
  have E (Δ : List VExpr) (hΔ : OnCtx Δ (env.IsType univs)) :
      proofErase Δ (.sort .zero) = .sort .zero :=
    if_neg (not_isProof_of_sort hΔ (HasType.sort (by trivial)))
  rw [show proofErase (.sort .zero :: Γ) (capturedPi (.sort .zero)) =
      .forallE (proofErase (.sort .zero :: Γ) (capturedDomain (.sort .zero)))
        (proofErase (capturedDomain (.sort .zero) :: .sort .zero :: Γ) (.sort .zero)) from
      if_neg (not_isProof_of_sort hΓS hPi)]
  rw [show proofErase (.sort .zero :: Γ) (capturedDomain (.sort .zero)) =
      .app (proofErase (.sort .zero :: Γ) (.lam (.sort .zero) (.sort .zero)))
        (proofErase (.sort .zero :: Γ) (.bvar 0)) from
      if_neg (not_isProof_of_sort hΓS hD)]
  rw [show proofErase (.sort .zero :: Γ) (.lam (.sort .zero) (.sort .zero)) =
      .lam (proofErase (.sort .zero :: Γ) (.sort .zero))
        (proofErase (.sort .zero :: .sort .zero :: Γ) (.sort .zero)) from
      if_neg (not_isProof_function_to_sort hΓS hL)]
  rw [show proofErase (.sort .zero :: Γ) (.bvar 0) = .bvar 0 from
      if_neg (not_isProof_of_sort hΓS hx), E _ hΓS, E _ hΓSS, E _ hΓD]
  rfl

/-- No finite compared-K stage can recover the captured erased type from the
lifted identity, despite its valid original typing at that selected type. -/
theorem identity_captured_not_recovered (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) :
    ¬ ProofShape.TypeRecovery (ErasedComparedKStage D stage) (erasedTypeOracle (.sort .zero :: Γ))
      (proofErase (.sort .zero :: Γ) (ident 0).lift)
      (proofErase (.sort .zero :: Γ) (capturedPi (.sort .zero))) := by
  intro R
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  rw [lift_eq_lift'] at R
  obtain ⟨A, _, EA⟩ := proofErase_context_typeRecovery_thinning
    (proofErase_compared_K_compute_thinning heq hs stage) hΓ hΓS (.skip .refl)
    (ident_typed env univs Γ 0) R
  rw [captured_erasure hΓ] at EA
  exact captured_not_thinned _ EA

/-- A fully typed substitution starts from a variable recovery certificate, but
its selected output erasure cannot be recovered after substitution at any finite
stage. The omitted variable is a proposition and therefore survives erasure. -/
theorem exact_substitution_failure (stage : Nat) (heq : env.HasCanonicalEq)
    (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) :
    let Δ := VExpr.sort .zero :: Γ
    let C := capturedPi (.sort .zero)
    OnCtx (C :: Δ) (env.IsType univs) ∧
    env.HasType univs Δ (ident 0).lift C ∧
    Ctx.InstN Δ (ident 0).lift C 0 (C :: Δ) Δ ∧
    ProofShape.TypeRecovery (ErasedComparedKStage D stage) (erasedTypeOracle (C :: Δ))
      (proofErase (C :: Δ) (.bvar 0)) (proofErase (C :: Δ) C.lift) ∧
    ∀ stage', ¬ ProofShape.TypeRecovery (ErasedComparedKStage D stage') (erasedTypeOracle Δ)
      (proofErase Δ ((VExpr.bvar 0).inst (ident 0).lift))
      (proofErase Δ (C.lift.inst (ident 0).lift)) := by
  dsimp only
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hf : env.HasType univs (.sort .zero :: Γ) (ident 0).lift (capturedPi (.sort .zero)) :=
    identity_at_captured_pi
  have hΓC : OnCtx (capturedPi (.sort .zero) :: .sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓS, hf.isType henv hΓS⟩
  have hl : Lookup (capturedPi (.sort .zero) :: .sort .zero :: Γ) 0
      (capturedPi (.sort .zero)).lift := .zero
  have hn := not_isProof_function_to_sort hΓC
    (A := (capturedDomain (.sort .zero)).lift) (u := .zero) (HasType.bvar hl)
  refine ⟨hΓC, hf, .zero, ?_, ?_⟩
  · rw [show proofErase (capturedPi (.sort .zero) :: .sort .zero :: Γ) (.bvar 0) = .bvar 0 from
      if_neg hn, ← erasedTypeOracle_valid hΓC hl]
    exact .bvar
  · intro stage'
    simpa only [inst, instVar_zero, liftN_zero, inst_lift] using
      (identity_captured_not_recovered (stage := stage') heq hs hΓ)

/-- The substituted identity still recovers its ordinary Pi type. The failure
concerns preserving a selected captured annotation, not recovery existence. -/
theorem identity_plain_recovery (hΓ : OnCtx Γ (env.IsType univs)) :
    ProofShape.TypeRecovery Step (erasedTypeOracle Γ) (proofErase Γ (ident 0))
      (.forallE (.sort .zero) (.sort .zero)) := by
  have hΓS : OnCtx (.sort .zero :: Γ) (env.IsType univs) :=
    ⟨hΓ, _, HasType.sort (by trivial)⟩
  have hn := not_isProof_function_to_sort hΓ (ident_typed env univs Γ 0)
  have hx : env.HasType univs (.sort .zero :: Γ) (.bvar 0) (.sort .zero) := .bvar .zero
  have hnx := not_isProof_of_sort hΓS hx
  have hns := not_isProof_of_sort hΓ (HasType.sort (l := .zero) (by trivial))
  change ProofShape.TypeRecovery Step (erasedTypeOracle Γ)
    (proofErase Γ (.lam (.sort .zero) (.bvar 0))) _
  change ¬ IsProof Γ (.lam (.sort .zero) (.bvar 0)) at hn
  simp only [proofErase, if_neg hn, if_neg hns, if_neg hnx]
  exact .lam .bvar

omit [Params] in
/-- The rejected selected type beta-computes to the ordinary recovered type. -/
theorem captured_beta_plain :
    ProofShape.BetaRed captured (.forallE (.sort .zero) (.sort .zero)) :=
  .forallE .beta .refl

end Lean4Lean.VEnv.Strengthening.ErasedRecoverySubstitutionBoundary
