import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedEtaApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedProjection
import Lean4Lean.Theory.Typing.Strengthening.EtaStep
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedTypedSingletonStages

/-! # Scoped certificates for eta at every compatible position

One typed function or structure eta step is covered, including function
positions, projections, dependent Pi bodies, and binder annotations. This is a
single-step coverage theorem, not comparison composition for finite eta paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params]

/-- Every single compatible typed eta expansion has a common scoped
certificate. Substitution is needed when an expansion in function position is
consumed by application; projection primitives consume structure expansions.
No transitivity or paired-instantiation hypothesis is used. -/
theorem proofErase_scoped_eta_step
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hprim : ∀ {Δ a b}, ProofShape.Primitive D a b → ProofShape.ScopedCompute Step Δ a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ a T)
    (R : TypedEtaStep Γ a b) :
    ProofShape.ScopedCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) := by
  classical
  induction R generalizing T with
  | root R =>
    cases R with
    | funEta hf =>
      rcases proofErase_eta_forward hΓ hf with E | H
      · rw [E]; exact .refl
      · exact .leaf (.etaR H)
    | structEta hi hp hx hm hc =>
      rcases proofErase_structure_eta_forward hΓ hi hp hx hm hc with E | H
      · rw [E]; exact .refl
      · exact .symm (.structure_head H)
  | appL R ih =>
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    have H := R.toExpansion.simAt hΓ _ hf
    exact proofErase_scoped_apply_same hstep hsubst hΓ hf H.hasType.2 hx (ih hΓ hf)
  | appR R ih =>
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    have H := R.toExpansion.simAt hΓ _ hx
    exact proofErase_scoped_apply_independent hstep hΓ hf hf hx H.hasType.2 .refl (ih hΓ hx)
  | @lamL Γ A A' b R ih =>
    obtain ⟨⟨u, hA⟩, C, hb⟩ := ht.lam_inv henv hΓ
    have HA := R.toExpansion.simAt hΓ _ hA
    have HE := (TypedEtaStep.lamL (b := b) R).toExpansion.simAt hΓ _ ht
    by_cases hp : IsProof Γ (.lam A b)
    · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)]
      exact .refl
    · have hp' := mt (isProof_congr hΓ HE).2 hp
      rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hp,
        show proofErase Γ (.lam A' b) = .lam _ _ from if_neg hp']
      have EB := proofErase_defeqCtx (Γ₁ := A :: Γ) ⟨hΓ, u, hA⟩ (.succ .zero HA) hb
      rw [← EB]
      exact .lamCommon .refl
  | @lamR A Γ b b' R ih =>
    obtain ⟨⟨u, hA⟩, C, hb⟩ := ht.lam_inv henv hΓ
    have HE := (TypedEtaStep.lamR R).toExpansion.simAt hΓ _ ht
    by_cases hp : IsProof Γ (.lam A b)
    · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)]
      exact .refl
    · have hp' := mt (isProof_congr hΓ HE).2 hp
      rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hp,
        show proofErase Γ (.lam A b') = .lam _ _ from if_neg hp']
      exact .lamCommon (ih ⟨hΓ, u, hA⟩ hb)
  | @forallL Γ A A' B R ih =>
    obtain ⟨⟨u, hA⟩, v, hB⟩ := ht.forallE_inv henv
    have HA := R.toExpansion.simAt hΓ _ hA
    have hctx : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have hB' := hB.defeqDFC henv (.succ .zero HA)
    have EB := proofErase_defeqCtx hctx (.succ .zero HA) hB
    rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB)),
      show proofErase Γ (.forallE A' B) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ (HasType.forallE HA.hasType.2 hB')), ← EB]
    exact .forallSorted (.of_typed hΓ hA) (.of_typed hΓ HA.hasType.2) (ih hΓ hA)
      (.of_typed hctx hB) (.of_typed hctx hB) .refl
  | @forallR A Γ B B' R ih =>
    obtain ⟨⟨u, hA⟩, v, hB⟩ := ht.forallE_inv henv
    have hctx : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HB := R.toExpansion.simAt hctx _ hB
    rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB)),
      show proofErase Γ (.forallE A B') = .forallE _ _ from
        if_neg (not_isProof_of_sort hΓ (HasType.forallE hA HB.hasType.2))]
    exact .forallSorted (.of_typed hΓ hA) (.of_typed hΓ hA) .refl
      (.of_typed hctx hB) (.of_typed hctx HB.hasType.2) (ih hctx hB)
  | proj R ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    have HM := R.toExpansion.simAt hΓ _ hm.hasType.2
    exact proofErase_scoped_project hstep hprim hΓ hm.hasType.2 HM.hasType.2 ht (ih hΓ hm.hasType.2)

/-- Single compatible eta coverage holds at every finite general-singleton
stage without increasing its guard depth, including stage zero. -/
theorem proofErase_scoped_typed_singleton_eta_step
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ a T)
    (R : TypedEtaStep Γ a b) :
    ProofShape.ScopedCompare (ErasedScopedTypedSingletonStage D stage)
      (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) := by
  have core : ∀ n {Δ a b}, ErasedIotaPrimitive D a b →
      ErasedScopedTypedSingletonStage D n Δ a b := by
    intro n
    induction n with
    | zero => exact fun H => H
    | succ n ih => exact fun H => .inl (ih H)
  exact proofErase_scoped_eta_step
    (erased_scoped_typed_singleton_stage_descent heq hs stage)
    (erased_scoped_typed_singleton_stage_subst heq hs stage)
    (fun H => .base (core stage (.inl (.inl H)))) hΓ ht R

end Lean4Lean.VEnv.Strengthening
