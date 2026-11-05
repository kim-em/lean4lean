import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveIdentityCarrierExposure

/-! # Execute Eq prefixes using identity-annotated carrier exposure

The two endpoint callers can insert written carrier annotations at stage one.
Consequently identity-annotated exposure supplies the exact Eq-prefix case
required by typed stage simulation, without native recovery of the endpoints.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A native caller inserts an identity annotation at its selected domain.
Both caller eta and generic-variable identity use the preceding guard stage;
the actual supplied argument has no recovery premise. -/
theorem staged_caller_argument_identity
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) Δ f (.forallE A B))
    (SD : DomainSort Δ A u) (hu : ¬ u ≈ .zero) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ (.app f x)
      (.app f (.app (.lam A (.bvar 0)) x)) := by
  have RF : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ f
      (.lam A (.app (f.liftN 1) (.bvar 0))) := by
    have R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) Δ f
        (.lam A (.app (f.liftN 1) (etaArgument u))) :=
      .base (.inr (.inr (.inr (.inr (.inl (.intro RN SD))))))
    simpa only [etaArgument, if_neg hu] using R
  have RI : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (n + 1)) (A :: Δ)
      (.bvar 0) (.app (.lam (A.liftN 1) (.bvar 0)) (.bvar 0)) :=
    .base (.inr (.inr (.inr (.inl (.intro .bvar)))))
  apply (ScopedCompute.app RF .refl).trans
  apply (ScopedCompute.app (.lam .refl (.app .refl RI)) .refl).trans
  have RB := BetaRed.beta (A := A)
    (b := .app (f.liftN 1) (.app (.lam (A.liftN 1) (.bvar 0)) (.bvar 0))) (a := x)
  exact .beta (by simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN,
    ProofShape.subst, ProofShape.Subst.one, ProofShape.Subst.cons, ProofShape.Subst.lift,
    ProofShape.lift_subst_cons, ProofShape.subst_id] using RB)

/-- The canonical endpoint callers write the original carrier around both
retained endpoints at stage one. Right then left insertion preserves the two
original caller guards throughout the construction. -/
theorem first_stage_eq_prefix_identity_endpoints
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (Strengthening.eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w α a M m b)) (hw : ¬ w ≈ .zero) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (Strengthening.eqRecBeforeMajor v w α a M m b))
      (ProofShape.eqRecBeforeMajor v w (proofErase Γ α)
        (.app (.lam (proofErase Γ α) (.bvar 0)) (proofErase Γ a))
        (proofErase Γ M) (proofErase Γ m)
        (.app (.lam (proofErase Γ α) (.bvar 0)) (proofErase Γ b))) := by
  obtain ⟨_, _, hα, _, _, _, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  obtain ⟨C1, C4, RN1, RN4⟩ := eq_prefix_endpoint_native_guards
    (Step := ErasedStaticStructureEtaExpansionStage D 0) heq hΓ ht hn
  have Ra := staged_caller_argument_identity RN1 (DomainSort.of_typed hΓ hα) hw (x := proofErase Γ a)
  have Rb := staged_caller_argument_identity RN4 (DomainSort.of_typed hΓ hα) hw (x := proofErase Γ b)
  have ES := proofErase_const_spine (args := [α, a, M, m, b]) hΓ ht hn
  change proofErase Γ (Strengthening.eqRecBeforeMajor v w α a M m b) =
    ProofShape.eqRecBeforeMajor v w (proofErase Γ α) (proofErase Γ a)
      (proofErase Γ M) (proofErase Γ m) (proofErase Γ b) at ES
  rw [ES]
  exact Rb.trans (.app (.app (.app Ra .refl) .refl) .refl)

/-- Identity-annotated carrier exposure suffices to execute the original Eq
prefix at stage one. The caller creates the annotations, exposure computes
inside them, and the outer eta frame preserves the exact original output.
Propositional carriers use equal proof erasures directly. -/
theorem first_stage_eq_prefix_of_identity_carrier_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (Strengthening.eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w α a M m b))
    (H : IdentityCarrierExposure D (proofEraseCtx Γ) (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (Strengthening.eqRecBeforeMajor v w α a M m b))
      (.lam (eqProofType w (proofErase Γ α) (proofErase Γ a) (proofErase Γ b)) ((proofErase Γ m).liftN 1)) := by
  obtain ⟨_, _, hα, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  by_cases hw : w ≈ .zero
  · have hα0 := (IsDefEq.sortDF (hα.sort_r henv hΓ) (by trivial) hw).defeq hα
    have Ea := proofErase_eq_proof.2 (show IsProof Γ a from ⟨_, ha, hα0⟩)
    have Eb := proofErase_eq_proof.2 (show IsProof Γ b from ⟨_, hb, hα0⟩)
    apply first_stage_eq_prefix_of_computed_guard heq hs hΓ ht hn .refl .refl .refl .refl
    rw [Ea, Eb]
    exact .carrierChecked (.leaf .refl)
  obtain ⟨C, x, y, RC, RX, RY, HG⟩ := H
  have Ropen := first_stage_eq_prefix_identity_endpoints (D := D) heq hΓ ht hn hw
  have Rchange : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (ProofShape.eqRecBeforeMajor v w (proofErase Γ α)
        (.app (.lam (proofErase Γ α) (.bvar 0)) (proofErase Γ a)) (proofErase Γ M) (proofErase Γ m)
        (.app (.lam (proofErase Γ α) (.bvar 0)) (proofErase Γ b)))
      (ProofShape.eqRecBeforeMajor v w C x (proofErase Γ M) (proofErase Γ m) y) :=
    .app (.app (.app (.app (.app .refl RC) RX) .refl) .refl) RY
  obtain ⟨body, RN, SD⟩ := eq_prefix_literal_native_guard
    (Step := ErasedStaticStructureEtaExpansionStage D 0) heq hΓ ht hn
  apply staged_eta_retains_constant_domain heq hs RN SD
  exact Ropen.trans (Rchange.trans (.base (.inr (.inr (.inl (.intro HG))))))

/-- A typed raw prefix has the same exact contraction from annotated carrier
exposure. The actual source realization is recovered from its raw spine. -/
theorem first_stage_typed_eq_prefix_of_identity_carrier_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HT : TypedSource Δ (ProofShape.eqRecBeforeMajor v w α a M m b))
    (H : IdentityCarrierExposure D Δ α a b) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ
      (ProofShape.eqRecBeforeMajor v w α a M m b) (.lam (eqProofType w α a b) (m.liftN 1)) := by
  obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
  obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Eα, Ea, EM, Em, Eb⟩ := proofErase_eqRecBeforeMajor_inv Ee
  have hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w α₀ a₀ M₀ m₀ b₀) := by
    intro hp
    rw [proofErase_eq_proof.2 hp] at Ee
    cases Ee
  have R := first_stage_eq_prefix_of_identity_carrier_exposure heq hs hΓ ht hn
    (by simpa only [EΓ, Eα, Ea, Eb] using H)
  simpa only [EΓ, Ee, Eα, Ea, Eb, Em] using R

/-- Annotated carrier exposure discharges the complete typed Eq-prefix rule
simulation interface. Exposure itself is a hypothesis here; the recursive
carrier theorem reduces it to common-comparison and record-family cases. -/
theorem first_stage_typed_eq_prefix_simulation_of_carrier_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (HE : ∀ {Γ A a b}, OnCtx Γ (env.IsType univs) →
      env.HasType univs Γ a A → env.HasType univs Γ b A →
      ComputedJointCarrierGuard Source (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) →
      IdentityCarrierExposure D (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b))
    (HT : TypedSource Δ e) (R : ComputedJointPrefixPrimitive Source Δ e out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ e out := by
  cases R with
  | intro HG =>
    apply first_stage_typed_eq_prefix_of_identity_carrier_exposure heq hs HT
    obtain ⟨Γ, e, T, hΓ, EΓ, ht, Ee⟩ := HT
    obtain ⟨α₀, a₀, M₀, m₀, b₀, rfl, Eα, Ea, EM, Em, Eb⟩ := proofErase_eqRecBeforeMajor_inv Ee
    obtain ⟨_, _, _, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
    have H := HE hΓ ha hb (by simpa only [EΓ, Eα, Ea, Eb] using HG)
    simpa only [EΓ, Eα, Ea, Eb] using H

end Lean4Lean.VEnv.Strengthening
