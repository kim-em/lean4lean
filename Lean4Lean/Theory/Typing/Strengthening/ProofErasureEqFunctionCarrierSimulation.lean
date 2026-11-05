import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedEqPrefixSimulation

/-! # Function-carrier exposure inside canonical Eq prefixes

The literal recursor declaration supplies native guards at its two endpoint
argument positions. Caller eta can therefore open function endpoints without
assuming that ordinary typing supplies native recovery for either endpoint.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Both endpoint callers of a retained canonical Eq prefix recover their
literal carrier domain at stage zero (indeed at any primitive language).
Their selected codomains need not be identified. -/
theorem eq_prefix_endpoint_native_guards
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (Strengthening.eqRecBeforeMajor v w α a M m b) T)
    (hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w α a M m b)) :
    ∃ C₁ C₄,
      ScopedTypeRecovery Step (proofEraseCtx Γ)
        (.app (.const ``Eq.rec [v, w]) (proofErase Γ α)) (.forallE (proofErase Γ α) C₁) ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ)
        (.app (.app (.app (.app (.const ``Eq.rec [v, w]) (proofErase Γ α))
          (proofErase Γ a)) (proofErase Γ M)) (proofErase Γ m))
        (.forallE (proofErase Γ α) C₄) := by
  obtain ⟨hv, hw, hα, ha, hM, hm, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have hls : ∀ l ∈ [v, w], l.WF univs := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> assumption
  have hc : env.HasType univs Γ (.const ``Eq.rec [v, w]) (canonicalEqRecType.instL [v, w]) :=
    .const heq.2.2.1 hls rfl
  have h4 := HasType.eqRec4 heq hv hw hα ha hM hm
  have hn4 := not_isProof_fn hΓ h4 hb hn
  obtain ⟨_, _, h3, hx4⟩ := h4.app_inv henv hΓ
  have hn3 := not_isProof_fn hΓ h3 hx4 hn4
  obtain ⟨_, _, h2, hx3⟩ := h3.app_inv henv hΓ
  have hn2 := not_isProof_fn hΓ h2 hx3 hn3
  obtain ⟨_, _, h1, hx2⟩ := h2.app_inv henv hΓ
  have hn1 := not_isProof_fn hΓ h1 hx2 hn2
  obtain ⟨res1, HW1, h1native⟩ := HasType.mkApps_telescope (args := [α]) henv hΓ hc ⟨_, h1⟩ (by rfl)
  obtain ⟨res4, HW4, h4native⟩ := HasType.mkApps_telescope (args := [α, a, M, m]) henv hΓ hc ⟨_, h4⟩ (by rfl)
  have E1 : ∃ C, res1 = .forallE α C := by
    cases HW1 with | cons _ H =>
    cases H
    simp [instL, VLevel.inst, VExpr.inst, instVar]
  have E4 : ∃ C, res4 = .forallE α C := by
    cases HW4 with | cons _ H =>
    cases H with | cons _ H =>
    cases H with | cons _ H =>
    cases H with | cons _ H =>
    cases H
    simp [instL, VLevel.inst, VExpr.inst, instVar, inst_liftN_lo]
  obtain ⟨C1, rfl⟩ := E1
  obtain ⟨C4, rfl⟩ := E4
  have RN1 := proofErase_const_native_recovery (Step := Step) hΓ heq.2.2.1 hls rfl HW1 hn1
  have RN4 := proofErase_const_native_recovery (Step := Step) hΓ heq.2.2.1 hls rfl HW4 hn4
  obtain ⟨_, hPi1⟩ := h1native.isType henv hΓ
  obtain ⟨_, hPi4⟩ := h4native.isType henv hΓ
  rw [proofErase_const_spine (args := [α]) hΓ h1native hn1,
    show proofErase Γ (.forallE α C1) = .forallE (proofErase Γ α) _ from
      if_neg (not_isProof_of_sort hΓ hPi1)] at RN1
  rw [proofErase_const_spine (args := [α, a, M, m]) hΓ h4native hn4,
    show proofErase Γ (.forallE α C4) = .forallE (proofErase Γ α) _ from
      if_neg (not_isProof_of_sort hΓ hPi4)] at RN4
  exact ⟨_, _, RN1, RN4⟩

/-- A function carrier lets the two declaration callers eta-expand both
endpoints in stage one. No native recovery of either endpoint is required.
The carrier must be non-propositional here; propositional endpoints already
erase to the same marker and need no opening. -/
theorem first_stage_eq_prefix_function_endpoints_eta
    (heq : env.HasCanonicalEq) (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (Strengthening.eqRecBeforeMajor v w (.forallE A B) a M m b) T)
    (hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w (.forallE A B) a M m b))
    (hA : env.HasType univs Γ A (.sort u)) (hw : ¬ w ≈ .zero) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (Strengthening.eqRecBeforeMajor v w (.forallE A B) a M m b))
      (ProofShape.eqRecBeforeMajor v w (proofErase Γ (.forallE A B))
        (.lam (proofErase Γ A) (.app ((proofErase Γ a).liftN 1) (etaArgument u)))
        (proofErase Γ M) (proofErase Γ m)
        (.lam (proofErase Γ A) (.app ((proofErase Γ b).liftN 1) (etaArgument u)))) := by
  obtain ⟨_, _, hQ, _, _, _, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have EQ : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hQ)
  have hΓQ : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, w, hQ⟩
  have SQ : DomainSort (proofEraseCtx Γ) (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) w :=
    EQ ▸ DomainSort.of_typed hΓ hQ
  have SA : DomainSort (.forallE (proofErase Γ A) (proofErase (A :: Γ) B) :: proofEraseCtx Γ)
      ((proofErase Γ A).liftN 1) u := by
    have H := DomainSort.of_typed hΓQ (hA.weakN henv Ctx.LiftN.one)
    simpa only [proofEraseCtx, EQ, proofErase_liftN hΓ hΓQ Ctx.LiftN.one hA] using H
  obtain ⟨C1, C4, RN1, RN4⟩ := eq_prefix_endpoint_native_guards
    (Step := ErasedStaticStructureEtaExpansionStage D 0) heq hΓ ht hn
  rw [EQ] at RN1 RN4
  have Ra := staged_caller_argument_eta RN1 SQ hw SA (x := proofErase Γ a)
  have Rb := staged_caller_argument_eta RN4 SQ hw SA (x := proofErase Γ b)
  have ES := proofErase_const_spine (args := [.forallE A B, a, M, m, b]) hΓ ht hn
  change proofErase Γ (Strengthening.eqRecBeforeMajor v w (.forallE A B) a M m b) =
    ProofShape.eqRecBeforeMajor v w (proofErase Γ (.forallE A B)) (proofErase Γ a)
      (proofErase Γ M) (proofErase Γ m) (proofErase Γ b) at ES
  rw [ES, EQ]
  exact Rb.trans (.app (.app (.app Ra .refl) .refl) .refl)

/-- A typed computed function body still obeys the eta/beta restoration law.
This includes a proof-valued domain: replay establishes that its erased fresh
variable cannot occur in the computed body, so the proof marker is harmless. -/
theorem computed_function_body_eta_beta
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B)) (hn : ¬ IsProof Γ f)
    (R : ScopedCompute Step (proofErase Γ A :: proofEraseCtx Γ)
      (.app ((proofErase Γ f).liftN 1) (etaArgument u)) out) :
    BetaRed (.app ((ProofShape.lam (proofErase Γ A) out).liftN 1) (etaArgument u)) out := by
  obtain ⟨_, _, hb⟩ := (IsDefEq.eta hf).hasType.1.lam_inv henv hΓ
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  obtain ⟨body, HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓA hb
    (by rfl) (proofErase_eta_body hΓ hA hf hn) R
  have E := proofErase_eta_inst hΓ hA HB.hasType.2
  rw [EB] at E
  simpa only [ProofShape.liftN, E] using
    (BetaRed.beta (A := (proofErase Γ A).liftN 1) (b := out.liftN 1 1) (a := etaArgument u))

/-- Function-carrier exposure can be performed inside the canonical endpoint
callers. Computations of the codomain and the two applied bodies expose a
stage-zero body guard; caller eta then gives a stage-zero function guard.
The prefix contracts at stage one with its exact original output annotation.
Neither endpoint needs native recovery, and proof domains and carriers are
included. General recursive exposure of the supplied body guard remains open. -/
theorem first_stage_eq_prefix_of_function_body_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (Strengthening.eqRecBeforeMajor v w (.forallE A B) a M m b) T)
    (hn : ¬ IsProof Γ (Strengthening.eqRecBeforeMajor v w (.forallE A B) a M m b))
    (hA : env.HasType univs Γ A (.sort u))
    (RC : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1)
      (proofErase Γ A :: proofEraseCtx Γ) (proofErase (A :: Γ) B) C')
    (Ra : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1)
      (proofErase Γ A :: proofEraseCtx Γ)
      (.app ((proofErase Γ a).liftN 1) (etaArgument u)) a')
    (Rb : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1)
      (proofErase Γ A :: proofEraseCtx Γ)
      (.app ((proofErase Γ b).liftN 1) (etaArgument u)) b')
    (HG : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0)
      (proofErase Γ A :: proofEraseCtx Γ) C' a' b') :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (proofErase Γ (Strengthening.eqRecBeforeMajor v w (.forallE A B) a M m b))
      (.lam (eqProofType w (proofErase Γ (.forallE A B)) (proofErase Γ a) (proofErase Γ b))
        ((proofErase Γ m).liftN 1)) := by
  obtain ⟨_, _, hQ, ha, _, _, hb⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  by_cases hw : w ≈ .zero
  · have hQ0 := (IsDefEq.sortDF (hQ.sort_r henv hΓ) (by trivial) hw).defeq hQ
    have Ea := proofErase_eq_proof.2 (show IsProof Γ a from ⟨_, ha, hQ0⟩)
    have Eb := proofErase_eq_proof.2 (show IsProof Γ b from ⟨_, hb, hQ0⟩)
    apply first_stage_eq_prefix_of_computed_guard heq hs hΓ ht hn .refl .refl .refl .refl
    rw [Ea, Eb]
    exact .carrierChecked (.leaf .refl)
  have hna : ¬ IsProof Γ a := by
    rintro ⟨P, haP, hP⟩
    have hQ0 := hP.defeqU_l henv hΓ (ha.uniqU henv hΓ haP).symm
    exact hw ((hQ.uniqU henv hΓ hQ0).sort_inv henv hΓ)
  have hnb : ¬ IsProof Γ b := by
    rintro ⟨P, hbP, hP⟩
    have hQ0 := hP.defeqU_l henv hΓ (hb.uniqU henv hΓ hbP).symm
    exact hw ((hQ.uniqU henv hΓ hQ0).sort_inv henv hΓ)
  have BA := computed_function_body_eta_beta
    (erased_static_structure_eta_expansion_stage_descent heq hs 1) hΓ hA ha hna Ra
  have BB := computed_function_body_eta_beta
    (erased_static_structure_eta_expansion_stage_descent heq hs 1) hΓ hA hb hnb Rb
  have HG' : ComputedJointCarrierGuard (ErasedStaticStructureEtaExpansionStage D 0)
      (proofEraseCtx Γ) (.forallE (proofErase Γ A) C')
      (.lam (proofErase Γ A) a') (.lam (proofErase Γ A) b') :=
    .carrierFunction (DomainSort.of_typed hΓ hA) (.carrierReduce (.beta BA) (.beta BB) HG)
  have Ropen := first_stage_eq_prefix_function_endpoints_eta (D := D) heq hΓ ht hn hA hw
  have EQ : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hQ)
  have Rchange : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) (proofEraseCtx Γ)
      (ProofShape.eqRecBeforeMajor v w (proofErase Γ (.forallE A B))
        (.lam (proofErase Γ A) (.app ((proofErase Γ a).liftN 1) (etaArgument u)))
        (proofErase Γ M) (proofErase Γ m)
        (.lam (proofErase Γ A) (.app ((proofErase Γ b).liftN 1) (etaArgument u))))
      (ProofShape.eqRecBeforeMajor v w (.forallE (proofErase Γ A) C')
        (.lam (proofErase Γ A) a') (proofErase Γ M) (proofErase Γ m) (.lam (proofErase Γ A) b')) := by
    rw [EQ]
    exact .app (.app (.app (.app (.app .refl (.forallE .refl RC)) (.lam .refl Ra)) .refl) .refl)
      (.lam .refl Rb)
  obtain ⟨body, RN, SD⟩ := eq_prefix_literal_native_guard
    (Step := ErasedStaticStructureEtaExpansionStage D 0) heq hΓ ht hn
  apply staged_eta_retains_constant_domain heq hs RN SD
  exact Ropen.trans (Rchange.trans (.base (.inr (.inr (.inl (.intro HG'))))))

end Lean4Lean.VEnv.Strengthening
