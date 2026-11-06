import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProofNeutralEtaCoreComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralEtaCoreChecking

/-! # Full-core comparison for proof-domain neutral eta consumers

Typed simulation validates erased proof arguments at beta contractions.
Native recovery and retained domain histories then read out the paired
residuals at one fixed stage, for arbitrary typed consumers.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ambient_cons subst_shift
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- A retained expansion computation for each ambient neutral mark reads out
all paired syntax in either mode. Actual source typing reconstructs binder
contexts, and exact renaming keeps each mark tied to its ambient origin. -/
theorem proof_neutral_eta_variant_computed_check
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hguard : ∀ {A i}, Guard A i → ScopedCompute Step Δ (.bvar i)
      (.lam A (.app (.bvar (i+1)) .proof)))
    (V : ProofNeutralEtaVariant Guard n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i+n))) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode a b := by
  induction V generalizing Γ e T mode with
  | refl => exact .leaf .refl
  | app VF VX ihf ihx =>
    obtain ⟨f, x, rfl, _, EF, EX⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    exact .app (ihf hΓ hf EF W) (ihx hΓ hx EX W)
  | proj V ih =>
    obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj (ih hΓ hm.hasType.2 EM W)
  | lam VA VB ihA ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    apply ComputedJointCheck.lam (ihA hΓ hA EA W)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    simpa only [proofEraseCtx, EA] using ihB hΓA hb EB (ambient_cons W hΓ hA)
  | forallE VA VB ihA ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.forallE_inv henv
    apply ComputedJointCheck.forallE (ihA hΓ hA EA W)
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    simpa only [proofEraseCtx, EA] using ihB hΓA hb EB (ambient_cons W hΓ hA)
  | @etaL A i n HG =>
    have R := (hguard HG).rename hrename W
    have R' : ScopedCompute Step (proofEraseCtx Γ) (.bvar (i+n))
        (.lam (A.liftN n) (.app (.bvar (i+n+1)) .proof)) := by
      simp only [subst_shift] at R
      simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero,
        Nat.add_lt_add_iff_right, if_false, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using R
    exact .compute .refl R' (.leaf .refl)
  | @etaR A i n HG =>
    have R := (hguard HG).rename hrename W
    have R' : ScopedCompute Step (proofEraseCtx Γ) (.bvar (i+n))
        (.lam (A.liftN n) (.app (.bvar (i+n+1)) .proof)) := by
      simp only [subst_shift] at R
      simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero,
        Nat.add_lt_add_iff_right, if_false, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using R
    exact .compute R' .refl (.leaf .refl)

/-- Native recovery gives the variable expansion at one later stage. Every
core-computed annotation retains that same source expansion, followed by its
recorded domain path. This is the guard required by neutral-variant readout. -/
theorem proof_neutral_eta_native_residual_expansion
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage) Δ (.bvar i) (.forallE A B))
    (SA : DomainSort Δ A .zero) (R : Compute (ErasedLevelCore D) A C) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ (.bvar i)
      (.lam C (.app (.bvar (i+1)) .proof)) := by
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ (.bvar i)
      (.lam A (.app (.bvar (i+1)) .proof)) := by
    have H : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ (.bvar i)
        (.lam A (.app (ProofShape.bvar i |>.liftN 1) (etaArgument .zero))) :=
      .base (.inr (.inr (.inr (.inr (.inl (.intro RN SA))))))
    simpa only [etaArgument, if_pos (show VLevel.zero ≈ VLevel.zero from rfl), ProofShape.liftN, liftVar, Nat.not_lt_zero,
      if_false, Nat.add_comm] using H
  exact RE.trans (.lam R.in_static_stage .refl)

/-- Actual proof-domain eta seeds the protected relation, and arbitrary typed
consumers retain its marks in every occurrence. The domain guard retains full
ordinary-core histories from the original proposition. -/
theorem proofErase_proof_neutral_eta_consumer_variant
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort .zero))
    (hf : env.HasType univs Γ (.bvar i) (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (ht : env.HasType univs (.forallE A B :: Γ) t T) :
    ProofNeutralEtaVariant (fun C j => j = i ∧ Compute (ErasedLevelCore D) (proofErase Γ A) C) 0
      (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0)))))
      (proofErase Γ (t.inst (.bvar i))) := by
  have V : ProofNeutralEtaVariant (fun C j => j = i ∧ Compute (ErasedLevelCore D) (proofErase Γ A) C) 0
      (proofErase Γ (.lam A (.app (VExpr.bvar i).lift (.bvar 0)))) (proofErase Γ (.bvar i)) := by
    have EF : proofErase Γ (.bvar i) = .bvar i := if_neg hn
    rw [proofErase_nativeEtaExpansion hΓ hA hf hn, EF]
    simpa only [etaArgument, if_pos (show VLevel.zero ≈ VLevel.zero from rfl), ProofShape.liftN,
      liftVar, Nat.not_lt_zero, if_false, Nat.add_zero, ProofShape.liftN_zero, Nat.add_comm] using
      (ProofNeutralEtaVariant.etaL (n := 0) (A := proofErase Γ A) (i := i)
        (Guard := fun C j => j = i ∧ Compute (ErasedLevelCore D) (proofErase Γ A) C) ⟨rfl, .refl⟩)
  have hΓF : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
  rw [proofErase_instN hΓF (IsDefEq.eta hf).hasType.1 Ctx.InstN.zero ht,
    proofErase_instN hΓF hf Ctx.InstN.zero ht]
  simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
  apply ProofNeutralEtaVariant.subst_images
  intro j
  cases j with
  | zero => exact V
  | succ j => exact .refl

/-- Every pair of independent full ordinary-core residuals of a proof-domain
neutral eta consumer compares. Both simulation directions retain actual source
typing; no raw confluence or arbitrary proof-marker substitution is assumed. -/
theorem proofErase_proof_neutral_eta_consumer_core_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort .zero))
    (hf : env.HasType univs Γ (.bvar i) (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) (.bvar i) (.forallE (proofErase Γ A) rawB))
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.bvar i))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) mode left right := by
  let Guard := fun C j => j = i ∧ Compute (ErasedLevelCore D) (proofErase Γ A) C
  have hsort {C j} (H : Guard C j) : DomainSort (proofEraseCtx Γ) C .zero := by
    obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ hA rfl rfl (H.2.scoped (fun H => .base H))
    exact EE ▸ DomainSort.of_typed hΓ HE.hasType.2
  have hg {C j C'} (H : Guard C j) (R : Compute (ErasedLevelCore D) C C') : Guard C' j :=
    ⟨H.1, H.2.trans R⟩
  have V := proofErase_proof_neutral_eta_consumer_variant (D := D) hΓ hA hf hn ht
  have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  have hright := ht.instN henv Ctx.InstN.zero hf
  obtain ⟨b₁, RB₁, V₁⟩ := proof_neutral_eta_core_left hs
    (Guard := Guard) (fun H R => hg H R) (fun H => hsort H) RL V hΓ hleft rfl ContextRenaming.identity
  obtain ⟨q', RQ, RB₁'⟩ := hc hΓ hright RR RB₁
  obtain ⟨eb, HB, EB⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hright rfl rfl (RB₁.scoped (fun H => .base H))
  obtain ⟨p', RP, V₂⟩ := proof_neutral_eta_core_left hs
    (Guard := Guard) (fun H R => hg H R) (fun H => hsort H) RB₁' V₁.symm
    hΓ HB.hasType.2 EB ContextRenaming.identity
  obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hleft rfl rfl ((RL.trans RP).scoped (fun H => .base H))
  have HG {C j} (H : Guard C j) :
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) (proofEraseCtx Γ)
        (.bvar j) (.lam C (.app (.bvar (j+1)) .proof)) := by
    obtain ⟨rfl, R⟩ := H
    exact proof_neutral_eta_native_residual_expansion RN (.of_typed hΓ hA) R
  have HC := proof_neutral_eta_variant_computed_check (mode := mode)
    (erased_static_structure_eta_expansion_stage_rename heq hs (stage+1)) (fun H => HG H)
    V₂.symm hΓ HE.hasType.2 EE ContextRenaming.identity
  exact .compute RP.in_static_stage RQ.in_static_stage HC

/-- Literal Pi lookup now covers every input sort and proof classification.
All independent full ordinary-core residuals of any typed eta consumer compare
at stage one. Proof-valued functions use equal erasures and typed confluence;
non-proof functions use the appropriate protected eta simulation. -/
theorem proofErase_lookup_eta_consumer_core
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs)) (HL : Lookup Γ i (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.bvar i))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 1)
      (proofEraseCtx Γ) mode left right := by
  have hf : env.HasType univs Γ (.bvar i) (.forallE A B) := .bvar HL
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _, _⟩ := hPi.forallE_inv henv
  by_cases hp : IsProof Γ (.bvar i)
  · have hη := IsDefEq.eta hf
    have E : proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0)))) =
        proofErase Γ (t.inst (.bvar i)) := by
      have hΓF : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
      rw [proofErase_instN hΓF hη.hasType.1 Ctx.InstN.zero ht,
        proofErase_instN hΓF hf Ctx.InstN.zero ht,
        proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ hη).2 hp)]
    obtain ⟨out, RP, RQ⟩ := hc hΓ (ht.instN henv Ctx.InstN.zero hf) (E ▸ RL) RR
    exact .compute RP.in_static_stage RQ.in_static_stage (.leaf .refl)
  by_cases hu : u ≈ .zero
  · have hA0 : env.HasType univs Γ A (.sort .zero) :=
      (IsDefEq.sortDF (hA.sort_r henv hΓ) (by trivial) hu).defeq hA
    have EF : proofErase Γ (.bvar i) = .bvar i := if_neg hp
    have EP : proofErase Γ (.forallE A B) =
        .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
      if_neg (not_isProof_of_sort hΓ hPi)
    have RN := proofErase_scoped_lookup_recovery
      (Step := ErasedStaticStructureEtaExpansionStage D 0) hΓ HL hp .refl
    rw [EF, EP] at RN
    exact proofErase_proof_neutral_eta_consumer_core_compare heq hs hc hΓ hA0 hf hp ht RN RL RR
  · exact proofErase_lookup_eta_consumer_core_compare heq hs hc hΓ hA HL hp hu ht RL RR

omit [Params] in
/-- Actual-environment native neutral eta coverage with no restriction on the
input sort, function proof classification, or ordinary core reduction paths.
The Pi must be the literal lookup type; arbitrary converted typing is still
outside this theorem. -/
theorem EnvironmentCore.lookup_eta_consumer_core
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {mode Γ A B i t T left right}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → Lookup Γ i (.forallE A B) →
      env.HasType U (.forallE A B :: Γ) t T →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.bvar i))) right →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 1)
        (proofEraseCtx Γ) mode left right := by
  letI := henv.params U
  intro mode Γ A B i t T left right heq hΓ HL ht RL RR
  exact proofErase_lookup_eta_consumer_core heq sound
    (typed_level_core_confluence (fun H => H)) hΓ HL ht RL RR

end Lean4Lean.VEnv.Strengthening
