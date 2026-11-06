import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralEtaConsumer
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking

/-! # Reading protected neutral eta residuals with retained native recovery

Each ambient eta mark has a checked expansion path from its short variable.
Exact renaming transports that path beneath the consumer's binders. Structural
readout then works in either mode, including nested lambda bodies. Native type
recovery supplies these paths; semantic function typing alone is not promoted
to recovery. Proof-domain marks and full-core simulation remain separate work.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ambient_cons subst_shift
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
variable [Params] {D : Definitions}

/-- A retained expansion computation for each ambient neutral mark reads out
all paired syntax in either mode. Actual source typing reconstructs binder
contexts, and exact renaming keeps each mark tied to its ambient origin. -/
theorem neutral_eta_variant_computed_check
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hguard : ∀ {A i}, Guard A i → ScopedCompute Step Δ (.bvar i)
      (.lam A (.app (.bvar (i+1)) (.bvar 0))))
    (V : NeutralEtaVariant Guard n a b)
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
        (.lam (A.liftN n) (.app (.bvar (i+n+1)) (.bvar 0))) := by
      simp only [subst_shift] at R
      simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero,
        Nat.zero_lt_succ, Nat.add_lt_add_iff_right, if_false, if_true, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using R
    exact .compute .refl R' (.leaf .refl)
  | @etaR A i n HG =>
    have R := (hguard HG).rename hrename W
    have R' : ScopedCompute Step (proofEraseCtx Γ) (.bvar (i+n))
        (.lam (A.liftN n) (.app (.bvar (i+n+1)) (.bvar 0))) := by
      simp only [subst_shift] at R
      simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero,
        Nat.zero_lt_succ, Nat.add_lt_add_iff_right, if_false, if_true, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using R
    exact .compute R' .refl (.leaf .refl)

/-- Native recovery gives the variable expansion at one later stage. Every
beta-computed annotation retains that same source expansion, followed by its
recorded domain path. This is the guard required by neutral-variant readout. -/
theorem neutral_eta_native_residual_expansion
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage) Δ (.bvar i) (.forallE A B))
    (SA : DomainSort Δ A u) (hu : ¬ u ≈ .zero) (R : ProofShape.BetaRed A C) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ (.bvar i)
      (.lam C (.app (.bvar (i+1)) (.bvar 0))) := by
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ (.bvar i)
      (.lam A (.app (.bvar (i+1)) (.bvar 0))) := by
    have H : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ (.bvar i)
        (.lam A (.app (ProofShape.bvar i |>.liftN 1) (etaArgument u))) :=
      .base (.inr (.inr (.inr (.inr (.inl (.intro RN SA))))))
    simpa only [etaArgument, if_neg hu, ProofShape.liftN, liftVar, Nat.not_lt_zero,
      if_false, Nat.add_comm] using H
  exact RE.trans (.lam (.beta R) .refl)

/-- Independent beta residuals of a typed neutral eta consumer compare at one
fixed finite stage whenever its actual variable retains native Pi recovery.
No normalization of the consumer or join of the paired residuals is assumed. -/
theorem proofErase_neutral_eta_consumer_beta_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hf : env.HasType univs Γ (.bvar i) (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage)
      (proofEraseCtx Γ) (.bvar i) (.forallE (proofErase Γ A) rawB))
    (RL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left)
    (RR : ProofShape.BetaRed (proofErase Γ (t.inst (.bvar i))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1))
      (proofEraseCtx Γ) mode left right := by
  obtain ⟨left', right', PL, PR, V⟩ := proofErase_neutral_eta_consumer_beta_residuals hΓ hA hf hn hu ht RL RR
  have hleft := ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1
  obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_stage_descent heq hs (stage+1))
    hΓ hleft rfl rfl (ScopedCompute.beta (RL.trans PL))
  have HG {C j} (H : j = i ∧ ProofShape.BetaRed (proofErase Γ A) C) :
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) (proofEraseCtx Γ)
        (.bvar j) (.lam C (.app (.bvar (j+1)) (.bvar 0))) := by
    obtain ⟨rfl, R⟩ := H
    exact neutral_eta_native_residual_expansion RN (.of_typed hΓ hA) hu R
  have HC := neutral_eta_variant_computed_check (mode := mode)
    (erased_static_structure_eta_expansion_stage_rename heq hs (stage+1)) (fun H => HG H)
    V hΓ HE.hasType.2 EE ContextRenaming.identity
  exact .compute (.beta PL) (.beta PR) HC

/-- A literal Pi assignment supplies the retained native recovery directly
from lookup. Thus all independent beta residuals of its typed eta consumers
compare at stage one, without a separate recovery hypothesis. -/
theorem proofErase_lookup_eta_consumer_beta_compare
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (HL : Lookup Γ i (.forallE A B))
    (hn : ¬ IsProof Γ (.bvar i)) (hu : ¬ u ≈ .zero)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : ProofShape.BetaRed (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left)
    (RR : ProofShape.BetaRed (proofErase Γ (t.inst (.bvar i))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 1)
      (proofEraseCtx Γ) mode left right := by
  have hf : env.HasType univs Γ (.bvar i) (.forallE A B) := .bvar HL
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  have EF : proofErase Γ (.bvar i) = .bvar i := if_neg hn
  have EP : proofErase Γ (.forallE A B) =
      .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  have RN := proofErase_scoped_lookup_recovery
    (Step := ErasedStaticStructureEtaExpansionStage D 0) hΓ HL hn .refl
  rw [EF, EP] at RN
  exact proofErase_neutral_eta_consumer_beta_compare heq hs hΓ hA hf hn hu ht RN RL RR

omit [Params] in
/-- The literal-lookup result in an actual well-formed canonical-Eq
environment. Only ordinary typing and the two beta paths are supplied. -/
theorem EnvironmentCore.lookup_eta_consumer_beta_compare
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {mode Γ A B i u t T left right}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) →
      Lookup Γ i (.forallE A B) → (¬ IsProof Γ (.bvar i)) → (¬ u ≈ .zero) →
      env.HasType U (.forallE A B :: Γ) t T →
      ProofShape.BetaRed (proofErase Γ (t.inst (.lam A (.app (VExpr.bvar i).lift (.bvar 0))))) left →
      ProofShape.BetaRed (proofErase Γ (t.inst (.bvar i))) right →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 1)
        (proofEraseCtx Γ) mode left right := by
  letI := henv.params U
  intro mode Γ A B i u t T left right heq hΓ hA HL hn hu ht RL RR
  exact proofErase_lookup_eta_consumer_beta_compare heq sound hΓ hA HL hn hu ht RL RR

end Lean4Lean.VEnv.Strengthening
