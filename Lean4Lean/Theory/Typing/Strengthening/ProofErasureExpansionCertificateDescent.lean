import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionNativeUnion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredStageCertificateDescent

/-! # Removing unused binders without losing expansion certificates

The recovered annotation of an identity wrapper descends as a native certificate,
not just as an actual typing. This closes certificate descent for the expanded
stages and lets a computation below an unused wrapper binder be reused outside.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Universe conversion retains its lower computation certificate. Raw retraction
is used only after semantic descent supplies an exactly lifted target. -/
theorem erased_level_primitive_certificate_descent :
    ErasedScopedPrimitiveCertificateDescent (fun _ => LevelPrimitive univs)
      (fun _ => LevelPrimitive univs) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨e', HE, Ee⟩ := erased_level_primitive_descent hΓ hΓ' W ht H
  refine ⟨e', HE, .base ?_, Ee⟩
  have HR := H.subst (τ := ProofShape.Subst.retract (.consN (.skipN .refl n) k))
  rw [← Ee, ← ProofShape.lift'_consN_skipN, ← ProofShape.lift'_consN_skipN,
    ProofShape.subst_retract_lift', ProofShape.subst_retract_lift'] at HR
  exact HR

/-- The fixed-argument wrapper retains the exact lower expansion rule. -/
theorem erased_constantExpansion_certificate_descent :
    ErasedScopedPrimitiveCertificateDescent (fun _ => ConstantExpansion)
      (fun _ => ConstantExpansion) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro hn =>
    have hne : ¬ IsProof Γ e := by
      intro hp
      exact hn (by rw [proofErase_eq_proof.2 hp]; rfl)
    refine ⟨_, (constantExpansion_equal ht).symm, ?_, ?_⟩
    · rw [proofErase_constantExpansion hΓ ht hne]
      exact .base (.intro (fun H => hne (proofErase_eq_proof.1 H)))
    · rw [proofErase_constantExpansion hΓ ht hne, constantExpansion_liftN]

/-- Identity annotations descend with their native guards. The lower identity
therefore has its own expansion certificate in the target relation. -/
theorem erased_nativeIdentityExpansion_certificate_descent
    (hstep : ErasedScopedPrimitiveCertificateDescent Step Target) :
    ErasedScopedPrimitiveCertificateDescent (NativeIdentityExpansion Step)
      (NativeIdentityExpansion Target) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  cases H with
  | intro R =>
    obtain ⟨A, he, RA, EA⟩ := proofErase_scoped_recovery_certificate_descend hstep hΓ hΓ' W ht rfl R
    have hn : ¬ IsProof Γ e := fun hp => RA.ne_proof (proofErase_eq_proof.2 hp)
    refine ⟨_, (nativeIdentityExpansion_equal he).symm.toU.of_l henv hΓ ht, ?_, ?_⟩
    · rw [proofErase_nativeIdentityExpansion hΓ he hn]
      exact .base (.intro RA)
    · rw [proofErase_nativeIdentityExpansion hΓ he hn]
      simp only [ProofShape.liftN, EA, liftVar, Nat.zero_lt_succ, ↓reduceIte]

/-- Every expanded stage preserves its exact lower computation certificates,
including generated singleton telescopes and recovered identity annotations. -/
theorem erased_expansion_stage_certificate_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage, ErasedScopedPrimitiveCertificateDescent (ErasedExpansionStage D stage)
      (ErasedExpansionStage D stage) := by
  intro stage
  induction stage with
  | zero =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with (H | H) | H
    · obtain ⟨e', HE, R, E⟩ := erased_joint_zero_certificate_descent hs hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inl (.inl H)), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_level_primitive_certificate_descent hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inl (.inr H)), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_constantExpansion_certificate_descent hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr H), E⟩
  | succ stage ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H | H
    · obtain ⟨e', HE, R, E⟩ := ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inl H), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_carrier_recovered_singleton_certificate_descent heq ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inl H)), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_computed_joint_prefix_certificate_descent heq ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inr (.inl H))), E⟩
    · obtain ⟨e', HE, R, E⟩ := erased_nativeIdentityExpansion_certificate_descent ih hΓ hΓ' W ht H
      exact ⟨e', HE, R.mono (fun H => .inr (.inr (.inr H))), E⟩

/-- The full expanded union also retains certificates when unused binders are removed. -/
theorem erased_expansion_union_certificate_descent
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveCertificateDescent (ErasedExpansionUnion D) (ErasedExpansionUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht H
  obtain ⟨stage, H⟩ := H
  obtain ⟨e', HE, R, E⟩ := erased_expansion_stage_certificate_descent heq hs stage hΓ hΓ' W ht H
  exact ⟨e', HE, R.mono (fun H => ⟨stage, H⟩), E⟩

/-- Computation certificates are invariant under insertion of unused binders,
without changing their finite expanded stage or prescribing inhabitants. -/
theorem proofErase_expansion_stage_compute_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ScopedCompute (ErasedExpansionStage D stage) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ScopedCompute (ErasedExpansionStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨e', _, R, E⟩ := proofErase_scoped_compute_certificate_descend
      (erased_expansion_stage_certificate_descent heq hs stage) hΓ hΓ' W ht rfl H
    exact ProofShape.liftN_inj.1 E ▸ R
  · intro H
    have R := H.rename (erased_expansion_stage_rename heq hs stage)
      (ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [subst_bvar_liftN] using R

/-- Native recovery certificates at prescribed lifted outputs also reflect
through the binder insertion at their unchanged stage. -/
theorem proofErase_expansion_stage_recovery_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ScopedTypeRecovery (ErasedExpansionStage D stage) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ScopedTypeRecovery (ErasedExpansionStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨A, _, R, E⟩ := proofErase_scoped_recovery_certificate_descend
      (erased_expansion_stage_certificate_descent heq hs stage) hΓ hΓ' W ht rfl H
    exact ProofShape.liftN_inj.1 E ▸ R
  · intro H
    have R := H.rename (erased_expansion_stage_rename heq hs stage)
      (ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [subst_bvar_liftN] using R

end Lean4Lean.VEnv.Strengthening
