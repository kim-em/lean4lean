import Lean4Lean.Theory.Typing.Strengthening.ProofErasureProofNeutralEtaChecking

/-! # Reading neutral eta with certified converted domains

The mark's comparison may expand the short variable at its recovered domain
and compare that domain with the written eta annotation. Exact renaming carries
this retained comparison beneath arbitrary consumer binders.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ambient_cons subst_shift
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
variable [Params] {D : Definitions}

/-- A retained comparison for each ambient eta mark reads out paired syntax
in either mode. This permits a native expansion whose domain differs from the
written annotation, provided their comparison is retained explicitly. -/
theorem neutral_eta_variant_guarded_check
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hguard : ∀ {A i mode}, Guard A i → ComputedJointCompare Step Δ mode
      (.lam A (.app (.bvar (i+1)) (.bvar 0))) (.bvar i))
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
    have H := (hguard (mode := mode) HG).rename hrename W
    simp only [JointCheckKind.subst, subst_shift] at H
    simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero,
      Nat.add_lt_add_iff_right, Nat.zero_lt_succ, if_false, if_true,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using H
  | @etaR A i n HG =>
    have H := (hguard (mode := mode) HG).rename hrename W
    simp only [JointCheckKind.subst, subst_shift] at H
    apply ComputedJointCheck.symm
    simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero,
      Nat.add_lt_add_iff_right, Nat.zero_lt_succ, if_false, if_true,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using H

/-- A retained comparison for each ambient eta mark reads out paired syntax
in either mode. This permits a native expansion whose domain differs from the
written annotation, provided their comparison is retained explicitly. -/
theorem proof_neutral_eta_variant_guarded_check
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hguard : ∀ {A i mode}, Guard A i → ComputedJointCompare Step Δ mode
      (.lam A (.app (.bvar (i+1)) .proof)) (.bvar i))
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
    have H := (hguard (mode := mode) HG).rename hrename W
    simp only [JointCheckKind.subst, subst_shift] at H
    simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero,
      Nat.add_lt_add_iff_right, if_false,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using H
  | @etaR A i n HG =>
    have H := (hguard (mode := mode) HG).rename hrename W
    simp only [JointCheckKind.subst, subst_shift] at H
    apply ComputedJointCheck.symm
    simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero,
      Nat.add_lt_add_iff_right, if_false,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using H

/-- Native expansion at its selected domain and an inferred domain check
compare an eta wrapper using a different annotation, in either mode. -/
theorem native_eta_converted_domain_check
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D stage) Δ (.bvar i) (.forallE C E))
    (SC : DomainSort Δ C u)
    (HA : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ false A C) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ mode
      (.lam A (.app (.bvar (i+1)) (etaArgument u))) (.bvar i) := by
  have RE : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ (.bvar i)
      (.lam C (.app (ProofShape.bvar i |>.liftN 1) (etaArgument u))) :=
    .base (.inr (.inr (.inr (.inr (.inl (.intro RN SC))))))
  have RE' : ScopedCompute (ErasedStaticStructureEtaExpansionStage D (stage+1)) Δ (.bvar i)
      (.lam C (.app (.bvar (i+1)) (etaArgument u))) := by
    simpa only [ProofShape.liftN, liftVar, Nat.not_lt_zero, if_false, Nat.add_comm] using RE
  exact .compute .refl RE' (.lam HA (.leaf .refl))

end Lean4Lean.VEnv.Strengthening
