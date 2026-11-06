import Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedCastGuard
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureControlWorlds

/-! # Paired annotation checking with finite cast certificates

Exact context renaming carries ambient domain checks beneath the consumer's
binders. Full-core simulation retains the finite staged cast certificates;
only ordinary core confluence is used to compare independent residual paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

omit [Params] in
private theorem subst_shift (a : ProofShape) :
    a.subst (fun i => .bvar (i + n)) = a.liftN n := by
  simpa only [liftVar, Nat.not_lt_zero, ↓reduceIte, Nat.add_comm] using
    (subst_bvar_liftN (n := n) (k := 0) a)

private theorem ambient_cons
    (W : ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i + n)))
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u)) :
    ContextRenaming Δ (proofEraseCtx (A :: Γ)) (fun i => .bvar (i + (n + 1))) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have R : ContextRenaming (proofEraseCtx Γ) (proofEraseCtx (A :: Γ))
      (fun i => .bvar (liftVar 1 i 0)) :=
    (ContextRenaming.of_liftN hΓ hΓA Ctx.LiftN.one)
  have H : ContextRenaming Δ (proofEraseCtx (A :: Γ))
      (fun i => (ProofShape.bvar (i + n)).subst (fun j => .bvar (liftVar 1 j 0))) := W.compose R
  simpa only [ProofShape.Subst.comp, ProofShape.subst, liftVar, Nat.not_lt_zero, ↓reduceIte,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using H

/-- Ambient domain checks read out a paired annotation variant. A marked pair
may use an inferred check, or a common-mode check with witnesses of a shared
sort. Exact renaming transports both the check and its sort witnesses. -/
theorem annotation_variant_domain_computed_check
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hguard : ∀ {A C}, Guard A C → ComputedJointCompare Step Δ false A C ∨
      ∃ u, DomainSort Δ A u ∧ DomainSort Δ C u ∧ ComputedJointCompare Step Δ true A C)
    (V : AnnotationVariant Guard n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i + n))) :
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
  | marked HG VB ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have HB := ihB (mode := mode) hΓA hb EB (ambient_cons W hΓ hA)
    simp only [proofEraseCtx, EA] at HB
    rcases hguard HG with HG | ⟨v, SA, SC, HG⟩
    · have HG' := HG.rename hrename W
      simp only [JointCheckKind.subst, subst_shift] at HG'
      exact .lam HG' HB
    · have HG' := HG.rename hrename W
      have SA' := ContextSubstitution.sort W.interpretation SA
      have SC' := ContextSubstitution.sort W.interpretation SC
      simp only [JointCheckKind.subst, subst_shift] at HG' SA' SC'
      exact .lamSorted SA' SC' HG' HB

/-- Ambient inferred checks preserved by exact renaming read out a paired
annotation variant at any typed left source. No arbitrary substitution closure
of the domain guard is assumed. -/
theorem annotation_variant_computed_check
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hguard : ∀ {A C}, Guard A C → ComputedJointCompare Step Δ false A C)
    (V : AnnotationVariant Guard n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i + n))) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode a b :=
  annotation_variant_domain_computed_check hrename (fun H => .inl (hguard H)) V hΓ ht Ee W

/-- Earlier-stage casts may occur inside the marked domains of arbitrary
annotation variants. Independent full-core paths preserve inferred comparison
at the same finite stage. Only the right source needs an actual typing. -/
theorem staged_annotation_core_residual_check
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (V : AnnotationVariant (LevelStagedCastGuard D stage false) 0 a (proofErase Γ e))
    (RA : ProofShape.Compute (ErasedLevelCore D) a p)
    (RB : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ e) q) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) mode p q := by
  have hg {A C A'} (H : LevelStagedCastGuard D stage false A C)
      (R : ProofShape.Compute (ErasedLevelCore D) A A') :
      LevelStagedCastGuard D stage false A' C := .reducts H R .refl
  obtain ⟨b₁, RB₁, V₁⟩ := V.level_core_left
    (Guard := LevelStagedCastGuard D stage false) (fun H R => hg H R) RA
  obtain ⟨q', RQ, RB₁'⟩ := hc hΓ ht RB RB₁
  obtain ⟨p', RP, V₂⟩ := (V₁.symm LevelStagedCastGuard.symm).level_core_left
    (Guard := LevelStagedCastGuard D stage false) (fun H R => hg H R) RB₁'
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ht rfl rfl ((RB.trans RQ).scoped (fun H => .base H))
  have W : ContextRenaming (proofEraseCtx Γ) (proofEraseCtx Γ) (fun i => .bvar (i + 0)) :=
    ContextRenaming.identity
  have H := annotation_variant_computed_check (mode := mode)
    (erased_static_structure_eta_expansion_stage_rename heq hs stage)
    (fun H => H.forward heq hs hl hcon hc hreg hoff hD .refl .refl)
    V₂ hΓ HE.hasType.2 EE W
  exact .compute RP.in_static_stage RQ.in_static_stage (.symm H)

end Lean4Lean.VEnv.Strengthening
