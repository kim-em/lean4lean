import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationConsumer

/-! # Contextual full-core annotation families

The domain comparison may live in its actual ambient context. Paired residuals
retain the original domain pair and its two computation paths, so a recursive
induction hypothesis suffices without a global substitution or transport law.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

private def ResidualPair (D : Definitions) (A C a c : ProofShape) : Prop :=
  (ProofShape.Compute (ErasedLevelCore D) A a ∧ ProofShape.Compute (ErasedLevelCore D) C c) ∨
  (ProofShape.Compute (ErasedLevelCore D) A c ∧ ProofShape.Compute (ErasedLevelCore D) C a)

private theorem ResidualPair.symm (H : ResidualPair D A C a c) : ResidualPair D A C c a := H.elim Or.inr Or.inl

private theorem ResidualPair.left (H : ResidualPair D A C a c)
    (R : ProofShape.Compute (ErasedLevelCore D) a a') : ResidualPair D A C a' c := by
  rcases H with ⟨RA, RC⟩ | ⟨RA, RC⟩
  · exact .inl ⟨RA.trans R, RC⟩
  · exact .inr ⟨RA, RC.trans R⟩

private theorem residual_check
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HG : ∀ {a c}, ProofShape.Compute (ErasedLevelCore D) A a →
      ProofShape.Compute (ErasedLevelCore D) C c →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) false a c)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (V : AnnotationVariant (ResidualPair D A C) 0 a (proofErase Γ e))
    (RA : ProofShape.Compute (ErasedLevelCore D) a p)
    (RB : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ e) q) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) mode p q := by
  obtain ⟨b₁, RB₁, V₁⟩ := V.level_core_left
    (Guard := ResidualPair D A C) (fun H R => H.left R) RA
  obtain ⟨q', RQ, RB₁'⟩ := hc hΓ ht RB RB₁
  obtain ⟨p', RP, V₂⟩ := (V₁.symm ResidualPair.symm).level_core_left
    (Guard := ResidualPair D A C) (fun H R => H.left R) RB₁'
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ht rfl rfl ((RB.trans RQ).scoped (fun H => .base H))
  have hguard {a c} (H : ResidualPair D A C a c) :
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) false a c := by
    rcases H with ⟨RA, RC⟩ | ⟨RA, RC⟩
    · exact HG RA RC
    · exact .symm (HG RA RC)
  have W : ContextRenaming (proofEraseCtx Γ) (proofEraseCtx Γ) (fun i => .bvar (i + 0)) :=
    ContextRenaming.identity
  have H := annotation_variant_computed_check (mode := mode)
    (erased_static_structure_eta_expansion_stage_rename heq hs stage)
    (fun H => hguard H) V₂ hΓ HE.hasType.2 EE W
  exact .compute RP.in_static_stage RQ.in_static_stage (.symm H)

private theorem lambda_variant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (HG : ∀ {a c}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ A) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ C) c →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) false a c) :
    env.HasType univs Γ (.lam C b) (.forallE A B) ∧
      AnnotationVariant (ResidualPair D (proofErase Γ A) (proofErase Γ C)) 0
        (proofErase Γ (.lam A b)) (proofErase Γ (.lam C b)) := by
  have HC : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ C) := HG .refl .refl
  obtain ⟨v, hS⟩ := hA.isType henv hΓ
  have HAC := ((proofErase_computed_joint_compare_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs stage) hΓ hA hC HC).1
    ⟨_, hS⟩).of_l henv hΓ hA
  have HL := IsDefEq.lamDF HAC hb
  refine ⟨HL.hasType.2, ?_⟩
  by_cases hp : IsProof Γ (.lam A b)
  · rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 ((isProof_congr hΓ HL).1 hp)]
    exact .refl
  have hpc : ¬ IsProof Γ (.lam C b) := fun H => hp ((isProof_congr hΓ HL).2 H)
  have EB := proofErase_defeqCtx (Γ₁ := A :: Γ) ⟨hΓ, u, hA⟩ (IsDefEqCtx.succ .zero HAC) hb
  rw [show proofErase Γ (.lam A b) = .lam (proofErase Γ A) (proofErase (A :: Γ) b)
      from if_neg hp,
    show proofErase Γ (.lam C b) = .lam (proofErase Γ C) (proofErase (C :: Γ) b)
      from if_neg hpc, ← EB]
  simpa only [ProofShape.liftN_zero] using
    (AnnotationVariant.marked (n := 0) (b := proofErase (A :: Γ) b) (.inl ⟨.refl, .refl⟩) .refl)

/-- A contextual full-core comparison of the marked domains suffices for
arbitrary typed consumers of the paired lambdas. This is an induction interface:
the recursive grammar below supplies the domain premise from a smaller child. -/
theorem contextual_annotation_consumer_core
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (HG : ∀ {a c}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ A) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ C) c →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) false a c)
    (RL : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A b))) left)
    (RR : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam C b))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) mode left right := by
  obtain ⟨hC', V⟩ := lambda_variant heq hs hΓ hA hC hb (fun RA RB => HG RA RB)
  have hf := HasType.lam hA hb
  have hΓPi : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
  have VT : AnnotationVariant (ResidualPair D (proofErase Γ A) (proofErase Γ C)) 0
      (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b))) := by
    rw [proofErase_instN hΓPi hf Ctx.InstN.zero ht, proofErase_instN hΓPi hC' Ctx.InstN.zero ht]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
    apply AnnotationVariant.subst_images
    intro i
    cases i with
    | zero => exact V
    | succ i => exact .refl
  exact residual_check heq hs hc (fun RA RB => HG RA RB) hΓ
    (ht.instN henv Ctx.InstN.zero hC') VT RL RR

end Lean4Lean.VEnv.Strengthening
