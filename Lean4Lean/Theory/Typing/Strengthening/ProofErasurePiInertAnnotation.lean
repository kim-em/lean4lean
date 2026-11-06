import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCastConsumer

/-! # Pi-inert annotation consumer comparisons

These refinements retain the outer primitive heads of the existing construction.
Guard comparisons use their original complete finite stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private ResidualPair ResidualPair.symm ResidualPair.left lambda_variant
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextualAnnotationCore
variable [Params] {D : Definitions}

private theorem residual_check
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HG : ∀ {a c}, ProofShape.Compute (ErasedLevelCore D) A a →
      ProofShape.Compute (ErasedLevelCore D) C c →
      ComputedJointCompare (PiInertStage D stage) (proofEraseCtx Γ) domainMode a c)
    (SA : DomainSort (proofEraseCtx Γ) A u) (SC : DomainSort (proofEraseCtx Γ) C u)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (V : AnnotationVariant (ResidualPair D A C) 0 a (proofErase Γ e))
    (RA : ProofShape.Compute (ErasedLevelCore D) a p)
    (RB : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ e) q) :
    ComputedJointCompare (PiInertStage D stage) (proofEraseCtx Γ) mode p q := by
  obtain ⟨b₁, RB₁, V₁⟩ := V.level_core_left
    (Guard := ResidualPair D A C) (fun H R => ResidualPair.left H R) RA
  obtain ⟨q', RQ, RB₁'⟩ := hc hΓ ht RB RB₁
  obtain ⟨p', RP, V₂⟩ := (V₁.symm ResidualPair.symm).level_core_left
    (Guard := ResidualPair D A C) (fun H R => ResidualPair.left H R) RB₁'
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ht rfl rfl ((RB.trans RQ).scoped (fun H => .base H))
  have sorted {a c} (RA : ProofShape.Compute (ErasedLevelCore D) A a)
      (RC : ProofShape.Compute (ErasedLevelCore D) C c) :
      DomainSort (proofEraseCtx Γ) a u ∧ DomainSort (proofEraseCtx Γ) c u := by
    have replay {x y} (S : DomainSort (proofEraseCtx Γ) x u)
        (R : ProofShape.Compute (ErasedLevelCore D) x y) : DomainSort (proofEraseCtx Γ) y u := by
      obtain ⟨Γ₀, X, hΓ₀, EΓ₀, hX, EX⟩ := S
      obtain ⟨Y, HY, EY⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
        hΓ₀ hX EΓ₀ EX (R.scoped (fun H => .base H))
      exact ⟨Γ₀, Y, hΓ₀, EΓ₀, HY.hasType.2, EY⟩
    exact ⟨replay SA RA, replay SC RC⟩
  have hguard {a c} (H : ResidualPair D A C a c) :
      ComputedJointCompare (PiInertStage D stage) (proofEraseCtx Γ) false a c ∨
      ∃ u, DomainSort (proofEraseCtx Γ) a u ∧ DomainSort (proofEraseCtx Γ) c u ∧
        ComputedJointCompare (PiInertStage D stage) (proofEraseCtx Γ) true a c := by
    cases domainMode with
    | false =>
      apply Or.inl
      rcases H with ⟨RA, RC⟩ | ⟨RA, RC⟩
      · exact HG RA RC
      · exact .symm (HG RA RC)
    | true =>
      apply Or.inr
      rcases H with ⟨RA, RC⟩ | ⟨RA, RC⟩
      · exact ⟨u, (sorted RA RC).1, (sorted RA RC).2, HG RA RC⟩
      · exact ⟨u, (sorted RA RC).2, (sorted RA RC).1, .symm (HG RA RC)⟩
  have W : ContextRenaming (proofEraseCtx Γ) (proofEraseCtx Γ) (fun i => .bvar (i + 0)) :=
    ContextRenaming.identity
  have H := annotation_variant_domain_computed_check (mode := mode)
    (pi_inert_stage_rename heq hs stage)
    (fun H => hguard H) V₂ hΓ HE.hasType.2 EE W
  exact .compute RP.in_pi_inert_stage RQ.in_pi_inert_stage (.symm H)




/-- A contextual full-core comparison of the marked domains suffices for
arbitrary typed consumers of the paired lambdas. Either domain-checking mode
suffices because the actual shared sort survives every core residual. The
recursive grammar supplies this premise from a smaller child. -/
theorem pi_inert_annotation_consumer_core
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (HG : ∀ {a c}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ A) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ C) c →
      ComputedJointCompare (PiInertStage D stage) (proofEraseCtx Γ) domainMode a c)
    (RL : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A b))) left)
    (RR : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam C b))) right) :
    ComputedJointCompare (PiInertStage D stage) (proofEraseCtx Γ) mode left right := by
  obtain ⟨hC', V⟩ := lambda_variant heq hs hΓ hA hC hb (fun RA RB => (HG RA RB).mono pi_inert_stage_embed)
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
  exact residual_check heq hs hc (fun RA RB => HG RA RB)
    ⟨Γ, A, hΓ, rfl, hA, rfl⟩ ⟨Γ, C, hΓ, rfl, hC, rfl⟩ hΓ
    (ht.instN henv Ctx.InstN.zero hC') VT RL RR


end Lean4Lean.VEnv.Strengthening
