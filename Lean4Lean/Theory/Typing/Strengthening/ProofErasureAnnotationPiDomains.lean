import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreContextTransport

/-! # Pi domains exposed by annotation consumers

Annotation simulation retains a structural relation after independent core
paths. At exposed Pis that relation compares the domains, using the same
ambient conversion child and stage as the whole consumer.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ResidualPair ResidualPair.symm ResidualPair.left lambda_variant
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextualAnnotationCore
variable [Params] {D : Definitions}

omit [Params] in
/-- Pi nodes cannot be annotation marks, so their domains remain structurally
paired even when marked lambda domains occur arbitrarily deep inside them. -/
theorem ProofShape.AnnotationVariant.pi_domains
    (H : AnnotationVariant Guard n (.forallE A B) (.forallE C E)) :
    AnnotationVariant Guard n A C := by
  cases H with
  | refl => exact .refl
  | forallE HA _ => exact HA

/-- Independent core paths exposing Pis retain domain comparison at the same
checking relation. Only the right source needs an actual typing. The guard
is closed under one-sided computation and symmetry, not arbitrary substitution. -/
theorem annotation_variant_pi_domain_residual_check
    (hs : D.Sound env univs) (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hcore : ∀ {Δ a b}, ErasedLevelCore D a b → Step Δ a b)
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hsym : ∀ {a b}, Guard a b → Guard b a)
    (hg : ∀ {a b a'}, Guard a b → Compute (ErasedLevelCore D) a a' → Guard a' b)
    (hguard : ∀ {A C}, Guard A C → ComputedJointCompare Step (proofEraseCtx Γ) false A C ∨
      ∃ u, DomainSort (proofEraseCtx Γ) A u ∧ DomainSort (proofEraseCtx Γ) C u ∧
        ComputedJointCompare Step (proofEraseCtx Γ) true A C)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (V : AnnotationVariant Guard 0 a (proofErase Γ e))
    (RA : Compute (ErasedLevelCore D) a (.forallE A B))
    (RB : Compute (ErasedLevelCore D) (proofErase Γ e) (.forallE C E)) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode A C := by
  obtain ⟨b₁, RB₁, V₁⟩ := V.level_core_left (Guard := Guard) (fun H R => hg H R) RA
  obtain ⟨q', RQ, RB₁'⟩ := hc hΓ ht RB RB₁
  obtain ⟨p', RP, V₂⟩ := (V₁.symm (fun H => hsym H)).level_core_left (Guard := Guard) (fun H R => hg H R) RB₁'
  obtain ⟨A', B', rfl, RDA, _⟩ := RP.pi_parts (fun H => erased_level_core_no_pi H)
  obtain ⟨C', E', rfl, RDC, _⟩ := RQ.pi_parts (fun H => erased_level_core_no_pi H)
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ht rfl rfl ((RB.trans RQ).scoped (fun H => .base H))
  obtain ⟨C₀, E₀, rfl, _, EC₀, _⟩ := erase_forallE_inv EE
  obtain ⟨⟨_, hC₀⟩, _, _⟩ := HE.hasType.2.forallE_inv henv
  have H := annotation_variant_domain_computed_check (mode := mode) hrename (fun H => hguard H)
    V₂.pi_domains hΓ hC₀ EC₀ ContextRenaming.identity
  exact .compute (RDA.scoped (fun H => .base (hcore H)))
    (RDC.scoped (fun H => .base (hcore H))) H.symm

/-- A smaller annotation-domain comparison child supplies the domains of any
Pis exposed by its two whole consumers. Either mode of the child suffices;
the output comparison keeps the exact stage and may use either mode. -/
theorem contextual_annotation_consumer_pi_domains
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (HG : ∀ {a c}, Compute (ErasedLevelCore D) (proofErase Γ A) a →
      Compute (ErasedLevelCore D) (proofErase Γ C) c →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) domainMode a c)
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A b))) (.forallE X Y))
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam C b))) (.forallE Z W)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) mode X Z := by
  obtain ⟨hC', V⟩ := lambda_variant heq hs hΓ hA hC hb (fun RA RC => HG RA RC)
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
  have guard {a c} (H : ResidualPair D (proofErase Γ A) (proofErase Γ C) a c) :
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) false a c ∨
      ∃ v, DomainSort (proofEraseCtx Γ) a v ∧ DomainSort (proofEraseCtx Γ) c v ∧
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) true a c := by
    cases domainMode with
    | false =>
      apply Or.inl
      rcases H with ⟨RA, RC⟩ | ⟨RA, RC⟩
      · exact HG RA RC
      · exact (HG RA RC).symm
    | true =>
      apply Or.inr
      rcases H with ⟨RA, RC⟩ | ⟨RA, RC⟩
      · exact ⟨u, (DomainSort.of_typed hΓ hA).level_core hs RA,
          (DomainSort.of_typed hΓ hC).level_core hs RC, HG RA RC⟩
      · exact ⟨u, (DomainSort.of_typed hΓ hC).level_core hs RC,
          (DomainSort.of_typed hΓ hA).level_core hs RA, (HG RA RC).symm⟩
  exact annotation_variant_pi_domain_residual_check
    (Guard := ResidualPair D (proofErase Γ A) (proofErase Γ C)) hs hc
    (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.zero_le stage) (.inl H))
    (erased_static_structure_eta_expansion_stage_rename heq hs stage)
    (fun H => ResidualPair.symm H) (fun H R => ResidualPair.left H R) (fun H => guard H)
    hΓ (ht.instN henv Ctx.InstN.zero hC') VT RL RR

end Lean4Lean.VEnv.Strengthening
