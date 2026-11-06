import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDomains

/-! # Whole Pi comparison evidence supplies eta readout at the same stage

The comparison can be any CoreFamilyCast certificate, including recursive
prefixes, annotation consumers, earlier guards, and weakening. Its refined
interpretation extracts the domain evidence uniformly over future core paths.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A whole-Pi comparison certificate supplies every domain residual check
needed by a converted lambda's eta readout, at the unchanged stage. The domain
certificate and a uniform bound are proved here rather than assumed. -/
theorem eta_core_readout_lambda_of_pi_comparison
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (H : CoreFamilyCast D stage (.compare comparisonMode) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E))) :
    EtaCoreReadout D (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) u
      (proofErase Γ A) (proofErase Γ (.lam C b)) := by
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB)),
    show proofErase Γ (.forallE C E) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ (HasType.forallE hC hE))] at H
  apply eta_core_readout_lambda_of_domains hs hΓ hA hC hf hn
  intro X Y RA RC
  exact H.pi_domains heq hs hl hcon hc hreg hoff hD (.forallE RA .refl) (.forallE RC .refl)

/-- Every typed identity-wrapped eta consumer retains comparison at the
whole-Pi certificate's original stage after arbitrary independent core paths.
The bound is uniform over those paths and consumers. -/
theorem pi_comparison_eta_identity_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (hC : env.HasType univs Γ C (.sort u)) (hE : env.HasType univs (C :: Γ) E (.sort z))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) (hn : ¬ IsProof Γ (.lam C b))
    (H : CoreFamilyCast D stage (.compare comparisonMode) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE C E)))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (RL : Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (.lam A (.app
        (VExpr.app (.lam (.forallE A B) (.bvar 0)) (.lam C b)).lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (.app (.lam (.forallE A B) (.bvar 0)) (.lam C b)))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) mode left right := by
  have HE := eta_core_readout_lambda_of_pi_comparison heq hs hl hcon hc hreg hoff hD
    hΓ hA hB hC hE hf hn H
  exact HE.identity_consumer hs hc
    (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.zero_le stage) (.inl H))
    (erased_static_structure_eta_expansion_stage_rename heq hs stage) hΓ hA hf ht RL RR

end Lean4Lean.VEnv.Strengthening
