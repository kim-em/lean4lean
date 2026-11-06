import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEnvironmentCore

/-! # Arbitrary consumers of cast-certified lambda annotations

Finite staged cast certificates may justify the marked lambda domains. Paired
simulation then covers arbitrary typed consumers and full-core residuals at
the same stage, without higher-stage confluence or arbitrary guard substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- A recursive level-core domain check constructs common Pi typing and a
marked pair of same-body lambdas, including proof-valued lambdas. -/
theorem staged_lambda_annotation_variant
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (HA : LevelStagedCastGuard D stage false (proofErase Γ A) (proofErase Γ C)) :
    env.HasType univs Γ (.lam C b) (.forallE A B) ∧
      AnnotationVariant (LevelStagedCastGuard D stage false) 0
        (proofErase Γ (.lam A b)) (proofErase Γ (.lam C b)) := by
  have HC : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) false
      (proofErase Γ A) (proofErase Γ C) := HA.forward heq hs hl hcon hc hreg hoff hD .refl .refl
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
    (AnnotationVariant.marked (n := 0) (b := proofErase (A :: Γ) b) HA .refl)

/-- Any typed consumer of a certified reannotation pair has inferred comparison
at every pair of full level-core residuals. The consumer may create arbitrary
new redexes by applying or duplicating the supplied lambdas. No domain join,
normal form, native recovery of the consumer, or global guarded confluence is
required. -/
theorem staged_annotation_consumer_core
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hb : env.HasType univs (A :: Γ) b B)
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (HA : LevelStagedCastGuard D stage false (proofErase Γ A) (proofErase Γ C))
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A b))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam C b))) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) (proofEraseCtx Γ) false left right := by
  obtain ⟨hC', V⟩ := staged_lambda_annotation_variant heq hs hl hcon hc hreg hoff hD hΓ hA hC hb HA
  have hf := HasType.lam hA hb
  have hΓPi : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
  have VT : AnnotationVariant (LevelStagedCastGuard D stage false) 0
      (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b))) := by
    rw [proofErase_instN hΓPi hf Ctx.InstN.zero ht, proofErase_instN hΓPi hC' Ctx.InstN.zero ht]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
    apply AnnotationVariant.subst_images
    intro i
    cases i with
    | zero => exact V
    | succ i => exact .refl
  exact staged_annotation_core_residual_check heq hs hl hcon hc hreg hoff hD hΓ
    (ht.instN henv Ctx.InstN.zero hC') VT RL RR

omit [Params] in
/-- Actual well-formed environments discharge core soundness, universe
compatibility, concrete pattern checks and typed core confluence. Only the
constructive recursive domain guard remains as an alignment premise. -/
theorem EnvironmentCore.staged_annotation_consumer_core
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {stage Γ A C u b B t T left right}, env.HasCanonicalEq → OnCtx Γ (env.IsType U) →
      env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort u) →
      env.HasType U (A :: Γ) b B → env.HasType U (.forallE A B :: Γ) t T →
      LevelStagedCastGuard definitions stage false (proofErase Γ A) (proofErase Γ C) →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A b))) left →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam C b))) right →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions stage) (proofEraseCtx Γ) false left right := by
  letI := henv.params U
  intro stage Γ A C u b B t T left right heq hΓ hA hC hb ht HA RL RR
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact Strengthening.staged_annotation_consumer_core heq sound
    (levelCompatible (fun H => H)) (fun H => H) (typed_level_core_confluence (fun H => H))
    hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq) hΓ hA hC hb ht HA RL RR


omit [Params] in
/-- Reflexive casts in written lambda domains are admissible under arbitrary
typed consumers and independent full-core paths. The finite guard is constructed
here from the actual typings, so no domain-certificate premise is supplied. -/
theorem EnvironmentCore.cast_domain_annotation_consumer
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ u X q b B t T left right}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) →
      env.HasType U Γ q (eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u)) →
      let A := typeCast (.succ u) (.sort u) (.sort u) q X
      env.HasType U (A :: Γ) b B → env.HasType U (.forallE A B :: Γ) t T →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A b))) left →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam X b))) right →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 1)
        (proofEraseCtx Γ) false left right := by
  letI := henv.params U
  intro Γ u X q b B t T left right heq hu hΓ hX hq A hb ht RL RR
  have hS : env.HasType U Γ (.sort u) (.sort (.succ u)) := .sort hu
  have hA := (IsDefEq.typeCast_refl henv heq (by exact hu) hΓ hS hq hX).hasType.1
  have HA : LevelStagedCastGuard definitions 1 false (proofErase Γ A) (proofErase Γ X) :=
    .cast (by exact hu) hΓ hS hS hq hX (.core (.join hΓ hS hS ⟨_, .refl, .refl⟩))
  exact staged_annotation_consumer_core henv U heq hΓ hA hX hb ht HA RL RR

omit [Params] in
/-- The new domain premise covers a Pi and its free-major reflexive cast,
which cannot carry the earlier inferred core guard. This proves a strict
extension of the admissible domain certificates, not a counterexample to
strengthening or a completeness result for the staged grammar. -/
theorem EnvironmentCore.cast_annotation_guard_beyond_core
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ u i A B}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ (.forallE A B) (.sort u) →
      env.HasType U Γ (.bvar i)
        (eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u)) →
      let C := typeCast (.succ u) (.sort u) (.sort u) (.bvar i) (.forallE A B)
      LevelStagedCastGuard definitions 1 false
        (proofErase Γ (.forallE A B)) (proofErase Γ C) ∧
      ¬ LevelRecursiveGuard definitions false
        (proofErase Γ (.forallE A B)) (proofErase Γ C) := by
  letI := henv.params U
  intro Γ u i A B heq hu hΓ hpi hq C
  have hS : env.HasType U Γ (.sort u) (.sort (.succ u)) := .sort hu
  refine ⟨.symm (.cast (by exact hu) hΓ hS hS hq hpi
    (.core (.join hΓ hS hS ⟨_, .refl, .refl⟩))), ?_⟩
  intro H
  have HC := H.forward sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) .refl .refl
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ hpi)] at HC
  obtain ⟨A', B', R⟩ := HC.level_pi_exposure
  exact level_cast_no_pi henv U heq (by exact hu) hΓ hS hq hpi R

end Lean4Lean.VEnv.Strengthening
