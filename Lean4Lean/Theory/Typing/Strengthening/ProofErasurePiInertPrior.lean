import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertAnnotation

/-! # Pi-inert interpretation of all earlier cast guards

These refinements retain the outer primitive heads of the existing construction.
Guard comparisons use their original complete finite stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : Definitions}

/-- Structural induction interprets every guard after independent arbitrary
full-core computation at its stated finite stage. Casts consume only their
child induction hypothesis and core confluence; no higher-stage confluence or
postulated endpoint conversion is needed. -/
theorem LevelStagedCastGuard.pi_inert_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : LevelStagedCastGuard D n mode a b)
    (RA : ProofShape.Compute (ErasedLevelCore D) a a')
    (RB : ProofShape.Compute (ErasedLevelCore D) b b') :
    ComputedJointCompare (PiInertStage D n) Δ mode a' b' := by
  induction H generalizing a' b' Δ with
  | core H => exact ((H.forward hs hl hcon hc RA RB).scoped (Step := ErasedLevelCore D)
      (fun H => .base (pi_inert_stage_core H))).joint.computed
  | raise hle _ ih => exact (ih RA RB).mono (fun H => pi_inert_stage_mono hle H)
  | cast hu hΓ hX hY hq hx _ ih =>
    obtain ⟨shared, RL, RR⟩ := pi_inert_staged_cast_level_core_join heq hs hl hcon hc hreg hoff hD
      hu hΓ hX hY hq hx (fun RA RB => (ih RA RB).mono pi_inert_stage_embed) RA RB
    exact .compute RL RR (.leaf .refl)
  | castSpine hu hΓ hX hY hq hf ht _ ih =>
    obtain ⟨shared, RL, RR⟩ := pi_inert_staged_cast_spine_level_core_join heq hs hl hcon hc hreg hoff hD
      hu hΓ hX hY hq hf ht (fun RA RB => (ih RA RB).mono pi_inert_stage_embed) RA RB
    exact .compute RL RR (.leaf .refl)
  | lam _ _ ihA ihb =>
    obtain ⟨_, _, rfl, RL, Rl⟩ := RA.level_core_lam_inv
    obtain ⟨_, _, rfl, RR, Rr⟩ := RB.level_core_lam_inv
    exact .lam (ihA RL RR) (ihb Rl Rr)
  | lamCommon _ ih =>
    obtain ⟨_, _, rfl, _, RL⟩ := RA.level_core_lam_inv
    obtain ⟨_, _, rfl, _, RR⟩ := RB.level_core_lam_inv
    exact .lamCommon (ih RL RR)
  | forallE _ _ ihA ihB =>
    obtain ⟨_, _, rfl, RL, Rl⟩ := RA.pi_parts (fun H => erased_level_core_no_pi H)
    obtain ⟨_, _, rfl, RR, Rr⟩ := RB.pi_parts (fun H => erased_level_core_no_pi H)
    exact .forallE (ihA RL RR) (ihB Rl Rr)
  | selfLoop _ ih =>
    obtain ⟨_, _, rfl, RL, _⟩ := RA.level_selfLoop_inv
    obtain ⟨_, _, rfl, RR, _⟩ := RB.level_selfLoop_inv
    exact .app (.lam (ih RL RR) (.leaf .refl)) (.lamCommon (.leaf .refl))
  | compute hΓ ha hb RL RR _ ih =>
    obtain ⟨left, RL', HL⟩ := hc hΓ ha RA RL
    obtain ⟨right, RR', HR⟩ := hc hΓ hb RB RR
    exact .compute RL'.in_pi_inert_stage RR'.in_pi_inert_stage (ih HL HR)
  | reducts _ RL RR ih => exact ih (RL.trans RA) (RR.trans RB)
  | symm _ ih => exact .symm (ih RB RA)

/-- A structural induction proves full-core stability for every recursive
certificate. Annotation children supply contextual residual checks; cast children
supply the next-stage endpoint guard. Only ordinary core confluence is used. -/
theorem ContextualCastGuard.pi_inert_forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : ContextualCastGuard D n mode Δ a b)
    (RA : ProofShape.Compute (ErasedLevelCore D) a a')
    (RB : ProofShape.Compute (ErasedLevelCore D) b b') :
    ComputedJointCompare (PiInertStage D n) Δ mode a' b' := by
  induction H generalizing a' b' with
  | prior H => exact H.pi_inert_forward heq hs hl hcon hc hreg hoff hD RA RB
  | raise hle _ ih => exact (ih RA RB).mono (fun H => pi_inert_stage_mono hle H)
  | cast hu hΓ hX hY hq hx _ ih =>
    obtain ⟨shared, RL, RR⟩ := pi_inert_contextual_cast_level_core_join heq hs hl hcon hc hreg hoff hD
      hu hΓ hX hY hq hx (fun RA RB => (ih RA RB).mono pi_inert_stage_embed) RA RB
    exact .compute RL RR (.leaf .refl)
  | castConsumer hu hΓ hX hY hq hx ht _ ih =>
    obtain ⟨shared, RL, RR⟩ := pi_inert_cast_consumer_core_join heq hs hl hcon hc hreg hoff hD
      hu hΓ hX hY hq hx ht (fun RA RB => (ih RA RB).mono pi_inert_stage_embed) RA RB
    exact .compute RL RR (.leaf .refl)
  | annotation hΓ hA hC hb ht _ ih =>
    exact pi_inert_annotation_consumer_core heq hs hc hΓ hA hC hb ht (fun RA RB => ih RA RB) RA RB
  | compute hΓ ha hb RL RR _ ih =>
    obtain ⟨left, RL', HL⟩ := hc hΓ ha RA RL
    obtain ⟨right, RR', HR⟩ := hc hΓ hb RB RR
    exact .compute RL'.in_pi_inert_stage RR'.in_pi_inert_stage (ih HL HR)
  | reducts _ RL RR ih => exact ih (RL.trans RA) (RR.trans RB)
  | weaken hΓ hΓ' W _ ih =>
    obtain ⟨a₀, RA₀, rfl⟩ := RA.level_core_lift_inv
    obtain ⟨b₀, RB₀, rfl⟩ := RB.level_core_lift_inv
    have H := (ih RA₀ RB₀).rename (pi_inert_stage_rename heq hs _)
      (ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [JointCheckKind.subst, subst_bvar_liftN] using H
  | symm _ ih => exact .symm (ih RB RA)



end Lean4Lean.VEnv.Strengthening
