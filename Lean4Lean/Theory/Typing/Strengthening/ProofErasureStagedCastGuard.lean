import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCastSpineResidual

/-! # Finite recursive cast repairs with certified endpoint types

A cast consumes a certificate between its actual endpoint types at an earlier
stage. The forward proof reconstructs their semantic equality and the residual
prefix guard from that recursive premise. Arbitrary core tails remain allowed;
no transport or confluence oracle for a higher stage is stored in the grammar.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Finite-stage recursive cast certificates. Different endpoint types are
allowed only when a strictly earlier child certificate compares their erasures.
The stage index bounds the resulting comparison, not the length of core paths.
This grammar does not claim arbitrary substitution or native-comparison coverage. -/
inductive LevelStagedCastGuard (D : Definitions) : Nat → Bool → ProofShape → ProofShape → Prop where
  | core : LevelRecursiveGuard D mode a b → LevelStagedCastGuard D 0 mode a b
  | raise (hle : n ≤ m) : LevelStagedCastGuard D n mode a b → LevelStagedCastGuard D m mode a b
  | cast (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
      (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
      (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
      (hx : env.HasType univs Γ x X)
      (H : LevelStagedCastGuard D n true (proofErase Γ X) (proofErase Γ Y)) :
      LevelStagedCastGuard D (n+1) mode (proofErase Γ (typeCast u X Y q x)) (proofErase Γ x)
  | castSpine (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
      (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
      (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
      (hf : env.HasType univs Γ f X)
      (ht : env.HasType univs Γ (VExpr.mkApps (typeCast u X Y q f) args) T)
      (H : LevelStagedCastGuard D n true (proofErase Γ X) (proofErase Γ Y)) :
      LevelStagedCastGuard D (n+1) mode
        (proofErase Γ (VExpr.mkApps (typeCast u X Y q f) args))
        (proofErase Γ (VExpr.mkApps f args))
  | lam : LevelStagedCastGuard D n false A A' → LevelStagedCastGuard D n mode b b' →
      LevelStagedCastGuard D n mode (.lam A b) (.lam A' b')
  | lamCommon : LevelStagedCastGuard D n true b b' →
      LevelStagedCastGuard D n true (.lam A b) (.lam A' b')
  | forallE : LevelStagedCastGuard D n false A A' → LevelStagedCastGuard D n false B B' →
      LevelStagedCastGuard D n mode (.forallE A B) (.forallE A' B')
  | selfLoop : LevelStagedCastGuard D n false A B →
      LevelStagedCastGuard D n mode (selfLoop A) (selfLoop B)
  | compute (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
      (hb : env.HasType univs Γ b B)
      (RA : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ a) a')
      (RB : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ b) b')
      (H : LevelStagedCastGuard D n mode a' b') :
      LevelStagedCastGuard D n mode (proofErase Γ a) (proofErase Γ b)
  | reducts (H : LevelStagedCastGuard D n mode a b)
      (RA : ProofShape.Compute (ErasedLevelCore D) a a')
      (RB : ProofShape.Compute (ErasedLevelCore D) b b') : LevelStagedCastGuard D n mode a' b'
  | symm : LevelStagedCastGuard D n mode a b → LevelStagedCastGuard D n mode b a

/-- Structural induction interprets every guard after independent arbitrary
full-core computation at its stated finite stage. Casts consume only their
child induction hypothesis and core confluence; no higher-stage confluence or
postulated endpoint conversion is needed. -/
theorem LevelStagedCastGuard.forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : LevelStagedCastGuard D n mode a b)
    (RA : ProofShape.Compute (ErasedLevelCore D) a a')
    (RB : ProofShape.Compute (ErasedLevelCore D) b b') :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ mode a' b' := by
  induction H generalizing a' b' Δ with
  | core H => exact ((H.forward hs hl hcon hc RA RB).scoped
      (fun H => .base (.inl H))).joint.computed
  | raise hle _ ih => exact (ih RA RB).mono (fun H => erased_static_structure_eta_expansion_stage_mono hle H)
  | cast hu hΓ hX hY hq hx _ ih =>
    obtain ⟨shared, RL, RR⟩ := staged_cast_level_core_join heq hs hl hcon hc hreg hoff hD
      hu hΓ hX hY hq hx (fun RA RB => ih RA RB) RA RB
    exact .compute RL RR (.leaf .refl)
  | castSpine hu hΓ hX hY hq hf ht _ ih =>
    obtain ⟨shared, RL, RR⟩ := staged_cast_spine_level_core_join heq hs hl hcon hc hreg hoff hD
      hu hΓ hX hY hq hf ht (fun RA RB => ih RA RB) RA RB
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
    exact .compute RL'.in_static_stage RR'.in_static_stage (ih HL HR)
  | reducts _ RL RR ih => exact ih (RL.trans RA) (RR.trans RB)
  | symm _ ih => exact .symm (ih RB RA)

/-- Every previous reflexive-cast certificate embeds at its original stage-one
bound. The new endpoint child is a reflexive core join, not a new hypothesis. -/
theorem LevelCastGuard.staged (H : LevelCastGuard D mode a b) :
    LevelStagedCastGuard D 1 mode a b := by
  induction H with
  | core H => exact .raise (by decide) (.core H)
  | cast hu hΓ hX hq hx => exact .cast hu hΓ hX hX hq hx (.core (.join hΓ hX hX ⟨_, .refl, .refl⟩))
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | lamCommon _ ih => exact .lamCommon ih
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | selfLoop _ ih => exact .selfLoop ih
  | compute hΓ ha hb RA RB _ ih => exact .compute hΓ ha hb RA RB ih
  | reducts _ RA RB ih => exact .reducts ih RA RB
  | symm _ ih => exact .symm ih

/-- Typed outputs independently joined to the references retain the staged
certificate itself at the same bound. -/
theorem LevelStagedCastGuard.of_typed_joins
    (H : LevelStagedCastGuard D n mode a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e A) (hf : env.HasType univs Γ f B)
    (JL : ComputeJoin (ErasedLevelCore D) (proofErase Γ e) a)
    (JR : ComputeJoin (ErasedLevelCore D) (proofErase Γ f) b) :
    LevelStagedCastGuard D n mode (proofErase Γ e) (proofErase Γ f) := by
  obtain ⟨left, RL, RA⟩ := JL
  obtain ⟨right, RR, RB⟩ := JR
  exact .compute hΓ he hf RL RR (.reducts H RA RB)

omit [Params] in
/-- Actual environments discharge the abstract core interfaces for every
finite cast depth. The resulting comparisons use that same depth bound. -/
theorem EnvironmentCore.staged_cast_guard_forward {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n mode a b a' b' Δ}, env.HasCanonicalEq → LevelStagedCastGuard definitions n mode a b →
      ProofShape.Compute (ErasedLevelCore definitions) a a' →
      ProofShape.Compute (ErasedLevelCore definitions) b b' →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions n) Δ mode a' b' := by
  letI := henv.params U
  intro n mode a b a' b' Δ heq H RA RB
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.forward heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) RA RB

end Lean4Lean.VEnv.Strengthening
