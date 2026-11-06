import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCastCoreResidual

/-! # A recursive guard retaining explicit first-stage cast repairs

This extends the level-core guard with actual reflexive casts. Its forward
interpretation compares arbitrary level-core reducts at singleton stage one.
Computation tails, typed prefixes, binder frames and self loops retain the new
certificate. This does not assert stability under arbitrary stage-one paths or
arbitrary typed substitution, nor coverage of all native comparisons.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- A recursive comparison with explicit reflexive-cast leaves. The cast
constructor records source typing, not a target comparison or confluence oracle.
The old level-core fragment embeds intact; new frames may contain cast repairs
at arbitrary depth. Its residual computations are still restricted to the core. -/
inductive LevelCastGuard (D : Definitions) : Bool → ProofShape → ProofShape → Prop where
  | core : LevelRecursiveGuard D mode a b → LevelCastGuard D mode a b
  | cast (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
      (hX : env.HasType univs Γ X (.sort u))
      (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X X))
      (hx : env.HasType univs Γ x X) :
      LevelCastGuard D mode (proofErase Γ (typeCast u X X q x)) (proofErase Γ x)
  | lam : LevelCastGuard D false A A' → LevelCastGuard D mode b b' →
      LevelCastGuard D mode (.lam A b) (.lam A' b')
  | lamCommon : LevelCastGuard D true b b' → LevelCastGuard D true (.lam A b) (.lam A' b')
  | forallE : LevelCastGuard D false A A' → LevelCastGuard D false B B' →
      LevelCastGuard D mode (.forallE A B) (.forallE A' B')
  | selfLoop : LevelCastGuard D false A B → LevelCastGuard D mode (selfLoop A) (selfLoop B)
  | compute (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
      (hb : env.HasType univs Γ b B)
      (RA : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ a) a')
      (RB : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ b) b')
      (H : LevelCastGuard D mode a' b') :
      LevelCastGuard D mode (proofErase Γ a) (proofErase Γ b)
  | reducts (H : LevelCastGuard D mode a b)
      (RA : ProofShape.Compute (ErasedLevelCore D) a a')
      (RB : ProofShape.Compute (ErasedLevelCore D) b b') : LevelCastGuard D mode a' b'
  | symm : LevelCastGuard D mode a b → LevelCastGuard D mode b a

/-- Every independent full level-core tail retains comparison at stage one.
The proof follows the guard structurally and uses only level-core confluence;
no confluence or forward-transport premise for singleton stages is assumed.
The checking context is arbitrary, including contexts introduced by outer frames. -/
theorem LevelCastGuard.forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : LevelCastGuard D mode a b)
    (RA : ProofShape.Compute (ErasedLevelCore D) a a')
    (RB : ProofShape.Compute (ErasedLevelCore D) b b') :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D 1) Δ mode a' b' := by
  have embed {Δ a b} (R : ProofShape.Compute (ErasedLevelCore D) a b) :
      ScopedCompute (ErasedStaticStructureEtaExpansionStage D 1) Δ a b :=
    R.scoped (fun H => .base (.inl (.inl H)))
  induction H generalizing a' b' Δ with
  | core H => exact ((H.forward hs hl hcon hc RA RB).scoped
      (fun H => .base (.inl (.inl H)))).joint.computed
  | cast hu hΓ hX hq hx =>
    obtain ⟨shared, RL, RR⟩ := reflexive_cast_level_core_join heq hs hl hcon hc
      hreg hoff hD hu hΓ hX hq hx RA RB
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
    exact .compute (embed RL') (embed RR') (ih HL HR)
  | reducts _ RL RR ih => exact ih (RL.trans RA) (RR.trans RB)
  | symm _ ih => exact .symm (ih RB RA)

/-- Independent typed outputs joined to the two references retain the extended
certificate itself, so surrounding frames and later core tails can reuse it.
This construction needs no confluence premise. -/
theorem LevelCastGuard.of_typed_joins
    (H : LevelCastGuard D mode a b)
    (hΓ : OnCtx Γ (env.IsType univs))
    (he : env.HasType univs Γ e A) (hf : env.HasType univs Γ f B)
    (JL : ComputeJoin (ErasedLevelCore D) (proofErase Γ e) a)
    (JR : ComputeJoin (ErasedLevelCore D) (proofErase Γ f) b) :
    LevelCastGuard D mode (proofErase Γ e) (proofErase Γ f) := by
  obtain ⟨left, RL, RA⟩ := JL
  obtain ⟨right, RR, RB⟩ := JR
  exact .compute hΓ he hf RL RR (.reducts H RA RB)

omit [Params] in
/-- In an actual environment the extended guard needs only canonical Eq to
interpret arbitrary core tails; all core and registration interfaces discharge. -/
theorem EnvironmentCore.cast_guard_forward {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {mode a b a' b' Δ}, env.HasCanonicalEq → LevelCastGuard definitions mode a b →
      ProofShape.Compute (ErasedLevelCore definitions) a a' →
      ProofShape.Compute (ErasedLevelCore definitions) b b' →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 1) Δ mode a' b' := by
  letI := henv.params U
  intro mode a b a' b' Δ heq H RA RB
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.forward heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) RA RB

omit [Params] in
/-- A free-major reflexive Pi cast strictly separates the new certificate
from the old level-core guard. Both the certificate and the old-guard exclusion
are constructed in the actual environment, not postulated as coverage. -/
theorem EnvironmentCore.cast_guard_strict {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u Γ X i A B}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) X X) →
      env.HasType U Γ (.forallE A B) X →
      let P := proofErase Γ (.forallE A B)
      let C := proofErase Γ (typeCast u X X (.bvar i) (.forallE A B))
      LevelCastGuard definitions false P C ∧ ¬ LevelRecursiveGuard definitions false P C := by
  letI := henv.params U
  intro u Γ X i A B heq hu hΓ hX hq hpi
  refine ⟨.symm (.cast hu hΓ hX hq hpi), ?_⟩
  intro H
  have HC := H.forward sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) .refl .refl
  obtain ⟨⟨_, hA⟩, _, hB⟩ := hpi.forallE_inv henv
  rw [show proofErase Γ (.forallE A B) = .forallE _ _ from
    if_neg (not_isProof_of_sort hΓ (HasType.forallE hA hB))] at HC
  obtain ⟨C, E, R⟩ := HC.level_pi_exposure
  exact level_cast_no_pi henv U heq hu hΓ hX hq hpi R

omit [Params] in
/-- The previous cast-loop obstruction now has a reusable certificate, and
all of its independent level-core reducts compare at stage one. The lambda
bodies may loop forever; no normalization or fixed reference is assumed. -/
theorem EnvironmentCore.cast_loop_guard_forward {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u Γ X q x left right Δ}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) X X) → env.HasType U Γ x X →
      ProofShape.Compute (ErasedLevelCore definitions) (selfLoop (proofErase Γ x)) left →
      ProofShape.Compute (ErasedLevelCore definitions)
        (selfLoop (proofErase Γ (typeCast u X X q x))) right →
      LevelCastGuard definitions false left right ∧
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 1) Δ false left right := by
  letI := henv.params U
  intro u Γ X q x left right Δ heq hu hΓ hX hq hx RL RR
  have H : LevelCastGuard definitions false (selfLoop (proofErase Γ x))
      (selfLoop (proofErase Γ (typeCast u X X q x))) := .selfLoop (.symm (.cast hu hΓ hX hq hx))
  exact ⟨H.reducts RL RR, cast_guard_forward henv U heq H RL RR⟩

end Lean4Lean.VEnv.Strengthening
