import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextualAnnotationCore
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureOpaqueCastConsumer

/-! # Recursive casts and annotation consumers in their actual contexts

Annotation-consumer results are retained as recursive certificates and can
justify a later cast. Each constructor has smaller certificate children; full
core stability is proved by interpretation, never stored as an oracle premise.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params] {D : Definitions}

/-- A context-indexed finite-stage certificate. Casts increase the stage bound;
annotation consumers preserve it. Arbitrary typed consumers of cast payloads
are included at the cast's next-stage bound. Core tails, typed core prefixes and actual
binder insertions retain the certificate. Arbitrary ambient substitution and
coverage of semantic equality are not asserted. -/
inductive ContextualCastGuard (D : Definitions) :
    Nat → Bool → List ProofShape → ProofShape → ProofShape → Prop where
  | prior : LevelStagedCastGuard D n mode a b → ContextualCastGuard D n mode Δ a b
  | raise (hle : n ≤ m) : ContextualCastGuard D n mode Δ a b → ContextualCastGuard D m mode Δ a b
  | cast (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
      (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
      (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
      (hx : env.HasType univs Γ x X)
      (H : ContextualCastGuard D n true (proofEraseCtx Γ) (proofErase Γ X) (proofErase Γ Y)) :
      ContextualCastGuard D (n+1) mode (proofEraseCtx Γ)
        (proofErase Γ (typeCast u X Y q x)) (proofErase Γ x)
  | castConsumer (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
      (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
      (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
      (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t T)
      (H : ContextualCastGuard D n true (proofEraseCtx Γ) (proofErase Γ X) (proofErase Γ Y)) :
      ContextualCastGuard D (n+1) mode (proofEraseCtx Γ)
        (proofErase Γ (t.inst (typeCast u X Y q x))) (proofErase Γ (t.inst x))
  | annotation (hΓ : OnCtx Γ (env.IsType univs))
      (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
      (hb : env.HasType univs (A :: Γ) b B)
      (ht : env.HasType univs (.forallE A B :: Γ) t T)
      (H : ContextualCastGuard D n false (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ C)) :
      ContextualCastGuard D n mode (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b)))
  | compute (hΓ : OnCtx Γ (env.IsType univs))
      (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
      (RA : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ a) a')
      (RB : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ b) b')
      (H : ContextualCastGuard D n mode (proofEraseCtx Γ) a' b') :
      ContextualCastGuard D n mode (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)
  | reducts (H : ContextualCastGuard D n mode Δ a b)
      (RA : ProofShape.Compute (ErasedLevelCore D) a a')
      (RB : ProofShape.Compute (ErasedLevelCore D) b b') : ContextualCastGuard D n mode Δ a' b'
  | weaken (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
      (W : Ctx.LiftN count k Γ Γ')
      (H : ContextualCastGuard D n mode (proofEraseCtx Γ) a b) :
      ContextualCastGuard D n mode (proofEraseCtx Γ') (a.liftN count k) (b.liftN count k)
  | symm : ContextualCastGuard D n mode Δ a b → ContextualCastGuard D n mode Δ b a

/-- A structural induction proves full-core stability for every recursive
certificate. Annotation children supply contextual residual checks; cast children
supply the next-stage endpoint guard. Only ordinary core confluence is used. -/
theorem ContextualCastGuard.forward
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : ContextualCastGuard D n mode Δ a b)
    (RA : ProofShape.Compute (ErasedLevelCore D) a a')
    (RB : ProofShape.Compute (ErasedLevelCore D) b b') :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ mode a' b' := by
  induction H generalizing a' b' with
  | prior H => exact H.forward heq hs hl hcon hc hreg hoff hD RA RB
  | raise hle _ ih => exact (ih RA RB).mono (fun H => erased_static_structure_eta_expansion_stage_mono hle H)
  | cast hu hΓ hX hY hq hx _ ih =>
    obtain ⟨shared, RL, RR⟩ := contextual_cast_level_core_join heq hs hl hcon hc hreg hoff hD
      hu hΓ hX hY hq hx (fun RA RB => ih RA RB) RA RB
    exact .compute RL RR (.leaf .refl)
  | castConsumer hu hΓ hX hY hq hx ht _ ih =>
    obtain ⟨shared, RL, RR⟩ := contextual_cast_consumer_core_join heq hs hl hcon hc hreg hoff hD
      hu hΓ hX hY hq hx ht (fun RA RB => ih RA RB) RA RB
    exact .compute RL RR (.leaf .refl)
  | annotation hΓ hA hC hb ht _ ih =>
    exact contextual_annotation_consumer_core heq hs hc hΓ hA hC hb ht (fun RA RB => ih RA RB) RA RB
  | compute hΓ ha hb RL RR _ ih =>
    obtain ⟨left, RL', HL⟩ := hc hΓ ha RA RL
    obtain ⟨right, RR', HR⟩ := hc hΓ hb RB RR
    exact .compute RL'.in_static_stage RR'.in_static_stage (ih HL HR)
  | reducts _ RL RR ih => exact ih (RL.trans RA) (RR.trans RB)
  | weaken hΓ hΓ' W _ ih =>
    obtain ⟨a₀, RA₀, rfl⟩ := RA.level_core_lift_inv
    obtain ⟨b₀, RB₀, rfl⟩ := RB.level_core_lift_inv
    have H := (ih RA₀ RB₀).rename (erased_static_structure_eta_expansion_stage_rename heq hs _)
      (ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [JointCheckKind.subst, subst_bvar_liftN] using H
  | symm _ ih => exact .symm (ih RB RA)

omit [Params] in
/-- Actual canonical-Eq environments discharge all primitive and confluence
interfaces. The output keeps the certificate's finite stage bound. -/
theorem EnvironmentCore.contextual_cast_guard_forward {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n mode Δ a b a' b'}, env.HasCanonicalEq → ContextualCastGuard definitions n mode Δ a b →
      ProofShape.Compute (ErasedLevelCore definitions) a a' →
      ProofShape.Compute (ErasedLevelCore definitions) b b' →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions n) Δ mode a' b' := by
  letI := henv.params U
  intro n mode Δ a b a' b' heq H RA RB
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.forward heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) RA RB

omit [Params] in
/-- Every actual typed consumer of a recursively certified cast joins its
payload consumer after arbitrary independent full-core reductions. This covers
application, duplication and occurrences beneath dependent binders. -/
theorem EnvironmentCore.contextual_cast_consumer_join {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n u Γ X Y q x t T left right}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ X (.sort u) → env.HasType U Γ Y (.sort u) →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) X Y) →
      env.HasType U Γ x X → env.HasType U (X :: Γ) t T →
      ContextualCastGuard definitions n true (proofEraseCtx Γ) (proofErase Γ X) (proofErase Γ Y) →
      ProofShape.Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (typeCast u X Y q x))) left →
      ProofShape.Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst x)) right →
      ∃ shared, ScopedCompute (ErasedStaticStructureEtaExpansionStage definitions (n+1))
          (proofEraseCtx Γ) left shared ∧
        ScopedCompute (ErasedStaticStructureEtaExpansionStage definitions (n+1))
          (proofEraseCtx Γ) right shared := by
  letI := henv.params U
  intro n u Γ X Y q x t T left right heq hu hΓ hX hY hq hx ht H RL RR
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact contextual_cast_consumer_core_join heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) hu hΓ hX hY hq hx ht
    (fun RA RB => contextual_cast_guard_forward henv U heq H RA RB) RL RR

end Lean4Lean.VEnv.Strengthening
