import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFamilyCast

/-! # Full-core computation joins feed later cast consumers

Sequential computation joins supply recursive endpoint comparisons and actual
canonical equality majors. The next cast may occur in any typed consumer, and
its computation certificate remains available for another join.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Two certified computation sequences to a shared output construct a later
cast's equality major and its arbitrary-consumer computation certificate. The
join is retained inside the grammar, not assumed as a future comparison. -/
theorem CoreFamilyCast.cast_consumer_of_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t T)
    (RX : CoreFamilyCast D n .compute (proofEraseCtx Γ) (proofErase Γ X) shared)
    (RY : CoreFamilyCast D n .compute (proofEraseCtx Γ) (proofErase Γ Y) shared) :
    ∃ q, env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y) ∧
      CoreFamilyCast D (n+1) .compute (proofEraseCtx Γ)
        (proofErase Γ (t.inst (typeCast u X Y q x))) (proofErase Γ (t.inst x)) := by
  have H : CoreFamilyCast D n (.compare true) (proofEraseCtx Γ) (proofErase Γ X) (proofErase Γ Y) :=
    .join RX RY
  have HXY := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY
    (.carrierChecked (H.forward heq hs hl hcon hc hreg hoff hD .refl .refl))
  have hq := (IsDefEq.eqApp_r heq (by exact hu) (HasType.sort hu) hX HXY).defeq
    (HasType.eqReflApp heq (by exact hu) (HasType.sort hu) hX)
  exact ⟨_, hq, .castConsumer hu hΓ hX hY hq hx ht H⟩

omit [Params] in
/-- Actual canonical-Eq environments interpret the complete recursive grammar,
including sequential computation, joins, prefixes and fresh binder insertion. -/
theorem EnvironmentCore.core_family_interpret {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n kind Δ a b}, env.HasCanonicalEq → CoreFamilyCast definitions n kind Δ a b →
      CoreFamilyCast.Interpret definitions n kind Δ a b := by
  letI := henv.params U
  intro n kind Δ a b heq H
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.interpret heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq)

omit [Params] in
/-- Independent full-core reductions of an actual recursive computation join
have finite-stage comparison in either checking mode. The two computation
histories can contain any finite number of certified cast consumers. -/
theorem EnvironmentCore.core_family_join_forward {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n mode Δ a b shared a' b'}, env.HasCanonicalEq →
      CoreFamilyCast definitions n .compute Δ a shared →
      CoreFamilyCast definitions n .compute Δ b shared →
      ProofShape.Compute (ErasedLevelCore definitions) a a' →
      ProofShape.Compute (ErasedLevelCore definitions) b b' →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions n) Δ mode a' b' := by
  letI := henv.params U
  intro n mode Δ a b shared a' b' heq RA RB PA PB
  exact core_family_interpret henv U heq (.join RA RB) PA PB

omit [Params] in
/-- The computation-join feedback construction needs only actual typings and
recursive computation histories in a canonical-Eq environment. -/
theorem EnvironmentCore.core_family_cast_consumer_of_join {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n Γ u X Y x t T shared}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ X (.sort u) → env.HasType U Γ Y (.sort u) →
      env.HasType U Γ x X → env.HasType U (X :: Γ) t T →
      CoreFamilyCast definitions n .compute (proofEraseCtx Γ) (proofErase Γ X) shared →
      CoreFamilyCast definitions n .compute (proofEraseCtx Γ) (proofErase Γ Y) shared →
      ∃ q, env.HasType U Γ q (eqApp (.succ u) (.sort u) X Y) ∧
        CoreFamilyCast definitions (n+1) .compute (proofEraseCtx Γ)
          (proofErase Γ (t.inst (typeCast u X Y q x))) (proofErase Γ (t.inst x)) := by
  letI := henv.params U
  intro n Γ u X Y x t T shared heq hu hΓ hX hY hx ht RX RY
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact CoreFamilyCast.cast_consumer_of_join heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) hu hΓ hX hY hx ht RX RY

end Lean4Lean.VEnv.Strengthening
