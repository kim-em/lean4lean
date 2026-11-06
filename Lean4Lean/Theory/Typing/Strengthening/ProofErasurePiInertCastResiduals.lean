import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertStages

/-! # Pi-inert cast and cast-spine residuals

These refinements retain the outer primitive heads of the existing construction.
Guard comparisons use their original complete finite stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Earlier-stage endpoint transport repairs arbitrary full-core reducts of a
cast at the next stage. Endpoint conversion is reconstructed from the supplied
certificate; no separate semantic equality between X and Y is assumed. -/
theorem pi_inert_staged_cast_level_core_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X)
    (HG : ∀ {a b Δ}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ true a b)
    (R : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (typeCast u X Y q x)) out) :
    ∃ minor, ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ x) minor ∧
      ScopedCompute (PiInertStage D (n+1)) Δ out minor := by
  have HXY := (proofErase_computed_joint_compare_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY (HG .refl .refl)).1
      ⟨_, HasType.sort hu⟩
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ (HXY.of_l henv hΓ hX) hq hx
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ HC.hasType.1 R
  by_cases hp : IsProof Γ (typeCast u X Y q x)
  · have Ex := proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)
    rw [proofErase_eq_proof.2 hp] at RM
    have E := (RM.scoped (Δ := []) (fun H => .base H)).proof_fixed
      (fun H => erased_iota_primitive_head H)
    subst mid
    exact ⟨.proof, Ex ▸ .refl, RT.in_pi_inert_stage⟩
  · have Eq : proofErase Γ q = .proof := proofErase_eq_proof.2
      ⟨_, hq, HasType.eqApp heq (by exact hu) (.sort hu) hX hY⟩
    have ES := proofErase_const_spine hΓ
      (args := [.sort u, X, castMotive u X, x, Y, q]) HC.hasType.1 hp
    change proofErase Γ (typeCast u X Y q x) = _ at ES
    simp only [List.map_cons, List.map_nil, Eq] at ES
    rw [ES] at RM
    obtain ⟨α', a', M', m', b', rfl, _, Ra, _, Rm, Rb⟩ := RM.eqRec_proof_core_inv hreg hoff hD
    have H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ true a' b' :=
      HG (Ra.mono (fun H => .inl H)) (Rb.mono (fun H => .inl H))
    exact ⟨m', Rm, RT.in_pi_inert_stage.trans H.next_pi_inert_stage⟩


/-- The same inductive endpoint premise joins arbitrary independent core tails
of the cast and its payload at one higher finite stage. Confluence is needed
only for the level core at the original payload, never for a singleton stage. -/
theorem pi_inert_staged_cast_level_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X)
    (HG : ∀ {a b Δ}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ true a b)
    (RC : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (typeCast u X Y q x)) castOut)
    (RX : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ x) payloadOut) :
    ∃ shared, ScopedCompute (PiInertStage D (n+1)) Δ castOut shared ∧
      ScopedCompute (PiInertStage D (n+1)) Δ payloadOut shared := by
  obtain ⟨minor, RM, RR⟩ := pi_inert_staged_cast_level_core_residual heq hs hl hcon hreg hoff hD
    hu hΓ hX hY hq hx HG RC
  obtain ⟨shared, RA, RB⟩ := hc hΓ hx (RM.mono (fun H => .inl H)) RX
  exact ⟨shared, RR.trans RA.in_pi_inert_stage, RB.in_pi_inert_stage⟩


/-- Earlier-stage endpoint transport repairs arbitrary full-core reducts of a
cast at the next stage. Endpoint conversion is reconstructed from the supplied
certificate; no separate semantic equality between X and Y is assumed. -/
theorem pi_inert_contextual_cast_level_core_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X)
    (HG : ∀ {a b}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ) true a b)
    (R : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (typeCast u X Y q x)) out) :
    ∃ minor, ProofShape.Compute (ErasedIotaPrimitive D) (proofErase Γ x) minor ∧
      ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) out minor := by
  have HXY := (proofErase_computed_joint_compare_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY (HG .refl .refl)).1
      ⟨_, HasType.sort hu⟩
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ (HXY.of_l henv hΓ hX) hq hx
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ HC.hasType.1 R
  by_cases hp : IsProof Γ (typeCast u X Y q x)
  · have Ex := proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)
    rw [proofErase_eq_proof.2 hp] at RM
    have E := (RM.scoped (Δ := []) (fun H => .base H)).proof_fixed
      (fun H => erased_iota_primitive_head H)
    subst mid
    exact ⟨.proof, Ex ▸ .refl, RT.in_pi_inert_stage⟩
  · have Eq : proofErase Γ q = .proof := proofErase_eq_proof.2
      ⟨_, hq, HasType.eqApp heq (by exact hu) (.sort hu) hX hY⟩
    have ES := proofErase_const_spine hΓ
      (args := [.sort u, X, castMotive u X, x, Y, q]) HC.hasType.1 hp
    change proofErase Γ (typeCast u X Y q x) = _ at ES
    simp only [List.map_cons, List.map_nil, Eq] at ES
    rw [ES] at RM
    obtain ⟨α', a', M', m', b', rfl, _, Ra, _, Rm, Rb⟩ := RM.eqRec_proof_core_inv hreg hoff hD
    have H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ) true a' b' :=
      HG (Ra.mono (fun H => .inl H)) (Rb.mono (fun H => .inl H))
    exact ⟨m', Rm, RT.in_pi_inert_stage.trans H.next_pi_inert_stage⟩


/-- The same inductive endpoint premise joins arbitrary independent core tails
of the cast and its payload at one higher finite stage. Confluence is needed
only for the level core at the original payload, never for a singleton stage. -/
theorem pi_inert_contextual_cast_level_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X)
    (HG : ∀ {a b}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ) true a b)
    (RC : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (typeCast u X Y q x)) castOut)
    (RX : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ x) payloadOut) :
    ∃ shared, ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) castOut shared ∧
      ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) payloadOut shared := by
  obtain ⟨minor, RM, RR⟩ := pi_inert_contextual_cast_level_core_residual heq hs hl hcon hreg hoff hD
    hu hΓ hX hY hq hx HG RC
  obtain ⟨shared, RA, RB⟩ := hc hΓ hx (RM.mono (fun H => .inl H)) RX
  exact ⟨shared, RR.trans RA.in_pi_inert_stage, RB.in_pi_inert_stage⟩


/-- A typed cast in function position can be removed after every full-core
path, leaving an ordinary-core reduct of the entire payload application.
The application suffix is arbitrary and may create beta redexes after removal.
Only the endpoint types require an earlier-stage comparison certificate. -/
theorem pi_inert_staged_cast_spine_level_core_residual
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hf : env.HasType univs Γ f X)
    (ht : env.HasType univs Γ (VExpr.mkApps (typeCast u X Y q f) args) T)
    (HG : ∀ {a b Δ}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ true a b)
    (R : ProofShape.Compute (ErasedLevelCore D)
      (proofErase Γ (VExpr.mkApps (typeCast u X Y q f) args)) out) :
    env.HasType univs Γ (VExpr.mkApps f args) T ∧
    ∃ minor, ProofShape.Compute (ErasedIotaPrimitive D)
        (proofErase Γ (VExpr.mkApps f args)) minor ∧
      ScopedCompute (PiInertStage D (n+1)) Δ out minor := by
  have HXY := (proofErase_computed_joint_compare_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY (HG .refl .refl)).1
      ⟨_, HasType.sort hu⟩
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ (HXY.of_l henv hΓ hX) hq hf
  have HE := (HC.toU.mkApps_congr_left henv hΓ ⟨_, ht⟩).of_l henv hΓ ht
  refine ⟨HE.hasType.2, ?_⟩
  obtain ⟨mid, RM, RT⟩ := proofErase_level_core_ordinary_return hs hl hcon hΓ ht R
  by_cases hp : IsProof Γ (VExpr.mkApps (typeCast u X Y q f) args)
  · have EF := proofErase_eq_proof.2 ((isProof_congr hΓ HE).1 hp)
    rw [proofErase_eq_proof.2 hp] at RM
    have E := (RM.scoped (Δ := []) (fun H => .base H)).proof_fixed
      (fun H => erased_iota_primitive_head H)
    subst mid
    exact ⟨.proof, EF ▸ .refl, RT.in_pi_inert_stage⟩
  · have hpf : ¬ IsProof Γ (VExpr.mkApps f args) := fun H => hp ((isProof_congr hΓ HE).2 H)
    have Eq : proofErase Γ q = .proof := proofErase_eq_proof.2
      ⟨_, hq, HasType.eqApp heq (by exact hu) (.sort hu) hX hY⟩
    have ES := proofErase_const_spine hΓ
      (args := [.sort u, X, castMotive u X, f, Y, q] ++ args) ht hp
    change proofErase Γ (VExpr.mkApps (typeCast u X Y q f) args) = _ at ES
    simp only [List.map_append, List.map_cons, List.map_nil, Eq] at ES
    rw [ES] at RM
    obtain ⟨α', a', M', m', b', args', rfl, _, Ra, _, Rm, Rb, Rargs⟩ :=
      RM.eqRec_proof_spine_core_inv hreg hoff hD
    have H : ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ true a' b' :=
      HG (Ra.mono (fun H => .inl H)) (Rb.mono (fun H => .inl H))
    refine ⟨ProofShape.mkApps m' args', ?_, RT.in_pi_inert_stage.trans ?_⟩
    · rw [proofErase_mkApps hΓ HE.hasType.2 hpf]
      exact ((Rm.scoped (Δ := []) (fun H => .base H)).mkApps
        (Rargs.imp (fun _ _ H => H.scoped (fun H => .base H)))).core_forget
    · exact H.next_pi_inert_stage.mkApps (Lean4Lean.List.Forall₂.rfl (fun _ _ => .refl))


/-- Independent full-core tails of a cast application and its payload
application join at the next stage. Confluence is used only at the original
typed payload application, so created beta redexes need no new closure axiom. -/
theorem pi_inert_staged_cast_spine_level_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hf : env.HasType univs Γ f X)
    (ht : env.HasType univs Γ (VExpr.mkApps (typeCast u X Y q f) args) T)
    (HG : ∀ {a b Δ}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) Δ true a b)
    (RC : ProofShape.Compute (ErasedLevelCore D)
      (proofErase Γ (VExpr.mkApps (typeCast u X Y q f) args)) castOut)
    (RF : ProofShape.Compute (ErasedLevelCore D)
      (proofErase Γ (VExpr.mkApps f args)) payloadOut) :
    ∃ shared, ScopedCompute (PiInertStage D (n+1)) Δ castOut shared ∧
      ScopedCompute (PiInertStage D (n+1)) Δ payloadOut shared := by
  obtain ⟨hfargs, minor, RM, RR⟩ := pi_inert_staged_cast_spine_level_core_residual
    heq hs hl hcon hreg hoff hD hu hΓ hX hY hq hf ht HG RC
  obtain ⟨shared, RA, RB⟩ := hc hΓ hfargs (RM.mono (fun H => .inl H)) RF
  exact ⟨shared, RR.trans RA.in_pi_inert_stage, RB.in_pi_inert_stage⟩



end Lean4Lean.VEnv.Strengthening
