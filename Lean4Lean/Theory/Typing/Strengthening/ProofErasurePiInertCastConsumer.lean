import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCastResiduals

/-! # Pi-inert computation of arbitrary cast consumers

These refinements retain the outer primitive heads of the existing construction.
Guard comparisons use their original complete finite stage.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Every typed consumer of a cast and its payload has a directed join
at independent full-core residuals, retaining an ordinary core payload path. The endpoint-family premise is
an induction interface for recursive cast guards; no consumer confluence or
normalization hypothesis is assumed. -/
theorem pi_inert_cast_consumer_core_commute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t T)
    (HG : ∀ {a b}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ) true a b)
    (RL : ProofShape.Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (typeCast u X Y q x))) left)
    (RR : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (t.inst x)) right) :
    ∃ shared, ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) left shared ∧
      ProofShape.Compute (ErasedLevelCore D) right shared := by
  have HXY := (proofErase_computed_joint_compare_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY (HG .refl .refl)).1
      ⟨_, HasType.sort hu⟩
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ (HXY.of_l henv hΓ hX) hq hx
  have hΓX : OnCtx (X :: Γ) (env.IsType univs) := ⟨hΓ, u, hX⟩
  have hcast : env.HasType univs Γ (typeCast u X Y q x) X :=
    (HXY.of_l henv hΓ hX).symm.defeq HC.hasType.1
  have hleft := ht.instN henv Ctx.InstN.zero hcast
  have hright := ht.instN henv Ctx.InstN.zero hx
  by_cases hp : IsProof Γ (typeCast u X Y q x)
  · have Ex := proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)
    have E : proofErase Γ (t.inst (typeCast u X Y q x)) = proofErase Γ (t.inst x) := by
      rw [proofErase_instN hΓX hcast Ctx.InstN.zero ht,
        proofErase_instN hΓX hx Ctx.InstN.zero ht, proofErase_eq_proof.2 hp, Ex]
    rw [E] at RL
    obtain ⟨shared, RA, RB⟩ := hc hΓ hright RL RR
    exact ⟨shared, RA.in_pi_inert_stage, RB⟩
  have Eq : proofErase Γ q = .proof := proofErase_eq_proof.2
    ⟨_, hq, HasType.eqApp heq (by exact hu) (.sort hu) hX hY⟩
  have ES := proofErase_const_spine hΓ
    (args := [.sort u, X, castMotive u X, x, Y, q]) HC.hasType.1 hp
  change proofErase Γ (typeCast u X Y q x) = _ at ES
  simp only [List.map_cons, List.map_nil, Eq] at ES
  have HS : EqCastShape (proofErase Γ (typeCast u X Y q x)) := ⟨_, _, _, _, _, _, _, ES⟩
  let Guard : ProofShape → ProofShape → Prop := fun a b =>
    ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (typeCast u X Y q x)) a ∧ b = proofErase Γ x
  have hshape {a b} (H : Guard a b) : EqCastShape a :=
    proofErase_eq_cast_shape_core hs hl hcon hreg hoff hD hΓ HC.hasType.1 HS H.1
  have hg {a b a'} (H : Guard a b) (R : ProofShape.Compute (ErasedLevelCore D) a a') : Guard a' b :=
    ⟨H.1.trans R, H.2⟩
  have hguard {a b} (H : Guard a b) : ∃ shared,
      ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) a shared ∧
      ProofShape.Compute (ErasedLevelCore D) b shared := by
    obtain ⟨minor, RM, RA⟩ := pi_inert_contextual_cast_level_core_residual heq hs hl hcon hreg hoff hD
      hu hΓ hX hY hq hx (fun RA RB => HG RA RB) H.1
    exact ⟨minor, RA, H.2 ▸ RM.mono (fun H => .inl H)⟩
  have V : OpaqueVariant Guard 0 (proofErase Γ (t.inst (typeCast u X Y q x)))
      (proofErase Γ (t.inst x)) := by
    rw [proofErase_instN hΓX hcast Ctx.InstN.zero ht, proofErase_instN hΓX hx Ctx.InstN.zero ht]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
    apply OpaqueVariant.subst_images
    intro i; cases i with
    | zero =>
      change OpaqueVariant Guard 0 (proofErase Γ (typeCast u X Y q x)) (proofErase Γ x)
      simpa only [ProofShape.liftN_zero] using
        (OpaqueVariant.marked (n := 0) (Guard := Guard) ⟨.refl, rfl⟩)
    | succ i => exact .refl
  obtain ⟨b₁, RB₁, V₁⟩ := V.level_core_left (Guard := Guard) heq hreg hoff (fun H => hshape H) (fun H R => hg H R) RL
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hleft rfl rfl (RL.scoped (fun H => .base H))
  have W : ContextRenaming (proofEraseCtx Γ) (proofEraseCtx Γ) (fun i => .bvar (i + 0)) :=
    ContextRenaming.identity
  obtain ⟨shared, RJ, RC⟩ := opaque_variant_join
    (pi_inert_stage_rename heq hs (n+1))
    (fun H => hguard H) V₁ hΓ HE.hasType.2 EE W
  obtain ⟨out, RS, RQ⟩ := hc hΓ hright (RB₁.trans RC) RR
  exact ⟨out, RJ.trans RS.in_pi_inert_stage, RQ⟩


/-- Every typed consumer of a cast and its payload has a finite-stage join
at arbitrary independent full-core residuals. The endpoint-family premise is
an induction interface for recursive cast guards; no consumer confluence or
normalization hypothesis is assumed. -/
theorem pi_inert_cast_consumer_core_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y))
    (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t T)
    (HG : ∀ {a b}, ProofShape.Compute (ErasedLevelCore D) (proofErase Γ X) a →
      ProofShape.Compute (ErasedLevelCore D) (proofErase Γ Y) b →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx Γ) true a b)
    (RL : ProofShape.Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (typeCast u X Y q x))) left)
    (RR : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (t.inst x)) right) :
    ∃ shared, ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) left shared ∧
      ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) right shared := by
  obtain ⟨shared, RL', RR'⟩ := pi_inert_cast_consumer_core_commute heq hs hl hcon hc hreg hoff hD
    hu hΓ hX hY hq hx ht HG RL RR
  exact ⟨shared, RL', RR'.in_pi_inert_stage⟩



end Lean4Lean.VEnv.Strengthening
