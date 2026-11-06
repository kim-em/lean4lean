import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqRecCarrier

/-! # Dependent Eq computation inside arbitrary typed consumers

Opaque recursor marks survive beta duplication and future substitution. Their
repair consumes carrier histories, including unit indices that have no common
Pi-inert comparison or shared argument history.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- An arbitrary typed consumer of a general dependent Eq recursor returns to
its minor consumer after any independent full-core paths. The output retains an
ordinary-core tail; no normalization or unrestricted substitution theorem is
assumed for guarded computation. -/
theorem pi_inert_eq_rec_consumer_core_commute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (ht : env.HasType univs (T :: Γ) t S)
    (HG : PiInertCarrierResidual D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b))
    (RL : ProofShape.Compute (ErasedLevelCore D)
      (proofErase Γ (t.inst (eqRecApp v w α a M m b p))) left)
    (RR : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (t.inst m)) right) :
    ∃ shared, ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) left shared ∧
      ProofShape.Compute (ErasedLevelCore D) right shared := by
  obtain ⟨_, hw, hα, ha, _, _, hb, hq⟩ := eqRecApp_typings henv heq hΓ ⟨_, hr⟩
  have hab := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb
    ((HG .refl .refl .refl).mono (fun R => pi_inert_stage_embed R))
  have HC := eqRecApp_simAt henv heq hΓ ⟨_, hab⟩ T hr
  have hm := HC.hasType.2
  have hΓT : OnCtx (T :: Γ) (env.IsType univs) := ⟨hΓ, hr.isType henv hΓ⟩
  have hleft := ht.instN henv Ctx.InstN.zero hr
  have hright := ht.instN henv Ctx.InstN.zero hm
  by_cases hp : IsProof Γ (eqRecApp v w α a M m b p)
  · have Ex := proofErase_eq_proof.2 ((isProof_congr hΓ HC).1 hp)
    have E : proofErase Γ (t.inst (eqRecApp v w α a M m b p)) = proofErase Γ (t.inst m) := by
      rw [proofErase_instN hΓT hr Ctx.InstN.zero ht,
        proofErase_instN hΓT hm Ctx.InstN.zero ht, proofErase_eq_proof.2 hp, Ex]
    rw [E] at RL
    obtain ⟨shared, RA, RB⟩ := hc hΓ hright RL RR
    exact ⟨shared, RA.in_pi_inert_stage, RB⟩
  have Eq : proofErase Γ p = .proof := proofErase_eq_proof.2
    ⟨_, hq, HasType.eqApp heq hw hα ha hb⟩
  have ES := proofErase_const_spine hΓ
    (args := [α, a, M, m, b, p]) HC.hasType.1 hp
  change proofErase Γ (eqRecApp v w α a M m b p) = _ at ES
  simp only [List.map_cons, List.map_nil, Eq] at ES
  have HS : EqCastShape (proofErase Γ (eqRecApp v w α a M m b p)) := ⟨_, _, _, _, _, _, _, ES⟩
  let Guard : ProofShape → ProofShape → Prop := fun leftOut rightOut =>
    ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (eqRecApp v w α a M m b p)) leftOut ∧
      rightOut = proofErase Γ m
  have hshape {a b} (H : Guard a b) : EqCastShape a :=
    proofErase_eq_cast_shape_core hs hl hcon hreg hoff hD hΓ HC.hasType.1 HS H.1
  have hg {a b a'} (H : Guard a b) (R : ProofShape.Compute (ErasedLevelCore D) a a') : Guard a' b :=
    ⟨H.1.trans R, H.2⟩
  have hguard {a b} (H : Guard a b) : ∃ shared,
      ScopedCompute (PiInertStage D (n+1)) (proofEraseCtx Γ) a shared ∧
      ProofShape.Compute (ErasedLevelCore D) b shared := by
    obtain ⟨minor, RM, RA⟩ := pi_inert_eq_rec_core_residual heq hs hl hcon hreg hoff hD
      hΓ hr HG H.1
    exact ⟨minor, RA, H.2 ▸ RM⟩
  have V : OpaqueVariant Guard 0 (proofErase Γ (t.inst (eqRecApp v w α a M m b p)))
      (proofErase Γ (t.inst m)) := by
    rw [proofErase_instN hΓT hr Ctx.InstN.zero ht, proofErase_instN hΓT hm Ctx.InstN.zero ht]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
    apply OpaqueVariant.subst_images
    intro i; cases i with
    | zero =>
      change OpaqueVariant Guard 0 (proofErase Γ (eqRecApp v w α a M m b p)) (proofErase Γ m)
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

/-- The arbitrary consumer construction has the retained computation
interpretation, with its output realized at the minor's assigned source type. -/
theorem PiInertInterpret.eq_rec_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (ht : env.HasType univs (T :: Γ) t S)
    (H : PiInertCarrierResidual D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertInterpret D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst (eqRecApp v w α a M m b p))) (proofErase Γ (t.inst m)) := by
  obtain ⟨_, _, _, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, hr⟩
  have hab := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb
    ((H .refl .refl .refl).mono (fun R => pi_inert_stage_embed R))
  have hm := (eqRecApp_simAt henv heq hΓ ⟨_, hab⟩ T hr).hasType.2
  refine ⟨⟨Γ, _, _, hΓ, rfl, ht.instN henv Ctx.InstN.zero hm, rfl⟩, ?_⟩
  intro left RL
  exact pi_inert_eq_rec_consumer_core_commute heq hs hl hcon hc hreg hoff hD
    hΓ hr ht H RL .refl

/-- General Eq computation inside a typed consumer retains every future typed
substitution. Index histories may be carrier-only, including function and
subsingleton guards; the complete result stays at the next finite stage. -/
theorem PiInertCarrierHistory.eq_rec_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hr : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (ht : env.HasType univs (T :: Γ) t S)
    (H : PiInertCarrierHistory D n (proofEraseCtx Γ) (proofErase Γ α)
      (proofErase Γ a) (proofErase Γ b)) :
    PiInertEvidence D (n+1) .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst (eqRecApp v w α a M m b p))) (proofErase Γ (t.inst m)) := by
  refine ⟨PiInertInterpret.eq_rec_consumer heq hs hl hcon hc hreg hoff hD hΓ hr ht H.base, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  obtain ⟨_, _, hα, ha, _, _, hb, _⟩ := eqRecApp_typings henv heq hΓ ⟨_, hr⟩
  have hab := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ ha hb
    ((H.base .refl .refl .refl).mono (fun R => pi_inert_stage_embed R))
  have hm := (eqRecApp_simAt henv heq hΓ ⟨_, hab⟩ T hr).hasType.2
  have hleft := ht.instN henv Ctx.InstN.zero hr
  have hright := ht.instN henv Ctx.InstN.zero hm
  obtain ⟨u, hT⟩ := hr.isType henv hΓ
  have hT' := hT.subst henv.orderedStrong WS hΓ₀
  have ht' := ht.subst henv.orderedStrong (WS.lift henv.ordered hT) ⟨hΓ₀, u, hT'⟩
  have H' := H.substitute W
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hα ES,
    ← proofErase_subst_with hΓ₀ WS ha ES, ← proofErase_subst_with hΓ₀ WS hb ES] at H'
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS hleft ES,
    ← proofErase_subst_with hΓ₀ WS hright ES]
  simp only [VExpr.subst_inst, eqRecApp_subst]
  exact PiInertInterpret.eq_rec_consumer heq hs hl hcon hc hreg hoff hD hΓ₀
    (by simpa only [eqRecApp_subst] using hr.subst henv.orderedStrong WS hΓ₀) ht' H'.base

end Lean4Lean.VEnv.Strengthening
