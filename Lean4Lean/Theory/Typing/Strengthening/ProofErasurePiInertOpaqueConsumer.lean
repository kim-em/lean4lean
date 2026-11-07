import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertUnitLambdaTerminal
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEqRecConsumer

/-! # Certified opaque computations survive arbitrary typed consumers

A saturated proof-major Eq source stays opaque through ordinary core paths.
Its retained computation evidence can therefore repair every copied occurrence
inside a typed consumer, including after beta has consumed a function position.
This uses the existing evidence, without reconstructing an index guard or
assuming application closure for arbitrary function heads.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

omit [Params] in
/-- Substitution preserves the saturated recursor and its erased proof major. -/
theorem ProofShape.EqCastShape.subst (H : EqCastShape e) : EqCastShape (e.subst τ) := by
  obtain ⟨v, w, α, a, M, m, b, rfl⟩ := H
  exact ⟨v, w, _, _, _, _, _, rfl⟩

/-- A retained computation whose actual source is an opaque Eq recursor
commutes with arbitrary core reduction of an actual typed consumer. Every
marked residual is repaired using the original evidence; the target keeps an
ordinary-core tail. Neither a new index history nor guarded confluence is used. -/
theorem PiInertInterpret.opaque_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs (A :: Γ) t T)
    (HS : EqCastShape (proofErase Γ a))
    (H : PiInertInterpret D stage .compute (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    PiInertInterpret D stage .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst a)) (proofErase Γ (t.inst b)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, ha.isType henv hΓ⟩
  have hleft := ht.instN henv Ctx.InstN.zero ha
  have hright := ht.instN henv Ctx.InstN.zero hb
  refine ⟨⟨Γ, _, _, hΓ, rfl, hright, rfl⟩, ?_⟩
  intro left RL
  let Guard : ProofShape → ProofShape → Prop := fun source target =>
    ProofShape.Compute (ErasedLevelCore D) (proofErase Γ a) source ∧ target = proofErase Γ b
  have hshape {source target} (HG : Guard source target) : EqCastShape source :=
    proofErase_eq_cast_shape_core hs hl hcon hreg hoff hD hΓ ha HS HG.1
  have hg {source target out} (HG : Guard source target)
      (R : ProofShape.Compute (ErasedLevelCore D) source out) : Guard out target :=
    ⟨HG.1.trans R, HG.2⟩
  have hguard {source target} (HG : Guard source target) : ∃ shared,
      ScopedCompute (PiInertStage D stage) (proofEraseCtx Γ) source shared ∧
      ProofShape.Compute (ErasedLevelCore D) target shared := by
    obtain ⟨shared, RS, RT⟩ := H.2 HG.1
    exact ⟨shared, RS, HG.2 ▸ RT⟩
  have V : OpaqueVariant Guard 0 (proofErase Γ (t.inst a)) (proofErase Γ (t.inst b)) := by
    rw [proofErase_instN hΓA ha Ctx.InstN.zero ht, proofErase_instN hΓA hb Ctx.InstN.zero ht]
    simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN]
    apply OpaqueVariant.subst_images
    intro i
    cases i with
    | zero =>
      change OpaqueVariant Guard 0 (proofErase Γ a) (proofErase Γ b)
      simpa only [ProofShape.liftN_zero] using
        (OpaqueVariant.marked (n := 0) (Guard := Guard) ⟨.refl, rfl⟩)
    | succ i => exact .refl
  obtain ⟨right, RR, V'⟩ := V.level_core_left (Guard := Guard) heq hreg hoff
    (fun HG => hshape HG) (fun HG R => hg HG R) RL
  obtain ⟨e, HE, EE⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ hleft rfl rfl (RL.scoped (fun R => .base R))
  have W : ContextRenaming (proofEraseCtx Γ) (proofEraseCtx Γ) (fun i => .bvar (i + 0)) :=
    ContextRenaming.identity
  obtain ⟨shared, RS, RT⟩ := opaque_variant_join (pi_inert_stage_rename heq hs stage)
    (fun HG => hguard HG) V' hΓ HE.hasType.2 EE W
  exact ⟨shared, RS, RR.trans RT⟩

/-- Opaque consumer computation retains every future typed substitution at
the same stage. The source shape is syntactically stable under substitution,
and the old evidence supplies each substituted residual repair. -/
theorem PiInertEvidence.opaque_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (ht : env.HasType univs (A :: Γ) t T)
    (HS : EqCastShape (proofErase Γ a))
    (H : PiInertEvidence D stage .compute (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b)) :
    PiInertEvidence D stage .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst a)) (proofErase Γ (t.inst b)) := by
  refine ⟨H.base.opaque_consumer heq hs hl hcon hreg hoff hD hΓ ha hb ht HS, ?_⟩
  intro Δ' τ W
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  obtain ⟨u, hA⟩ := ha.isType henv hΓ
  have hA' := hA.subst henv.orderedStrong WS hΓ₀
  have ht' := ht.subst henv.orderedStrong (WS.lift henv.ordered hA) ⟨hΓ₀, u, hA'⟩
  have H' := H.future W
  have HS' := HS.subst (τ := τ)
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS ha ES,
    ← proofErase_subst_with hΓ₀ WS hb ES] at H'
  rw [← proofErase_subst_with hΓ₀ WS ha ES] at HS'
  rw [← EΓ₀, ← proofErase_subst_with hΓ₀ WS (ht.instN henv Ctx.InstN.zero ha) ES,
    ← proofErase_subst_with hΓ₀ WS (ht.instN henv Ctx.InstN.zero hb) ES]
  simp only [VExpr.subst_inst]
  exact H'.opaque_consumer heq hs hl hcon hreg hoff hD hΓ₀
    (ha.subst henv.orderedStrong WS hΓ₀) (hb.subst henv.orderedStrong WS hΓ₀) ht' HS'

/-- A certified opaque function prefix survives shared application, even
after the consumer has created beta redexes. The assigned function type can be
dependent; the target function and actual argument are otherwise unrestricted. -/
theorem PiInertEvidence.opaque_application
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (hx : env.HasType univs Γ x A) (HS : EqCastShape (proofErase Γ f))
    (H : PiInertEvidence D stage .compute (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ g)) :
    PiInertEvidence D stage .compute (proofEraseCtx Γ)
      (proofErase Γ (.app f x)) (proofErase Γ (.app g x)) := by
  have ht := HasType.app (HasType.bvar (env := env) (U := univs)
    (Lookup.zero (ty := .forallE A B) (Γ := Γ))) (hx.weak henv (B := .forallE A B))
  have HC := H.opaque_consumer heq hs hl hcon hreg hoff hD hΓ hf hg ht HS
  simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using HC

/-- A certified opaque function-to-lambda prefix can now precede the complete
unit application history. The actual target body carries unit frames; all
future substitutions and carrier/endpoint residuals survive at the input
stage. The original function may have any assigned type: the certificate
supplies its needed Pi typing. A raw path is not promoted to a certificate. -/
theorem pi_inert_opaque_unit_application_history
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hRec : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hi : env.projections family info) (hp : info.nparams = 0)
    (hx : info.nindices = 0) (hfields : info.numFields = 0)
    (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f F)
    (hd : env.HasType univs (C :: Γ) d (.sort u)) (hy : env.HasType univs Γ y C)
    (HS : EqCastShape (proofErase Γ f))
    (H : PiInertEvidence D stage .compute (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ (.lam C d)))
    (HF : RigidSortFrames family (proofEraseCtx (C :: Γ)) (proofErase (C :: Γ) d)) :
    PiInertCarrierHistory D stage (proofEraseCtx Γ) (proofErase Γ (.app f y)) a b := by
  obtain ⟨w, hC⟩ := hy.isType henv hΓ
  have htarget := HasType.lam hC hd
  obtain ⟨shared, RL, RR⟩ := H.base.2 .refl
  have HCmp : ComputedJointCompare (PiInertStage D stage) (proofEraseCtx Γ) false
      (proofErase Γ f) (proofErase Γ (.lam C d)) :=
    .compute RL RR.in_pi_inert_stage (.leaf .refl)
  have hnf : ¬ IsProof Γ f := by
    intro hp
    have HH := HS.head
    rw [proofErase_eq_proof.2 hp] at HH
    cases HH
  have hdsc : ErasedScopedPrimitiveDescent (PiInertStage D stage) :=
    fun hΓ hΓ' W ht HR => erased_static_structure_eta_expansion_stage_descent heq hs stage
      hΓ hΓ' W ht HR.1
  have HE := (proofErase_computed_joint_compare_reflect hdsc hΓ hf htarget HCmp).2 rfl hnf
    (not_isProof_function_to_sort hΓ htarget)
  have hfPi := (HE.of_r henv hΓ htarget).hasType.1
  have HP := H.opaque_application heq hs hl hcon hreg hoff hRec hΓ hfPi htarget hy HS
  exact PiInertCarrierHistory.carrier_prefix HP
    (HF.unit_application_history hs hc hi hp hx hfields hD hΓ hd hy)

end Lean4Lean.VEnv.Strengthening
