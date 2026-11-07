import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandOpaqueArguments

/-! # Function calls that consume retained guarded interfaces

Fresh arguments retain every finite demand after a guarded type exposure.
Testing an actual function pair on such an argument constructs its ground
history. An evaluator lambda supplies this stronger input action directly,
including when its selected input type is opaque to ordinary core reduction.
General strong-derivation coverage is not asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private weak_subst from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandBinders
open private value_inst_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertWorldValues
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- Fresh arguments construct all interface demands after a guarded exposure
of their declared domain. Both proof and non-proof fresh arguments are covered;
no interface action is assumed for the fresh variable. -/
theorem PiInertGuardedDemand.fresh
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (S : DomainSort Δ A u) (R : PiInertWorldComputation D n Δ A U) :
    PiInertGuardedDemand D (A::Δ) p (etaArgument u) (etaArgument u)
      (A.liftN 1) (U.liftN 1) := by
  have W := PiInertCoreWorld.weakening (D := D) heq hc S
  have RW : PiInertWorldComputation D n (A::Δ) (A.liftN 1) (U.liftN 1) := by
    simpa only [weak_subst] using R.move W
  obtain ⟨Γ, C, hΓ, EΓ, hC, EC⟩ := S
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have Ev := proofErase_fresh_argument hΓ hC
  have ET := proofErase_liftN hΓ hΓC Ctx.LiftN.one hC
  have HA : TypedAt (A::Δ) (etaArgument u) (A.liftN 1) :=
    ⟨C::Γ, .bvar 0, C.lift, hΓC, by simp only [proofEraseCtx, EC, EΓ],
      .bvar .zero, Ev, ET.trans (congrArg (fun e => e.liftN 1) EC)⟩
  refine ⟨HA, HA, ⟨n, RW⟩, ?_⟩
  classical
  by_cases hu : u ≈ .zero
  · simp only [etaArgument, if_pos hu] at HA ⊢
    exact pi_inert_proof_demand_value hc HA.sources.1 RW.base.1
  · simp only [etaArgument, if_neg hu] at HA ⊢
    have HV : PiInertWorldValue D 0 (A::Δ) (.bvar 0) (.bvar 0) (A.liftN 1) :=
      pi_inert_native_variable_world_neutral.value HA.sources.1 HA.sources.1
    exact (PiInertCarrierValue.neutral ((HV.raise (Nat.zero_le n)).convert RW)).demand
      heq hs hc hRigid RW.base.1

/-- Calls consume the retained action at U, separately from the selected
domain C. The output carrier E is dependent on the left input. This does not
identify such an action with an ordinary arrow demand at an opaque C. -/
def PiInertGuardedInputAction (D : Definitions) (Δ : List ProofShape)
    (r s : PiInertDemand) (f g C U E : ProofShape) : Prop :=
  ∀ {Λ σ x y}, PiInertCoreWorld D Δ Λ σ →
    PiInertGuardedDemand D Λ r x y (C.subst σ) (U.subst σ) →
    TypedSource Λ (.app (f.subst σ) x) → TypedSource Λ (.app (g.subst σ) y) →
    PiInertDemandValue s D Λ (.app (f.subst σ) x) (.app (g.subst σ) y)
      ((E.subst σ.lift).inst x)

/-- Guarded calls of actual functions construct a ground function history by
fresh-variable testing. The domain exposure is explicit, but no equality or
ground history between the functions is supplied. -/
theorem PiInertGuardedInputAction.typed_base
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E))
    (hg : env.HasType univs Γ g (.forallE C E))
    (R : PiInertWorldComputation D n (proofEraseCtx Γ) (proofErase Γ C) U)
    (H : PiInertGuardedInputAction D (proofEraseCtx Γ) r s
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ C) U (proofErase (C::Γ) E)) :
    PiInertDemandBase D (proofEraseCtx Γ)
      (proofErase Γ f) (proofErase Γ g) (proofErase Γ (.forallE C E)) := by
  have TF := TypedAt.of_typed hΓ hf
  have TG := TypedAt.of_typed hΓ hg
  by_cases hp : IsProof Γ f
  · have hgp := isProof_of_common_type hΓ hf hg hp
    have HF := TF.sources.1
    rw [proofErase_eq_proof.2 hp] at HF
    have HT := TF.sources.2
    rw [proofErase_eq_proof.2 hp, proofErase_eq_proof.2 hgp]
    exact PiInertDemandBase.refl hc HF HT
  have hng : ¬ IsProof Γ g := fun hgp => hp (isProof_of_common_type hΓ hg hf hgp)
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hC⟩, ⟨v, hE⟩⟩ := hPi.forallE_inv henv.ordered
  have EP : proofErase Γ (.forallE C E) =
      .forallE (proofErase Γ C) (proofErase (C::Γ) E) := if_neg (not_isProof_of_sort hΓ hPi)
  have SC := DomainSort.of_typed hΓ hC
  have W := PiInertCoreWorld.weakening (D := D) heq hc SC
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have hFresh (a : VExpr) (ha : env.HasType univs Γ a (.forallE C E)) :
      env.HasType univs (C::Γ) (.app a.lift (.bvar 0)) E := by
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar, VExpr.inst] using
      HasType.app (ha.weak henv) (.bvar .zero)
  have freshSource (a : VExpr) (ha : env.HasType univs Γ a (.forallE C E))
      (hn : ¬ IsProof Γ a) :
      TypedSource (proofErase Γ C :: proofEraseCtx Γ)
        (.app ((proofErase Γ a).liftN 1) (etaArgument u)) :=
    ⟨C::Γ, .app a.lift (.bvar 0), E, hΓC, rfl, hFresh a ha, proofErase_eta_body hΓ hC ha hn⟩
  have HX : PiInertGuardedDemand D (proofErase Γ C :: proofEraseCtx Γ) r
      (etaArgument u) (etaArgument u) ((proofErase Γ C).subst (fun i => .bvar (i+1)))
      (U.subst (fun i => .bvar (i+1))) := by
    simpa only [weak_subst] using PiInertGuardedDemand.fresh heq hs hc hRigid SC R
  have body := H W HX
    (by simpa only [weak_subst] using freshSource f hf hp)
    (by simpa only [weak_subst] using freshSource g hg hng)
  have HE : TypedSource (proofErase Γ C :: proofEraseCtx Γ) (proofErase (C::Γ) E) :=
    ⟨C::Γ, E, .sort v, hΓC, rfl, hE, rfl⟩
  rw [HE.fresh_inst heq hc SC] at body
  simp only [weak_subst] at body
  obtain ⟨m, history⟩ := body.base.history
  exact ⟨TF.sources.1, TG.sources.1, TF.sources.2, m,
    EP.symm ▸ history.function heq hs hc SC⟩

/-- The fresh guarded-call construction also applies to raw assigned
functions. Common actual representatives are recovered from those assignments. -/
theorem PiInertGuardedInputAction.base
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (hf : TypedAt Δ f (.forallE C E)) (hg : TypedAt Δ g (.forallE C E))
    (R : PiInertWorldComputation D n Δ C U)
    (H : PiInertGuardedInputAction D Δ r s f g C U E) :
    PiInertDemandBase D Δ f g (.forallE C E) := by
  obtain ⟨Γ, f₀, F, hΓ, rfl, hf₀, Ef, EF⟩ := hf
  obtain ⟨C₀, E₀, rfl, _, EC, EE⟩ := erase_forallE_inv EF
  obtain ⟨_, hPi⟩ := hf₀.isType henv hΓ
  obtain ⟨g₀, hg₀, Eg⟩ := hg.realize_carrier hΓ hPi EF
  rw [← Ef, ← Eg, ← EF]
  apply PiInertGuardedInputAction.typed_base (r := r) (s := s) heq hs hc hRigid hΓ hf₀ hg₀
    (by simpa only [EC] using R)
  intro Λ σ x y W HX HL HR
  simp only [EC, EE, Ef, Eg] at HX HL HR ⊢
  exact H W HX HL HR

/-- An evaluator lambda consumes guarded function action at an explicit Pi
interface, regardless of its selected domain C. Paired captured arguments may
differ. Beta replay supplies the typed body sources, and core prefixes preserve
the full result demand in every future core world. -/
theorem pi_inert_guarded_evaluator_action
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (HZ : PiInertDemandValue p D Δ z w A) :
    PiInertGuardedInputAction D Δ (.arrow p q) q
      (.lam C (.app (.bvar 0) (z.liftN 1)))
      (.lam C (.app (.bvar 0) (w.liftN 1))) C (.forallE A B) ((B.inst z).liftN 1) := by
  intro Λ σ x y W HX HL HR
  have beta (a x : ProofShape) : Compute (ErasedLevelCore D)
      (.app ((ProofShape.lam C (.app (.bvar 0) (a.liftN 1))).subst σ) x)
      (.app x (a.subst σ)) := by
    have E : ((ProofShape.app (.bvar 0) (a.liftN 1)).subst σ.lift).inst x =
        .app x (a.subst σ) := by
      simp only [ProofShape.subst, ProofShape.Subst.lift, ProofShape.lift_subst_lift,
        ProofShape.inst, Nat.lt_irrefl, ↓reduceIte, ProofShape.liftN_zero]
      exact congrArg (ProofShape.app x) (value_inst_lift (a.subst σ) x)
    exact E ▸ ProofShape.Compute.beta (ProofShape.BetaRed.beta (A := C.subst σ))
  have HL' := (PiInertEvidence.core_source (n := 0) hs hc HL (beta z x)).base.1
  have HR' := (PiInertEvidence.core_source (n := 0) hs hc HR (beta w y)).base.1
  have body := HX.app heq hs hc (HZ.move W) HL' HR'
  simpa only [ProofShape.lift_subst_lift, value_inst_lift, ProofShape.subst_inst] using
    body.prefixes hs hc HL HR (beta z x) (beta w y)

/-- Assigned evaluator lambdas construct their own ground equality and retain
their guarded-input action. Only the captured-argument demand and guarded
domain exposure are supplied; no equality between the evaluators is assumed. -/
theorem pi_inert_guarded_evaluator_value
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hRigid : ∀ {c}, env.Rigid c → ∀ levels rhs, ¬ D.unfolds c levels rhs)
    (HZ : PiInertDemandValue p D Δ z w A)
    (R : PiInertWorldComputation D n Δ C (.forallE A B))
    (HL : TypedAt Δ (.lam C (.app (.bvar 0) (z.liftN 1)))
      (.forallE C ((B.inst z).liftN 1)))
    (HR : TypedAt Δ (.lam C (.app (.bvar 0) (w.liftN 1)))
      (.forallE C ((B.inst z).liftN 1))) :
    PiInertDemandBase D Δ
      (.lam C (.app (.bvar 0) (z.liftN 1))) (.lam C (.app (.bvar 0) (w.liftN 1)))
      (.forallE C ((B.inst z).liftN 1)) ∧
    PiInertGuardedInputAction D Δ (.arrow p q) q
      (.lam C (.app (.bvar 0) (z.liftN 1))) (.lam C (.app (.bvar 0) (w.liftN 1)))
      C (.forallE A B) ((B.inst z).liftN 1) := by
  have H : PiInertGuardedInputAction D Δ (.arrow p q) q
      (.lam C (.app (.bvar 0) (z.liftN 1))) (.lam C (.app (.bvar 0) (w.liftN 1)))
      C (.forallE A B) ((B.inst z).liftN 1) :=
    pi_inert_guarded_evaluator_action heq hs hc HZ
  exact ⟨H.base heq hs hc hRigid HL HR R, H⟩

/-- Actual typing constructs the evaluator's assigned raw lambda when its
function argument returns a universe. Ordinary type equality converts the
fresh head; all erasure equations and non-proof facts are derived here. -/
theorem ProofShape.TypedAt.evaluator_to_sort
    (hΓ : OnCtx Γ (env.IsType univs))
    (HC : env.IsDefEq univs Γ C (.forallE A (.sort v)) (.sort u))
    (hz : env.HasType univs Γ z A) :
    TypedAt (proofEraseCtx Γ)
      (.lam (proofErase Γ C) (.app (.bvar 0) ((proofErase Γ z).liftN 1)))
      (.forallE (proofErase Γ C) (.sort v)) := by
  have hC := HC.hasType.1
  have hΓC : OnCtx (C::Γ) (env.IsType univs) := ⟨hΓ, u, hC⟩
  have hx : env.HasType univs (C::Γ) (.bvar 0) (.forallE A.lift (.sort v)) :=
    (HC.weak henv).defeq (.bvar .zero)
  have hb : env.HasType univs (C::Γ) (.app (.bvar 0) z.lift) (.sort v) :=
    hx.app (hz.weak henv)
  have hf := HasType.lam hC hb
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  have ES : proofErase (C::Γ) (.sort v) = .sort v :=
    if_neg (not_isProof_of_sort hΓC (HasType.sort (hb.sort_r henv hΓC)))
  refine ⟨Γ, .lam C (.app (.bvar 0) z.lift), .forallE C (.sort v), hΓ, rfl, hf, ?_, ?_⟩
  · rw [show proofErase Γ (.lam C (.app (.bvar 0) z.lift)) = .lam _ _ from
      if_neg (not_isProof_function_to_sort hΓ hf),
      show proofErase (C::Γ) (.app (.bvar 0) z.lift) = .app _ _ from
        if_neg (not_isProof_of_sort hΓC hb),
      show proofErase (C::Γ) (.bvar 0) = .bvar 0 from
        if_neg (not_isProof_function_to_sort hΓC hx),
      proofErase_liftN hΓ hΓC Ctx.LiftN.one hz]
  · rw [show proofErase Γ (.forallE C (.sort v)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPi), ES]

omit [Params] in
/-- In the full environment core, an evaluator lambda at a free-major
reflexive cast domain constructs guarded-input action at every result profile.
Its selected domain has no ordinary-core arrow certificate. The evaluator's
typing, captured ground demand and stage-one exposure are all constructed
from actual typings; none is supplied as a raw source or action hypothesis. -/
theorem EnvironmentCore.cast_evaluator_guarded_action
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u v w Γ j A z}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ (.sort v) (.sort u) →
      env.HasType U Γ (.bvar j) (eqApp (.succ u) (.sort u) (.sort v) (.sort v)) →
      env.HasType U Γ (.forallE A (.sort w)) (.sort v) → env.HasType U Γ z A →
      let C := proofErase Γ (typeCast u (.sort v) (.sort v) (.bvar j) (.forallE A (.sort w)))
      let e := ProofShape.lam C (.app (.bvar 0) ((proofErase Γ z).liftN 1))
      PiInertDemandBase definitions (proofEraseCtx Γ) e e (.forallE C (.sort w)) ∧
      (∀ q, PiInertGuardedInputAction definitions (proofEraseCtx Γ) (.arrow .ground q) q
        e e C (.forallE (proofErase Γ A) (.sort w)) (.sort w)) ∧
      (∀ p q, ¬ PiInertCoreTypeCarrier definitions (proofEraseCtx Γ) (.arrow p q) C) := by
  letI := henv.params U
  intro u v w Γ j A z heq hu hΓ hX hq hPi hz
  dsimp only
  have hs : definitions.Sound env U := EnvironmentCore.sound
  have hcon : ∀ {p r}, Pat p r → ConcretePattern env p r := fun H => H
  have hc : TypedCoreConfluence (ErasedLevelCore definitions) :=
    EnvironmentCore.typed_level_core_confluence hcon
  obtain ⟨data, hreg, hr, hn, _⟩ := heq.recursorRegistration henv
  have RX := PiInertEvidence.core (stage := 0) hs hc hΓ hX (.refl)
  have HX : PiInertEvidence definitions 0 (.compare true) (proofEraseCtx Γ)
      (proofErase Γ (.sort v)) (proofErase Γ (.sort v)) := RX.join hc RX
  have ht : env.HasType U (.sort v :: Γ) (.bvar 0) (VExpr.sort v).lift := .bvar .zero
  have RC := HX.castConsumer heq hs (EnvironmentCore.levelCompatible hcon) hcon hc
    hreg (hr.eqRec_target heq hn).2.1 (EnvironmentCore.no_eqRec heq)
    hu hΓ hX hX hq hPi ht
  obtain ⟨⟨a, hA⟩, ⟨b, hB⟩⟩ := hPi.forallE_inv henv.ordered
  have hΓA : OnCtx (A::Γ) (env.IsType U) := ⟨hΓ, a, hA⟩
  have EP : proofErase Γ (.forallE A (.sort w)) = .forallE (proofErase Γ A) (.sort w) := by
    rw [show proofErase Γ (.forallE A (.sort w)) = .forallE _ _ from
      if_neg (not_isProof_of_sort hΓ hPi),
      show proofErase (A::Γ) (.sort w) = .sort w from if_neg (not_isProof_of_sort hΓA hB)]
  have R : PiInertWorldComputation definitions 1 (proofEraseCtx Γ)
      (proofErase Γ (typeCast u (.sort v) (.sort v) (.bvar j) (.forallE A (.sort w))))
      (.forallE (proofErase Γ A) (.sort w)) := by
    simpa only [VExpr.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, VExpr.liftN_zero, EP]
      using RC.world_computation
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hX hq hPi
  have HF := TypedAt.evaluator_to_sort hΓ HC hz
  have HZ : PiInertDemandValue .ground definitions (proofEraseCtx Γ)
      (proofErase Γ z) (proofErase Γ z) (proofErase Γ A) :=
    PiInertDemandBase.refl hc (TypedAt.of_typed hΓ hz).sources.1
      (TypedAt.of_typed hΓ hz).sources.2
  have HV (q : PiInertDemand) := pi_inert_guarded_evaluator_value (q := q)
    heq hs hc (fun h => EnvironmentCore.no_rigid h) HZ R HF HF
  exact ⟨(HV .ground).1, fun q => (HV q).2,
    fun _ _ => reflexive_cast_no_core_type_carrier henv U heq hu hΓ hX hq hPi⟩

end Lean4Lean.VEnv.Strengthening
