import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreFamilyFeedback
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRecursiveSubstitutionBarrier

/-! # Increasing the cast stage does not remove the substitution front

Even stage-zero inferred inputs, one actual typed argument, and an arbitrary
finite output stage suffice to recover PropositionFront. The proof uses only
neutral applications of constant-body probes and identity substitution. No
cast, annotation-consumer, or sequential-computation input is necessary.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Missing finite-stage closure under one genuine typed instantiation. Only
stage-zero inferred inputs are requested, and each output may choose any finite
stage. This is not a strictly smaller sufficient obligation: the reduction below
recovers the complete proposition front from it. -/
def FiniteCoreFamilyInstantiation (D : Definitions) : Prop :=
  ∀ {Γ A b c B p}, OnCtx (A :: Γ) (env.IsType univs) →
    env.HasType univs (A :: Γ) b B → env.HasType univs (A :: Γ) c B →
    env.HasType univs Γ p A →
    CoreFamilyCast D 0 (.compare false) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) c) →
    ∃ n, CoreFamilyCast D n (.compare false) (proofEraseCtx Γ)
      (proofErase Γ (b.inst p)) (proofErase Γ (c.inst p))

/-- A weaker proposed readout: after identity instantiation of an old recursive input,
each pair of core residuals may choose its own finite comparison stage. No
recursive output certificate or uniform stage bound is required. This missing
readout already contains PropositionFront, as proved below. -/
def FiniteRecursiveIdentityReadout (D : Definitions) : Prop :=
  ∀ {Γ T b c B left right}, let A := VExpr.forallE T T.lift;
    let p := VExpr.lam T (.bvar 0);
    OnCtx (A :: Γ) (env.IsType univs) →
    env.HasType univs (A :: Γ) b B → env.HasType univs (A :: Γ) c B →
    env.HasType univs Γ p A →
    LevelRecursiveGuard D false (proofErase (A :: Γ) b) (proofErase (A :: Γ) c) →
    ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (b.inst p)) left →
    ProofShape.Compute (ErasedLevelCore D) (proofErase Γ (c.inst p)) right →
    ∃ n, ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n)
      (proofEraseCtx Γ) false left right

/-- The new grammar contains the old stage-zero probes. Its established
interpretation reads out every residual pair after the proposed instantiation.
There is no requirement to keep the output at stage zero. -/
theorem FiniteCoreFamilyInstantiation.readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : FiniteCoreFamilyInstantiation D) : FiniteRecursiveIdentityReadout D := by
  intro Γ T b c B left right A p hΓA hb hc' hp HG RL RR
  obtain ⟨n, HF⟩ := H hΓA hb hc' hp (.prior (.prior (.core HG)))
  exact ⟨n, HF.forward heq hs hl hcon hc hreg hoff hD RL RR⟩

/-- The identity-substitution witness extracts inferred comparisons of domain
probes at a freely chosen finite stage. The source guard contains no comparison
of these domains; their equality is used only for genuine common source typing. -/
theorem FiniteRecursiveIdentityReadout.probe_compare
    (H : FiniteRecursiveIdentityReadout D)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    ∃ n, ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D n)
      (proofEraseCtx Γ) false (proofErase Γ (domainProbe P)) (proofErase Γ (domainProbe Q)) := by
  obtain ⟨T, b, c, B, hΓA, hb, hc, hp, HG, RL, RR⟩ :=
    recursive_neutral_probe_instantiation (D := D) hΓ hP hQ HPQ
  exact H hΓA hb hc hp HG RL RR

/-- Finite-stage inferred readout after a typed identity substitution still
implies the full proposition front. Inferred descent of the probes requires
neither equality of their types below the removed binder nor stage confluence. -/
theorem FiniteRecursiveIdentityReadout.implies_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (H : FiniteRecursiveIdentityReadout D) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hR' : env.HasType univs (Q :: Γ) R.lift (.sort .zero) := hR.weak henv
  obtain ⟨n, HR⟩ := H.probe_compare hΓ' hP' hR' (HE.of_l henv hΓ' hP')
  have EP : (domainProbe P).lift = domainProbe P.lift := rfl
  have ER : (domainProbe R).lift = domainProbe R.lift := rfl
  rw [← EP, ← ER, proofErase_liftN hΓ hΓ' Ctx.LiftN.one (domainProbe_typed hP),
    proofErase_liftN hΓ hΓ' Ctx.LiftN.one (domainProbe_typed hR)] at HR
  have HP := (proofErase_computed_joint_compare_descend
    (erased_static_structure_eta_expansion_stage_descent heq hs n)
    hΓ hΓ' Ctx.LiftN.one rfl (domainProbe_typed hP) (domainProbe_typed hR) HR).2
    rfl (not_isProof_function_to_sort hΓ (domainProbe_typed hP))
    (not_isProof_function_to_sort hΓ (domainProbe_typed hR))
  have HQ := HP.of_l henv hΓ (domainProbe_typed hP)
  obtain ⟨⟨_, HPR⟩, _⟩ := (HQ.hasType.2.uniqU henv hΓ (domainProbe_typed hR)).forallE_inv henv hΓ
  exact ⟨_, HPR⟩

/-- Allowing arbitrarily many later cast stages does not make unrestricted
inferred instantiation a smaller goal. This implication is not a refutation of
that closure law or of strengthening. -/
theorem FiniteCoreFamilyInstantiation.implies_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : FiniteCoreFamilyInstantiation D) : PropositionFront :=
  FiniteRecursiveIdentityReadout.implies_propositionFront heq hs
    (H.readout heq hs hl hcon hc hreg hoff hD)

omit [Params] in
/-- The implication applies to the actual total environment core, including
universe conversion and its registered primitive programs. -/
theorem EnvironmentCore.finite_core_family_instantiation_implies_propositionFront
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    env.HasCanonicalEq → FiniteCoreFamilyInstantiation definitions → PropositionFront := by
  letI := henv.params U
  intro heq H
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.implies_propositionFront heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq)

end Lean4Lean.VEnv.Strengthening
