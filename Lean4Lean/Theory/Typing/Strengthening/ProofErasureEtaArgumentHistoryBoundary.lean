import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHereditaryArgumentHistory
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedCompositionBarrier

/-! # The cost of treating eta comparison as argument computation

Typed eta already has a hereditary common comparison. Giving every such pair
a shared computation output, even at an arbitrary finite stage, would
settle PropositionFront. A typed eta/beta fork exposes the domain probes.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Missing promotion of typed eta to a shared finite-stage computation output.
Both paths and the common output may be chosen freely. This is stronger than
common-mode eta comparison and still retains the entire proposition front. -/
def FiniteEtaComputationJoin (D : Definitions) : Prop :=
  ∀ {Γ A B f}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ f (.forallE A B) →
    ∃ n shared, CoreFamilyCast D n .compute (proofEraseCtx Γ)
      (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) shared ∧
      CoreFamilyCast D n .compute (proofEraseCtx Γ) (proofErase Γ f) shared

/-- Proposed shared-output histories for every typed eta pair. Both paths,
the output and stage may depend on the typing. No particular orientation or
normalization is requested. This would still imply the full proposition front. -/
def FiniteEtaArgumentJoin (D : Definitions) : Prop :=
  ∀ {Γ A B f}, OnCtx Γ (env.IsType univs) → env.HasType univs Γ f (.forallE A B) →
    ∃ n shared, ArgumentHistory D n Γ (.forallE A B)
      (proofErase Γ (.lam A (.app f.lift (.bvar 0)))) shared ∧
      ArgumentHistory D n Γ (.forallE A B) (proofErase Γ f) shared

/-- The identity typed consumer reads proposed eta argument histories as a
shared computation output. Its raw output is the same on both sides even when
the function carrier is proof-valued and the identity variable erases. -/
theorem FiniteEtaArgumentJoin.computationJoin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : FiniteEtaArgumentJoin D) : FiniteEtaComputationJoin D := by
  intro Γ A B f hΓ hf
  obtain ⟨n, shared, RL, RR⟩ := H hΓ hf
  have hΓF : OnCtx (.forallE A B :: Γ) (env.IsType univs) := ⟨hΓ, hf.isType henv hΓ⟩
  have hi : env.HasType univs (.forallE A B :: Γ) (.bvar 0) (VExpr.forallE A B).lift := .bvar .zero
  have IL := (RL.interpret heq hs hl hcon hc hreg hoff hD).2 hi
  have IR := (RR.interpret heq hs hl hcon hc hreg hoff hD).2 hi
  rw [← proofErase_instN hΓF (IsDefEq.eta hf).hasType.1 Ctx.InstN.zero hi] at IL
  rw [← proofErase_instN hΓF hf Ctx.InstN.zero hi] at IR
  refine ⟨n, (proofErase (.forallE A B :: Γ) (.bvar 0)).inst shared, ?_, ?_⟩
  · simpa only [VExpr.inst, VExpr.instVar, Nat.lt_irrefl, ↓reduceIte, VExpr.liftN_zero] using IL.base
  · simpa only [VExpr.inst, VExpr.instVar, Nat.lt_irrefl, ↓reduceIte, VExpr.liftN_zero] using IR.base

/-- A computation join of the eta pair would compare the two domain probes in
inferred mode. The long eta term beta-reduces to the right probe; the join also
compares it to the left probe. The output can be any raw shape. -/
theorem FiniteEtaComputationJoin.probe_guard
    (H : FiniteEtaComputationJoin D) (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort u)) (_hQ : env.HasType univs Γ Q (.sort u))
    (HPQ : env.IsDefEq univs Γ P Q (.sort u)) :
    ∃ n, CoreFamilyCast D n (.compare false) (proofEraseCtx Γ)
      (proofErase Γ (domainProbe P)) (proofErase Γ (domainProbe Q)) := by
  have hf : env.HasType univs Γ (domainProbe P) (.forallE Q (.sort (.succ .zero))) :=
    (IsDefEq.forallEDF HPQ (HasType.sort (by trivial))).defeq (domainProbe_typed hP)
  obtain ⟨n, shared, RL, RR⟩ := H hΓ hf
  have HG : CoreFamilyCast D n (.compare false) (proofEraseCtx Γ)
      (proofErase Γ (.lam Q (.app (domainProbe P).lift (.bvar 0))))
      (proofErase Γ (domainProbe P)) := .join RL RR
  refine ⟨n, .symm (.reducts HG (.beta ?_) .refl)⟩
  apply proofErase_beta_forward hΓ (IsDefEq.eta hf).hasType.1
  change VExpr.BetaRed (.lam Q (.app (.lam P.lift (.sort .zero)) (.bvar 0)))
    (.lam Q (.sort .zero))
  exact .lam .refl .beta

/-- Even unbounded finite-stage eta computation joins would prove strengthening's
proposition front: inferred descent of the probes forces their domain equality
below the removed binder. This is an implication, not a refutation of eta. -/
theorem FiniteEtaComputationJoin.implies_propositionFront
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : FiniteEtaComputationJoin D) : PropositionFront := by
  intro Γ Q P R hΓ hQ hP hR HE
  have hΓ' : OnCtx (Q :: Γ) (env.IsType univs) := ⟨hΓ, hQ⟩
  have hP' : env.HasType univs (Q :: Γ) P.lift (.sort .zero) := hP.weak henv
  have hR' : env.HasType univs (Q :: Γ) R.lift (.sort .zero) := hR.weak henv
  obtain ⟨n, HG⟩ := H.probe_guard hΓ' hP' hR' (HE.of_l henv hΓ' hP')
  have HR := HG.forward heq hs hl hcon hc hreg hoff hD .refl .refl
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

omit [Params] in
/-- The eta-history promotion would settle the front for actual canonical-Eq
environments, including their full universe-extended primitive core. -/
theorem EnvironmentCore.eta_argument_join_implies_propositionFront
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    env.HasCanonicalEq → FiniteEtaArgumentJoin definitions → PropositionFront := by
  letI := henv.params U
  intro heq H
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  have HE : FiniteEtaComputationJoin definitions := H.computationJoin heq sound
    (levelCompatible (fun H => H)) (fun H => H) (typed_level_core_confluence (fun H => H))
    hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq)
  intro Γ Q P R hΓ hQ hP hR HEQ
  exact FiniteEtaComputationJoin.implies_propositionFront heq sound
    (levelCompatible (fun H => H)) (fun H => H) (typed_level_core_confluence (fun H => H))
    hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq) HE hΓ hQ hP hR HEQ

end Lean4Lean.VEnv.Strengthening
