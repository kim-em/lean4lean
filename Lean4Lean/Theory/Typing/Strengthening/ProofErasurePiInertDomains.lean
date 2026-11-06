import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertCoreFamily
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaPiDomainReadout

/-! # Domain extraction for every recursive cast comparison

The refined interpretation never rewrites a Pi root. Domain projection therefore
works directly on raw syntax at the original stage, including after weakening.
No lower actual Pi typing is needed for that projection.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
variable [Params] {D : Definitions}

omit [Params] in
/-- A scoped path with no Pi-root primitives retains the exact domain path
in its original context, even while the codomain's binder context changes. -/
theorem ProofShape.ScopedCompute.pi_domain_path
    (hpi : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (R : ScopedCompute Step Δ (.forallE A B) out) :
    ∃ C E, out = .forallE C E ∧ ScopedCompute Step Δ A C := by
  generalize EQ : ProofShape.forallE A B = source at R
  induction R generalizing A B with
  | base H => exact (hpi (EQ ▸ H)).elim
  | beta H =>
    cases EQ
    obtain ⟨C, E, HE, HC, _⟩ := beta_forallE_parts H
    exact ⟨C, E, HE, .beta HC⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, rfl, RA₁⟩ := ih₁ EQ
    obtain ⟨A₂, B₂, HE, RA₂⟩ := ih₂ rfl
    exact ⟨A₂, B₂, HE, RA₁.trans RA₂⟩
  | forallE RA _ => cases EQ; exact ⟨_, _, rfl, RA⟩
  | app | proj | lam => cases EQ

/-- Both checking modes expose common domain comparison when the primitive
skeleton cannot rewrite a Pi root. This is raw certificate projection: no
typing, native recovery, confluence or domain-conversion premise is required. -/
theorem ProofShape.ComputedJointCompare.pi_domains_of_no_pi
    (hpi : ∀ {Δ A B out}, ¬ Step Δ (.forallE A B) out)
    (H : ComputedJointCompare Step Δ mode (.forallE A B) (.forallE C E)) :
    ComputedJointCompare Step Δ true A C := by
  change ComputedJointCheck Step Δ (.compare mode) _ _ at H
  generalize hk : JointCheckKind.compare mode = kind at H
  generalize EL : ProofShape.forallE A B = left at H
  generalize ER : ProofShape.forallE C E = right at H
  induction H generalizing A B C E mode with
  | leaf H =>
    cases hk
    cases H with
    | refl => cases EL; cases ER; exact .leaf .refl
    | sort | const => cases EL
    | etaL HE => obtain ⟨_, _, HE, _⟩ := HE.shape; cases EL.trans HE
    | etaR HE => obtain ⟨_, _, HE, _⟩ := HE.shape; cases ER.trans HE
  | forallE HA _ => cases EL; cases ER; exact ComputedJointCompare.common HA
  | forallSorted _ _ HA _ _ _ => cases EL; cases ER; exact HA
  | compute RL RR _ ih =>
    obtain ⟨A', B', EA, RA⟩ := (EL ▸ RL).pi_domain_path hpi
    obtain ⟨C', E', EC, RC⟩ := (ER ▸ RR).pi_domain_path hpi
    exact .compute RA RC (ih hk EA.symm EC.symm)
  | symm _ ih => exact (ih hk ER EL).symm
  | structFields =>
    have HE := congrArg ProofShape.constHead EL
    simp only [ProofShape.constHead, ProofShape.constHead_mkApps] at HE
    cases HE
  | etaBodyR => cases ER
  | app | appCarrier | appComputed | proj | lam | lamSorted | lamCommon | etaBodyL | etaLams => cases EL
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases hk

/-- Every recursive comparison, including earlier guards and arbitrary
weakening constructors, supplies domains at core-exposed Pis at its exact stage. -/
theorem CoreFamilyCast.pi_domains
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CoreFamilyCast D stage (.compare mode) Δ a b)
    (RA : Compute (ErasedLevelCore D) a (.forallE A B))
    (RB : Compute (ErasedLevelCore D) b (.forallE C E)) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D stage) Δ true A C :=
  ((H.pi_inert_forward heq hs hl hcon hc hreg hoff hD RA RB).pi_domains_of_no_pi
    (fun H => pi_inert_stage_no_pi H)).mono pi_inert_stage_embed

/-- The earlier named prior case is discharged by the refined interpretation
of the entire contextual guard grammar, not only its core subfragment. -/
theorem core_family_pi_prior
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs) : CoreFamilyPiPrior D := by
  intro stage mode Δ a b H Γ A B C E u v w z _ _ _ _ _ _ RA RB
  exact ((H.pi_inert_forward heq hs hl hcon hc hreg hoff hD RA RB).pi_domains_of_no_pi
    (fun H => pi_inert_stage_no_pi H)).mono (fun H => ⟨stage, H.1⟩)

/-- The earlier weakening case is discharged without using the lower readout
premise or assuming lower typings. Interpretation retains the Pi-inert skeleton
through the actual weakening certificate, then raw domain projection applies. -/
theorem core_family_pi_weakening
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs) : CoreFamilyPiWeakening D := by
  intro Γ Γ' count k stage mode a b hΓ hΓ' W H _
  intro Γ₀ A B C E u v w z _ _ _ _ _ _ RA RB
  exact ((H.weaken hΓ hΓ' W).pi_domains heq hs hl hcon hc hreg hoff hD RA RB).mono
    (fun H => ⟨stage, H⟩)

/-- Unconditional core-exposed Pi readout for this recursive certificate
language. This does not assert coverage of arbitrary declarative equalities. -/
theorem CoreFamilyCast.pi_core_domain_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : CoreFamilyCast D stage (.compare mode) Δ a b) : PiCoreDomainReadout D Δ a b := by
  intro Γ A B C E u v w z _ _ _ _ _ _ RA RB
  exact (H.pi_domains heq hs hl hcon hc hreg hoff hD RA RB).mono (fun H => ⟨stage, H⟩)

omit [Params] in
/-- Actual well-formed canonical-Eq environments discharge every primitive,
registry and confluence premise of the same-stage domain extraction theorem. -/
theorem EnvironmentCore.core_family_pi_domains {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {stage mode Δ a b A B C E}, env.HasCanonicalEq →
      CoreFamilyCast definitions stage (.compare mode) Δ a b →
      Compute (ErasedLevelCore definitions) a (.forallE A B) →
      Compute (ErasedLevelCore definitions) b (.forallE C E) →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions stage) Δ true A C := by
  letI := henv.params U
  intro stage mode Δ a b A B C E heq H RA RB
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.pi_domains heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) RA RB

end Lean4Lean.VEnv.Strengthening
