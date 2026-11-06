import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHereditaryBetaApplication
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureRawJoinedSubstitution

/-! # Argument histories transport through every typed body

Ordinary core paths and certified value casts compose at a fixed actual
carrier. Their interpretation retains a target realization at that carrier
and a hereditary computation for every typed body using the argument.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private level_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
variable [Params] {D : Definitions}

/-- A computation history for an argument at a fixed actual carrier. The cast
child is a previously constructed hereditary type comparison. Ordinary paths
may have raw outputs, and successive histories need only agree on that output. -/
inductive ArgumentHistory (D : Definitions) :
    Nat → List VExpr → VExpr → ProofShape → ProofShape → Prop where
  | core (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x A)
      (R : ProofShape.Compute (ErasedLevelCore D) (proofErase Γ x) out) :
      ArgumentHistory D n Γ A (proofErase Γ x) out
  | cast (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
      (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
      (hq : env.HasType univs Γ q (eqApp (.succ u) (.sort u) A C))
      (hx : env.HasType univs Γ x A)
      (H : CoreFamilyCast.Hereditary D n (.compare true) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ C)) :
      ArgumentHistory D (n+1) Γ A (proofErase Γ (typeCast u A C q x)) (proofErase Γ x)
  | trans : ArgumentHistory D n Γ A a b → ArgumentHistory D n Γ A b c →
      ArgumentHistory D n Γ A a c
  | raise (hle : n ≤ m) : ArgumentHistory D n Γ A a b → ArgumentHistory D m Γ A a b

/-- The target is realized at the original carrier, and every genuinely typed
body retains hereditary computation between its two raw argument instances. -/
def ArgumentHistory.Interpret (D : Definitions) (n : Nat) (Γ : List VExpr)
    (A : VExpr) (a b : ProofShape) : Prop :=
  (∃ y, env.HasType univs Γ y A ∧ proofErase Γ y = b) ∧
  ∀ {t T}, env.HasType univs (A :: Γ) t T →
    CoreFamilyCast.Hereditary D n .compute (proofEraseCtx Γ)
      ((proofErase (A :: Γ) t).inst a) ((proofErase (A :: Γ) t).inst b)

/-- Interpretation composes the computations of each body directly. Thus no
global congruence or substitution closure is required for arbitrary prior
comparisons, and no original representative is chosen at transitive joints. -/
theorem ArgumentHistory.interpret
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (H : ArgumentHistory D n Γ A a b) : ArgumentHistory.Interpret D n Γ A a b := by
  induction H with
  | @core Γ x A out n hΓ hx R =>
    obtain ⟨y, HY, EY⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ hx rfl rfl (R.scoped (fun H => .base H))
    refine ⟨⟨y, HY.hasType.2, EY⟩, ?_⟩
    intro t T ht
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, hx.isType henv hΓ⟩
    have RT := R.inst_argument (fun H => level_lift H) (proofErase (A :: Γ) t)
    rw [← proofErase_instN hΓA hx Ctx.InstN.zero ht] at RT ⊢
    exact .core hΓ (ht.instN henv Ctx.InstN.zero hx) RT
  | cast hu hΓ hA hC hq hx H =>
    refine ⟨⟨_, hx, rfl⟩, ?_⟩
    intro t T ht
    have HAC := proofErase_computed_joint_carrier_reflect
      (erased_static_structure_eta_expansion_stage_descent heq hs _) hΓ hA hC
      (.carrierChecked (H.base.forward heq hs hl hcon hc hreg hoff hD .refl .refl))
    have hcast := HAC.symm.defeq (IsDefEq.typeCast_refl henv heq hu hΓ HAC hq hx).hasType.1
    have hΓA : OnCtx (_ :: _) (env.IsType univs) := ⟨hΓ, _, hA⟩
    rw [← proofErase_instN hΓA hcast Ctx.InstN.zero ht,
      ← proofErase_instN hΓA hx Ctx.InstN.zero ht]
    exact H.castConsumer heq hs hl hcon hc hreg hoff hD hu hΓ hA hC hq hx ht
  | trans _ _ ih₁ ih₂ => exact ⟨ih₂.1, fun ht => .trans (ih₁.2 ht) (ih₂.2 ht)⟩
  | raise hle _ ih => exact ⟨ih.1, fun ht => .raise hle (ih.2 ht)⟩

/-- Joined argument histories instantiate a hereditary body comparison. The
domains, bodies and actual arguments may differ. Only the shared raw output
is common, and the left history constructs its needed typed realization. -/
theorem CoreFamilyCast.Hereditary.instantiate_argument_histories
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hcore : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort v))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (C :: Γ) c E)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y C)
    (H : CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) (proofErase (C :: Γ) c))
    (RX : ArgumentHistory D n Γ A (proofErase Γ x) shared)
    (RY : ArgumentHistory D n Γ C (proofErase Γ y) shared) :
    CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) (proofErase Γ (c.inst y)) := by
  have IX := RX.interpret heq hs hl hcon hcore hreg hoff hD
  have IY := RY.interpret heq hs hl hcon hcore hreg hoff hD
  obtain ⟨z, hz, Ez⟩ := IX.1
  have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
  have hΓC : OnCtx (C :: Γ) (env.IsType univs) := ⟨hΓ, v, hC⟩
  have W : ContextSubstitution (proofEraseCtx (A :: Γ)) (proofEraseCtx Γ)
      (ProofShape.Subst.one shared) := by
    rw [← Ez]
    exact ContextSubstitution.of_typed hΓ (Ctx.InstN.zero.substEq hΓA hz)
      (erasedSubstAgreement_one hΓA hz)
  have HM := H.substitute W
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb,
    proofErase_instN hΓC hy Ctx.InstN.zero hc]
  apply CoreFamilyCast.Hereditary.prefixes (IX.2 hb) (IY.2 hc)
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one] using HM

/-- Displayed beta applications at distinct computationally related arguments
retain their full hereditary comparison. Casts may occur in the argument
histories, so an ordinary-core common reduct is not required. -/
theorem CoreFamilyCast.Hereditary.beta_application_argument_histories
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hcore : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort v))
    (hb : env.HasType univs (A :: Γ) b B) (hc : env.HasType univs (C :: Γ) c E)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y C)
    (H : CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) b) (proofErase (C :: Γ) c))
    (RX : ArgumentHistory D n Γ A (proofErase Γ x) shared)
    (RY : ArgumentHistory D n Γ C (proofErase Γ y) shared) :
    CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam A b) x)) (proofErase Γ (.app (.lam C c) y)) := by
  have hleft := (HasType.lam hA hb).app hx
  have hright := (HasType.lam hC hc).app hy
  exact .prefixes
    (.core hΓ hleft (.beta (proofErase_beta_forward hΓ hleft .beta)))
    (.core hΓ hright (.beta (proofErase_beta_forward hΓ hright .beta)))
    (H.instantiate_argument_histories heq hs hl hcon hcore hreg hoff hD hΓ hA hC hb hc hx hy RX RY)

omit [Params] in
/-- Actual canonical-Eq environments turn shared-output argument histories into
hereditary comparisons of the two beta applications. All abstract core and
registration hypotheses are discharged here. -/
theorem EnvironmentCore.hereditary_argument_histories_application
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n mode Γ u v A C b c B E x y shared}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort v) →
      env.HasType U (A :: Γ) b B → env.HasType U (C :: Γ) c E →
      env.HasType U Γ x A → env.HasType U Γ y C →
      CoreFamilyCast.Hereditary definitions n (.compare mode) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) b) (proofErase (C :: Γ) c) →
      ArgumentHistory definitions n Γ A (proofErase Γ x) shared →
      ArgumentHistory definitions n Γ C (proofErase Γ y) shared →
      CoreFamilyCast.Hereditary definitions n (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A b) x)) (proofErase Γ (.app (.lam C c) y)) := by
  letI := henv.params U
  intro n mode Γ u v A C b c B E x y shared heq hΓ hA hC hb hc hx hy H RX RY
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.beta_application_argument_histories heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) hΓ hA hC hb hc hx hy RX RY

omit [Params] in
/-- Ordinary-core joins are included without selecting a representative of the
shared reduct or requiring the two written domains to be identical. -/
theorem EnvironmentCore.hereditary_core_joined_application
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n mode Γ u v A C b c B E x y shared}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort v) →
      env.HasType U (A :: Γ) b B → env.HasType U (C :: Γ) c E →
      env.HasType U Γ x A → env.HasType U Γ y C →
      CoreFamilyCast.Hereditary definitions n (.compare mode) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) b) (proofErase (C :: Γ) c) →
      ProofShape.Compute (ErasedLevelCore definitions) (proofErase Γ x) shared →
      ProofShape.Compute (ErasedLevelCore definitions) (proofErase Γ y) shared →
      CoreFamilyCast.Hereditary definitions n (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A b) x)) (proofErase Γ (.app (.lam C c) y)) := by
  letI := henv.params U
  intro n mode Γ u v A C b c B E x y shared heq hΓ hA hC hb hc hx hy H RX RY
  exact hereditary_argument_histories_application henv U heq hΓ hA hC hb hc hx hy H
    (.core hΓ hx RX) (.core hΓ hy RY)

omit [Params] in
/-- A free-proof reflexive cast can be removed from one application argument
while the two lambda bodies differ. The retained body history supplies their
comparison; the argument histories are constructed here from actual typings. -/
theorem EnvironmentCore.hereditary_cast_argument_application
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n mode Γ u A q x b c B E}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ A (.sort u) → env.HasType U Γ q (eqApp (.succ u) (.sort u) A A) →
      env.HasType U Γ x A → env.HasType U (A :: Γ) b B → env.HasType U (A :: Γ) c E →
      CoreFamilyCast.Hereditary definitions n (.compare mode) (proofEraseCtx (A :: Γ))
        (proofErase (A :: Γ) b) (proofErase (A :: Γ) c) →
      CoreFamilyCast.Hereditary definitions (n+1) (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (.app (.lam A b) (typeCast u A A q x)))
        (proofErase Γ (.app (.lam A c) x)) := by
  letI := henv.params U
  intro n mode Γ u A q x b c B E heq hu hΓ hA hq hx hb hc H
  have hcast := (IsDefEq.typeCast_refl henv heq hu hΓ hA hq hx).hasType.1
  have HA : CoreFamilyCast.Hereditary definitions n (.compare true) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ A) := .join (.core hΓ hA .refl) (.core hΓ hA .refl)
  exact hereditary_argument_histories_application henv U heq hΓ hA hA hb hc hcast hx
    (H.raise (Nat.le_succ n)) (.cast hu hΓ hA hA hq hx HA) (.core hΓ hx .refl)

omit [Params] in
/-- Shared-output argument histories strictly exceed ordinary-core joins: a
Pi and its free-proof reflexive cast share the constructed history output,
but cannot have a common reduct in the full ordinary core. -/
theorem EnvironmentCore.argument_histories_beyond_core_join
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ u i A B}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ (.forallE A B) (.sort u) →
      env.HasType U Γ (.bvar i)
        (eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u)) →
      let C := typeCast (.succ u) (.sort u) (.sort u) (.bvar i) (.forallE A B)
      ArgumentHistory definitions 1 Γ (.sort u) (proofErase Γ C) (proofErase Γ (.forallE A B)) ∧
      ArgumentHistory definitions 1 Γ (.sort u) (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE A B)) ∧
      ¬ ComputeJoin (ErasedLevelCore definitions) (proofErase Γ C) (proofErase Γ (.forallE A B)) := by
  letI := henv.params U
  intro Γ u i A B heq hu hΓ hpi hq C
  have hS : env.HasType U Γ (.sort u) (.sort (.succ u)) := .sort hu
  have HA : CoreFamilyCast.Hereditary definitions 0 (.compare true) (proofEraseCtx Γ)
      (proofErase Γ (.sort u)) (proofErase Γ (.sort u)) :=
    .join (.core hΓ hS .refl) (.core hΓ hS .refl)
  refine ⟨.cast (by exact hu) hΓ hS hS hq hpi HA, .core hΓ hpi .refl, ?_⟩
  intro HJ
  have hcast := (IsDefEq.typeCast_refl henv heq (by exact hu) hΓ hS hq hpi).hasType.1
  exact (cast_annotation_guard_beyond_core henv U heq hu hΓ hpi hq).2
    (.join hΓ hpi hcast HJ.symm)

end Lean4Lean.VEnv.Strengthening
