import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHereditaryCoreFamily

/-! # Substitution-stable full-core histories feed later casts

The generated equality major and the entire cast consumer remain available
for later substitutions, core reductions, joins and further casts.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Two certified computation sequences to a shared output construct a later
cast's equality major and its arbitrary-consumer computation certificate. Every future
typed substitution retains the same finite-stage construction. -/
theorem CoreFamilyCast.Hereditary.cast_consumer_of_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hu : u.WF univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hX : env.HasType univs Γ X (.sort u)) (hY : env.HasType univs Γ Y (.sort u))
    (hx : env.HasType univs Γ x X) (ht : env.HasType univs (X :: Γ) t T)
    (RX : CoreFamilyCast.Hereditary D n .compute (proofEraseCtx Γ) (proofErase Γ X) shared)
    (RY : CoreFamilyCast.Hereditary D n .compute (proofEraseCtx Γ) (proofErase Γ Y) shared) :
    ∃ q, env.HasType univs Γ q (eqApp (.succ u) (.sort u) X Y) ∧
      CoreFamilyCast.Hereditary D (n+1) .compute (proofEraseCtx Γ)
        (proofErase Γ (t.inst (typeCast u X Y q x))) (proofErase Γ (t.inst x)) := by
  have H : CoreFamilyCast.Hereditary D n (.compare true) (proofEraseCtx Γ) (proofErase Γ X) (proofErase Γ Y) :=
    .join RX RY
  have HXY := proofErase_computed_joint_carrier_reflect
    (erased_static_structure_eta_expansion_stage_descent heq hs n) hΓ hX hY
    (.carrierChecked (H.base.forward heq hs hl hcon hc hreg hoff hD .refl .refl))
  have hq := (IsDefEq.eqApp_r heq (by exact hu) (HasType.sort hu) hX HXY).defeq
    (HasType.eqReflApp heq (by exact hu) (HasType.sort hu) hX)
  exact ⟨_, hq, H.castConsumer heq hs hl hcon hc hreg hoff hD hu hΓ hX hY hq hx ht⟩

/-- Ordinary typed substitution reconstructs hereditary certificates for the
actual substituted source terms. It preserves the stage and both checking modes. -/
theorem CoreFamilyCast.Hereditary.typed_substitute
    (H : CoreFamilyCast.Hereditary D n kind (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ b))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B) :
    CoreFamilyCast.Hereditary D n kind (proofEraseCtx Γ₀)
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  have ES : ErasedSubstAgreement Γ Γ₀ σ (fun i => proofErase Γ₀ (σ i)) := fun _ _ => rfl
  rw [proofErase_subst_with hΓ₀ W ha ES, proofErase_subst_with hΓ₀ W hb ES]
  exact H.substitute (ContextSubstitution.of_typed hΓ₀ W ES)

omit [Params] in
/-- In actual canonical-Eq environments every retained history has its full
ordinary-core interpretation after any interpreted substitution. Computation
retains a typed output and directed commutation; comparison covers independent
core residuals, including redexes created by the substitution. -/
theorem EnvironmentCore.hereditary_core_family_after {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n kind Δ a b Δ' τ}, env.HasCanonicalEq →
      CoreFamilyCast.Hereditary definitions n kind Δ a b → ContextSubstitution Δ Δ' τ →
      CoreFamilyCast.Interpret definitions n kind Δ' (a.subst τ) (b.subst τ) := by
  letI := henv.params U
  intro n kind Δ a b Δ' τ heq H W
  exact core_family_interpret henv U heq (H.future W)

omit [Params] in
/-- A genuine reflexive cast in any typed consumer supplies a concrete stable
computation seed. Its equality major is arbitrary, including a free proof. -/
theorem EnvironmentCore.hereditary_reflexive_cast_consumer {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ u X q x t T}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ X (.sort u) → env.HasType U Γ q (eqApp (.succ u) (.sort u) X X) →
      env.HasType U Γ x X → env.HasType U (X :: Γ) t T →
      CoreFamilyCast.Hereditary definitions 1 .compute (proofEraseCtx Γ)
        (proofErase Γ (t.inst (typeCast u X X q x))) (proofErase Γ (t.inst x)) := by
  letI := henv.params U
  intro Γ u X q x t T heq hu hΓ hX hq hx ht
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  have HC : CoreFamilyCast.Hereditary definitions 0 (.compare true)
      (proofEraseCtx Γ) (proofErase Γ X) (proofErase Γ X) :=
    .join (.core hΓ hX .refl) (.core hΓ hX .refl)
  exact HC.castConsumer heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) hu hΓ hX hX hq hx ht

omit [Params] in
/-- Actual-environment computation joins generate a later cast and keep all
future substitutions, with the next finite stage known in advance. -/
theorem EnvironmentCore.hereditary_cast_consumer_of_join {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n Γ u X Y x t T shared}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ X (.sort u) → env.HasType U Γ Y (.sort u) →
      env.HasType U Γ x X → env.HasType U (X :: Γ) t T →
      CoreFamilyCast.Hereditary definitions n .compute (proofEraseCtx Γ) (proofErase Γ X) shared →
      CoreFamilyCast.Hereditary definitions n .compute (proofEraseCtx Γ) (proofErase Γ Y) shared →
      ∃ q, env.HasType U Γ q (eqApp (.succ u) (.sort u) X Y) ∧
        CoreFamilyCast.Hereditary definitions (n+1) .compute (proofEraseCtx Γ)
          (proofErase Γ (t.inst (typeCast u X Y q x))) (proofErase Γ (t.inst x)) := by
  letI := henv.params U
  intro n Γ u X Y x t T shared heq hu hΓ hX hY hx ht RX RY
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact CoreFamilyCast.Hereditary.cast_consumer_of_join heq sound (levelCompatible (fun H => H))
    (fun H => H) (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) hu hΓ hX hY hx ht RX RY

omit [Params] in
/-- The identity consumer gives a reusable reflexive-cast computation history
for arbitrary payloads, not only propositions. -/
theorem EnvironmentCore.hereditary_reflexive_cast {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ u X q x}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ X (.sort u) → env.HasType U Γ q (eqApp (.succ u) (.sort u) X X) →
      env.HasType U Γ x X →
      CoreFamilyCast.Hereditary definitions 1 .compute (proofEraseCtx Γ)
        (proofErase Γ (typeCast u X X q x)) (proofErase Γ x) := by
  letI := henv.params U
  intro Γ u X q x heq hu hΓ hX hq hx
  simpa only [VExpr.inst, VExpr.instVar, Nat.lt_irrefl, ↓reduceIte, VExpr.liftN_zero] using
    hereditary_reflexive_cast_consumer henv U heq hu hΓ hX hq hx
      (HasType.bvar (i := 0) (A := X.lift) Lookup.zero)

omit [Params] in
/-- A cast in a written lambda domain now retains arbitrary typed substitution
as well as full-core residual comparison inside every typed consumer. All
history premises are constructed here from the actual typings. -/
theorem EnvironmentCore.hereditary_cast_domain_annotation_consumer
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ u X q b B t T mode}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) →
      env.HasType U Γ q (eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u)) →
      let A := typeCast (.succ u) (.sort u) (.sort u) q X
      env.HasType U (A :: Γ) b B → env.HasType U (.forallE A B :: Γ) t T →
      CoreFamilyCast.Hereditary definitions 1 (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam X b))) := by
  letI := henv.params U
  intro Γ u X q b B t T mode heq hu hΓ hX hq A hb ht
  have hS : env.HasType U Γ (.sort u) (.sort (.succ u)) := .sort hu
  have hA := (IsDefEq.typeCast_refl henv heq (by exact hu) hΓ hS hq hX).hasType.1
  have HA : CoreFamilyCast.Hereditary definitions 1 (.compare false)
      (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ X) :=
    .join (hereditary_reflexive_cast henv U heq (by exact hu) hΓ hS hq hX)
      (.core hΓ hX .refl)
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact HA.annotation heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1
    (no_eqRec heq) hΓ hA hX hb ht

omit [Params] in
/-- The constructive stable fragment includes a Pi and its free-major cast,
which provably lack an old inferred core guard. This tests an actual higher-stage
repair, without claiming coverage of every earlier recursive comparison. -/
theorem EnvironmentCore.hereditary_cast_guard_beyond_core
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ u i A B}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ (.forallE A B) (.sort u) →
      env.HasType U Γ (.bvar i)
        (eqApp (.succ (.succ u)) (.sort (.succ u)) (.sort u) (.sort u)) →
      let C := typeCast (.succ u) (.sort u) (.sort u) (.bvar i) (.forallE A B)
      CoreFamilyCast.Hereditary definitions 1 (.compare false) (proofEraseCtx Γ)
        (proofErase Γ (.forallE A B)) (proofErase Γ C) ∧
      ¬ LevelRecursiveGuard definitions false (proofErase Γ (.forallE A B)) (proofErase Γ C) := by
  letI := henv.params U
  intro Γ u i A B heq hu hΓ hpi hq C
  have hS : env.HasType U Γ (.sort u) (.sort (.succ u)) := .sort hu
  exact ⟨.join (.core hΓ hpi .refl)
    (hereditary_reflexive_cast henv U heq (by exact hu) hΓ hS hq hpi),
    (cast_annotation_guard_beyond_core henv U heq hu hΓ hpi hq).2⟩

end Lean4Lean.VEnv.Strengthening
