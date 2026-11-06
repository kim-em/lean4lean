import Lean4Lean.Theory.Typing.Strengthening.ProofErasureConvertedNeutralEtaConsumer
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaHistoryConsumer

/-! # Eta residual comparison along certified function histories

A history transports both the eta-expanded and short consumer instances.
Commuting arbitrary source core paths leaves ordinary core tails at the target,
where the native neutral readout applies. The target comparison need not be
hereditary, and no arbitrary substitution closure is inferred from it.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- A supplied function history transports any target eta residual readout.
The two history computations retain ordinary target tails, so no confluence of
higher stages or promotion of the target comparison to hereditary form is used. -/
theorem ArgumentHistory.eta_consumer_residuals
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (hg : env.HasType univs Γ g (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (R : ArgumentHistory D n Γ (.forallE A B) (proofErase Γ f) (proofErase Γ g))
    (H : ∀ {p q},
      Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app g.lift (.bvar 0))))) p →
      Compute (ErasedLevelCore D) (proofErase Γ (t.inst g)) q →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D m) (proofEraseCtx Γ) mode p q)
    (RL : Compute (ErasedLevelCore D) (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left)
    (RR : Compute (ErasedLevelCore D) (proofErase Γ (t.inst f)) right) :
    ComputedJointCompare (ErasedStaticStructureEtaExpansionStage D (max n m))
      (proofEraseCtx Γ) mode left right := by
  have EL := R.eta_consumer heq hs hl hcon hc hreg hoff hD hΓ hf hg ht
  have ER := R.consumer heq hs hl hcon hc hreg hoff hD hΓ hf hg ht
  obtain ⟨p, RP, TP⟩ := EL.base.commute heq hs hl hcon hc hreg hoff hD RL
  obtain ⟨q, RQ, TQ⟩ := ER.base.commute heq hs hl hcon hc hreg hoff hD RR
  exact .compute
    (RP.mono (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.le_max_left n m) H))
    (RQ.mono (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.le_max_left n m) H))
    ((H TP TQ).mono (fun H => erased_static_structure_eta_expansion_stage_mono (Nat.le_max_right n m) H))

omit [Params] in
/-- Certified histories ending at a literal-Pi variable give eta comparison
for every supplied source function and every typed consumer, through arbitrary
independent ordinary-core paths. The function need not itself be a variable. -/
theorem EnvironmentCore.history_to_lookup_eta_consumer_core
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n mode Γ A B i f t T left right}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → Lookup Γ i (.forallE A B) →
      env.HasType U Γ f (.forallE A B) → env.HasType U (.forallE A B :: Γ) t T →
      ArgumentHistory definitions n Γ (.forallE A B) (proofErase Γ f) (proofErase Γ (.bvar i)) →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst f)) right →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions (max n 1))
        (proofEraseCtx Γ) mode left right := by
  letI := henv.params U
  intro n mode Γ A B i f t T left right heq hΓ HL hf ht R RL RR
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact R.eta_consumer_residuals heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq)
    hΓ hf (.bvar HL) ht (fun RP RQ => lookup_eta_consumer_core henv U heq hΓ HL ht RP RQ) RL RR

omit [Params] in
/-- The target variable may use a certified converted domain. History stage
and domain stage combine by maximum; neither is tied to core path length. -/
theorem EnvironmentCore.history_to_converted_lookup_eta_consumer_core
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n stage mode Γ u A B C E i f t T left right}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort u) →
      Lookup Γ i (.forallE C E) → env.HasType U Γ (.bvar i) (.forallE A B) →
      env.HasType U Γ f (.forallE A B) → env.HasType U (.forallE A B :: Γ) t T →
      LevelStagedCastGuard definitions stage false (proofErase Γ A) (proofErase Γ C) →
      ArgumentHistory definitions n Γ (.forallE A B) (proofErase Γ f) (proofErase Γ (.bvar i)) →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) left →
      Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst f)) right →
      ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions (max n (stage+1)))
        (proofEraseCtx Γ) mode left right := by
  letI := henv.params U
  intro n stage mode Γ u A B C E i f t T left right heq hΓ hA hC HL hg hf ht HA R RL RR
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact R.eta_consumer_residuals heq sound (levelCompatible (fun H => H)) (fun H => H)
    (typed_level_core_confluence (fun H => H)) hlookup (hr.eqRec_target heq hn).2.1 (no_eqRec heq)
    hΓ hf hg ht
    (fun RP RQ => staged_converted_lookup_eta_consumer_core henv U heq hΓ hA hC HL hg ht HA RP RQ) RL RR

omit [Params] in
/-- A reflexive cast of a native function variable is a concrete supplied
function covered at stage one. The required history is built from its actual
typing and a reflexive carrier certificate, with no exposure premise. -/
theorem EnvironmentCore.cast_lookup_function_eta_consumer_core
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {mode Γ u A B i q}, env.HasCanonicalEq → OnCtx Γ (env.IsType U) →
      env.HasType U Γ (.forallE A B) (.sort u) → Lookup Γ i (.forallE A B) →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) (.forallE A B) (.forallE A B)) →
      let F := typeCast u (.forallE A B) (.forallE A B) q (.bvar i)
      ∀ {t T left right}, env.HasType U (.forallE A B :: Γ) t T →
        Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A (.app F.lift (.bvar 0))))) left →
        Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst F)) right →
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 1)
          (proofEraseCtx Γ) mode left right := by
  letI := henv.params U
  intro mode Γ u A B i q heq hΓ hPi HL hq F t T left right ht RL RR
  have hu := hPi.sort_r henv hΓ
  have hg : env.HasType U Γ (.bvar i) (.forallE A B) := .bvar HL
  have hf := (IsDefEq.typeCast_refl henv heq hu hΓ hPi hq hg).hasType.1
  have HPi : CoreFamilyCast.Hereditary definitions 0 (.compare true) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE A B)) :=
    .join (.core hΓ hPi .refl) (.core hΓ hPi .refl)
  have R : ArgumentHistory definitions 1 Γ (.forallE A B) (proofErase Γ F) (proofErase Γ (.bvar i)) :=
    .cast hu hΓ hPi hPi hq hg HPi
  exact history_to_lookup_eta_consumer_core henv U heq hΓ HL hf ht R RL RR

omit [Params] in
/-- A non-proof reflexive cast cannot expose an ambient variable by ordinary
core computation. Its erased Eq recursor spine persists along every path. -/
theorem EnvironmentCore.reflexive_cast_no_core_variable
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ u X q x i}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ X (.sort u) → env.HasType U Γ x X →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) X X) → ¬ IsProof Γ x →
      ¬ Compute (ErasedLevelCore definitions) (proofErase Γ (typeCast u X X q x)) (.bvar i) := by
  letI := henv.params U
  intro Γ u X q x i heq hu hΓ hX hx hq hn R
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hX hq hx
  have hnC : ¬ IsProof Γ (typeCast u X X q x) := fun H => hn ((isProof_congr hΓ HC).1 H)
  have Eq : proofErase Γ q = .proof := proofErase_eq_proof.2
    ⟨_, hq, HasType.eqApp heq (by exact hu) (.sort hu) hX hX⟩
  have ES := proofErase_const_spine hΓ
    (args := [.sort u, X, castMotive u X, x, X, q]) HC.hasType.1 hnC
  change proofErase Γ (typeCast u X X q x) = _ at ES
  simp only [List.map_cons, List.map_nil, Eq] at ES
  have HS : EqCastShape (proofErase Γ (typeCast u X X q x)) := ⟨_, _, _, _, _, _, _, ES⟩
  obtain ⟨data, hlookup, hr, hne, _⟩ := heq.recursorRegistration henv
  have HO := proofErase_eq_cast_shape_core sound (levelCompatible (fun H => H))
    (fun H => H) hlookup (hr.eqRec_target heq hne).2.1 (no_eqRec heq) hΓ HC.hasType.1 HS R
  obtain ⟨v, w, α, z, M, m, y, E⟩ := HO
  cases E

omit [Params] in
/-- This supplied function has residual eta comparison in every typed consumer,
but no ordinary-core path exposes a variable or a lambda. The certified cast
history therefore adds coverage beyond either ordinary exposure case. -/
theorem EnvironmentCore.cast_lookup_eta_beyond_core_exposure
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {mode Γ u A B i q}, env.HasCanonicalEq → OnCtx Γ (env.IsType U) →
      env.HasType U Γ (.forallE A B) (.sort u) → Lookup Γ i (.forallE A B) →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) (.forallE A B) (.forallE A B)) →
      (¬ IsProof Γ (.bvar i)) →
      let F := typeCast u (.forallE A B) (.forallE A B) q (.bvar i)
      ∀ {t T left right}, env.HasType U (.forallE A B :: Γ) t T →
        Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst (.lam A (.app F.lift (.bvar 0))))) left →
        Compute (ErasedLevelCore definitions) (proofErase Γ (t.inst F)) right →
        ComputedJointCompare (ErasedStaticStructureEtaExpansionStage definitions 1)
          (proofEraseCtx Γ) mode left right ∧
        (∀ j, ¬ Compute (ErasedLevelCore definitions) (proofErase Γ F) (.bvar j)) ∧
        (∀ C c, ¬ Compute (ErasedLevelCore definitions) (proofErase Γ F) (.lam C c)) := by
  letI := henv.params U
  intro mode Γ u A B i q heq hΓ hPi HL hq hn F t T left right ht RL RR
  have hu := hPi.sort_r henv hΓ
  have hg : env.HasType U Γ (.bvar i) (.forallE A B) := .bvar HL
  exact ⟨cast_lookup_function_eta_consumer_core henv U heq hΓ hPi HL hq ht RL RR,
    (fun _ => reflexive_cast_no_core_variable henv U heq hu hΓ hPi hg hq hn),
    (fun _ _ => reflexive_cast_no_core_lambda henv U heq hu hΓ hPi hg hq hn)⟩

end Lean4Lean.VEnv.Strengthening
