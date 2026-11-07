import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertDemandCoreExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortRecursiveSubstitutionBoundary

/-! # Strong conversion does not manufacture ordinary-core demand exposure

A free-major reflexive Pi cast is strongly equal to a literal function type
but has no ordinary level-core Pi exposure, including in the full environment
core. The new selected-carrier certificate therefore cannot cover every strong
conversion edge. A stage-one interpreted computation handles the same cast;
the obstruction concerns core exposure, not strengthening or all computation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {D : Definitions}

/-- Any arrow certificate forces a directed ordinary-core Pi exposure.
The common reduct of the exposed Pi still has Pi shape, so an existential
join or a deeper finite tree cannot hide this requirement. -/
theorem PiInertCoreTypeCarrier.arrow_exposes
    (H : PiInertCoreTypeCarrier D Δ (.arrow p q) T) :
    ∃ A B, Compute (ErasedLevelCore D) T (.forallE A B) := by
  obtain ⟨_, U, _, ⟨out, RT, RU⟩, HE⟩ := H
  cases HE with
  | function HA HB =>
    obtain ⟨A, B, rfl, _, _⟩ := RU.pi_parts (fun R => erased_level_core_no_pi R)
    exact ⟨A, B, RT⟩

omit [Params] in
/-- Free-major reflexive casts refute arrow exposure certificates in the full
actual level core, at every finite demand with an outer arrow. -/
theorem EnvironmentCore.reflexive_cast_no_core_type_carrier
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {u Γ X i A B p q}, env.HasCanonicalEq → u.WF U →
      OnCtx Γ (env.IsType U) → env.HasType U Γ X (.sort u) →
      env.HasType U Γ (.bvar i) (eqApp (.succ u) (.sort u) X X) →
      env.HasType U Γ (.forallE A B) X →
      ¬ PiInertCoreTypeCarrier definitions (proofEraseCtx Γ) (.arrow p q)
        (proofErase Γ (typeCast u X X (.bvar i) (.forallE A B))) := by
  letI := henv.params U
  intro u Γ X i A B p q heq hu hΓ hX hq hPi H
  obtain ⟨A', B', R⟩ := H.arrow_exposes
  exact level_cast_no_pi henv U heq hu hΓ hX hq hPi R

omit [Params] in
/-- Every canonical-Eq environment supplies an original finite strong
conversion edge from a non-exposable carrier to an exposed Pi. The very same
edge has stage-one interpreted computation with all typed-substitution futures.
Thus core exposure completeness is false even for the full actual core. -/
theorem EnvironmentCore.strong_core_exposure_boundary
    {env : VEnv} (henv : env.WF) (U : Nat) (heq : env.HasCanonicalEq) :
    letI := henv.params U
    ∃ Γ C A B v n, OnCtx Γ (env.IsType U) ∧
      StrongBounded env U n Γ C (.forallE A B) (.sort v) ∧
      PiInertCoreTypeCarrier definitions (proofEraseCtx Γ) (.arrow .ground .ground)
        (proofErase Γ (.forallE A B)) ∧
      (∀ p q, ¬ PiInertCoreTypeCarrier definitions (proofEraseCtx Γ) (.arrow p q)
        (proofErase Γ C)) ∧
      PiInertEvidence definitions 1 .compute (proofEraseCtx Γ)
        (proofErase Γ C) (proofErase Γ (.forallE A B)) := by
  letI := henv.params U
  let u : VLevel := .succ (.succ (.succ .zero))
  let X : VExpr := .sort (.succ (.succ .zero))
  let F : VExpr := .forallE (.sort (.succ .zero)) (.sort (.succ .zero))
  let Q := eqApp (.succ u) (.sort u) X X
  have hu : u.WF U := by trivial
  have hX : env.HasType U [] X (.sort u) := .sort (by trivial)
  have hF : env.HasType U [] F X :=
    (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
      (HasType.forallE (HasType.sort (by trivial)) (HasType.sort (by trivial)))
  have hQ : env.HasType U [] Q (.sort .zero) :=
    HasType.eqApp heq hu (HasType.sort hu) hX hX
  have hΓ : OnCtx [Q] (env.IsType U) := ⟨trivial, _, hQ⟩
  have hXΓ : env.HasType U [Q] X (.sort u) := hX.weak0 henv.ordered
  have hFΓ : env.HasType U [Q] F X := hF.weak0 henv.ordered
  have hq : env.HasType U [Q] (.bvar 0) Q := by
    have HH : env.HasType U [Q] (.bvar 0) Q.lift := .bvar .zero
    simpa [Q, X, eqApp, VExpr.lift, VExpr.liftN] using HH
  have HC := IsDefEq.typeCast_refl henv heq hu hΓ hXΓ hq hFΓ
  obtain ⟨n, HN⟩ := strong_has_bound (HC.strong henv.orderedStrong hΓ)
  have EP : proofErase [Q] F = .forallE
      (proofErase [Q] (.sort (.succ .zero)))
      (proofErase (.sort (.succ .zero) :: [Q]) (.sort (.succ .zero))) :=
    if_neg (not_isProof_of_sort hΓ hFΓ)
  have HP : PiInertTypeCarrier (.arrow .ground .ground) (proofErase [Q] F) := by
    rw [EP]
    exact .function .base .base
  have hs : definitions.Sound env U := EnvironmentCore.sound
  have hcon : ∀ {p r}, Pat p r → ConcretePattern env p r := fun H => H
  have hc : TypedCoreConfluence (ErasedLevelCore definitions) :=
    EnvironmentCore.typed_level_core_confluence hcon
  obtain ⟨data, hreg, hr, hn, _⟩ := heq.recursorRegistration henv
  have RX := PiInertEvidence.core (stage := 0) hs hc hΓ hXΓ (.refl)
  have HX : PiInertEvidence definitions 0 (.compare true) (proofEraseCtx [Q])
      (proofErase [Q] X) (proofErase [Q] X) := RX.join hc RX
  have ht : env.HasType U (X :: [Q]) (.bvar 0) X.lift := .bvar .zero
  have RC := HX.castConsumer heq hs (EnvironmentCore.levelCompatible hcon) hcon hc
    hreg (hr.eqRec_target heq hn).2.1 (EnvironmentCore.no_eqRec heq)
    hu hΓ hXΓ hXΓ hq hFΓ ht
  refine ⟨[Q], _, _, _, _, n, hΓ, HN,
    .literal ⟨[Q], F, X, hΓ, rfl, hFΓ, rfl⟩ HP, ?_, ?_⟩
  · intro p q
    exact reflexive_cast_no_core_type_carrier henv U heq hu hΓ hXΓ hq hFΓ
  · simpa only [VExpr.inst, instVar, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, VExpr.liftN_zero] using RC

omit [Params] in
/-- It is false that original strong type-equality edges pull ordinary-core
exposure certificates backwards. Increasing the finite strong bound cannot
repair the obstruction. Richer guarded exposure must be retained separately. -/
theorem EnvironmentCore.not_strong_core_exposure_transport
    {env : VEnv} (henv : env.WF) (U : Nat) (heq : env.HasCanonicalEq) :
    letI := henv.params U
    ¬ (∀ {Γ A B v n p}, OnCtx Γ (env.IsType U) →
      StrongBounded env U n Γ A B (.sort v) →
      PiInertCoreTypeCarrier definitions (proofEraseCtx Γ) p (proofErase Γ B) →
      PiInertCoreTypeCarrier definitions (proofEraseCtx Γ) p (proofErase Γ A)) := by
  letI := henv.params U
  intro transport
  obtain ⟨Γ, C, A, B, v, n, hΓ, HE, HP, HN, _⟩ := strong_core_exposure_boundary henv U heq
  exact HN .ground .ground (transport hΓ HE HP)

end Lean4Lean.VEnv.Strengthening
