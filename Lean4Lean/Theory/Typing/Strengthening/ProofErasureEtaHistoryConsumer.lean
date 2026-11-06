import Lean4Lean.Theory.Typing.Strengthening.ProofErasureEtaConsumerReduction

/-! # Eta consumers along certified argument histories

Fixed-result typed templates compose with arbitrary typed consumers. This
transports eta consumers along core/cast argument histories without requiring
ordinary-core exposure of the source function. Domain certificates remain
explicit at the exposed target lambda; no semantic coverage is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
variable [Params] {D : Definitions}

/-- Read a history through an actual consumer at two typed endpoints. The
raw intermediate outputs used inside the history remain unconstrained. -/
theorem ArgumentHistory.consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x X)
    (hy : env.HasType univs Γ y X) (ht : env.HasType univs (X :: Γ) t T)
    (R : ArgumentHistory D n Γ X (proofErase Γ x) (proofErase Γ y)) :
    CoreFamilyCast.Hereditary D n .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst x)) (proofErase Γ (t.inst y)) := by
  have H := (R.interpret heq hs hl hcon hc hreg hoff hD).2 ht
  have hΓX : OnCtx (X :: Γ) (env.IsType univs) := ⟨hΓ, hx.isType henv hΓ⟩
  rw [← proofErase_instN hΓX hx Ctx.InstN.zero ht,
    ← proofErase_instN hΓX hy Ctx.InstN.zero ht] at H
  exact H

/-- A fixed-result template and an arbitrary outer consumer can be composed
before interpreting the history. The fixed result type is essential to the
construction: a dependent result does not type the generic composite here. -/
theorem ArgumentHistory.consumer_compose
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x X)
    (hy : env.HasType univs Γ y X) (ht : env.HasType univs (X :: Γ) t Y.lift)
    (hu : env.HasType univs (Y :: Γ) u T)
    (R : ArgumentHistory D n Γ X (proofErase Γ x) (proofErase Γ y)) :
    CoreFamilyCast.Hereditary D n .compute (proofEraseCtx Γ)
      (proofErase Γ (u.inst (t.inst x))) (proofErase Γ (u.inst (t.inst y))) := by
  have hu' := hu.weakN henv (Ctx.LiftN.one.succ : Ctx.LiftN 1 1 (Y :: Γ) (Y.lift :: X :: Γ))
  have hcomp := hu'.instN henv Ctx.InstN.zero ht
  have H := R.consumer heq hs hl hcon hc hreg hoff hD hΓ hx hy hcomp
  have E (z : VExpr) : ((u.liftN 1 1).inst t).inst z = u.inst (t.inst z) := by
    simpa only [VExpr.inst_liftN] using VExpr.inst_inst_hi (u.liftN 1 1) t z 0 0
  simpa only [E] using H

/-- Eta expansion is a fixed-result typed template. Composing it with the
original consumer carries an arbitrary certified core/cast history through
both layers at the same stage. -/
theorem ArgumentHistory.eta_consumer
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ g (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (R : ArgumentHistory D n Γ (.forallE A B) (proofErase Γ f) (proofErase Γ g)) :
    CoreFamilyCast.Hereditary D n .compute (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0)))))
      (proofErase Γ (t.inst (.lam A (.app g.lift (.bvar 0))))) := by
  have hi : env.HasType univs (.forallE A B :: Γ) (.bvar 0) (VExpr.forallE A B).lift := .bvar .zero
  have he := (IsDefEq.eta hi).hasType.1
  have H := R.consumer_compose heq hs hl hcon hc hreg hoff hD hΓ hf hg he ht
  have E (z : VExpr) :
      (VExpr.lam A.lift (.app (VExpr.bvar 0).lift (.bvar 0))).inst z =
        .lam A (.app z.lift (.bvar 0)) := by
    simp [VExpr.inst, VExpr.inst_lift, VExpr.instVar, VExpr.lift, VExpr.liftN, liftVar]
  simpa only [E] using H

/-- A comparison of the target eta pair transports backward along the retained
function history. Only computation prefixes are composed; no transitivity or
substitution principle for arbitrary comparison certificates is assumed. -/
theorem CoreFamilyCast.Hereditary.eta_consumer_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ g (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (R : ArgumentHistory D n Γ (.forallE A B) (proofErase Γ f) (proofErase Γ g))
    (H : CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A (.app g.lift (.bvar 0))))) (proofErase Γ (t.inst g))) :
    CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) (proofErase Γ (t.inst f)) :=
  .prefixes (R.eta_consumer heq hs hl hcon hc hreg hoff hD hΓ hf hg ht)
    (R.consumer heq hs hl hcon hc hreg hoff hD hΓ hf hg ht) H

/-- Certified core/cast exposure suffices for the lambda case. Its domain
certificate is supplied at the target and remains usable all the way back
through the source history, without an ordinary-core path to that target. -/
theorem CoreFamilyCast.Hereditary.eta_consumer_of_history_lambda
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs) (hl : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hreg : recursorData ``Eq.rec = some data) (hoff : data.majorOffset = 5)
    (hD : ∀ levels rhs, ¬ D.unfolds ``Eq.rec levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hC : env.HasType univs Γ C (.sort u))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ (.lam C b) (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (R : ArgumentHistory D n Γ (.forallE A B) (proofErase Γ f) (proofErase Γ (.lam C b)))
    (H : CoreFamilyCast.Hereditary D n (.compare domainMode) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C)) :
    CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) (proofErase Γ (t.inst f)) := by
  have HG := H.eta_consumer_of_exposed_lambda (mode := mode) heq hs hl hcon hc hreg hoff hD
    hΓ hA hC hg hg ht .refl
  exact HG.eta_consumer_prefix heq hs hl hcon hc hreg hoff hD hΓ hf hg ht R

omit [Params] in
/-- Actual environments interpret core/cast histories to exposed lambdas with
retained domain comparison. No ordinary-core exposure premise remains. -/
theorem EnvironmentCore.hereditary_eta_consumer_of_history_lambda
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n mode domainMode Γ u A B C b f t T}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort u) →
      env.HasType U Γ f (.forallE A B) → env.HasType U Γ (.lam C b) (.forallE A B) →
      env.HasType U (.forallE A B :: Γ) t T →
      ArgumentHistory definitions n Γ (.forallE A B) (proofErase Γ f) (proofErase Γ (.lam C b)) →
      CoreFamilyCast.Hereditary definitions n (.compare domainMode) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ C) →
      CoreFamilyCast.Hereditary definitions n (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) (proofErase Γ (t.inst f)) := by
  letI := henv.params U
  intro n mode domainMode Γ u A B C b f t T heq hΓ hA hC hf hg ht R H
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.eta_consumer_of_history_lambda heq sound (levelCompatible (fun H => H))
    (fun H => H) (typed_level_core_confluence (fun H => H)) hlookup
    (hr.eqRec_target heq hn).2.1 (no_eqRec heq) hΓ hA hC hf hg ht R

omit [Params] in
/-- Eta of a reflexively cast lambda is comparable inside every typed consumer
at stage one. The cast history is constructed from a reflexive carrier check;
no domain comparison or exposure oracle is supplied by the caller. -/
theorem EnvironmentCore.hereditary_cast_function_eta_consumer
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {mode Γ u A B b q t T}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ (.forallE A B) (.sort u) →
      env.HasType U Γ (.lam A b) (.forallE A B) →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) (.forallE A B) (.forallE A B)) →
      env.HasType U (.forallE A B :: Γ) t T →
      let F := typeCast u (.forallE A B) (.forallE A B) q (.lam A b)
      CoreFamilyCast.Hereditary definitions 1 (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam A (.app F.lift (.bvar 0))))) (proofErase Γ (t.inst F)) := by
  letI := henv.params U
  intro mode Γ u A B b q t T heq hu hΓ hPi hf hq ht F
  have hF := (IsDefEq.typeCast_refl henv heq hu hΓ hPi hq hf).hasType.1
  obtain ⟨⟨v, hA⟩, _, _⟩ := hPi.forallE_inv henv
  have HPi : CoreFamilyCast.Hereditary definitions 0 (.compare true) (proofEraseCtx Γ)
      (proofErase Γ (.forallE A B)) (proofErase Γ (.forallE A B)) :=
    .join (.core hΓ hPi .refl) (.core hΓ hPi .refl)
  have HA : CoreFamilyCast.Hereditary definitions 1 (.compare true) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ A) := .join (.core hΓ hA .refl) (.core hΓ hA .refl)
  exact hereditary_eta_consumer_of_history_lambda henv U heq hΓ hA hA hF hf ht
    (.cast hu hΓ hPi hPi hq hf HPi) HA

omit [Params] in
/-- A non-proof reflexive cast cannot expose any raw lambda in the full
ordinary core. Its erased proof major keeps the Eq recursor blocked. Together
with the preceding consumer theorem this witnesses strictly wider exposure. -/
theorem EnvironmentCore.reflexive_cast_no_core_lambda
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {Γ u X q x A b}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ X (.sort u) → env.HasType U Γ x X →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) X X) → ¬ IsProof Γ x →
      ¬ Compute (ErasedLevelCore definitions) (proofErase Γ (typeCast u X X q x)) (.lam A b) := by
  letI := henv.params U
  intro Γ u X q x A b heq hu hΓ hX hx hq hn R
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
/-- The same function has hereditary eta comparison in every typed consumer
while no ordinary-core path exposes a lambda. Thus certified history exposure
strictly extends the preceding ordinary-core-exposure route on this instance. -/
theorem EnvironmentCore.cast_eta_beyond_core_exposure
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {mode Γ u A B b q t T}, env.HasCanonicalEq → u.WF U → OnCtx Γ (env.IsType U) →
      env.HasType U Γ (.forallE A B) (.sort u) →
      env.HasType U Γ (.lam A b) (.forallE A B) →
      env.HasType U Γ q (eqApp (.succ u) (.sort u) (.forallE A B) (.forallE A B)) →
      env.HasType U (.forallE A B :: Γ) t T → ¬ IsProof Γ (.lam A b) →
      let F := typeCast u (.forallE A B) (.forallE A B) q (.lam A b)
      CoreFamilyCast.Hereditary definitions 1 (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam A (.app F.lift (.bvar 0))))) (proofErase Γ (t.inst F)) ∧
      ∀ C c, ¬ Compute (ErasedLevelCore definitions) (proofErase Γ F) (.lam C c) := by
  letI := henv.params U
  intro mode Γ u A B b q t T heq hu hΓ hPi hf hq ht hn F
  exact ⟨hereditary_cast_function_eta_consumer henv U heq hu hΓ hPi hf hq ht,
    fun _ _ => reflexive_cast_no_core_lambda henv U heq hu hΓ hPi hf hq hn⟩

end Lean4Lean.VEnv.Strengthening
