import Lean4Lean.Theory.Typing.Strengthening.ProofErasureHereditaryArgumentHistory

/-! # Eta consumers reduce exactly to the exposed lambda's annotation pair

An ordinary core path exposing a lambda reduces the eta-consumer problem to
reannotation of that lambda inside the same typed consumer. Both directions
retain the stage, checking mode, and all future typed substitutions. No domain
comparison is assumed in the equivalence; a separate theorem uses one when it
is available. This does not supply that certificate for arbitrary conversions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private level_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
open private isProof_congr from Lean4Lean.Theory.Typing.Strengthening.ProofErasurePrimitives
open private beta_eq from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : Definitions}

/-- An ordinary core path propagates through any actual typed consumer. This
is a raw computation path, not merely a retained comparison certificate. -/
theorem proofErase_level_core_consumer
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x X)
    (hy : env.HasType univs Γ y X) (ht : env.HasType univs (X :: Γ) t T)
    (R : Compute (ErasedLevelCore D) (proofErase Γ x) (proofErase Γ y)) :
    Compute (ErasedLevelCore D) (proofErase Γ (t.inst x)) (proofErase Γ (t.inst y)) := by
  have hΓX : OnCtx (X :: Γ) (env.IsType univs) := ⟨hΓ, hx.isType henv hΓ⟩
  rw [proofErase_instN hΓX hx Ctx.InstN.zero ht, proofErase_instN hΓX hy Ctx.InstN.zero ht]
  exact R.inst_argument (fun H => level_lift H) _

/-- Eta expansion preserves an ordinary core path between functions at one
assigned Pi type. Whole-proof functions are included by erasure. -/
theorem proofErase_level_core_eta
    (hΓ : OnCtx Γ (env.IsType univs)) (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ g (.forallE A B))
    (R : Compute (ErasedLevelCore D) (proofErase Γ f) (proofErase Γ g)) :
    Compute (ErasedLevelCore D)
      (proofErase Γ (.lam A (.app f.lift (.bvar 0))))
      (proofErase Γ (.lam A (.app g.lift (.bvar 0)))) := by
  have HP : IsProof Γ f ↔ IsProof Γ g := by
    constructor
    · rintro ⟨P, hp, hP⟩
      exact ⟨P, hg.defeqU_r henv hΓ (hf.uniqU henv hΓ hp), hP⟩
    · rintro ⟨P, hp, hP⟩
      exact ⟨P, hf.defeqU_r henv hΓ (hg.uniqU henv hΓ hp), hP⟩
  by_cases hp : IsProof Γ f
  · rw [proofErase_eq_proof.2 ((isProof_congr hΓ (IsDefEq.eta hf)).2 hp),
      proofErase_eq_proof.2 ((isProof_congr hΓ (IsDefEq.eta hg)).2 (HP.1 hp))]
    exact .refl
  · obtain ⟨_, hPi⟩ := hf.isType henv hΓ
    obtain ⟨⟨u, hA⟩, _, _⟩ := hPi.forallE_inv henv
    rw [proofErase_nativeEtaExpansion hΓ hA hf hp,
      proofErase_nativeEtaExpansion hΓ hA hg (fun H => hp (HP.2 H))]
    exact .lam .refl (.app (R.liftN (fun H => level_lift H)) .refl)

/-- The beta half of the eta/lambda critical pair changes only the written
annotation. It is valid even when the assigned and written domains differ. -/
theorem typed_eta_lambda_beta
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (.lam C b) (.forallE A B)) :
    env.HasType univs Γ (.lam A b) (.forallE A B) ∧
      Compute (ErasedLevelCore D)
        (proofErase Γ (.lam A (.app (VExpr.lam C b).lift (.bvar 0))))
        (proofErase Γ (.lam A b)) := by
  have R : VExpr.BetaRed (.lam A (.app (VExpr.lam C b).lift (.bvar 0))) (.lam A b) := by
    apply VExpr.BetaRed.lam .refl
    simpa only [VExpr.lift, VExpr.liftN, VExpr.inst_liftN_bvar] using
      (VExpr.BetaRed.beta (A := C.lift) (b := b.liftN 1 1) (a := .bvar 0))
  have ht := (IsDefEq.eta hf).hasType.1
  exact ⟨(beta_eq hΓ ht R).hasType.2, .beta (proofErase_beta_forward hΓ ht R)⟩

/-- Once ordinary computation exposes a typed lambda, comparing an arbitrary
consumer of the eta pair is equivalent to comparing that consumer of the two
lambda annotations. The equivalence preserves both modes and the exact stage;
it does not promote common comparison to shared computation outputs. -/
theorem CoreFamilyCast.Hereditary.eta_consumer_iff_annotation
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (hg : env.HasType univs Γ (.lam C b) (.forallE A B))
    (ht : env.HasType univs (.forallE A B :: Γ) t T)
    (R : Compute (ErasedLevelCore D) (proofErase Γ f) (proofErase Γ (.lam C b))) :
    CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) (proofErase Γ (t.inst f)) ↔
    CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A b))) (proofErase Γ (t.inst (.lam C b))) := by
  obtain ⟨ha, RB⟩ := typed_eta_lambda_beta (D := D) hΓ hg
  have RL := proofErase_level_core_consumer hΓ (IsDefEq.eta hf).hasType.1 ha ht
    ((proofErase_level_core_eta hΓ hf hg R).trans RB)
  have RR := proofErase_level_core_consumer hΓ hf hg ht R
  exact ⟨fun H => H.reducts RL RR,
    fun H => .prefixes (.core hΓ (ht.instN henv Ctx.InstN.zero (IsDefEq.eta hf).hasType.1) RL)
      (.core hΓ (ht.instN henv Ctx.InstN.zero hf) RR) H⟩

/-- A retained domain comparison solves the exposed-lambda eta consumer case.
The consumer keeps its originally assigned Pi type; inversion and context
conversion reconstruct the natural type needed by annotation transport. -/
theorem CoreFamilyCast.Hereditary.eta_consumer_of_exposed_lambda
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
    (R : Compute (ErasedLevelCore D) (proofErase Γ f) (proofErase Γ (.lam C b)))
    (H : CoreFamilyCast.Hereditary D n (.compare domainMode) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C)) :
    CoreFamilyCast.Hereditary D n (.compare mode) (proofEraseCtx Γ)
      (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) (proofErase Γ (t.inst f)) := by
  apply (eta_consumer_iff_annotation hΓ hf hg ht R).2
  have ha := (typed_eta_lambda_beta (D := D) hΓ hg).1
  obtain ⟨E, HPi, hb⟩ := ha.lam_inv_forallE henv hΓ
  obtain ⟨v, hPi⟩ := hf.isType henv hΓ
  have ht' := ht.defeqDFC henv (IsDefEqCtx.succ .zero (HPi.symm.of_l henv hΓ hPi))
  exact H.annotation heq hs hl hcon hc hreg hoff hD hΓ hA hC hb ht'

omit [Params] in
/-- Actual canonical-Eq environments discharge the primitive-core interfaces.
A finite ordinary path may expose the lambda; its written domain need not
match the caller's domain, but their retained comparison is still explicit. -/
theorem EnvironmentCore.hereditary_eta_consumer_of_exposed_lambda
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {n mode domainMode Γ u A B C b f t T}, env.HasCanonicalEq →
      OnCtx Γ (env.IsType U) → env.HasType U Γ A (.sort u) → env.HasType U Γ C (.sort u) →
      env.HasType U Γ f (.forallE A B) → env.HasType U Γ (.lam C b) (.forallE A B) →
      env.HasType U (.forallE A B :: Γ) t T →
      Compute (ErasedLevelCore definitions) (proofErase Γ f) (proofErase Γ (.lam C b)) →
      CoreFamilyCast.Hereditary definitions n (.compare domainMode) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ C) →
      CoreFamilyCast.Hereditary definitions n (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) (proofErase Γ (t.inst f)) := by
  letI := henv.params U
  intro n mode domainMode Γ u A B C b f t T heq hΓ hA hC hf hg ht R H
  obtain ⟨data, hlookup, hr, hn, _⟩ := heq.recursorRegistration henv
  exact H.eta_consumer_of_exposed_lambda heq sound (levelCompatible (fun H => H))
    (fun H => H) (typed_level_core_confluence (fun H => H)) hlookup
    (hr.eqRec_target heq hn).2.1 (no_eqRec heq) hΓ hA hC hf hg ht R

omit [Params] in
/-- If the exposed lambda uses the assigned domain literally, arbitrary typed
eta consumers are covered at stage zero without a domain-comparison premise.
The body and consumer need not normalize, and the source may take any finite
ordinary-core path to expose the lambda. -/
theorem EnvironmentCore.hereditary_eta_consumer_of_native_lambda
    {env : VEnv} (henv : env.WF) (U : Nat) :
    letI := henv.params U
    ∀ {mode Γ A B b f t T}, env.HasCanonicalEq → OnCtx Γ (env.IsType U) →
      env.HasType U Γ f (.forallE A B) → env.HasType U Γ (.lam A b) (.forallE A B) →
      env.HasType U (.forallE A B :: Γ) t T →
      Compute (ErasedLevelCore definitions) (proofErase Γ f) (proofErase Γ (.lam A b)) →
      CoreFamilyCast.Hereditary definitions 0 (.compare mode) (proofEraseCtx Γ)
        (proofErase Γ (t.inst (.lam A (.app f.lift (.bvar 0))))) (proofErase Γ (t.inst f)) := by
  letI := henv.params U
  intro mode Γ A B b f t T heq hΓ hf hg ht R
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨⟨u, hA⟩, _, _⟩ := hPi.forallE_inv henv
  have HA : CoreFamilyCast.Hereditary definitions 0 (.compare true) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ A) := .join (.core hΓ hA .refl) (.core hΓ hA .refl)
  exact hereditary_eta_consumer_of_exposed_lambda henv U heq hΓ hA hA hf hg ht R HA

end Lean4Lean.VEnv.Strengthening
