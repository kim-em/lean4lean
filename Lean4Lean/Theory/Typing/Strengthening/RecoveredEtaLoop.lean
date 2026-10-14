import Lean4Lean.Theory.Typing.Strengthening.RecoveredEtaComputation
import Lean4Lean.Theory.Typing.Strengthening.CertifiedKLoopBoundary
import Lean4Lean.Theory.Typing.Strengthening.DeclarationHeadExamples
import Lean4Lean.Theory.Typing.Strengthening.EtaScope

/-! # Recoverable eta repairs the recursive-loop boundary

The loop's variable is looked up at the recursive type D, whose stored equation
exposes a Pi. Recovering the self-application's type then justifies body eta.
This exact repair was impossible for every choice of guarded K matching alone.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]

/-- One stored delta step exposes the recursive variable's function type. -/
theorem recovered_domain_compute (hd : D.unfolds c [] (domainValue c)) :
    CertifiedKCompute D depth Γ (domain c) (domainValue c) :=
  .base (.base (.base (.base (.delta hd))))

/-- Recovery infers the self-application's Pi type using the variable lookup and
one delta step. The argument typing is not stored as a new conversion premise. -/
theorem selfBody_type_recovery (hd : D.unfolds c [] (domainValue c)) :
    TypeRecovery D depth (domain c :: Γ) selfBody resultType := by
  have hv : TypeRecovery D depth (domain c :: Γ) (.bvar 0) (domain c) := .bvar .zero
  have hf := TypeRecovery.convert hv (recovered_domain_compute hd)
  have hb := TypeRecovery.app (a := .bvar 0) hf
  simpa only [selfBody, domainValue, resultType, prop, inst] using hb

/-- The missed body-eta step now has a finite recovery certificate. -/
theorem recovered_diagonal_eta (hd : D.unfolds c [] (domainValue c)) :
    RecoveredEtaCompute D depth Γ (diagonal c) (etaDiagonal c) :=
  .lam .refl (.eta (selfBody_type_recovery hd))

/-- Two compatible expansions repair the loop, with no recursive normalization. -/
theorem recovered_omega_eta (hd : D.unfolds c [] (domainValue c)) :
    RecoveredEtaCompute D depth Γ (omegaTerm c) (etaOmega c) :=
  .app (recovered_diagonal_eta hd) (recovered_diagonal_eta hd)

/-- This certificate remains valid above every finite binder insertion. -/
theorem recovered_omega_eta_weakN (hd : D.unfolds c [] (domainValue c))
    (W : Ctx.LiftN n k Γ Γ') :
    RecoveredEtaCompute D depth Γ' ((omegaTerm c).liftN n k) ((etaOmega c).liftN n k) :=
  (recovered_omega_eta hd).weakN W

omit [Params] in
/-- In an actual canonical-Eq environment the new relation supplies the exact
repair excluded for all old matching predicates, and typed replay verifies it. -/
theorem canonical_recovered_eta_repair (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    let henv := extended_wf hbase hfresh
    letI := henv.params 0
    let D := Definitions.ofEnv (extended base c) 0 henv
    (extended base c).HasCanonicalEq ∧
    (extended base c).HasType 0 [] (omegaTerm c) resultType ∧
    RecoveredEtaCompute D 0 [] (omegaTerm c) (etaOmega c) ∧
    (extended base c).IsDefEq 0 [] (omegaTerm c) (etaOmega c) resultType ∧
    (∀ Cmp, ¬ GuardedKCompute D Cmp [] (omegaTerm c) (etaOmega c)) := by
  let henv := extended_wf hbase hfresh
  letI := henv.params 0
  let D := Definitions.ofEnv (extended base c) 0 henv
  have hEq := extended_canonicalEq heq hfresh
  have hc : Params.env.constants c = some (declaration c).toVConstant := by
    change (extended base c).constants c = _
    simp [extended, stub, VEnv.addDefEq]
  have hδ : ∀ Γ, Params.env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)) :=
    fun Γ => equation 0 Γ
  have ht := omega_typed (Γ := []) hc hδ
  have R : RecoveredEtaCompute D 0 [] (omegaTerm c) (etaOmega c) :=
    recovered_omega_eta (PureObservation.guarded_definition henv 0)
  refine ⟨hEq, ht, R, ?_, fun _ => no_guarded_eta_repair⟩
  exact R.simAt hEq (Definitions.ofEnv_sound henv) trivial _ ht

end Lean4Lean.VEnv.Strengthening.GuardedEta

namespace Lean4Lean.VEnv.Strengthening.EtaScope
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params Developments
variable [Params]

/-- Exact coverage of arbitrary ambient eta annotations is deliberately absent:
the existing captured-domain step cannot be a recoverable eta path. Full coverage
would require choosing another scoped repair, not copying every ambient target. -/
theorem captured_eta_not_recovered (heq : env.HasCanonicalEq)
    (hs : PureObservation.Definitions.Sound D env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hQ : env.HasType univs Γ Q (.sort u)) :
    ¬ RecoveredEtaCompute D depth (Q :: Γ) (ident 0).lift (expanded Q) := by
  intro R
  rw [lift_eq_lift'] at R
  obtain ⟨out, hout, _⟩ := R.descend heq hs (Ctx.Lift'.skip .refl) hΓ
    ⟨hΓ, _, hQ⟩ (ident_typed env univs Γ 0)
  have hscope : (expanded Q).Skips 1 0 := by
    rw [hout, ← lift_eq_lift']
    exact .liftN
  exact captured_not_lift hscope

end Lean4Lean.VEnv.Strengthening.EtaScope
