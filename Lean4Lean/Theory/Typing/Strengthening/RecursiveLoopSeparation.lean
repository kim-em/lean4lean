import Lean4Lean.Theory.Typing.Strengthening.RecursiveLoopObservation
import Lean4Lean.Theory.Typing.Strengthening.SingletonIndexAlignmentBoundary

/-! # Same-typed loops separated under full canonical-Eq conversion

Two self-application loops using distinct recursive domains have identical
lambda-annotation erasures and the same result type, but are not convertible.
This refutes reflection by raw lambda-annotation erasure, not strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- Full confluence cannot join loops using separated recursive domains. A normal
comparison would remove every recursive role from one reduct, whereas finite
observation shows that every full reduct retains such a role. -/
theorem recursive_loop_separation {env : VEnv} (henv : env.WF) (heq : env.HasCanonicalEq)
    (hc : env.constants c = some (declaration c).toVConstant)
    (hd : env.constants d = some (declaration d).toVConstant)
    (hδc : ∀ Δ, env.IsDefEq U Δ (domain c) (domainValue c) (.sort (.succ .zero)))
    (hδd : ∀ Δ, env.IsDefEq U Δ (domain d) (domainValue d) (.sort (.succ .zero)))
    (hsep : ∀ {Δ}, OnCtx Δ (env.IsType U) → ¬ env.IsDefEqU U Δ (domain c) (domain d)) :
    ¬ env.IsDefEqU U [] (omegaTerm c) (omegaTerm d) := by
  letI := henv.params U
  have hΓ : OnCtx [] (env.IsType U) := trivial
  intro H
  have H := H.of_l henv hΓ (omega_typed hc hδc)
  obtain ⟨left, right, Rl, Rr, n, HN⟩ := henv.church_rosser heq hΓ H
  have Hl := (omega_loopBody hc hδc).fullReduction hδc hΓ Rl
  have Hr := (omega_loopBody hd hδd).fullReduction hδd hΓ Rr
  have HN := NormalEqN.cross_noRecursive hδc hsep hc hδd HN Hl Hr hΓ
  exact omega_full_not_noRecursive hc hδc Rl HN

/-- An actual extension of any canonical-Eq environment exhibits the annotation
erasure failure at a common result type. Both recursive declarations are checked
by the existing mutual-definition rule; no additional axiom or reduction rule
is installed. -/
theorem canonical_loop_erasure_counterexample (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfc : base.constants c = none) (hfd : base.constants d = none)
    (hqc : c ≠ ``Quot.lift) (hqd : d ≠ ``Quot.lift) (hne : c ≠ d) :
    let env := extended (extended base c) d
    env.WF ∧ env.HasCanonicalEq ∧ ∀ U,
      env.HasType U [] (omegaTerm c) resultType ∧
      env.HasType U [] (omegaTerm d) resultType ∧
      eraseLamDomains (omegaTerm c) = eraseLamDomains (omegaTerm d) ∧
      ¬ env.IsDefEqU U [] (omegaTerm c) (omegaTerm d) := by
  obtain ⟨hw, hEq, hsep⟩ := canonical_distinct_recursive_types hbase heq hfc hfd hqc hqd hne
  refine ⟨hw, hEq, fun U => ?_⟩
  letI := hw.params U
  have hfd' : (extended base c).constants d = none := by
    simpa only [extended, VEnv.addDefEq, stub, if_neg hne] using hfd
  have hstep := declaration_wf hfd'
  have hc : (extended (extended base c) d).constants c = some (declaration c).toVConstant :=
    hstep.le.1 (by simp [extended, stub, VEnv.addDefEq])
  have hd : (extended (extended base c) d).constants d = some (declaration d).toVConstant := by
    simp [extended, stub, VEnv.addDefEq]
  have hδc : ∀ Δ, (extended (extended base c) d).IsDefEq U Δ
      (domain c) (domainValue c) (.sort (.succ .zero)) :=
    fun Δ => (equation (base := base) (c := c) U Δ).mono hstep.le
  have hδd := equation (base := extended base c) (c := d) U
  refine ⟨omega_typed hc hδc, omega_typed hd hδd, rfl, ?_⟩
  exact recursive_loop_separation hw hEq hc hd hδc hδd hsep

/-- Equality of the two function-valued loops, viewed as a proposition. -/
def loopEq (c d : Name) : VExpr :=
  eqApp (.succ .zero) resultType (omegaTerm c) (omegaTerm d)

/-- Canonical Eq lifts the same-typed loop obstruction to propositions themselves.
The diagonal proposition and the mixed proposition have identical erased syntax,
but rigid Eq-family injectivity would recover the impossible loop conversion. -/
theorem canonical_proposition_erasure_counterexample
    (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfc : base.constants c = none) (hfd : base.constants d = none)
    (hqc : c ≠ ``Quot.lift) (hqd : d ≠ ``Quot.lift) (hne : c ≠ d) :
    let env := extended (extended base c) d
    env.WF ∧ env.HasCanonicalEq ∧ ∀ U,
      env.HasType U [] (loopEq c c) prop ∧
      env.HasType U [] (loopEq c d) prop ∧
      eraseLamDomains (loopEq c c) = eraseLamDomains (loopEq c d) ∧
      ¬ env.IsDefEqU U [] (loopEq c c) (loopEq c d) := by
  obtain ⟨hw, hEq, H⟩ := canonical_loop_erasure_counterexample hbase heq hfc hfd hqc hqd hne
  refine ⟨hw, hEq, fun U => ?_⟩
  obtain ⟨hc, hd, _, hne⟩ := H U
  have hP : (extended (extended base c) d).HasType U [] (loopEq c c) prop :=
    HasType.eqApp hEq (by trivial) (result_typed _ _ _) hc hc
  have hQ : (extended (extended base c) d).HasType U [] (loopEq c d) prop :=
    HasType.eqApp hEq (by trivial) (result_typed _ _ _) hc hd
  refine ⟨hP, hQ, rfl, fun HE => ?_⟩
  have HE' : (extended (extended base c) d).IsDefEqU U []
      (mkApps (.const ``Eq [.succ .zero]) [resultType, omegaTerm c, omegaTerm c])
      (mkApps (.const ``Eq [.succ .zero]) [resultType, omegaTerm c, omegaTerm d]) := HE
  obtain ⟨_, hargs⟩ := HE'.rigidApp_inv hw (by trivial) (hEq.rigid hw) hP
  cases hargs with | cons _ hargs =>
  cases hargs with | cons _ hargs =>
  cases hargs with | cons hcd _ => exact hne hcd

end Lean4Lean.VEnv.Strengthening.GuardedEta
