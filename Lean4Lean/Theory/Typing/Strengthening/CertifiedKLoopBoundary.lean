import Lean4Lean.Theory.Typing.Strengthening.PureBodyComputation
import Lean4Lean.Theory.Typing.Strengthening.GuardedEtaLoop

/-! # Recursive K guards do not supply body eta repair

The ordinary recursive loop keeps exactly the same computational body under
all guarded K computations, even with arbitrary matching and closed equations.
Its actual finite eta repair therefore lies outside that computation relation.
This does not exclude a different final comparison or refute strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedEta
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- The recursive type occurs only as an annotation in the ordinary loop. -/
theorem omega_pure_body : PureBody (omegaTerm c) :=
  .app (.lam (.app .bvar .bvar)) (.lam (.app .bvar .bvar))

/-- Every computation leaves the loop's body exactly fixed after annotation
erasure. Matching strength and the declaration collection are unrestricted. -/
theorem omega_body_fixed [Params] (R : GuardedKCompute D Cmp Γ (omegaTerm c) out) :
    eraseLamDomains out = eraseLamDomains (omegaTerm c) := by
  have h := (R.body_simulation omega_pure_body).2
  change BetaRed (RecursiveDomain.omegaTerm (.sort .zero)) (eraseLamDomains out) at h
  exact RecursiveDomain.omega_beta_eq (by simp [Developments.HasBeta]) h

/-- No enhancement of the K matching predicate can simulate this particular
body-eta repair. The computational syntax must change, or the final comparison
must handle the mismatch without demanding this exact target. -/
theorem no_guarded_eta_repair [Params] :
    ¬ GuardedKCompute D Cmp Γ (omegaTerm c) (etaOmega c) := by
  intro H
  have h := omega_body_fixed H
  have hn : eraseLamDomains (etaOmega c) ≠ eraseLamDomains (omegaTerm c) := by
    intro h
    cases h
  exact hn h

/-- The missed repair occurs between well-typed terms in a canonical-Eq
preserving recursive extension. It is an actual finite full reduction, not an
untyped eta proposal. This is a computation-model boundary, not a failed join. -/
theorem canonical_guarded_repair_failure (hbase : base.WF) (heq : base.HasCanonicalEq)
    (hfresh : base.constants c = none) :
    (extended base c).HasCanonicalEq ∧
    letI := (extended_wf hbase hfresh).params 0
    (extended base c).HasType 0 [] (omegaTerm c) resultType ∧
    (extended base c).HasType 0 [] (etaOmega c) resultType ∧
    FullReduction [] (omegaTerm c) (etaOmega c) ∧
    ∀ D Cmp, ¬ GuardedKCompute D Cmp [] (omegaTerm c) (etaOmega c) := by
  refine ⟨extended_canonicalEq heq hfresh, ?_⟩
  letI := (extended_wf hbase hfresh).params 0
  have hc : Params.env.constants c = some (declaration c).toVConstant := by
    change (extended base c).constants c = _
    simp [extended, stub, VEnv.addDefEq]
  have hδ : ∀ Γ, Params.env.IsDefEq univs Γ (domain c) (domainValue c) (.sort (.succ .zero)) :=
    fun Γ => equation 0 Γ
  have hΓ : OnCtx [] (Params.env.IsType univs) := trivial
  have ht := omega_typed (Γ := []) hc hδ
  have R := (full_repair hc hδ hΓ).1
  exact ⟨ht, R.hasType hΓ ht, R, fun _ _ => no_guarded_eta_repair⟩

end Lean4Lean.VEnv.Strengthening.GuardedEta
