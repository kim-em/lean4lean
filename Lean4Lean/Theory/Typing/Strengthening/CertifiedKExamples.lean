import Lean4Lean.Theory.Typing.Strengthening.CertifiedKComputation
import Lean4Lean.Theory.Typing.Strengthening.EqRecEtaBoundary

/-! # Typed checks of recursive K matching

The earlier typed eta-removal obstruction computes using a depth-zero endpoint
certificate. It can itself be an endpoint of another well-typed K application,
which computes using depth one. The tests use every canonical-Eq environment,
without extra registry, constant, or endpoint-alignment hypotheses.
-/
namespace Lean4Lean.VEnv.Strengthening.CertifiedKExamples
open _root_.Lean4Lean _root_.Lean4Lean.VExpr EqRecEtaBoundary
open PureObservation (Definitions)
variable {env : VEnv}

/-- The earlier typed eta obstruction is supported by a normal endpoint guard. -/
theorem eta_compute (henv : env.WF) (heq : env.HasCanonicalEq) :
    @CertifiedKCompute (henv.params U) D 0 context source carrier := by
  letI := henv.params U
  exact .eqRec (KCertificate.eta (context_wf heq) (function_typed henv))

/-- Reuse the first computation as the endpoint of an enclosing K application. -/
def nestedSource : VExpr := eqRecApp (.succ (.succ .zero)) (.succ (.succ .zero))
  (.sort (.succ .zero)) source
  (constantEqMotive (.succ (.succ .zero)) (.sort (.succ .zero)) source (.sort (.succ .zero)))
  carrier carrier (eqReflApp (.succ (.succ .zero)) (.sort (.succ .zero)) source)

/-- Both the nested computation and its comparison guard have finite checked
depth. The new guard computes the first endpoint rather than merely eta-matching it. -/
theorem nested_compute (henv : env.WF) (heq : env.HasCanonicalEq) :
    @CertifiedKCompute (henv.params U) D 1 context nestedSource carrier := by
  letI := henv.params U
  exact .eqRec (KCertificate.of_compute (eta_compute henv heq) (carrier_typed env U context))

/-- The nested source is genuinely type-valued in the same well-formed context;
its equality proof is constructed from the checked inner equation. -/
theorem nested_typed (henv : env.WF) (heq : env.HasCanonicalEq) :
    env.HasType U context nestedSource (.sort (.succ .zero)) := by
  have hΓ := context_wf (U := U) heq
  have hS := source_typed (U := U) henv heq
  have hC := carrier_typed env U context
  have hα : env.HasType U context (.sort (.succ .zero)) (.sort (.succ (.succ .zero))) :=
    .sort (by trivial)
  have hp := (IsDefEq.eqApp_r heq (by trivial) hα hS (source_eq_minor henv heq)).defeq
    (HasType.eqReflApp heq (by trivial) hα hS)
  exact constant_eqRec_typed henv heq (by trivial) (by trivial) hΓ hα hS
    hα hC hC hp

/-- The nested case remains supported after arbitrary finite binder insertion.
Together with certified descent, this exercises computational endpoint alignment
at arbitrary scope, not only the unextended example. -/
theorem nested_compute_weakN (henv : env.WF) (heq : env.HasCanonicalEq)
    (W : Ctx.LiftN n k context Γ') :
    @CertifiedKCompute (henv.params U) D 1 Γ'
      (nestedSource.liftN n k) (carrier.liftN n k) := by
  letI := henv.params U
  exact (nested_compute henv heq).weakN (fun W H => KCertificate.weakN W H) W

/-- A typed example with nested K matching and no assumed alignment witness. -/
theorem typed_nested_example (henv : env.WF) (heq : env.HasCanonicalEq) (U : Nat) :
    OnCtx context (env.IsType U) ∧
    env.HasType U context nestedSource (.sort (.succ .zero)) ∧
    @CertifiedKCompute (henv.params U) D 1 context nestedSource carrier :=
  ⟨context_wf heq, nested_typed henv heq, nested_compute henv heq⟩

end Lean4Lean.VEnv.Strengthening.CertifiedKExamples
