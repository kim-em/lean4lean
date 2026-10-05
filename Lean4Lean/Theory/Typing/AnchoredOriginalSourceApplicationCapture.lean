import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGraph
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericApplicationStep

/-! Application-specific consequences of the common source capture graph.
The graph and its realization are defined independently of the application
interpreter; these producers retain their existing exact-frame statements. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private capture_comp frame_castSubstitution_environment from
  Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGraph
set_option backward.isDefEq.respectTransparency false

/-- The application producer's computed captured frame realizes the same
recursive SOURCE map. It keeps the original replacement queries and charges
the actual argument closure; this works after any earlier source captures. -/
theorem GenericApplicationCapture.sourceRealization
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (base : OriginalCaptureRealization graph env registry target locals commonSubst commonSubst available)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (argument : EndpointState sourceEnv U source a A)
    (argumentProvenance : EndpointProvenance context argument)
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (capture : GenericApplicationCapture base.frame domain body argument support) :
    ∃ realized : OriginalCaptureRealization (.capture graph domain graph argument argumentProvenance)
        env registry target (Locals.push locals) commonSubst commonSubst (available.push capture.needs),
      (∀ ordered : sourceEnv.Ordered,
        realized.frame.dependencyEnvironment ordered =
          .bundle (.close (argument.dependencyOrigin ordered) (base.frame.dependencyEnvironment ordered))
            (.close (domain.dependencyOrigin ordered) (base.frame.dependencyEnvironment ordered)) ::
          base.frame.dependencyEnvironment ordered) ∧
      Nonempty (RichCert sourceEnv env U registry target body (Locals.push locals)
        ((raw.cons (a.subst raw)).comp commonSubst) true support capture.capture.footprint) ∧
      capture.capture.footprint.Available (available.push capture.needs) := by
  have realizationEq : (raw.comp commonSubst).cons (a.subst (raw.comp commonSubst)) =
      (raw.cons (a.subst raw)).comp commonSubst := (capture_comp raw raw a commonSubst).symm
  let realized : OriginalCaptureRealization (.capture graph domain graph argument argumentProvenance)
      env registry target (Locals.push locals) commonSubst commonSubst (available.push capture.needs) := {
    frame := realizationEq ▸ capture.frame
    substitutions := realizationEq ▸ capture.substitutions }
  refine ⟨realized, ?_, ⟨realizationEq ▸ capture.capture.certificate⟩, capture.capture.sourceAvailable⟩
  intro ordered
  exact (frame_castSubstitution_environment realizationEq capture.frame ordered).trans (capture.environment_eq ordered)

/-- The nested own-codomain comparison uses the SAME produced frame and
query as application F. Its strict reserve is computed from the actual
original application, including the captured argument and domain. -/
theorem GenericApplicationCapture.sourceComparison
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (ordered : sourceEnv.Ordered)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (function : EndpointState sourceEnv U source f (.forallE A B))
    (argument : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (base : OriginalCaptureRealization graph env registry target locals commonSubst commonSubst available)
    (capture : GenericApplicationCapture base.frame domain body argument support) :
    ∃ realized : OriginalCaptureRealization
        (.capture graph domain graph argument (.ofLocation (.appArgument location) initial))
        env registry target (Locals.push locals) commonSubst commonSubst (available.push capture.needs),
      Nonempty (RichCert sourceEnv env U registry target body (Locals.push locals)
        ((raw.cons (a.subst raw)).comp commonSubst) true support capture.capture.footprint) ∧
      capture.capture.footprint.Available (available.push capture.needs) ∧
      richSchedule .expressionReindex
        ((Closure.close (result.dependencyOrigin ordered) (base.frame.dependencyEnvironment ordered)).cost +
         (Closure.close (body.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)).cost) <
      richSchedule .fundamental
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
          (base.frame.dependencyEnvironment ordered)).cost := by
  obtain ⟨realized, environmentEq, certificate, resources⟩ := capture.sourceRealization base domain argument
    (.ofLocation (.appArgument location) initial) body
  refine ⟨realized, certificate, resources, ?_⟩
  rw [environmentEq ordered]
  apply richSchedule_strict
  exact capturedApplication_comparison (domain.dependencyOrigin ordered) (body.dependencyOrigin ordered)
    (function.dependencyOrigin ordered) (argument.dependencyOrigin ordered) (result.dependencyOrigin ordered)
    (base.frame.dependencyEnvironment ordered)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
