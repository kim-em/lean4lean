import Lean4Lean.Theory.Typing.AnchoredOriginalRichReferenceExposure
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBetaBackward

/-! Backward beta accepts a query at the original public equality endpoint.
Inward exposure retains all original children and consumes no semantic call. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option Elab.async false

section Beta
open OriginalTail
set_option quotPrecheck false
variable
  (context : ContextDerivation sourceEnv U source)
  (domainWF : u.WF U) (bodyWF : v.WF U)
  (domain : Derivation sourceEnv U source A A (.sort u))
  (codomain : Derivation sourceEnv U (A :: source) B B (.sort v))
  (body : Derivation sourceEnv U (A :: source) e e B)
  (argument : Derivation sourceEnv U source a a A)
  (result : Derivation sourceEnv U source (B.inst a) (B.inst a) (.sort v))
  (instantiated : Derivation sourceEnv U source (e.inst a) (e.inst a) (B.inst a))
  (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)
  (ordered : sourceEnv.Ordered)

local notation "original" => Derivation.beta domainWF bodyWF domain codomain body argument result instantiated
local notation "bodyDisplay" => betaCapturedBodyDisplay context domain body argument (.identity context)
local notation "capacity" => environmentCost (Closure.bundle (.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)) (.close (domain.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)) :: frame.dependencyEnvironment ordered)
local notation "limit" => (Closure.close ((original).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost

/-- The public right beta endpoint and its retained instantiated child have
the same exposure. The transformation keeps the exact incoming resources. -/
def RichObs.betaInstantiated
    (query : RichObs sourceEnv env U registry target (.ref (.right original))
      locals σ profile footprint) :
    RichObs sourceEnv env U registry target (.ref (.left instantiated))
      locals σ profile footprint :=
  RichObs.changeReference (first := .right original) (second := .left instantiated) rfl query

/-- The symmetric public beta endpoint uses the same inward transformation. -/
def RichObs.betaSymmInstantiated
    (query : RichObs sourceEnv env U registry target (.ref (.left (original).symm))
      locals σ profile footprint) :
    RichObs sourceEnv env U registry target (.ref (.left instantiated))
      locals σ profile footprint :=
  RichObs.changeReference (first := .left (original).symm) (second := .left instantiated) rfl query

/-- Backward beta at its actual public equality endpoint. Inward query
exposure is structural; every semantic call remains at the smaller original
children already required by the instantiated-child beta rule. -/
theorem generatedBetaBackwardAtReference
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (bodyR : GeneratedObservationCall (frame.captureBase substitutions) ((frame.captureBase substitutions)).initialCaps
      (betaInstantiatedDisplay context instantiated (.identity context)) bodyDisplay
      σ τ ordered ordered (richSchedule .fundamental limit))
    (domainF : OriginalCodeInductionAt env registry ordered context (.here (root := .left domain)) limit)
    (leftF : OriginalComputationalInductionAt env registry ordered context
      (.expose (.here (root := .left original))) limit)
    (instantiatedF : OriginalComputationalInductionAt env registry ordered context (.here (root := .left instantiated)) limit)
    (query : RichObs sourceEnv env U registry target (.ref (.left (original).symm))
      locals σ (profile : Profile n) footprint)
    (resources : footprint.Available available) :
    ∃ ledgers : List (Σ needs, CapturedArgumentQueries (frame.captureBase substitutions) ((frame.captureBase substitutions)).initialCaps source σ τ a capacity needs),
      (∀ entry ∈ ledgers,
        entry.2.Calls (OriginalNestedDisplay.identity (frame.captureBase substitutions) (.ref (.left argument)) (.ofLocation .here context))
          ordered (richSchedule .fundamental limit)) →
      Nonempty (OriginalEqualityQueryResult (original).symm env registry target locals σ τ available profile) := by
  exact generatedBetaBackward context domainWF bodyWF domain codomain body argument result instantiated
    frame substitutions ordered henv hscoped below formed closed bodyR domainF leftF instantiatedF
    (query.betaSymmInstantiated domainWF bodyWF domain codomain body argument result instantiated) resources

end Beta

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
