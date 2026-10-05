import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemand
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureHeadReplyData

/-! The recursive variable task returns a finite demanded resource at its
actual selected frame. The original destination node stays outside this
packet, so descending a source context never manufactures a shorter-context
variable derivation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

structure WorldVariableDemandReply
    {strata : EquationStratification env} (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (commonLeft commonRight : Subst)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length)) (index : Nat) (requested : Profile n) where
  locals : List Nat
  available : Valuation
  realization : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available
  generation : WorldGenerated strata P base caps commonLeft commonRight graph realization.frame.raw controls
  replayable : generation.Replayable
  controlled : generation.Controlled frontier
  compatible : generation.UsesControlPrefix controls.cutoff controls.fuel
  hereditary : generation.Hereditary frontier
  capacity : ∀ ordered : sourceEnv.Ordered,
    environmentCost (realization.frame.dependencyEnvironment ordered) ≤ environmentCost environment
  covered : Covered (@EquationControlMeasure.Less strata.rules.length) generation.worlds baseline.worlds
  demand : WorldVariableDemand env U registry target available index requested

/-- Read the exact resource from the SAME already constructed head reply. -/
noncomputable def WorldCaptureHeadReplyData.toDemand
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {display : OriginalNestedDisplay U common expression assigned}
    {controls : OriginalWorldControls strata display.sourceEnv}
    {localBaseline : WorldEnvironmentProvenance strata U localEnvironment}
    {outerBaseline : WorldEnvironmentProvenance strata U outerEnvironment}
    {frontier : List (World strata.rules.length)}
    {reply : AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight requested
      (environmentCost outerEnvironment)}
    {index : Nat}
    (data : WorldCaptureHeadReplyData (P := P) controls localBaseline outerBaseline frontier reply index) :
    WorldVariableDemandReply P base caps display.graph commonLeft commonRight controls localBaseline frontier index requested where
  locals := reply.answer.reply.locals
  available := reply.answer.reply.available
  realization := reply.answer.reply.realization
  generation := data.generation
  replayable := data.replayable
  controlled := data.controlled
  compatible := data.compatible
  hereditary := data.hereditary
  capacity := data.localCapacity
  covered := data.localCovered
  demand := WorldVariableDemand.ofQuery reply.answer.reply.query data.footprint

/-- Attach a recursive resource result to the actual original destination.
This construction uses no smaller-context original node. -/
noncomputable def WorldVariableDemandReply.atNode
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U environment}
    {frontier : List (World strata.rules.length)}
    (answer : WorldVariableDemandReply P base caps graph commonLeft commonRight controls baseline frontier index requested)
    (node : EndpointState sourceEnv U source (.bvar index) assigned)
    (provenance : EndpointProvenance context node) :
    let display : OriginalNestedDisplay U common (raw index) (assigned.subst raw) :=
      ⟨sourceEnv, source, .bvar index, assigned, context, node, provenance, raw, graph, rfl, rfl⟩
    AmbientBoundedGeneratedQueryReply base caps display commonLeft commonRight requested (environmentCost environment) := {
  answer := {
    reply := {
      locals := answer.locals
      available := answer.available
      realization := answer.realization
      generated := answer.generation.erase.capped.generated
      query := answer.demand.atNode node answer.locals (raw.comp commonLeft)
      closed := answer.hereditary.tablesClosed.closed }
    capped := answer.generation.erase.capped }
  bounded := answer.capacity
  generation := answer.generation.erase.ambientGenerated }

noncomputable def WorldVariableDemandReply.atNode_data
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U environment}
    {frontier : List (World strata.rules.length)}
    (answer : WorldVariableDemandReply P base caps graph commonLeft commonRight controls baseline frontier index requested)
    (node : EndpointState sourceEnv U source (.bvar index) assigned)
    (provenance : EndpointProvenance context node) :
    WorldCaptureHeadReplyData (P := P) controls baseline baseline frontier (answer.atNode node provenance) index where
  generation := answer.generation
  replayable := answer.replayable
  controlled := answer.controlled
  compatible := answer.compatible
  query := answer.demand.atNode_controlled controls frontier node answer.locals (raw.comp commonLeft)
  covered := answer.covered
  hereditary := answer.hereditary
  localCapacity := answer.capacity
  localCovered := answer.covered
  footprint := rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
