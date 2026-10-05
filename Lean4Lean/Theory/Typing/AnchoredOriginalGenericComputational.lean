import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalPrefix

/-! Original computational and code induction at arbitrary original source
contexts. The recursive bound uses the retained generic frame's computed
environment, including all heterogeneous grouped owners. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

def OriginalComputationalInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (ordered : sourceEnv.Ordered)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation sourceEnv U rootSource)
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located root node) (limit : Nat) : Prop :=
  ∀ target locals σ τ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initialContext) locals σ τ available,
    (Closure.close (node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs sourceEnv env U registry target node locals σ profile footprint →
    footprint.Available available →
    Nonempty (RichComputationalValue sourceEnv env U registry target node locals σ τ available profile)

def OriginalCodeInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (ordered : sourceEnv.Ordered)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initialContext : ContextDerivation sourceEnv U rootSource)
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (location : Located root node) (limit : Nat) : Prop :=
  ∀ target locals σ τ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initialContext) locals σ τ available,
    (Closure.close (node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ source →
    RichCodeTransfer env U registry target node node locals locals σ τ available available

theorem OriginalComputationalInductionAt.code
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression (.sort level)}
    {location : Located root node}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (induction : OriginalComputationalInductionAt env registry ordered initialContext location limit) :
    OriginalCodeInductionAt env registry ordered initialContext location limit := by
  intro target locals σ τ available frame bound closed formed substitutions relevant n profile footprint query resources
  obtain ⟨answer⟩ := induction target locals σ τ available frame bound closed formed substitutions (.code query) resources
  exact answer.code henv hscoped formed query.formed

/-- Lazy exposure changes the certificate occurrence only when the actual
source reference reserved a strictly smaller two-formation comparison. -/
theorem OriginalRichFrame.restoreExposure
    {context : ContextDerivation sourceEnv U source}
    (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (answer : RichSupportedValue sourceEnv env U registry target reference.expose locals σ τ available profile)
    (typeR : FormationRestoreCall env U registry target ordered (frame.dependencyEnvironment ordered)
      (reference.dependencyOrigin ordered) reference.expose.typeFormation.node reference.typeFormation.node
      locals σ available) :
    Nonempty (RichSupportedValue sourceEnv env U registry target (.ref reference) locals σ τ available profile) := by
  rcases reference.exposure_formation_cost_reserve ordered (frame.dependencyEnvironment ordered) with same | smaller
  · refine ⟨{
      support := answer.support, footprint := answer.footprint, certificate := ?_, resources := answer.resources
      typed := answer.typed, related := answer.related, typeCode := answer.typeCode }⟩
    change RichCert sourceEnv env U registry target reference.typeFormation.node locals σ true answer.support answer.footprint
    exact same ▸ answer.certificate
  · obtain ⟨changed⟩ := typeR (richSchedule_strict smaller _ _) answer.certificate answer.resources
    exact ⟨{
      support := answer.support, footprint := changed.footprint, certificate := changed.certificate
      resources := changed.resources, typed := answer.typed, related := answer.related, typeCode := answer.typeCode }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource

namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.DirectPrefixRoute
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalRecordSource OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Both restored output channels keep their real source occurrences while
all recursive bounds use this generic frame's captured environment. -/
theorem restoreOriginalComputational
    {context : ContextDerivation sourceEnv U source}
    (henv : env.Ordered) (ordered : sourceEnv.Ordered)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    {first : EndpointState sourceEnv U source expression assigned}
    {last : EndpointState sourceEnv U source expression natural}
    (route : DirectPrefixRoute sourceEnv U source expression first last)
    (calls : route.RestoreCalls env registry target ordered (frame.dependencyEnvironment ordered) locals σ available)
    (answer : RichComputationalValue sourceEnv env U registry target last locals σ τ available profile) :
    Nonempty (RichComputationalValue sourceEnv env U registry target first locals σ τ available profile) := by
  induction route with
  | done node => exact ⟨answer⟩
  | expose reference rest ih =>
    obtain ⟨tail⟩ := ih calls.2 answer
    obtain ⟨value⟩ := frame.restoreExposure ordered reference tail.toRichSupportedValue calls.1
    exact ⟨{ value with rightQuery := tail.rightQuery.restoreRoute (.expose reference (.done _)) }⟩
  | forward levelWF original term rest ih =>
    obtain ⟨tail⟩ := ih calls.2.2 answer
    obtain ⟨value⟩ := tail.toRichSupportedValue.convertForward henv ordered
      (frame.dependencyEnvironment ordered) levelWF original calls.1 calls.2.1
    exact ⟨{ value with rightQuery := (tail.rightQuery.restoreRoute
      (.convert (.forward levelWF original) term (.done _))) }⟩
  | backward levelWF original term rest ih =>
    obtain ⟨tail⟩ := ih calls.2.2 answer
    obtain ⟨value⟩ := tail.toRichSupportedValue.convertBackward henv ordered
      (frame.dependencyEnvironment ordered) levelWF original calls.1 calls.2.1
    exact ⟨{ value with rightQuery := (tail.rightQuery.restoreRoute
      (.convert (.backward levelWF original) term (.done _))) }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.DirectPrefixRoute
