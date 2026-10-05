import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderFrameTransportMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalDependencyEndpoints

/-! A native constructor plan follows the exact original header context spine.
Its terminal result may equal the header (the nullary case), but its measured
closure never exceeds the header at the empty original environment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem Located.contextDerivation_dependencyClosures
    {root : EndpointRef env U source expression type}
    {node : EndpointState env U context selectedExpression selectedType}
    (ordered : env.Ordered) (location : Located root node)
    (initial : ContextDerivation env U source) :
    (location.contextDerivation initial).dependencyClosures ordered =
      location.dependencyEnvironment ordered (initial.dependencyClosures ordered) := by
  induction location with
  | here => rfl
  | expose _ ih | convertTerm _ ih | appDomain _ ih | appResult _ ih | appFunction _ ih | appArgument _ ih | lamDomain _ ih | piDomain _ ih | projField _ ih | projMajor _ ih | assignedFormation _ ih | appPiFormation _ ih => exact ih
  | appCodomain parent ih | lamCodomain parent ih | lamBody parent ih | piBody parent ih =>
    have equal := Classical.choose_spec parent.originalDomains.1
    have originEq := congrArg (EndpointState.dependencyOrigin ordered) equal
    simp only [EndpointState.dependencyOrigin] at originEq
    change Closure.close ((Classical.choose parent.originalDomains.1).dependencyOrigin ordered)
      ((parent.contextDerivation initial).dependencyClosures ordered) ::
        (parent.contextDerivation initial).dependencyClosures ordered =
      Closure.close _ (parent.dependencyEnvironment ordered (initial.dependencyClosures ordered)) ::
        parent.dependencyEnvironment ordered (initial.dependencyClosures ordered)
    rw [ih, originEq]

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

theorem HeaderBinderFrame.constructorResult_cost_le
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {node : EndpointState headerEnv U headerSource expression assigned}
    {context : ContextDerivation headerEnv U headerSource}
    (ordered : headerEnv.Ordered) (capturedOrdered : sourceEnv.Ordered)
    (location : Located header node) (lineage : location.contextDerivation .nil = context)
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available)
    (exactEnvironment : frame.dependencyEnvironment ordered capturedOrdered initial =
      context.dependencyClosures ordered) :
    (Closure.close (node.dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered capturedOrdered initial)).cost ≤
      (Closure.close (header.dependencyOrigin ordered) []).cost := by
  rw [exactEnvironment, ← lineage, location.contextDerivation_dependencyClosures]
  exact location.dependency_cost_le ordered []

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
