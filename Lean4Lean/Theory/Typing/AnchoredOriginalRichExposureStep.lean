import Lean4Lean.Theory.Typing.AnchoredOriginalRichExposureMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConversionStep

/-! Restoring a lazy reference preserves the original assigned-type occurrence.
No recursive comparison is needed when exposure selected that very occurrence.
Otherwise the two retained formations fit strictly inside the original rule. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

variable {header : EndpointRef headerEnv U [] headerExpression headerType}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}

/-- The source query is reindexed only between the two actual formation
occurrences. The cost environment is the concrete fitted header frame. -/
theorem HeaderBinderFrame.restoreExposure
    {context : ContextDerivation headerEnv U headerSource}
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    (frame : HeaderBinderFrame header field major env registry target context locals σ τ available)
    (reference : EndpointRef headerEnv U headerSource expression assigned)
    (answer : RichSupportedValue headerEnv env U registry target reference.expose
      locals σ τ available profile)
    (typeR : richSchedule .expressionReindex
        ((Closure.close (reference.expose.typeFormation.node.dependencyOrigin hf)
          (frame.dependencyEnvironment hf sf initial)).cost +
         (Closure.close (reference.typeFormation.node.dependencyOrigin hf)
          (frame.dependencyEnvironment hf sf initial)).cost) <
      richSchedule .fundamental
        (Closure.close (reference.dependencyOrigin hf)
          (frame.dependencyEnvironment hf sf initial)).cost →
      RichCodeTransfer env U registry target reference.expose.typeFormation.node
        reference.typeFormation.node locals locals σ σ available available) :
    Nonempty (RichSupportedValue headerEnv env U registry target (.ref reference)
      locals σ τ available profile) := by
  rcases reference.exposure_formation_cost_reserve hf
    (frame.dependencyEnvironment hf sf initial) with same | smaller
  · refine ⟨{
      support := answer.support
      footprint := answer.footprint
      certificate := ?_
      resources := answer.resources
      typed := answer.typed
      related := answer.related
      typeCode := answer.typeCode }⟩
    change RichCert headerEnv env U registry target reference.typeFormation.node locals σ true
      answer.support answer.footprint
    exact same ▸ answer.certificate
  · obtain ⟨changed⟩ := typeR (richSchedule_strict smaller _ _) answer.certificate answer.resources
    exact ⟨{
      support := answer.support
      footprint := changed.footprint
      certificate := changed.certificate
      resources := changed.resources
      typed := answer.typed
      related := answer.related
      typeCode := answer.typeCode }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
