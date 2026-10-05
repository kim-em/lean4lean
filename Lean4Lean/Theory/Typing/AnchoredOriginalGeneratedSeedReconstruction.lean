import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedSeedData
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedNativePiReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingInterpretation

/-! A retained seed is queried before declaration alignment. Query selection
keeps the actual owner occurrence and replaces only its finite resource frame;
its original owner budget is preserved. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

section
variable
  {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  {domain : EndpointRef headerEnv U headerSource A (.sort level)}
  (seed : PendingRichCapture (field := field) (major := major) domain env registry target
    headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
  (graph : OriginalCaptureMap (common := common) (seed.owner.context seed.initialContext) raw)
  (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph seed.frame.raw)

include generated in
/-- Source-to-seed R is smaller than the original source-to-captured-variable
pair. The seed's concrete frame is charged before its new query is selected. -/
theorem PendingRichCapture.reconstructSeed
    {context : ContextDerivation headerEnv U headerSource}
    (tail : OriginalRichFrame headerEnv env U registry target context
      headerLocals declaredLeft declaredRight headerAvailable)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (left : OriginalNestedDisplay U common (seed.owner.expression.subst raw) leftAssigned)
    (leftOrdered : left.sourceEnv.Ordered)
    (leftFrame : OriginalCaptureRealization left.graph env registry target
      leftLocals commonLeft commonRight leftAvailable)
    (leftCapped : CappedCaptureGenerated base commonCaps commonLeft commonRight left.graph leftFrame.frame.raw)
    (leftClosed : leftAvailable.AtomClosed)
    (reindex : GeneratedObservationCall base commonCaps left (seed.seedDisplay graph)
      commonLeft commonRight leftOrdered ordered
      (richSchedule .expressionReindex
        ((Closure.close (left.node.dependencyOrigin leftOrdered) (leftFrame.frame.dependencyEnvironment leftOrdered)).cost +
         (Closure.close (variableNode.dependencyOrigin headerOrdered)
           ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost)))
    {footprint : Footprint}
    (query : RichObs left.sourceEnv env U registry target left.node leftLocals
      (left.raw.comp commonLeft) (requested : Profile n) footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps (seed.seedDisplay graph)
      commonLeft commonRight requested (environmentCost (seed.frame.dependencyEnvironment ordered))) := by
  obtain ⟨seedFrame, seedCapped, same⟩ := generated.realize seed.frame seed.substitutions
  have ownerBound := seed.group_owner_activation_bound ordered headerOrdered tail entries
    (variableNode.dependencyOrigin headerOrdered)
  have strict : richSchedule .expressionReindex
      ((Closure.close (left.node.dependencyOrigin leftOrdered) (leftFrame.frame.dependencyEnvironment leftOrdered)).cost +
       (Closure.close (seed.owner.node.dependencyOrigin ordered) (seedFrame.frame.dependencyEnvironment ordered)).cost) <
      richSchedule .expressionReindex
      ((Closure.close (left.node.dependencyOrigin leftOrdered) (leftFrame.frame.dependencyEnvironment leftOrdered)).cost +
       (Closure.close (variableNode.dependencyOrigin headerOrdered)
         ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost) := by
    rw [same ordered]
    exact richSchedule_strict (Nat.add_lt_add_left
      (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) ownerBound) _) _ _
  obtain ⟨answer⟩ := reindex leftFrame leftCapped leftClosed seedFrame seedCapped seed.ownerClosed
    strict query resources
  exact ⟨⟨answer.answer, fun formed => by simpa only [same ordered] using answer.bounded formed⟩⟩

/-- Interpreting the newly reconstructed query uses the original owner F,
not a correctness premise for a fabricated declaration-domain expression. -/
theorem PendingRichCapture.requeryValue
    {context : ContextDerivation headerEnv U headerSource}
    (tail : OriginalRichFrame headerEnv env U registry target context
      headerLocals declaredLeft declaredRight headerAvailable)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (formed : OnCtx target (env.IsType U))
    (answer : BoundedGeneratedQueryReply base commonCaps (seed.seedDisplay graph)
      commonLeft commonRight (requested : Profile n)
      (environmentCost (seed.frame.dependencyEnvironment ordered)))
    (ownerF : seed.owner.ComputationalInductionAt env registry ordered seed.initialContext
      (Closure.close (variableNode.dependencyOrigin headerOrdered)
        ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost) :
    let pending := seed.requery graph generated ordered answer
    Nonempty (RichComputationalValue sourceEnv env U registry target pending.owner.node pending.ownerLocals
      pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input) := by
  let pending := seed.requery graph generated ordered answer
  have bound := pending.group_owner_activation_bound ordered headerOrdered tail entries
    (variableNode.dependencyOrigin headerOrdered)
  exact ownerF.apply pending.frame (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) bound)
    pending.ownerClosed formed pending.substitutions pending.query pending.queryAvailable

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
