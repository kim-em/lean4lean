import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations

/-! Primitive retained-route R/C execution at fixed original bounds. The
actual selected source frame is admitted by capacity AND captured-world
coverage; the strict recursive edge names the retained original budget. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem AmbientBoundedParameterReply.reindexAtWorld
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U common expression leftType}
    {right : OriginalNestedDisplay U common expression rightType}
    (henv : env.Ordered)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (sameCutoff : leftControls.cutoff = rightControls.cutoff)
    (sameFuel : leftControls.fuel = rightControls.fuel)
    (leftWorld : WorldEnvironmentProvenance strata U initialEnvironment)
    (rightWorld : WorldEnvironmentProvenance strata U finalEnvironment)
    (frontier parent : List (World strata.rules.length))
    (answer : AmbientBoundedParameterReply base commonCaps start left commonLeft commonRight
      (profile : Profile n) (environmentCost initialEnvironment))
    (answerData : WorldParameterReplyData (P := P) leftControls leftWorld frontier answer)
    (sorted : profile.HasType (.sort relevant))
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals
      commonLeft commonRight rightAvailable)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := commonCaps)
      (display := right) rightControls rightWorld frontier rightFrame)
    (sponsored : Sponsored frontier
      [originalCallWorld leftControls .expressionReindex left.node leftWorld,
       originalCallWorld rightControls .expressionReindex right.node rightWorld])
    (smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld leftControls .expressionReindex left.node leftWorld,
        originalCallWorld rightControls .expressionReindex right.node rightWorld]) parent)
    (bank : WorldBoundedCallBank env U registry strata P parent) :
    ∃ result : AmbientBoundedParameterReply base commonCaps start right commonLeft commonRight
        profile (environmentCost finalEnvironment),
      Nonempty (WorldParameterReplyData (P := P) rightControls rightWorld frontier result) := by
  let prior := answer.reply.answer.reply
  obtain ⟨footprint, certificate, ready, resources, _⟩ :=
    prior.query.code_controlled henv leftControls answerData.query sorted
  obtain ⟨replayed, ⟨replayedData⟩⟩ := (bank _ smaller).observation base commonCaps left right
    commonLeft commonRight leftControls rightControls sameCutoff sameFuel leftWorld rightWorld
    frontier rfl sponsored prior.realization answerData.callFrame rightFrame rightData
    (.code certificate) resources ready.code
  let result : AmbientBoundedParameterReply base commonCaps start right commonLeft commonRight
      profile (environmentCost finalEnvironment) := {
    toBoundedParameterReply := ⟨replayed.toBoundedGeneratedQueryReply, answer.related, answer.path⟩
    generation := replayed.generation }
  exact ⟨result, ⟨{
    generation := replayedData.generation
    hereditary := replayedData.hereditary
    replayable := replayedData.replayable
    controlled := replayedData.controlled
    compatible := replayedData.compatible
    query := replayedData.query
    covered := replayedData.covered }⟩⟩

theorem AmbientBoundedParameterReply.assignedAtWorld
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U common expression leftAssigned}
    {right : OriginalNestedDisplay U common expression rightAssigned}
    (henv : env.Ordered)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (sameCutoff : leftControls.cutoff = rightControls.cutoff)
    (sameFuel : leftControls.fuel = rightControls.fuel)
    (leftWorld : WorldEnvironmentProvenance strata U initialEnvironment)
    (rightWorld : WorldEnvironmentProvenance strata U finalEnvironment)
    (frontier parent : List (World strata.rules.length))
    (answer : AmbientBoundedParameterReply base commonCaps start left.formationDisplay commonLeft commonRight
      (profile : Profile n) (environmentCost initialEnvironment))
    (answerData : WorldParameterReplyData (P := P) (display := left.formationDisplay)
      leftControls leftWorld frontier answer)
    (sorted : profile.HasType (.sort relevant))
    (rightFrame : OriginalCaptureRealization right.graph env registry target rightLocals
      commonLeft commonRight rightAvailable)
    (rightData : WorldCallFrameData (P := P) (base := base) (caps := commonCaps)
      (display := right) rightControls rightWorld frontier rightFrame)
    (sponsored : Sponsored frontier
      [originalCallWorld leftControls .assignedComparison left.node leftWorld,
       originalCallWorld rightControls .assignedComparison right.node rightWorld])
    (smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld leftControls .assignedComparison left.node leftWorld,
        originalCallWorld rightControls .assignedComparison right.node rightWorld]) parent)
    (bank : WorldBoundedCallBank env U registry strata P parent) :
    ∃ result : AmbientBoundedParameterReply base commonCaps start right.formationDisplay commonLeft commonRight
        profile (environmentCost finalEnvironment),
      Nonempty (WorldParameterReplyData (P := P) (display := right.formationDisplay)
        rightControls rightWorld frontier result) := by
  let prior := answer.reply.answer.reply
  obtain ⟨footprint, certificate, ready, resources, _⟩ :=
    prior.query.code_controlled henv leftControls answerData.query sorted
  let leftData : WorldCallFrameData (P := P) (base := base) (caps := commonCaps)
      (display := left) leftControls leftWorld frontier prior.realization := {
    generation := answerData.generation
    hereditary := answerData.hereditary
    replayable := answerData.replayable
    controlled := answerData.controlled
    compatible := answerData.compatible
    closed := prior.closed
    capacity := answer.reply.bounded leftControls.ordered
    covered := answerData.covered }
  obtain ⟨changed, ⟨changedData⟩⟩ := (bank _ smaller).assigned base commonCaps left right
    commonLeft commonRight leftControls rightControls sameCutoff sameFuel leftWorld rightWorld
    frontier rfl sponsored prior.realization leftData rightFrame rightData certificate resources ready
  let result : AmbientBoundedParameterReply base commonCaps start right.formationDisplay commonLeft commonRight
      profile (environmentCost finalEnvironment) := {
    toBoundedParameterReply := ⟨changed.reply, answer.related.trans henv changed.related,
      answer.path.trans changed.path⟩
    generation := changed.generation }
  exact ⟨result, ⟨{
    generation := changedData.generation
    hereditary := changedData.hereditary
    replayable := changedData.replayable
    controlled := changedData.controlled
    compatible := changedData.compatible
    query := changedData.query
    covered := changedData.covered }⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
