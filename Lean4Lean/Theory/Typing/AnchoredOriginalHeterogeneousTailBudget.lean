import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderPriorField
import Lean4Lean.Theory.Typing.AnchoredOriginalDependencyHeaderCapture

/-! The actual rich header tail determines the declaration-dependent replay
budget. Its capture tuple includes raw empty slots, and every queried slot
retains the same original owner/domain locations used by semantic lookup.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

def HeaderRichTail.dependencySteps
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (headerFormed : headerEnv.Ordered) (sourceFormed : sourceEnv.Ordered)
    (tail : HeaderRichTail header field major env registry target context locals left right available) :
    List (Dependency.HeaderCaptureStep headerFormed sourceFormed header field major) :=
  tail.steps.map (Dependency.measureStep headerFormed sourceFormed)

noncomputable def HeaderRichTail.dependencyEnvironment
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (headerFormed : headerEnv.Ordered) (sourceFormed : sourceEnv.Ordered)
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (initial : List Closure) : List Closure :=
  Dependency.headerCaptureEnvironment (tail.dependencySteps headerFormed sourceFormed) initial

/-- The equality is the actual ordered capture tuple produced by replay.
Its length, including unqueried raw slots, is derived internally. -/
theorem HeaderRichTail.projection_reindex_schedule
    (formed : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
    (major : Derivation sourceEnv U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    {context : ContextDerivation
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).source U headerSource}
    (tail : HeaderRichTail
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      field (.left major) env registry target context locals left right available)
    (captureTuple : tail.arguments =
      (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).map (·.subst σ))
    (selectedHeader : LocatedOrigin
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original))
    (selectedField : LocatedOrigin field) (initial : List Closure) :
    schedule .coherence
      (((Dependency.measureLocated formed selectedField).closure initial).cost +
       (Closure.close (selectedHeader.node.dependencyOrigin
          (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered)
         (tail.dependencyEnvironment
           (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
           formed initial)).cost) <
    schedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin formed) initial).cost := by
  apply Dependency.projection_reindex_schedule formed registered levelsWF levelCount parameterCount
    indexCount selected fieldWF field major closed allowed
    (tail.dependencySteps
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered formed)
    ?_ (Dependency.measureLocated _ selectedHeader) (Dependency.measureLocated formed selectedField) initial
  rw [dependencySteps, List.length_map, ← tail.arguments_length, captureTuple, List.length_map]

/-- The same concrete replay edge is strict below its actual original
projection root, including all retained source exposure conversions. -/
theorem HeaderRichTail.projection_reindex_located_schedule
    (formed : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
    (major : Derivation sourceEnv U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    {context : ContextDerivation
      (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).source U headerSource}
    (tail : HeaderRichTail
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original)
      field (.left major) env registry target context locals left right available)
    (captureTuple : tail.arguments =
      (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).map (·.subst σ))
    (selectedHeader : LocatedOrigin
      (.left (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).original))
    (selectedField : LocatedOrigin field) (initial : List Closure)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (location : Located root (EndpointState.proj registered levelsWF levelCount parameterCount indexCount
      selected fieldWF (.ref field) major closed allowed)) :
    schedule .coherence
      (((Dependency.measureLocated formed selectedField).closure (location.dependencyEnvironment formed initial)).cost +
       (Closure.close (selectedHeader.node.dependencyOrigin
          (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered)
         (tail.dependencyEnvironment
           (selectOriginalHeader formed (formed.projectionConstructor registered) levelsWF).ordered
           formed (location.dependencyEnvironment formed initial))).cost) <
    schedule .fundamental
      (Closure.close (root.dependencyOrigin formed) initial).cost := by
  have headBound := HeaderRichTail.projection_reindex_schedule formed registered levelsWF levelCount
    parameterCount indexCount selected fieldWF field major closed allowed tail captureTuple selectedHeader
    selectedField (location.dependencyEnvironment formed initial)
  have rootBound := location.dependency_cost_le formed initial
  simp only [schedule, Phase.code] at *
  omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
