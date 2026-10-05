import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingInterpretation

/-! The owner stage precedes declaration alignment. Every retained source
query is interpreted at its own actual original frame. The resulting type
certificates, rather than guessed target demands, are available to discover
all dependencies before constructing any header group. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive RichPendingValues
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType} :
    List (PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) → Type where
  | nil : RichPendingValues []
  | cons (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
      (value : RichComputationalValue sourceEnv env U registry target pending.owner.node pending.ownerLocals
        pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input)
      (rest : RichPendingValues tail) : RichPendingValues (pending :: tail)

theorem PendingRichCapture.projectionValues
    (sourceOrdered : sourceEnv.Ordered)
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
    (pending : List (PendingRichCapture (field := field) (major := .left major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue))
    (formed : OnCtx target (env.IsType U))
    (ownerF : ∀ query ∈ pending,
      query.owner.ComputationalInductionAt env registry sourceOrdered query.initialContext
        (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
          selected fieldWF (.ref field) major closed allowed).dependencyOrigin sourceOrdered) ownerInitial).cost) :
    Nonempty (RichPendingValues pending) := by
  induction pending with
  | nil => exact ⟨.nil⟩
  | cons query rest ih =>
    obtain ⟨value⟩ := query.projectionValue sourceOrdered registered levelsWF levelCount parameterCount
      indexCount selected fieldWF field major closed allowed formed (ownerF query List.mem_cons_self)
    obtain ⟨values⟩ := ih (fun entry member => ownerF entry (List.mem_cons_of_mem _ member))
    exact ⟨.cons query value values⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
