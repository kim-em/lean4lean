import Lean4Lean.Theory.Typing.AnchoredOriginalGroupedCaptureCapacity

/-! A query-independent output envelope for a captured header slot. Both
original owner roots are reserved even when the selected query list is empty.
The exact retained type-history reserve sits outside this head-local group. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def groupCaptureBaseline
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (initial previous : List Closure) : List Closure :=
  let declared := Closure.close (domain.dependencyOrigin headerOrdered) previous
  declared ::
    Closure.bundle (.close (field.dependencyOrigin ordered) initial) declared ::
    Closure.bundle (.close (major.dependencyOrigin ordered) initial) declared :: previous

/-- The selected query count does not affect the fixed output capacity.
Every actual owner is an original occurrence below one of the two roots. -/
theorem RichGroupedCapture.environment_le_baseline
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    (previous actual : List Closure)
    (tailBound : environmentCost actual ≤ environmentCost previous) :
    environmentCost (entries.environment ordered headerOrdered initial actual) ≤
      environmentCost (groupCaptureBaseline field major domain ordered headerOrdered initial previous) := by
  have bound := RichGroupedCapture.environment_mono ordered headerOrdered
    ([] : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    entries previous actual tailBound
  simpa only [RichGroupedCapture.environment, groupCaptureBaseline, List.map_nil,
    List.cons_append, List.nil_append] using bound

/-- The reserve is exactly the stored history's list. Appending it preserves
the group bound while allowing positive-depth peeling to discard this head. -/
theorem OriginalRichFrame.reservedGroup_environment_le_baseline
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    (previous reserve : List Closure)
    (tailBound : environmentCost (tail.dependencyEnvironment headerOrdered) ≤ environmentCost previous) :
    environmentCost (((tail.group domain ordered initial entries).reserve reserve).dependencyEnvironment headerOrdered) ≤
      environmentCost (reserve ++ groupCaptureBaseline field major domain ordered headerOrdered initial previous) := by
  rw [OriginalRichFrame.reserve_environment, OriginalRichFrame.group_environment]
  simp only [merge_environmentCost_append]
  have bound := entries.environment_le_baseline ordered headerOrdered
    previous (tail.dependencyEnvironment headerOrdered) tailBound
  omega

/-- Retain both the exact route ledger and the fixed group envelope. The
latter pays the domain/owner multiplication when replay selects a new tail. -/
noncomputable def groupCaptureHistoryReserve
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (initial previous history : List Closure) : List Closure :=
  history ++ groupCaptureBaseline field major domain ordered headerOrdered initial previous

/-- Every selected group below the retained prior has exactly the same
reserved capacity, independently of its queries, locals, or resource table. -/
theorem OriginalRichFrame.historyGroup_environmentCost
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    (previous history : List Closure)
    (tailBound : environmentCost (tail.dependencyEnvironment headerOrdered) ≤ environmentCost previous) :
    environmentCost (((tail.group domain ordered initial entries).reserve
      (groupCaptureHistoryReserve field major domain ordered headerOrdered initial previous history)).dependencyEnvironment headerOrdered) =
      environmentCost (groupCaptureHistoryReserve field major domain ordered headerOrdered initial previous history) := by
  rw [OriginalRichFrame.reserve_environment, OriginalRichFrame.group_environment,
    merge_environmentCost_append]
  apply Nat.max_eq_left
  exact Nat.le_trans (entries.environment_le_baseline ordered headerOrdered previous
    (tail.dependencyEnvironment headerOrdered) tailBound) (by
      simp only [groupCaptureHistoryReserve, merge_environmentCost_append]
      exact Nat.le_max_right _ _)

/-- Replay into any newly selected tail below the retained prior cannot grow
past an incoming frame carrying the same exact history and baseline reserve.
No equality of the incoming and outgoing resource tables is required. -/
theorem OriginalRichFrame.historyGroup_replay_nonGrowth
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    (previous history : List Closure)
    (tailBound : environmentCost (tail.dependencyEnvironment headerOrdered) ≤ environmentCost previous)
    (incoming : OriginalRichFrame headerEnv env U registry target incomingContext
      incomingLocals incomingLeft incomingRight incomingAvailable) :
    environmentCost (((tail.group domain ordered initial entries).reserve
      (groupCaptureHistoryReserve field major domain ordered headerOrdered initial previous history)).dependencyEnvironment headerOrdered) ≤
      environmentCost ((incoming.reserve
        (groupCaptureHistoryReserve field major domain ordered headerOrdered initial previous history)).dependencyEnvironment headerOrdered) := by
  rw [tail.historyGroup_environmentCost ordered headerOrdered entries previous history tailBound,
    OriginalRichFrame.reserve_environment, merge_environmentCost_append]
  exact Nat.le_max_left _ _

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
