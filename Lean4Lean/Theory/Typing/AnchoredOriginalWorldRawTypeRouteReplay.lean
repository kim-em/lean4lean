import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteExecutionData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteFunding
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEqualityReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTypedEqualityReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiDomainRouteStep
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplyPiReplay

/-! Structural execution of the actual finite retained route. Primitive calls
use the exact occurrence baselines; only strict subroutes are interpreted
recursively, and application packing is computed from the incoming query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000
namespace RawGeneratedTypeRoute.WorldBoundary
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
  {commonLeft commonRight : Subst} {strata : EquationStratification env}
  {left : OriginalNestedDisplay U common leftExpression leftAssigned}
  {right : OriginalNestedDisplay U common rightExpression rightAssigned}
  {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
  {inputs : route.WorldInputs strata}
  {leftControls : OriginalWorldControls strata left.sourceEnv}
  {rightControls : OriginalWorldControls strata right.sourceEnv}
  {leftWorld : WorldEnvironmentProvenance strata U initial}
  {rightWorld : WorldEnvironmentProvenance strata U final}
  {P : VEnv → Prop} {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
  {frontier : List (World strata.rules.length)}


theorem replayWorldCalls
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (generated : route.SourceGenerated P base caps)
    (execution : boundary.ExecutionFrames P base caps frontier)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (parent : List (World strata.rules.length))
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (unary : WorldBoundedUnaryCallBank env U registry strata P parent)
    (sponsored : Sponsored frontier boundary.calls)
    (smaller : CallBelow strata.rules.length (frontier ++ boundary.calls) parent)
    {n : Nat} {start : VExpr} {profile : Profile n}
    (incoming : AmbientBoundedParameterReply base caps start left commonLeft commonRight
      profile (environmentCost initial))
    (incomingData : WorldParameterReplyData (P := P) leftControls leftWorld frontier incoming)
    (sorted : profile.HasType (.sort true)) :
    ∃ output : AmbientBoundedParameterReply base caps start right commonLeft commonRight profile
      (environmentCost final),
      Nonempty (WorldParameterReplyData (P := P) rightControls rightWorld frontier output) := by
  induction boundary generalizing n start with
  | identity => exact ⟨incoming, ⟨incomingData⟩⟩
  | same left right lf rf frame lc rc lw rw compatible =>
    let data := execution ⟨frame.box, rc, rw⟩ (by simp only [frames, List.mem_singleton])
    exact incoming.reindexAtWorld henv lc rc compatible.1 compatible.2 lw rw frontier parent
      incomingData sorted frame.realization (data.callFrame right frame rc rw) sponsored smaller bank
  | assigned left right lf rf frame lc rc lw rw compatible =>
    let data := execution ⟨frame.box, rc, rw⟩ (by simp only [frames, List.mem_singleton])
    exact incoming.assignedAtWorld henv lc rc compatible.1 compatible.2 lw rw frontier parent
      incomingData sorted frame.realization (data.callFrame right frame rc rw) sponsored smaller bank
  | equality graph original forward ordered below controls world =>
    exact incoming.equalityStepWorld graph original forward henv hscoped formed controls world
      frontier parent incomingData sorted sponsored smaller unary
  | typedEquality graph original left same lf ordered below frame lc rc lw rw compatible =>
    cases same
    let data := execution ⟨frame.box, rc, rw⟩ (by simp only [frames, List.mem_singleton])
    have pairSub : [originalCallWorld lc .expressionReindex left.node lw,
        originalCallWorld rc .expressionReindex (.ref (.left original)) rw].Sublist
        [originalCallWorld lc .expressionReindex left.node lw,
        originalCallWorld rc .expressionReindex (.ref (.left original)) rw,
        originalCallWorld rc .fundamental (.ref (.left original)) rw] := by simp
    have equalitySub : [originalCallWorld rc .fundamental (.ref (.left original)) rw].Sublist
        [originalCallWorld lc .expressionReindex left.node lw,
        originalCallWorld rc .expressionReindex (.ref (.left original)) rw,
        originalCallWorld rc .fundamental (.ref (.left original)) rw] := by simp
    exact incoming.typedEqualityStepWorld graph original left henv hscoped formed lc rc
      compatible.1 compatible.2 lw rw frontier parent incomingData sorted frame.realization
      (data.callFrame (graph.typeEqualityDisplay original true) frame rc rw)
      (fun world member => sponsored world (pairSub.subset member))
      (callBelow_of_sublist (pairSub.append_left frontier) smaller)
      (fun world member => sponsored world (equalitySub.subset member))
      (callBelow_of_sublist (equalitySub.append_left frontier) smaller) bank unary
  | trans before after ihBefore ihAfter =>
    have ambient := generated.ambient
    rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient
    have sources := generated.sources
    rw [RawGeneratedTypeRoute.AllSources.eq_def] at sources
    have firstGenerated := (show RawGeneratedTypeRoute.SourceGenerated P base caps _ from
      ⟨before.wellFormed, ambient.1, sources.2.2.1, fun boxed member =>
        generated.frames boxed (by rw [RawGeneratedTypeRoute.frames.eq_def]; exact List.mem_append_left _ member)⟩)
    have secondGenerated := (show RawGeneratedTypeRoute.SourceGenerated P base caps _ from
      ⟨after.wellFormed, ambient.2, sources.2.2.2, fun boxed member =>
        generated.frames boxed (by rw [RawGeneratedTypeRoute.frames.eq_def]; exact List.mem_append_right _ member)⟩)
    obtain ⟨middle, ⟨middleData⟩⟩ := ihBefore firstGenerated execution.trans_left
      (fun world member => sponsored world (List.mem_append_left _ member))
      (callBelow_of_sublist ((List.sublist_append_left _ _).append_left frontier) smaller)
      incoming incomingData sorted
    exact ihAfter secondGenerated execution.trans_right
      (fun world member => sponsored world (List.mem_append_right _ member))
      (callBelow_of_sublist ((List.sublist_append_right _ _).append_left frontier) smaller)
      middle middleData sorted
  | piDomain left right below child ih =>
    have childGenerated := (show RawGeneratedTypeRoute.SourceGenerated P base caps _ from
      ⟨child.wellFormed, by have ambient := generated.ambient; rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient; exact ambient,
        by have sources := generated.sources; rw [RawGeneratedTypeRoute.AllSources.eq_def] at sources; exact sources.2.2,
        fun boxed member => generated.frames boxed (by rw [RawGeneratedTypeRoute.frames.eq_def]; exact member)⟩)
    exact incoming.piDomainStepWorld left right below henv hscoped formed _ _ _ _ frontier
      (fun answer data sorted => ih childGenerated execution sponsored smaller answer data sorted)
      incomingData sorted
  | applyPi initial domain body function argument result hu hv location sourceGraph noBinders
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      sourceOrdered headerOrdered sourceBelow headerBelow sourceFrame headerFrame ownerInitial sourceBound
      whole claimedSeedReserve sourceControls headerControls sourceWorld priorWorld ownerWorld sourceAdmission wholeInputs
      child claim ih =>
    let sourceData := execution ⟨sourceFrame.box, sourceControls, sourceWorld⟩
      (by simp only [frames, List.mem_cons]; exact .inl trivial)
    let headerData := execution ⟨headerFrame.box, headerControls, priorWorld⟩
      (by simp only [frames, List.mem_cons]; exact .inr (.inl trivial))
    let childExecution : child.ExecutionFrames P base caps frontier :=
      fun occurrence member => execution occurrence (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
    have childGenerated : whole.SourceGenerated P base caps := {
      wellFormed := child.wellFormed
      ambient := by have ambient := generated.ambient; rw [RawGeneratedTypeRoute.Ambient.eq_def] at ambient; exact ambient
      sources := by
        have sources := generated.sources
        rw [RawGeneratedTypeRoute.AllSources.eq_def] at sources
        exact sources.2.2
      frames := fun boxed member => generated.frames boxed
        (by rw [RawGeneratedTypeRoute.frames.eq_def]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)) }
    let childData := child.controlledDataOfExecution childGenerated childExecution
    let history : OriginalApplyPiHistory env registry target commonLeft commonRight
        (originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph)
        (originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph) :=
      ⟨sourceOrdered, headerOrdered, sourceBelow, headerDomain, rfl, sourceFrame, headerFrame, whole⟩
    let application := originalCallWorld sourceControls .fundamental
      (.app hu hv (.ref domain) body function argument result) sourceWorld
    let header := originalCallWorld headerControls .fundamental
      (.pi hcu hdv (.ref headerDomain) headerBody) priorWorld
    have sourceSub : [application].Sublist (child.calls ++ [application, application, header, header]) := by simp
    have headerSub : [header].Sublist (child.calls ++ [application, application, header, header]) := by simp
    have sourceSmall := callBelow_of_sublist (sourceSub.append_left frontier) smaller
    have headerSmall := callBelow_of_sublist (headerSub.append_left frontier) smaller
    have sourceSponsored : Sponsored frontier [application] :=
      fun world member => sponsored world (sourceSub.subset member)
    have headerSponsored : Sponsored frontier [header] :=
      fun world member => sponsored world (headerSub.subset member)
    have childSponsored : Sponsored frontier child.calls :=
      fun world member => sponsored world (List.mem_append_left _ member)
    have childSmaller := callBelow_of_sublist
      ((List.sublist_append_left child.calls [application, application, header, header]).append_left frontier) smaller
    obtain ⟨output, ⟨outputData⟩⟩ := history.replayApplicationReplyWorldStep
      initial domain body function argument result hu hv location sourceGraph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      sourceControls headerControls frontier sourceData.generation headerData.generation sourceWorld priorWorld
      sourceData.covered headerData.covered sourceData.replayable headerData.replayable
      sourceData.controlled sourceData.hereditary headerData.controlled headerData.hereditary sourceData.compatible
      (by simpa only [child.controls_match.1, child.controls_match.2] using headerData.compatible)
      childData child (child.controlledDataOfExecution_coherent childGenerated childExecution)
      noBinders sourceBound ownerWorld sourceAdmission henv hscoped headerBelow formed
      sourceSponsored headerSponsored
      (fun reserve lower => unary reserve (lower.trans sourceSmall))
      (fun reserve lower => bank reserve (lower.trans sourceSmall))
      (fun reserve lower => unary reserve (lower.trans headerSmall))
      (fun answer data sorted => ih childGenerated childExecution childSponsored childSmaller answer data sorted)
      incoming incomingData sorted
    have reserveEq : claimedSeedReserve = history.argumentSeedReserve := by
      simpa only [history, OriginalApplyPiHistory.argumentSeedReserve, OriginalApplyPiHistory.argumentDomainRoute,
        RawGeneratedTypeRoute.reserve, OriginalApplyPiHistory.final, originalNativePiRouteSide,
        EndpointState.dependencyOrigin, originalApplicationTypeRouteSide,
        OriginalApplicationTypeRouteSide.argumentDisplay, OriginalApplicationTypeRouteSide.pi,
        OriginalPiTypeRouteSide.domainDisplay, OriginalNestedDisplay.formationDisplay,
        OriginalNestedDisplay.ofOccurrence] using claim
    cases reserveEq
    refine ⟨output, ?_⟩
    exact ⟨by simpa only [history, OriginalApplyPiHistory.outputWorld,
      OriginalApplyPiHistory.argumentSeedWorld, originalApplicationTypeRouteSide,
      OriginalApplyPiHistory.final, OriginalApplyPiHistory.outputEnvironment,
      OriginalApplyPiHistory.destination, childData, controlledDataOfExecution_inputs] using outputData⟩

/-- Execute the retained positive reserve without changing its sponsor frontier. -/
theorem replayWorld
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld)
    (generated : route.SourceGenerated P base caps)
    (execution : boundary.ExecutionFrames P base caps frontier)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (parent : List (World strata.rules.length))
    (bank : WorldBoundedCallBank env U registry strata P parent)
    (unary : WorldBoundedUnaryCallBank env U registry strata P parent)
    (sponsored : Sponsored frontier (route.worldReserve inputs).worlds)
    (smaller : CallBelow strata.rules.length (frontier ++ (route.worldReserve inputs).worlds) parent)
    {n : Nat} {start : VExpr} {profile : Profile n}
    (incoming : AmbientBoundedParameterReply base caps start left commonLeft commonRight
      profile (environmentCost initial))
    (incomingData : WorldParameterReplyData (P := P) leftControls leftWorld frontier incoming)
    (sorted : profile.HasType (.sort true)) :
    ∃ output : AmbientBoundedParameterReply base caps start right commonLeft commonRight profile
      (environmentCost final),
      Nonempty (WorldParameterReplyData (P := P) rightControls rightWorld frontier output) := by
  apply boundary.replayWorldCalls generated execution henv hscoped formed parent bank unary
    (by simpa only [boundary.calls_eq_reserve] using sponsored)
    (by simpa only [boundary.calls_eq_reserve] using smaller) incoming incomingData sorted

end RawGeneratedTypeRoute.WorldBoundary
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
