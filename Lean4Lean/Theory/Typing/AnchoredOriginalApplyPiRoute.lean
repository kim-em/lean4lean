import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiHistoryGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiSeedHistory

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace OriginalApplyPiHistory
section
variable {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
  {commonLeft commonRight : Subst}
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  {headerRoot : EndpointRef headerEnv U headerRootSource headerExpression headerType}
  (headerInitial : ContextDerivation headerEnv U headerRootSource)
  (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
  (headerBody : EndpointState headerEnv U (C :: headerSource) D (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
  (headerGraph : OriginalCaptureMap (common := common) (headerLocation.contextDerivation headerInitial) headerRaw)

local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph

/-- Specialize an actual whole-Pi history at its retained source argument.
The next capture envelope is computed from the complete seed history. -/
noncomputable def applyRoute
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = [])
    (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env) :
    RawGeneratedTypeRoute env registry target commonLeft commonRight (sourceSide).resultDisplay
      ((headerSide).capturedBody headerDomain rfl sourceSide)
      (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)
      (groupCaptureHistoryReserve field major headerDomain history.leftOrdered history.rightOrdered
        ownerInitial history.final history.argumentSeedReserve) :=
  .applyPi (field := field) initial domain body function argument result hu hv location sourceGraph noBinders
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    history.leftOrdered history.rightOrdered history.leftBelow headerBelow
    history.sourceFrame history.headerFrame ownerInitial sourceBound history.whole history.argumentSeedReserve

theorem applyRoute_frames
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = [])
    (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env) :
    (history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow).frames = history.sourceFrame.box :: history.headerFrame.box :: history.whole.frames := by
  rw [applyRoute, RawGeneratedTypeRoute.frames.eq_def]

theorem applyRoute_reserve
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = [])
    (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env) : (history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow).reserve = history.reserve := by
  rw [applyRoute, RawGeneratedTypeRoute.reserve.eq_def]
  rfl

theorem applyRoute_schedule
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = [])
    (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env) : (history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow).schedule = history.schedule := by
  rw [applyRoute, RawGeneratedTypeRoute.schedule.eq_def]
  rfl

theorem applyRoute_wellFormed
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = [])
    (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env)
    (wholeFormed : history.whole.WellFormed) : (history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow).WellFormed := by
  rw [applyRoute, RawGeneratedTypeRoute.WellFormed.eq_def]
  refine ⟨wholeFormed, ?_⟩
  have headerEq : history.rightDomain = headerDomain :=
    (EndpointState.ref.inj history.rightDomainEq).symm
  simp only [argumentSeedReserve, argumentDomainRoute, RawGeneratedTypeRoute.reserve]
  simp only [headerEq, originalNativePiRouteSide, EndpointState.dependencyOrigin, final]

theorem applyRoute_generated
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    (noBinders : location.binderPrefix = [])
    (ownerInitial : List Closure)
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (headerBelow : headerEnv ≤ env)
    (generated : history.Generated base commonCaps) : (history.applyRoute (field := field) initial domain body function argument result hu hv location sourceGraph
  headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow).Generated base commonCaps := by
  refine ⟨history.applyRoute_wellFormed (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow
    generated.whole.wellFormed, ?_⟩
  intro boxed member
  rw [history.applyRoute_frames (field := field) initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph noBinders ownerInitial sourceBound headerBelow] at member
  simp only [List.mem_cons] at member
  rcases member with rfl | rfl | member
  · exact generated.source
  · exact generated.header
  · exact generated.whole.frames boxed member

end
end OriginalApplyPiHistory
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
