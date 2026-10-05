import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyApplicationRouteSide
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyTelescopeCursor

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

private theorem emptyPrefixEnvironment
    (ordered : sourceEnv.Ordered)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (location : Located root node) (empty : location.binderPrefix = [])
    (initial : List Closure) : location.dependencyEnvironment ordered initial = initial := by
  induction location with
  | here => rfl
  | expose parent ih | convertTerm parent ih | appFunction parent ih | appArgument parent ih
  | appDomain parent ih | appResult parent ih | lamDomain parent ih | piDomain parent ih
  | projField parent ih | projMajor parent ih | assignedFormation parent ih | appPiFormation parent ih => exact ih empty
  | lamBody parent _ | lamCodomain parent _ | appCodomain parent _ | piBody parent _ => cases empty

section
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
  (initial : ContextDerivation sourceEnv U source)
  (graph : OriginalCaptureMap (common := common) initial raw)
  (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
  (index : Nat) (selected : arguments[index]? = some argument)
  {headerRoot : EndpointRef headerEnv U headerRootSource headerExpression headerType}
  (headerInitial : ContextDerivation headerEnv U headerRootSource)
  (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
  (headerBody : EndpointState headerEnv U (C :: headerSource) D (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
  (headerGraph : OriginalCaptureMap (common := common) (headerLocation.contextDerivation headerInitial) headerRaw)

local notation "left" => assignedFamilyRouteSide major initial graph index selected
local notation "right" => originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph

include field in
/-- Select the next actual source application and parse the next original
header binder. Only the original induction call bank and its checked budget
remain external; source adjacency, the next frame and header shape are
computed from the two retained finite spines. -/
theorem familyParameterSuccessor
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    {base : OriginalCaptureBase env U registry target}
    (generated : history.Generated base commonCaps)
    (frameGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.realization.frame.raw)
    (sourceFrameEq : history.sourceFrame = assignedFamilyRouteFrame major initial graph index selected frame)
    (frameBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (frame.realization.frame.dependencyEnvironment ordered) ≤ environmentCost ownerInitial)
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (calls : history.ApplicationCalls (left).initial (left).domain (left).body (left).function (left).argument (left).result
      (left).hu (left).hv (left).location (left).graph
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph limit)
    (historyCalls : history.whole.Calls base commonCaps limit)
    (scheduled : history.schedule < limit)
    (cursor : FamilyTelescopeCursor domains tail index right)
    (remaining : index + 1 < domains.length)
    (sourceLength : domains.length ≤ arguments.length) :
    let nextSelected : arguments[index+1]? = some arguments[index+1] :=
      List.getElem?_eq_getElem (Nat.lt_of_lt_of_le remaining sourceLength)
    let next := assignedFamilyRouteSide major initial graph (index+1) nextSelected
    ∃ nextHeader : OriginalPiTypeRouteSide U common,
      ∃ nextHistory : OriginalApplyPiHistory env registry target commonLeft commonRight next nextHeader,
        nextHistory.Generated base commonCaps ∧
        nextHistory.sourceFrame = assignedFamilyRouteFrame major initial graph (index+1) nextSelected frame ∧
        nextHeader.sourceEnv = headerEnv ∧ nextHeader.sourceEnv ≤ env ∧
        nextHeader.raw = headerRaw.cons (argument.subst raw) ∧
        FamilyTelescopeCursor domains tail (index+1) nextHeader := by
  have sourceNext := Nat.lt_of_lt_of_le remaining sourceLength
  let nextSelected : arguments[index+1]? = some arguments[index+1] := List.getElem?_eq_getElem sourceNext
  let next := assignedFamilyRouteSide major initial graph (index+1) nextSelected
  let nextFrame := assignedFamilyRouteFrame major initial graph (index+1) nextSelected frame
  have sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost ((left).location.dependencyEnvironment ordered ownerInitial) := by
    intro ordered
    rw [sourceFrameEq, assignedFamilyRouteFrame_environment,
      emptyPrefixEnvironment ordered (left).location (assignedFamilyRouteSide_prefix major initial graph index selected)]
    exact frameBound ordered
  obtain ⟨nextDomain, nextBody, headerShape, cursorNext⟩ := cursor.next remaining
  obtain ⟨nextHeader, nextHistory, nextGenerated, frameEq, headerEnvEq, below, domainEq, bodyEq, rawEq⟩ :=
    history.nextParameterGenerated (field := field) (left).initial (left).domain (left).body (left).function (left).argument (left).result
      (left).hu (left).hv (left).location (left).graph headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      generated (assignedFamilyRouteSide_prefix major initial graph index selected) sourceBound
      henv hscoped headerBelow formed calls historyCalls scheduled next history.leftOrdered history.leftBelow nextFrame
      (assignedFamilyRouteFrame_generated major initial graph (index+1) nextSelected frame frameGenerated)
      (assignedFamilyRouteSide_adjacent major initial graph index selected nextSelected) headerShape
  exact ⟨nextHeader, nextHistory, nextGenerated, frameEq, headerEnvEq, below, rawEq,
    cursorNext nextHeader domainEq bodyEq⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
