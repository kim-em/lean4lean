import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRouteProvenance

/-! Executable world boundaries for finite original routes. These indices
retain actual controls and annotated environments at every composition join.
No semantic replay result is part of this structural evidence. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Exact provenance for the seed reserve of one actual application. The
claim is checked against original endpoint closures before any transport. -/
noncomputable def applicationSeedWorld
    {strata : EquationStratification env}
    {sourceEnv headerEnv : VEnv}
    (argument : EndpointState sourceEnv U source a A)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
    (sourceControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (sourceWorld : WorldEnvironmentProvenance strata U sourceEnvironment)
    (priorWorld : WorldEnvironmentProvenance strata U headerEnvironment)
    (wholeWorld : WorldEnvironmentProvenance strata U wholeReserve)
    (claim : claimedSeedReserve =
      ([Closure.bundle (.close (argument.typeFormation.node.dependencyOrigin sourceControls.ordered) sourceEnvironment)
        (.close (domain.dependencyOrigin sourceControls.ordered) sourceEnvironment)] ++ wholeReserve) ++
      [Closure.bundle (.close (headerDomain.dependencyOrigin headerControls.ordered) headerEnvironment)
        (.close (headerDomain.dependencyOrigin headerControls.ordered) headerEnvironment)]) :
    WorldEnvironmentProvenance strata U claimedSeedReserve :=
  claim.symm ▸
    ((WorldEnvironmentProvenance.cons
      (.bundle (.scheduled .expressionReindex argument.typeFormation.node sourceControls sourceWorld)
        (.scheduled .expressionReindex (.ref domain) sourceControls sourceWorld)) .nil).append wholeWorld).append
      (.cons (.bundle (.scheduled .expressionReindex (.ref headerDomain) headerControls priorWorld)
        (.scheduled .expressionReindex (.ref headerDomain) headerControls priorWorld)) .nil)

/-- One concrete stored frame occurrence with its execution baseline. Repeated
boxes remain separate entries when the same raw frame has different annotations. -/
structure WorldBoundaryFrame
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target common : List VExpr) (commonLeft commonRight : Subst)
    (strata : EquationStratification env) where
  box : OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight
  controls : OriginalWorldControls strata box.sourceEnv
  world : WorldEnvironmentProvenance strata U
    (box.frame.realization.frame.dependencyEnvironment controls.ordered)

/-- A boundary identifies exact annotations, not only their costs or their
lists of descendants. Consequently transitivity has one actual middle world. -/
inductive RawGeneratedTypeRoute.WorldBoundary
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
    {commonLeft commonRight : Subst} {strata : EquationStratification env} :
    {leftExpression leftAssigned rightExpression rightAssigned : VExpr} →
    {left : OriginalNestedDisplay U common leftExpression leftAssigned} →
    {right : OriginalNestedDisplay U common rightExpression rightAssigned} →
    {initial final : List Closure} →
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) →
    route.WorldInputs strata →
    OriginalWorldControls strata left.sourceEnv → OriginalWorldControls strata right.sourceEnv →
    WorldEnvironmentProvenance strata U initial → WorldEnvironmentProvenance strata U final → Type where
  | identity
      (display : OriginalNestedDisplay U common expression assignedType)
      (controls : OriginalWorldControls strata display.sourceEnv)
      (world : WorldEnvironmentProvenance strata U environment) :
      WorldBoundary (strata := strata) (.identity display environment)
        (by rw [WorldInputs.eq_def]; exact ()) controls controls world world
  | same
      (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
      (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
      (leftControls : OriginalWorldControls strata left.sourceEnv)
      (rightControls : OriginalWorldControls strata right.sourceEnv)
      (leftWorld : WorldEnvironmentProvenance strata U initial)
      (rightWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf))
      (compatible : leftControls.cutoff = rightControls.cutoff ∧ leftControls.fuel = rightControls.fuel) :
      WorldBoundary (strata := strata) (.same left right lf rf initial frame)
        (leftControls, rightControls, leftWorld, rightWorld) leftControls rightControls leftWorld rightWorld
  | equality
      {context : ContextDerivation sourceEnv U source}
      (graph : OriginalCaptureMap (common := common) context raw)
      (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
      (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
      (controls : OriginalWorldControls strata sourceEnv)
      (world : WorldEnvironmentProvenance strata U environment) :
      WorldBoundary (strata := strata) (.equality graph original forward ordered below environment)
        (by rw [WorldInputs.eq_def]; exact (controls, world)) controls controls world world
  | typedEquality
      {context : ContextDerivation sourceEnv U source}
      (graph : OriginalCaptureMap (common := common) context raw)
      (original : Derivation sourceEnv U source A B assignedType)
      (left : OriginalNestedDisplay U common expression (.sort level))
      (same : expression = A.subst raw)
      (lf : left.sourceEnv.Ordered) (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
      (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
      (leftControls : OriginalWorldControls strata left.sourceEnv)
      (rightControls : OriginalWorldControls strata sourceEnv)
      (leftWorld : WorldEnvironmentProvenance strata U initial)
      (rightWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment ordered))
      (compatible : leftControls.cutoff = rightControls.cutoff ∧ leftControls.fuel = rightControls.fuel) :
      WorldBoundary (strata := strata) (.typedEquality graph original left same lf ordered below initial frame)
        (leftControls, rightControls, leftWorld, rightWorld) leftControls rightControls leftWorld rightWorld
  | assigned
      (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
      (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
      (leftControls : OriginalWorldControls strata left.sourceEnv)
      (rightControls : OriginalWorldControls strata right.sourceEnv)
      (leftWorld : WorldEnvironmentProvenance strata U initial)
      (rightWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf))
      (compatible : leftControls.cutoff = rightControls.cutoff ∧ leftControls.fuel = rightControls.fuel) :
      WorldBoundary (strata := strata) (.assigned left right lf rf initial frame)
        (leftControls, rightControls, leftWorld, rightWorld) leftControls rightControls leftWorld rightWorld
  | trans
      {left : OriginalNestedDisplay U common leftExpression leftAssigned}
      {middle : OriginalNestedDisplay U common middleExpression middleAssigned}
      {right : OriginalNestedDisplay U common rightExpression rightAssigned}
      {first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate}
      {second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final}
      {firstInputs : first.WorldInputs strata} {secondInputs : second.WorldInputs strata}
      {leftControls : OriginalWorldControls strata left.sourceEnv}
      {middleControls : OriginalWorldControls strata middle.sourceEnv}
      {rightControls : OriginalWorldControls strata right.sourceEnv}
      {leftWorld : WorldEnvironmentProvenance strata U initial}
      {middleWorld : WorldEnvironmentProvenance strata U intermediate}
      {rightWorld : WorldEnvironmentProvenance strata U final}
      (before : WorldBoundary first firstInputs leftControls middleControls leftWorld middleWorld)
      (after : WorldBoundary second secondInputs middleControls rightControls middleWorld rightWorld) :
      WorldBoundary (strata := strata) (first.trans second)
        (by rw [WorldInputs.eq_def]; exact (firstInputs, secondInputs)) leftControls rightControls leftWorld rightWorld
  | piDomain
      (left right : OriginalPiTypeRouteSide U common) (below : left.sourceEnv ≤ env)
      {whole : RawGeneratedTypeRoute env registry target commonLeft commonRight left.display right.display initial final}
      {inputs : whole.WorldInputs strata}
      {leftControls : OriginalWorldControls strata left.sourceEnv}
      {rightControls : OriginalWorldControls strata right.sourceEnv}
      {leftWorld : WorldEnvironmentProvenance strata U initial}
      {rightWorld : WorldEnvironmentProvenance strata U final}
      (boundary : WorldBoundary whole inputs leftControls rightControls leftWorld rightWorld) :
      WorldBoundary (strata := strata) (.piDomain left right below whole) inputs leftControls rightControls leftWorld rightWorld
  | applyPi
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
      (noBinders : location.binderPrefix = [])
      {headerRoot : EndpointRef headerEnv U headerRootSource headerRootExpression headerRootType}
      (headerInitial : ContextDerivation headerEnv U headerRootSource)
      (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
      (headerBody : EndpointState headerEnv U (C :: headerSource) D (.sort dv))
      (hcu : cu.WF U) (hdv : dv.WF U)
      (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
      (headerGraph : OriginalCaptureMap (common := common) (headerLocation.contextDerivation headerInitial) headerRaw)
      (sourceOrdered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
      (sourceBelow : sourceEnv ≤ env) (headerBelow : headerEnv ≤ env)
      (sourceFrame : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight)
      (headerFrame : OriginalTypeRouteFrame env registry target headerGraph commonLeft commonRight)
      (ownerInitial : List Closure)
      (sourceBound : ∀ ordered : sourceEnv.Ordered,
        environmentCost (sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
          environmentCost (location.dependencyEnvironment ordered ownerInitial))
      (whole : RawGeneratedTypeRoute env registry target commonLeft commonRight
        (originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph).pi.display
        (originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph).display
        (sourceFrame.realization.frame.dependencyEnvironment sourceOrdered)
        (headerFrame.realization.frame.dependencyEnvironment headerOrdered))
      (claimedSeedReserve : List Closure)
      (sourceControls : OriginalWorldControls strata sourceEnv)
      (headerControls : OriginalWorldControls strata headerEnv)
      (sourceWorld : WorldEnvironmentProvenance strata U (sourceFrame.realization.frame.dependencyEnvironment sourceOrdered))
      (priorWorld : WorldEnvironmentProvenance strata U (headerFrame.realization.frame.dependencyEnvironment headerOrdered))
      (ownerWorld : WorldEnvironmentProvenance strata U ownerInitial)
      (sourceAdmission : Covered (@EquationControlMeasure.Less strata.rules.length)
        sourceWorld.worlds ownerWorld.worlds)
      (wholeInputs : whole.WorldInputs strata)
      (boundary : WorldBoundary whole wholeInputs sourceControls headerControls sourceWorld priorWorld)
      (claim : claimedSeedReserve =
        ([Closure.bundle
          (.close (argument.typeFormation.node.dependencyOrigin sourceOrdered) (sourceFrame.realization.frame.dependencyEnvironment sourceOrdered))
          (.close (domain.dependencyOrigin sourceOrdered) (sourceFrame.realization.frame.dependencyEnvironment sourceOrdered))] ++ whole.reserve) ++
        [Closure.bundle (.close (headerDomain.dependencyOrigin headerOrdered) (headerFrame.realization.frame.dependencyEnvironment headerOrdered))
          (.close (headerDomain.dependencyOrigin headerOrdered) (headerFrame.realization.frame.dependencyEnvironment headerOrdered))]) :
      WorldBoundary (strata := strata)
        (.applyPi (field := field) initial domain body function argument result hu hv location sourceGraph noBinders
          headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph sourceOrdered headerOrdered
          sourceBelow headerBelow sourceFrame headerFrame ownerInitial sourceBound whole claimedSeedReserve)
        (sourceControls, headerControls, sourceWorld, priorWorld, wholeInputs)
        sourceControls headerControls sourceWorld
        (.groupHistory field major headerDomain sourceControls headerControls ownerWorld priorWorld
          (applicationSeedWorld argument domain headerDomain sourceControls headerControls sourceWorld priorWorld
            (whole.worldReserve wholeInputs) claim))

namespace RawGeneratedTypeRoute.WorldBoundary

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
  {commonLeft commonRight : Subst}
  {left : OriginalNestedDisplay U common leftExpression leftAssigned}
  {right : OriginalNestedDisplay U common rightExpression rightAssigned}
  {strata : EquationStratification env}
  {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
  {inputs : route.WorldInputs strata}
  {leftControls : OriginalWorldControls strata left.sourceEnv}
  {rightControls : OriginalWorldControls strata right.sourceEnv}
  {leftWorld : WorldEnvironmentProvenance strata U initial}
  {rightWorld : WorldEnvironmentProvenance strata U final}

/-- The exact primitive frame occurrences used by the execution boundary. -/
noncomputable def frames
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld) :
    List (WorldBoundaryFrame env U registry target common commonLeft commonRight strata) :=
  by
  induction boundary with
  | identity | equality => exact []
  | same _ _ _ _ frame _ controls _ world _ => exact [⟨frame.box, controls, world⟩]
  | typedEquality _ _ _ _ _ _ _ frame _ controls _ world _ => exact [⟨frame.box, controls, world⟩]
  | assigned _ _ _ _ frame _ controls _ world _ => exact [⟨frame.box, controls, world⟩]
  | trans _ _ before after => exact before ++ after
  | piDomain _ _ _ _ child => exact child
  | applyPi initial domain body function argument result hu hv location sourceGraph noBinders
      headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
      sourceOrdered headerOrdered sourceBelow headerBelow sourceFrame headerFrame ownerInitial sourceBound
      whole claimedSeedReserve sourceControls headerControls sourceWorld priorWorld ownerWorld sourceAdmission wholeInputs
      boundary claim child =>
      exact ⟨sourceFrame.box, sourceControls, sourceWorld⟩ ::
        ⟨headerFrame.box, headerControls, priorWorld⟩ :: child

/-- Forgetting annotations recovers the exact raw frame list, including
multiplicity and order, rather than only a membership relation. -/
theorem frames_boxes
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld) :
    boundary.frames.map WorldBoundaryFrame.box = route.frames := by
  induction boundary with
  | identity | equality | same | assigned | typedEquality =>
    simp only [frames, List.map_nil, List.map_cons, RawGeneratedTypeRoute.frames]
  | trans before after ihBefore ihAfter =>
    change List.map WorldBoundaryFrame.box (before.frames ++ after.frames) = _
    rw [List.map_append, ihBefore, ihAfter]
    conv => rhs; rw [RawGeneratedTypeRoute.frames.eq_def]
  | piDomain _ _ _ _ ih => simpa only [frames, RawGeneratedTypeRoute.frames] using ih
  | applyPi =>
    simp only [frames, List.map_cons, RawGeneratedTypeRoute.frames]
    congr 2

end RawGeneratedTypeRoute.WorldBoundary

/-- The boundary evidence includes the only nontrivial well-formedness
condition: every application reserve is exactly its finite child history. -/
theorem RawGeneratedTypeRoute.WorldBoundary.wellFormed
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
    {commonLeft commonRight : Subst}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {strata : EquationStratification env}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    {inputs : route.WorldInputs strata}
    {leftControls : OriginalWorldControls strata left.sourceEnv}
    {rightControls : OriginalWorldControls strata right.sourceEnv}
    {leftWorld : WorldEnvironmentProvenance strata U initial}
    {rightWorld : WorldEnvironmentProvenance strata U final}
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld) :
    route.WellFormed := by
  induction boundary with
  | identity | same | equality | assigned | typedEquality => rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
  | trans before after ihBefore ihAfter => rw [RawGeneratedTypeRoute.WellFormed.eq_def]; exact ⟨ihBefore, ihAfter⟩
  | piDomain _ _ _ _ ih => rw [RawGeneratedTypeRoute.WellFormed.eq_def]; exact ih
  | applyPi =>
    rw [RawGeneratedTypeRoute.WellFormed.eq_def]
    exact ⟨by assumption, by assumption⟩

/-- World execution preserves the caller's control prefix even when it
changes declaration source, as every actual retained-header producer does. -/
theorem RawGeneratedTypeRoute.WorldBoundary.controls_match
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}
    {commonLeft commonRight : Subst}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {strata : EquationStratification env}
    {route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final}
    {inputs : route.WorldInputs strata}
    {leftControls : OriginalWorldControls strata left.sourceEnv}
    {rightControls : OriginalWorldControls strata right.sourceEnv}
    {leftWorld : WorldEnvironmentProvenance strata U initial}
    {rightWorld : WorldEnvironmentProvenance strata U final}
    (boundary : route.WorldBoundary inputs leftControls rightControls leftWorld rightWorld) :
    leftControls.cutoff = rightControls.cutoff ∧ leftControls.fuel = rightControls.fuel := by
  induction boundary with
  | identity | equality => exact ⟨rfl, rfl⟩
  | same | assigned | typedEquality => assumption
  | trans before after ihBefore ihAfter => exact ⟨ihBefore.1.trans ihAfter.1, ihBefore.2.trans ihAfter.2⟩
  | piDomain _ _ _ _ ih => exact ih
  | applyPi => assumption

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
