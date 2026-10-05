import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGraph
import Lean4Lean.Theory.Typing.AnchoredOriginalTypeRouteSyntax
import Lean4Lean.Theory.Typing.AnchoredOriginalGroupBaselineBudget

/-! Query-independent original alignment data below generated-frame proofs.
The reserve contains actual original endpoint/equality closures and actual
baseline frame environments. No semantic callback or completed alignment
is stored in the route. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

structure OriginalTypeRouteFrame
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (commonLeft commonRight : Subst) where
  locals : List Nat
  available : Valuation
  realization : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available
  closed : available.AtomClosed

structure OriginalTypeRouteFrameBox
    (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target common : List VExpr)
    (commonLeft commonRight : Subst) where
  sourceEnv : VEnv
  source : List VExpr
  context : ContextDerivation sourceEnv U source
  raw : Subst
  graph : OriginalCaptureMap (common := common) context raw
  frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight

def OriginalTypeRouteFrame.box
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) :
    OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight :=
  ⟨sourceEnv, source, context, raw, graph, frame⟩

inductive RawGeneratedTypeRoute
    (env : VEnv) {U : Nat} (registry : CanonicalHead.Registry) (target : List VExpr) {common : List VExpr}
    (commonLeft commonRight : Subst) :
    {leftExpression leftAssigned rightExpression rightAssigned : VExpr} →
    OriginalNestedDisplay U common leftExpression leftAssigned →
    OriginalNestedDisplay U common rightExpression rightAssigned → List Closure → List Closure → Type where
  | identity (display : OriginalNestedDisplay U common expression assigned) (environment : List Closure) :
      RawGeneratedTypeRoute env registry target commonLeft commonRight display display environment environment
  | same
      (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered)
      (environment : List Closure)
      (rightFrame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight) :
      RawGeneratedTypeRoute env registry target commonLeft commonRight left right environment
        (rightFrame.realization.frame.dependencyEnvironment rightOrdered)
  | equality
      {context : ContextDerivation sourceEnv U source}
      (graph : OriginalCaptureMap (common := common) context raw)
      (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
      (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (environment : List Closure) :
      RawGeneratedTypeRoute env registry target commonLeft commonRight
        (graph.typeEqualityDisplay original forward) (graph.typeEqualityDisplay original (!forward))
        environment environment
  | typedEquality
      {context : ContextDerivation sourceEnv U source}
      (graph : OriginalCaptureMap (common := common) context raw)
      (original : Derivation sourceEnv U source A B assigned)
      (left : OriginalNestedDisplay U common expression (.sort level))
      (same : expression = A.subst raw)
      (leftOrdered : left.sourceEnv.Ordered) (ordered : sourceEnv.Ordered)
      (below : sourceEnv ≤ env) (environment : List Closure)
      (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) :
      RawGeneratedTypeRoute env registry target commonLeft commonRight
        left (graph.typeEqualityDisplay original false) environment
        (frame.realization.frame.dependencyEnvironment ordered)
  | trans
      (first : RawGeneratedTypeRoute env registry target commonLeft commonRight left middle initial intermediate)
      (second : RawGeneratedTypeRoute env registry target commonLeft commonRight middle right intermediate final) :
      RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final
  | assigned
      (left : OriginalNestedDisplay U common expression leftAssigned)
      (right : OriginalNestedDisplay U common expression rightAssigned)
      (leftOrdered : left.sourceEnv.Ordered) (rightOrdered : right.sourceEnv.Ordered)
      (environment : List Closure)
      (rightFrame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight) :
      RawGeneratedTypeRoute env registry target commonLeft commonRight
        left.formationDisplay right.formationDisplay environment
        (rightFrame.realization.frame.dependencyEnvironment rightOrdered)
  | piDomain
      (left right : OriginalPiTypeRouteSide U common)
      (leftBelow : left.sourceEnv ≤ env)
      (route : RawGeneratedTypeRoute env registry target commonLeft commonRight
        left.display right.display initial final) :
      RawGeneratedTypeRoute env registry target commonLeft commonRight
        left.domainDisplay right.domainDisplay initial final

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
      (sourceGraph : OriginalCaptureMap (common := common)
        (location.contextDerivation initial) sourceRaw)
      (noBinders : location.binderPrefix = [])
      {headerRoot : EndpointRef headerEnv U headerRootSource headerRootExpression headerRootType}
      (headerInitial : ContextDerivation headerEnv U headerRootSource)
      (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
      (headerBody : EndpointState headerEnv U (C :: headerSource) D (.sort dv))
      (hcu : cu.WF U) (hdv : dv.WF U)
      (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
      (headerGraph : OriginalCaptureMap (common := common)
        (headerLocation.contextDerivation headerInitial) headerRaw)
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
      (claimedSeedReserve : List Closure) :
      RawGeneratedTypeRoute env registry target commonLeft commonRight
        (originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph).resultDisplay
        ((originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph).capturedBody
          headerDomain rfl
          (originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph))
        (sourceFrame.realization.frame.dependencyEnvironment sourceOrdered)
        (groupCaptureHistoryReserve field major headerDomain sourceOrdered headerOrdered ownerInitial
          (headerFrame.realization.frame.dependencyEnvironment headerOrdered) claimedSeedReserve)

variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target common : List VExpr}

noncomputable def RawGeneratedTypeRoute.frames
    {leftExpression leftAssigned rightExpression rightAssigned : VExpr}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) :
    List (OriginalTypeRouteFrameBox env U registry target common commonLeft commonRight) :=
  match route with
  | .identity .. | .equality .. => []
  | .same _ _ _ _ _ frame => [frame.box]
  | .typedEquality (frame := frame) .. => [frame.box]
  | .assigned _ _ _ _ _ frame => [frame.box]
  | .trans first second => first.frames ++ second.frames
  | .piDomain _ _ _ route => route.frames
  | .applyPi (sourceFrame := sourceFrame) (headerFrame := headerFrame) (whole := whole) .. =>
      sourceFrame.box :: headerFrame.box :: whole.frames
termination_by sizeOf route

/-- Each comparison is charged as the SUM of its two actual closures;
independent route edges share only the outer maximum. -/
noncomputable def RawGeneratedTypeRoute.reserve
    {leftExpression leftAssigned rightExpression rightAssigned : VExpr}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) : List Closure :=
  match route with
  | .identity .. => []
  | .same left right lf rf initial frame =>
      [.bundle (.close (left.node.dependencyOrigin lf) initial)
        (.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf))]
  | .equality _ original _ ordered _ initial => [.close (original.dependencyOrigin ordered) initial]
  | .typedEquality (original := original) (left := left) (leftOrdered := lf)
      (ordered := ordered) (environment := initial) (frame := frame) .. =>
      let equality := Closure.close (original.dependencyOrigin ordered)
        (frame.realization.frame.dependencyEnvironment ordered)
      [.bundle (.close (left.node.dependencyOrigin lf) initial) equality, equality]
  | .assigned left right lf rf initial frame =>
      [.bundle (.close (left.node.dependencyOrigin lf) initial)
        (.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf))]
  | .trans first second => first.reserve ++ second.reserve
  | .piDomain _ _ _ route => route.reserve
  | .applyPi (domain := domain) (body := body) (function := function) (argument := argument)
      (result := result) (hu := hu) (hv := hv) (headerDomain := headerDomain) (headerBody := headerBody)
      (hcu := hcu) (hdv := hdv) (sourceOrdered := sourceOrdered) (headerOrdered := headerOrdered)
      (sourceFrame := sourceFrame) (headerFrame := headerFrame) (whole := whole) .. =>
      let application := Closure.close
        ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin sourceOrdered)
        (sourceFrame.realization.frame.dependencyEnvironment sourceOrdered)
      let header := Closure.close
        ((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin headerOrdered)
        (headerFrame.realization.frame.dependencyEnvironment headerOrdered)
      whole.reserve ++ [.bundle application application, .bundle header header]
termination_by sizeOf route

noncomputable def RawGeneratedTypeRoute.schedule
    {leftExpression leftAssigned rightExpression rightAssigned : VExpr}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) : Nat :=
  match route with
  | .identity .. => 0
  | .same left right lf rf initial frame =>
      richSchedule .expressionReindex
        ((Closure.close (left.node.dependencyOrigin lf) initial).cost +
         (Closure.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf)).cost)
  | .equality _ original _ ordered _ initial =>
      richSchedule .fundamental (Closure.close (original.dependencyOrigin ordered) initial).cost
  | .typedEquality (original := original) (left := left) (leftOrdered := lf)
      (ordered := ordered) (environment := initial) (frame := frame) .. =>
      let equality := Closure.close (original.dependencyOrigin ordered)
        (frame.realization.frame.dependencyEnvironment ordered)
      max (richSchedule .expressionReindex
        ((Closure.close (left.node.dependencyOrigin lf) initial).cost + equality.cost))
        (richSchedule .fundamental equality.cost)
  | .assigned left right lf rf initial frame =>
      richSchedule .assignedComparison
        ((Closure.close (left.node.dependencyOrigin lf) initial).cost +
         (Closure.close (right.node.dependencyOrigin rf) (frame.realization.frame.dependencyEnvironment rf)).cost)
  | .trans first second => max first.schedule second.schedule
  | .piDomain _ _ _ route => route.schedule
  | .applyPi (domain := domain) (body := body) (function := function) (argument := argument)
      (result := result) (hu := hu) (hv := hv) (headerDomain := headerDomain) (headerBody := headerBody)
      (hcu := hcu) (hdv := hdv) (sourceOrdered := sourceOrdered) (headerOrdered := headerOrdered)
      (sourceFrame := sourceFrame) (headerFrame := headerFrame) (whole := whole) .. =>
      max whole.schedule (max
        (richSchedule .fundamental (Closure.close
          ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin sourceOrdered)
          (sourceFrame.realization.frame.dependencyEnvironment sourceOrdered)).cost)
        (richSchedule .fundamental (Closure.close
          ((EndpointState.pi hcu hdv (.ref headerDomain) headerBody).dependencyOrigin headerOrdered)
          (headerFrame.realization.frame.dependencyEnvironment headerOrdered)).cost))
termination_by sizeOf route

/-- Structural validation of claimed capture envelopes. It contains only
exact finite-list equality and validation of recursive histories. -/
noncomputable def RawGeneratedTypeRoute.WellFormed
    {leftExpression leftAssigned rightExpression rightAssigned : VExpr}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) : Prop :=
  match route with
  | .identity .. | .same .. | .equality .. | .assigned .. | .typedEquality .. => True
  | .trans first second => first.WellFormed ∧ second.WellFormed
  | .piDomain _ _ _ route => route.WellFormed
  | .applyPi (initial := initial) (domain := domain) (body := body) (function := function)
      (argument := argument) (result := result) (hu := hu) (hv := hv) (location := location)
      (sourceGraph := sourceGraph) (headerDomain := headerDomain)
      (sourceOrdered := sourceOrdered) (headerOrdered := headerOrdered)
      (sourceFrame := sourceFrame) (headerFrame := headerFrame) (whole := whole)
      (claimedSeedReserve := claimedSeedReserve) .. =>
      let side := originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
      let sourceEnvironment := sourceFrame.realization.frame.dependencyEnvironment sourceOrdered
      let headerEnvironment := headerFrame.realization.frame.dependencyEnvironment headerOrdered
      whole.WellFormed ∧ claimedSeedReserve =
        ([Closure.bundle (.close (side.argumentDisplay.formationDisplay.node.dependencyOrigin sourceOrdered) sourceEnvironment)
          (.close (side.pi.domainDisplay.node.dependencyOrigin sourceOrdered) sourceEnvironment)] ++ whole.reserve) ++
        [Closure.bundle (.close (headerDomain.dependencyOrigin headerOrdered) headerEnvironment)
          (.close (headerDomain.dependencyOrigin headerOrdered) headerEnvironment)]
termination_by sizeOf route

private theorem environment_append (left right : List Closure) :
    environmentCost (left ++ right) = max (environmentCost left) (environmentCost right) := by
  induction left with
  | nil => simp [environmentCost]
  | cons head tail ih => simp only [List.cons_append, environmentCost, ih, Nat.max_assoc]

theorem RawGeneratedTypeRoute.schedule_le
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    (route : RawGeneratedTypeRoute env registry target commonLeft commonRight left right initial final) :
    route.schedule ≤ richSchedule .expressionReindex (environmentCost route.reserve) := by
  induction route with
  | identity => simp [schedule]
  | same => simp [schedule, reserve, environmentCost, Closure.cost]
  | equality => simp [schedule, reserve, environmentCost, Closure.cost, richSchedule, RichPhase.code]
  | assigned => simp [schedule, reserve, environmentCost, Closure.cost, richSchedule, RichPhase.code]
  | typedEquality =>
    simp only [schedule, reserve, environmentCost, Closure.cost, richSchedule, RichPhase.code]
    omega
  | piDomain _ _ _ _ ih =>
    rw [schedule.eq_def, reserve.eq_def]
    exact ih
  | applyPi =>
    rename_i whole claimedSeedReserve ih
    rw [schedule.eq_def, reserve.eq_def]
    simp only [environment_append, environmentCost,
      Closure.cost, Nat.max_zero, richSchedule, RichPhase.code] at ih ⊢
    omega
  | trans first second hl hr =>
    rw [schedule, reserve, environment_append]
    apply Nat.max_le.mpr
    constructor
    · exact Nat.le_trans hl (by
        change 3 * _ + 2 ≤ 3 * _ + 2
        exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.le_max_left _ _)) 2)
    · exact Nat.le_trans hr (by
        change 3 * _ + 2 ≤ 3 * _ + 2
        exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (Nat.le_max_right _ _)) 2)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
