import Lean4Lean.Theory.Typing.AnchoredOriginalGenericApplicationReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericReindexCode
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiDisplays

/-! Application R after recursive original captures. The child displays
are built from actual routes from the retained roots. Their source syntax,
frames, and closure costs are preserved before any target substitution. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- One exact source query at a pair of already produced frames. The
destination frame may have been selected for this very query. -/
def OriginalGeneratedDisplayObservationAnswer
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U displayed expression leftType}
    {right : OriginalNestedDisplay U displayed expression rightType}
    (_leftFrame : OriginalGeneratedDisplayFrame base left common leftLocals leftAvailable)
    (_rightFrame : OriginalGeneratedDisplayFrame base right common rightLocals rightAvailable)
    (_query : RichObs left.sourceEnv env U registry target left.node leftLocals
      (left.raw.comp common) profile footprint) : Prop :=
  Nonempty (RichGradedResult right.sourceEnv env U registry target right.node rightLocals
    (right.raw.comp common) rightAvailable profile)

/-- The observation channel at a fixed pair of actual source displays.
This is a local induction obligation, not an assertion that arbitrary
independently supplied frames have compatible resources. -/
def OriginalGeneratedDisplayObservationReindex
    {base : OriginalCaptureBase env U registry target}
    {left : OriginalNestedDisplay U displayed expression leftType}
    {right : OriginalNestedDisplay U displayed expression rightType}
    (_leftFrame : OriginalGeneratedDisplayFrame base left common leftLocals leftAvailable)
    (_rightFrame : OriginalGeneratedDisplayFrame base right common rightLocals rightAvailable) : Prop :=
  ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs left.sourceEnv env U registry target left.node leftLocals (left.raw.comp common) profile footprint →
    footprint.Available leftAvailable →
    Nonempty (RichGradedResult right.sourceEnv env U registry target right.node rightLocals
      (right.raw.comp common) rightAvailable profile)

section
variable
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {parent : EndpointState sourceEnv U source (.app f a) assigned}
    (location : Located root parent)
    (initial : ContextDerivation sourceEnv U rootSource)
    (graph : OriginalCaptureMap (common := displayed) (location.contextDerivation initial) raw)

noncomputable def applicationGeneratedSourceDisplay
    (functionEq : displayedFunction = f.subst raw)
    (argumentEq : displayedArgument = a.subst raw) :
    OriginalNestedDisplay U displayed (.app displayedFunction displayedArgument) (assigned.subst raw) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := .app f a
  sourceType := assigned
  context := location.contextDerivation initial
  node := parent
  provenance := .ofLocation location initial
  raw := raw
  graph := graph
  expression_eq := by simp only [subst, ← functionEq, ← argumentEq]
  type_eq := rfl

/-- Retain the parent's context verbatim; the route proves it is also the
actual child's original context. No reorigining of a semantic frame occurs. -/
noncomputable def applicationGeneratedFunctionSourceDisplay
    {A B : VExpr} {u v : VLevel}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {fn : EndpointState sourceEnv U source f (.forallE A B)}
    {arg : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (route : PrefixRoute sourceEnv U source (.app f a) parent (.app hu hv domain body fn arg result))
    (functionEq : displayedFunction = f.subst raw) :
    OriginalNestedDisplay U displayed displayedFunction ((VExpr.forallE A B).subst raw) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := f
  sourceType := .forallE A B
  context := location.contextDerivation initial
  node := fn
  provenance := {
    rootSource := rootSource
    rootExpression := rootExpression
    rootType := rootType
    root := root
    initial := initial
    location := .appFunction (route.locate location)
    context_eq := by exact (route.locate_contextDerivation location initial).symm }
  raw := raw
  graph := graph
  expression_eq := functionEq
  type_eq := rfl

noncomputable def applicationGeneratedArgumentSourceDisplay
    {A B : VExpr} {u v : VLevel}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {fn : EndpointState sourceEnv U source f (.forallE A B)}
    {arg : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (route : PrefixRoute sourceEnv U source (.app f a) parent (.app hu hv domain body fn arg result))
    (argumentEq : displayedArgument = a.subst raw) :
    OriginalNestedDisplay U displayed displayedArgument (A.subst raw) where
  sourceEnv := sourceEnv
  source := source
  sourceExpression := a
  sourceType := A
  context := location.contextDerivation initial
  node := arg
  provenance := {
    rootSource := rootSource
    rootExpression := rootExpression
    rootType := rootType
    root := root
    initial := initial
    location := .appArgument (route.locate location)
    context_eq := by exact (route.locate_contextDerivation location initial).symm }
  raw := raw
  graph := graph
  expression_eq := argumentEq
  type_eq := rfl

end

section
variable
    {base : OriginalCaptureBase env U registry target}
    {leftRoot : EndpointRef leftEnv U leftRootSource le lt}
    {rightRoot : EndpointRef rightEnv U rightRootSource re rt}
    {leftNode : EndpointState leftEnv U leftSource (.app f a) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.app g b) rightAssigned}
    (leftLocation : Located leftRoot leftNode) (rightLocation : Located rightRoot rightNode)
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftGraph : OriginalCaptureMap (common := displayed) (leftLocation.contextDerivation leftInitial) leftRaw)
    (rightGraph : OriginalCaptureMap (common := displayed) (rightLocation.contextDerivation rightInitial) rightRaw)
    (leftFunction : displayedFunction = f.subst leftRaw)
    (rightFunction : displayedFunction = g.subst rightRaw)
    (leftArgument : displayedArgument = a.subst leftRaw)
    (rightArgument : displayedArgument = b.subst rightRaw)

/-- Only the two actual child displays can be requested by this step.
All wrappers and original conversion routes are handled by the observation
worker; equality of arguments is derived from common source syntax. -/
theorem applicationGeneratedSourceObservationReindex
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftFrame : OriginalGeneratedDisplayFrame base
      (applicationGeneratedSourceDisplay leftLocation leftInitial leftGraph leftFunction leftArgument)
      common leftLocals leftAvailable)
    (rightFrame : OriginalGeneratedDisplayFrame base
      (applicationGeneratedSourceDisplay rightLocation rightInitial rightGraph rightFunction rightArgument)
      common rightLocals rightAvailable)
    (rightClosed : rightAvailable.AtomClosed)
    (functionR : ∀ (origin : RichAppOrigin leftRoot env registry target leftSource leftLocals
        (leftRaw.comp common) f a) (rooted : origin.RootedAt leftNode),
      let leftChild : OriginalGeneratedDisplayFrame base
          (applicationGeneratedFunctionSourceDisplay leftLocation leftInitial leftGraph
            (Classical.choice rooted) leftFunction) common leftLocals leftAvailable :=
        ⟨leftFrame.capture, leftFrame.generated⟩
      let rightChild : OriginalGeneratedDisplayFrame base
          (applicationGeneratedFunctionSourceDisplay rightLocation rightInitial rightGraph
            (applicationPrefix rightLocation).route rightFunction) common rightLocals rightAvailable :=
        ⟨rightFrame.capture, rightFrame.generated⟩
      richSchedule .expressionReindex (leftChild.cost lf + rightChild.cost rf) <
        richSchedule .expressionReindex (leftFrame.cost lf + rightFrame.cost rf) →
      origin.functionFootprint.Available leftAvailable →
      OriginalGeneratedDisplayObservationAnswer leftChild rightChild origin.function)
    (argumentR : ∀ (origin : RichAppOrigin leftRoot env registry target leftSource leftLocals
        (leftRaw.comp common) f a) (rooted : origin.RootedAt leftNode),
      let leftChild : OriginalGeneratedDisplayFrame base
          (applicationGeneratedArgumentSourceDisplay leftLocation leftInitial leftGraph
            (Classical.choice rooted) leftArgument) common leftLocals leftAvailable :=
        ⟨leftFrame.capture, leftFrame.generated⟩
      let rightChild : OriginalGeneratedDisplayFrame base
          (applicationGeneratedArgumentSourceDisplay rightLocation rightInitial rightGraph
            (applicationPrefix rightLocation).route rightArgument) common rightLocals rightAvailable :=
        ⟨rightFrame.capture, rightFrame.generated⟩
      richSchedule .expressionReindex (leftChild.cost lf + rightChild.cost rf) <
        richSchedule .expressionReindex (leftFrame.cost lf + rightFrame.cost rf) →
      origin.argumentFootprint.Available leftAvailable →
      OriginalGeneratedDisplayObservationAnswer leftChild rightChild origin.argument) :
    OriginalGeneratedDisplayObservationReindex leftFrame rightFrame := by
  intro n profile footprint query resources
  have same := congrArg (fun expression => expression.subst common)
    (leftArgument.symm.trans rightArgument)
  simp only [subst_subst] at same
  exact OriginalRichFrame.applicationObservationReindexStep henv hscoped formed lf rf
    leftFrame.capture.frame rightFrame.capture.frame leftLocation rightLocation rightClosed same
    (fun origin rooted smaller supplied => functionR origin rooted smaller supplied)
    (fun origin rooted smaller supplied => argumentR origin rooted smaller supplied)
    query resources

end

/-- The code channel uses the observation reconstruction above and exactly
one smaller unary F at the same original formation occurrence. -/
theorem applicationGeneratedSourceCodeReindex
    {base : OriginalCaptureBase env U registry target}
    {leftRoot : EndpointRef leftEnv U leftRootSource le lt}
    {rightRoot : EndpointRef rightEnv U rightRootSource re rt}
    {leftNode : EndpointState leftEnv U leftSource (.app f a) (.sort leftLevel)}
    {rightNode : EndpointState rightEnv U rightSource (.app g b) (.sort rightLevel)}
    (leftLocation : Located leftRoot leftNode) (rightLocation : Located rightRoot rightNode)
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftGraph : OriginalCaptureMap (common := displayed) (leftLocation.contextDerivation leftInitial) leftRaw)
    (rightGraph : OriginalCaptureMap (common := displayed) (rightLocation.contextDerivation rightInitial) rightRaw)
    (leftFunction : displayedFunction = f.subst leftRaw)
    (rightFunction : displayedFunction = g.subst rightRaw)
    (leftArgument : displayedArgument = a.subst leftRaw)
    (rightArgument : displayedArgument = b.subst rightRaw)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftFrame : OriginalGeneratedDisplayFrame base
      (applicationGeneratedSourceDisplay leftLocation leftInitial leftGraph leftFunction leftArgument)
      common leftLocals leftAvailable)
    (rightFrame : OriginalGeneratedDisplayFrame base
      (applicationGeneratedSourceDisplay rightLocation rightInitial rightGraph rightFunction rightArgument)
      common rightLocals rightAvailable)
    (leftClosed : leftAvailable.AtomClosed)
    (sourceF : OriginalCodeInductionAt env registry lf leftInitial leftLocation
      (leftFrame.cost lf + rightFrame.cost rf))
    (observations : OriginalGeneratedDisplayObservationReindex leftFrame rightFrame) :
    OriginalGeneratedDisplayReindex leftFrame rightFrame := by
  intro leftSortLevel rightSortLevel leftSort rightSort
  change VExpr.sort leftLevel = .sort leftSortLevel at leftSort
  change VExpr.sort rightLevel = .sort rightSortLevel at rightSort
  cases leftSort
  cases rightSort
  have same : (VExpr.app f a).subst leftRaw = (VExpr.app g b).subst rightRaw := by
    simp only [subst, ← leftFunction, ← rightFunction, ← leftArgument, ← rightArgument]
  intro relevant n profile footprint query resources
  obtain ⟨destination⟩ := observations (.code query) resources
  obtain ⟨required, ⟨certificate⟩, available⟩ := destination.code henv query.formed
  have positive := (Closure.close (rightNode.dependencyOrigin rf)
    (rightFrame.capture.frame.dependencyEnvironment rf)).cost_pos
  obtain ⟨semantics⟩ := sourceF target leftLocals _ _ leftAvailable leftFrame.capture.frame
    (Nat.lt_add_of_pos_right positive) leftClosed formed leftFrame.capture.substitutions query resources
  have equal := congrArg (fun expression => expression.subst common) same
  simp only [subst_subst] at equal
  refine ⟨⟨required, certificate, available, ?_⟩⟩
  change TypeRelated env U registry target ((VExpr.app f a).subst (leftRaw.comp common))
    ((VExpr.app g b).subst (rightRaw.comp common)) profile
  rw [← equal]
  exact semantics.related


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
