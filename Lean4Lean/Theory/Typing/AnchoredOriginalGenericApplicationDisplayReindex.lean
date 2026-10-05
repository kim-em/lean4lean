import Lean4Lean.Theory.Typing.AnchoredOriginalGenericApplicationReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericReindexCode
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericDisplay

/-! Application R at common original source displays. The child displays
are built from actual routes from the retained roots. Their source syntax,
frames, and closure costs are preserved before any target substitution. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- One exact source query at a pair of already produced frames. The
destination frame may have been selected for this very query. -/
def OriginalRichDisplayObservationAnswer
    {left : EndpointDisplay leftEnv U displayed expression leftType}
    {right : EndpointDisplay rightEnv U displayed expression rightType}
    (_leftFrame : OriginalRichDisplayFrame env registry target left common leftLocals leftAvailable)
    (_rightFrame : OriginalRichDisplayFrame env registry target right common rightLocals rightAvailable)
    (_query : RichObs leftEnv env U registry target left.node leftLocals
      (left.sourceSubst common) profile footprint) : Prop :=
  Nonempty (RichGradedResult rightEnv env U registry target right.node rightLocals
    (right.sourceSubst common) rightAvailable profile)

/-- The observation channel at a fixed pair of actual source displays.
This is a local induction obligation, not an assertion that arbitrary
independently supplied frames have compatible resources. -/
def OriginalRichDisplayObservationReindex
    {left : EndpointDisplay leftEnv U displayed expression leftType}
    {right : EndpointDisplay rightEnv U displayed expression rightType}
    (_leftFrame : OriginalRichDisplayFrame env registry target left common leftLocals leftAvailable)
    (_rightFrame : OriginalRichDisplayFrame env registry target right common rightLocals rightAvailable) : Prop :=
  ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs leftEnv env U registry target left.node leftLocals (left.sourceSubst common) profile footprint →
    footprint.Available leftAvailable →
    Nonempty (RichGradedResult rightEnv env U registry target right.node rightLocals
      (right.sourceSubst common) rightAvailable profile)

section
variable
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {parent : EndpointState sourceEnv U source (.app f a) assigned}
    (location : Located root parent)
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)

noncomputable def applicationSourceDisplay
    (functionEq : displayedFunction = f.lift' map)
    (argumentEq : displayedArgument = a.lift' map) :
    EndpointDisplay sourceEnv U displayed (.app displayedFunction displayedArgument) (assigned.lift' map) where
  source := source
  sourceExpression := .app f a
  sourceType := assigned
  context := location.contextDerivation initial
  node := parent
  provenance := .ofLocation location initial
  map := map
  insertion := insertion
  expression_eq := by simp only [lift', ← functionEq, ← argumentEq]
  type_eq := rfl

/-- Retain the parent's context verbatim; the route proves it is also the
actual child's original context. No reorigining of a semantic frame occurs. -/
noncomputable def applicationFunctionSourceDisplay
    {A B : VExpr} {u v : VLevel}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {fn : EndpointState sourceEnv U source f (.forallE A B)}
    {arg : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (route : PrefixRoute sourceEnv U source (.app f a) parent (.app hu hv domain body fn arg result))
    (functionEq : displayedFunction = f.lift' map) :
    EndpointDisplay sourceEnv U displayed displayedFunction ((VExpr.forallE A B).lift' map) where
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
  map := map
  insertion := insertion
  expression_eq := functionEq
  type_eq := rfl

noncomputable def applicationArgumentSourceDisplay
    {A B : VExpr} {u v : VLevel}
    {domain : EndpointState sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {fn : EndpointState sourceEnv U source f (.forallE A B)}
    {arg : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (route : PrefixRoute sourceEnv U source (.app f a) parent (.app hu hv domain body fn arg result))
    (argumentEq : displayedArgument = a.lift' map) :
    EndpointDisplay sourceEnv U displayed displayedArgument (A.lift' map) where
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
  map := map
  insertion := insertion
  expression_eq := argumentEq
  type_eq := rfl

end

section
variable
    {leftRoot : EndpointRef leftEnv U leftRootSource le lt}
    {rightRoot : EndpointRef rightEnv U rightRootSource re rt}
    {leftNode : EndpointState leftEnv U leftSource (.app f a) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.app g b) rightAssigned}
    (leftLocation : Located leftRoot leftNode) (rightLocation : Located rightRoot rightNode)
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
    (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
    (leftFunction : displayedFunction = f.lift' leftMap)
    (rightFunction : displayedFunction = g.lift' rightMap)
    (leftArgument : displayedArgument = a.lift' leftMap)
    (rightArgument : displayedArgument = b.lift' rightMap)

/-- Only the two actual child displays can be requested by this step.
All wrappers and original conversion routes are handled by the observation
worker; equality of arguments is derived from common source syntax. -/
theorem applicationSourceObservationReindex
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftFrame : OriginalRichDisplayFrame env registry target
      (applicationSourceDisplay leftLocation leftInitial leftInsertion leftFunction leftArgument)
      common leftLocals leftAvailable)
    (rightFrame : OriginalRichDisplayFrame env registry target
      (applicationSourceDisplay rightLocation rightInitial rightInsertion rightFunction rightArgument)
      common rightLocals rightAvailable)
    (rightClosed : rightAvailable.AtomClosed)
    (functionR : ∀ (origin : RichAppOrigin leftRoot env registry target leftSource leftLocals
        (Subst.lift_l leftMap common) f a) (rooted : origin.RootedAt leftNode),
      let leftChild : OriginalRichDisplayFrame env registry target
          (applicationFunctionSourceDisplay leftLocation leftInitial leftInsertion
            (Classical.choice rooted) leftFunction) common leftLocals leftAvailable :=
        ⟨leftFrame.frame, leftFrame.substitutions⟩
      let rightChild : OriginalRichDisplayFrame env registry target
          (applicationFunctionSourceDisplay rightLocation rightInitial rightInsertion
            (applicationPrefix rightLocation).route rightFunction) common rightLocals rightAvailable :=
        ⟨rightFrame.frame, rightFrame.substitutions⟩
      richSchedule .expressionReindex (leftChild.cost lf + rightChild.cost rf) <
        richSchedule .expressionReindex (leftFrame.cost lf + rightFrame.cost rf) →
      origin.functionFootprint.Available leftAvailable →
      OriginalRichDisplayObservationAnswer leftChild rightChild origin.function)
    (argumentR : ∀ (origin : RichAppOrigin leftRoot env registry target leftSource leftLocals
        (Subst.lift_l leftMap common) f a) (rooted : origin.RootedAt leftNode),
      let leftChild : OriginalRichDisplayFrame env registry target
          (applicationArgumentSourceDisplay leftLocation leftInitial leftInsertion
            (Classical.choice rooted) leftArgument) common leftLocals leftAvailable :=
        ⟨leftFrame.frame, leftFrame.substitutions⟩
      let rightChild : OriginalRichDisplayFrame env registry target
          (applicationArgumentSourceDisplay rightLocation rightInitial rightInsertion
            (applicationPrefix rightLocation).route rightArgument) common rightLocals rightAvailable :=
        ⟨rightFrame.frame, rightFrame.substitutions⟩
      richSchedule .expressionReindex (leftChild.cost lf + rightChild.cost rf) <
        richSchedule .expressionReindex (leftFrame.cost lf + rightFrame.cost rf) →
      origin.argumentFootprint.Available leftAvailable →
      OriginalRichDisplayObservationAnswer leftChild rightChild origin.argument) :
    OriginalRichDisplayObservationReindex leftFrame rightFrame := by
  intro n profile footprint query resources
  have same := congrArg (fun expression => expression.subst common)
    (leftArgument.symm.trans rightArgument)
  simp only [subst_lift'] at same
  exact OriginalRichFrame.applicationObservationReindexStep henv hscoped formed lf rf
    leftFrame.frame rightFrame.frame leftLocation rightLocation rightClosed same
    (fun origin rooted smaller supplied => functionR origin rooted smaller supplied)
    (fun origin rooted smaller supplied => argumentR origin rooted smaller supplied)
    query resources

end

/-- The code channel uses the observation reconstruction above and exactly
one smaller unary F at the same original formation occurrence. -/
theorem applicationSourceCodeReindex
    {leftRoot : EndpointRef leftEnv U leftRootSource le lt}
    {rightRoot : EndpointRef rightEnv U rightRootSource re rt}
    {leftNode : EndpointState leftEnv U leftSource (.app f a) (.sort leftLevel)}
    {rightNode : EndpointState rightEnv U rightSource (.app g b) (.sort rightLevel)}
    (leftLocation : Located leftRoot leftNode) (rightLocation : Located rightRoot rightNode)
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
    (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
    (leftFunction : displayedFunction = f.lift' leftMap)
    (rightFunction : displayedFunction = g.lift' rightMap)
    (leftArgument : displayedArgument = a.lift' leftMap)
    (rightArgument : displayedArgument = b.lift' rightMap)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftFrame : OriginalRichDisplayFrame env registry target
      (applicationSourceDisplay leftLocation leftInitial leftInsertion leftFunction leftArgument)
      common leftLocals leftAvailable)
    (rightFrame : OriginalRichDisplayFrame env registry target
      (applicationSourceDisplay rightLocation rightInitial rightInsertion rightFunction rightArgument)
      common rightLocals rightAvailable)
    (leftClosed : leftAvailable.AtomClosed)
    (sourceF : OriginalCodeInductionAt env registry lf leftInitial leftLocation
      (leftFrame.cost lf + rightFrame.cost rf))
    (observations : OriginalRichDisplayObservationReindex leftFrame rightFrame) :
    OriginalRichDisplayReindex leftFrame rightFrame := by
  intro leftSortLevel rightSortLevel leftSort rightSort
  change VExpr.sort leftLevel = .sort leftSortLevel at leftSort
  change VExpr.sort rightLevel = .sort rightSortLevel at rightSort
  cases leftSort
  cases rightSort
  have same : (VExpr.app f a).lift' leftMap = (VExpr.app g b).lift' rightMap := by
    simp only [lift', ← leftFunction, ← rightFunction, ← leftArgument, ← rightArgument]
  intro relevant n profile footprint query resources
  exact OriginalRichFrame.codeReindexOfObservation henv hscoped formed lf rf leftInitial rightInitial
    leftLocation rightLocation leftInsertion rightInsertion same common leftFrame.frame rightFrame.frame
    leftClosed leftFrame.substitutions sourceF observations query resources

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
