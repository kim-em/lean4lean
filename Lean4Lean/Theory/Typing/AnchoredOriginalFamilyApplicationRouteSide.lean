import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentPair

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

private noncomputable def appReferenceLocation
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node} (view : AppView start)
    (domain : EndpointRef sourceEnv U source view.domainExpression (.sort view.domainLevel))
    (equal : view.domain = .ref domain) :
    Located root (.app view.domainWF view.bodyWF (.ref domain) view.codomain view.function view.argument view.result) :=
  equal ▸ view.location

private theorem appReferenceLocation_context
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node} (view : AppView start)
    (domain : EndpointRef sourceEnv U source view.domainExpression (.sort view.domainLevel))
    (equal : view.domain = .ref domain) (initial : ContextDerivation sourceEnv U rootSource) :
    (appReferenceLocation view domain equal).contextDerivation initial = view.location.contextDerivation initial := by
  rcases view with ⟨_, _, _, _, _, _, domainState, _, _, _, _, _, _, _⟩
  dsimp only at domain equal ⊢
  subst domainState
  rfl

private theorem appReferenceLocation_prefix
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {start : Located root node} (view : AppView start)
    (domain : EndpointRef sourceEnv U source view.domainExpression (.sort view.domainLevel))
    (equal : view.domain = .ref domain) :
    (appReferenceLocation view domain equal).binderPrefix = view.location.binderPrefix := by
  rcases view with ⟨_, _, _, _, _, _, domainState, _, _, _, _, _, _, _⟩
  dsimp only at domain equal ⊢
  subst domainState
  rfl

private def transportRouteFrame
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) :
    OriginalTypeRouteFrame env registry target (equal ▸ graph) commonLeft commonRight := by
  cases equal
  exact frame

private theorem transportRouteFrame_environment
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) :
    (transportRouteFrame equal frame).realization.frame.dependencyEnvironment ordered =
      frame.realization.frame.dependencyEnvironment ordered := by
  cases equal
  rfl

private theorem transportRouteFrame_generated
    {first second : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) first raw}
    (equal : first = second)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.realization.frame.raw) :
    CappedCaptureGenerated base commonCaps commonLeft commonRight (equal ▸ graph)
      (transportRouteFrame equal frame).realization.frame.raw := by
  cases equal
  exact generated

/-- An actual assigned-family application supplies its original domain
reference and inherits the caller's unchanged source graph and frame. -/
noncomputable def assignedFamilyRouteSide
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (index : Nat) (selected : arguments[index]? = some argument) :
    OriginalApplicationTypeRouteSide U common :=
  let application := assignedFamilyApplication major index selected
  let domain := Classical.choose application.view.location.originalDomains.1
  let equal := Classical.choose_spec application.view.location.originalDomains.1
  let location := appReferenceLocation application.view domain equal
  have contextEq : location.contextDerivation initial = initial :=
    (appReferenceLocation_context application.view domain equal initial).trans
      (assignedFamilyApplication_context major index selected initial)
  originalApplicationTypeRouteSide initial domain application.view.codomain application.view.function
    application.view.argument application.view.result application.view.domainWF application.view.bodyWF
    location (contextEq.symm ▸ graph)

noncomputable def assignedFamilyRouteFrame
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (index : Nat) (selected : arguments[index]? = some argument)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight) :
    OriginalTypeRouteFrame env registry target
      (assignedFamilyRouteSide major initial graph index selected).graph commonLeft commonRight :=
  transportRouteFrame _ frame

theorem assignedFamilyRouteFrame_environment
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (index : Nat) (selected : arguments[index]? = some argument)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (ordered : sourceEnv.Ordered) :
    (assignedFamilyRouteFrame major initial graph index selected frame).realization.frame.dependencyEnvironment ordered =
      frame.realization.frame.dependencyEnvironment ordered :=
  transportRouteFrame_environment _ frame ordered

theorem assignedFamilyRouteFrame_generated
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (index : Nat) (selected : arguments[index]? = some argument)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.realization.frame.raw) :
    CappedCaptureGenerated base commonCaps commonLeft commonRight
      (assignedFamilyRouteSide major initial graph index selected).graph
      (assignedFamilyRouteFrame major initial graph index selected frame).realization.frame.raw :=
  transportRouteFrame_generated _ frame generated

theorem assignedFamilyRouteSide_prefix
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (index : Nat) (selected : arguments[index]? = some argument) :
    (assignedFamilyRouteSide major initial graph index selected).location.binderPrefix = [] := by
  exact (appReferenceLocation_prefix _ _ _).trans
    ((assignedFamilyApplication major index selected).view.prefix_eq.trans
      (assignedFamilyApplication major index selected).prefix_eq)

theorem assignedFamilyRouteSide_function
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (index : Nat) (selected : arguments[index]? = some argument) :
    (assignedFamilyRouteSide major initial graph index selected).f =
      mkApps (.const name levels) (arguments.take index) :=
  spineApplication_functionExpression arguments (.assignedFormation (.here (root := major))) index selected

theorem assignedFamilyRouteSide_adjacent
    (major : EndpointRef sourceEnv U source majorExpression (mkApps (.const name levels) arguments))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (index : Nat) (selected : arguments[index]? = some argument)
    (nextSelected : arguments[index+1]? = some nextArgument) :
    let previous := assignedFamilyRouteSide major initial graph index selected
    let next := assignedFamilyRouteSide major initial graph (index+1) nextSelected
    (VExpr.app previous.f previous.a).subst previous.raw = next.f.subst next.raw := by
  have adjacent :
      (spineApplication arguments (.assignedFormation (.here (root := major))) (index + 1) nextSelected).functionExpression =
        .app (spineApplication arguments (.assignedFormation (.here (root := major))) index selected).functionExpression argument := by
    rw [spineApplication_functionExpression, spineApplication_functionExpression,
      List.take_add_one, selected]
    simp only [Option.toList_some, mkApps, List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact congrArg (fun expression : VExpr => expression.subst raw) adjacent.symm

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
