import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPath
import Lean4Lean.Theory.Typing.AnchoredOriginalCoherenceContract

/-! Natural application comparison consumes the actual smaller argument F
and function C hypotheses. Query preparation, original fitted contexts, and
both the raw result path and exact result certificate are constructed here. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

noncomputable def AppView.functionDisplayAs
    {function argument : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (function_eq : displayedFunction = function.lift' map) :
    EndpointDisplay sourceEnv U displayed displayedFunction
      ((VExpr.forallE view.domainExpression view.codomainExpression).lift' map) where
  source := source
  sourceExpression := function
  sourceType := .forallE view.domainExpression view.codomainExpression
  context := (Located.appFunction view.location).contextDerivation initial
  node := view.function
  provenance := .ofLocation (.appFunction view.location) initial
  map := map
  insertion := insertion
  expression_eq := function_eq
  type_eq := rfl

noncomputable def AppView.functionDisplayFits
    {function argument : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (function_eq : displayedFunction = function.lift' map)
    (tail : TailFits sourceEnv env U registry target source locals
      (Subst.lift_l map common) (Subst.lift_l map common)
      (fun index => commonAvailable (map.liftVar index)))
    (substitutions : Ctx.SubstEq env U target
      (Subst.lift_l map common) (Subst.lift_l map common) source) :
    DisplayFits env registry target (view.functionDisplayAs initial insertion function_eq)
      common commonAvailable locals :=
  { fits := tail.reorigin ((Located.appFunction view.location).contextDerivation initial)
    original := tail.reorigin_contextDerivation _
    substitutions := substitutions }

section
variable
    {leftEnv rightEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {leftRootSource rightRootSource leftSource rightSource displayed : List VExpr}
    {leftRootExpression leftRootType rightRootExpression rightRootType : VExpr}
    {leftFunction leftArgument leftAssigned rightFunction rightArgument rightAssigned displayedFunction : VExpr}
    {leftMap rightMap : Lift}
    {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
    {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
    {leftNode : EndpointState leftEnv U leftSource (.app leftFunction leftArgument) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.app rightFunction rightArgument) rightAssigned}
    {leftStart : Located leftRoot leftNode} {rightStart : Located rightRoot rightNode}
    (leftView : AppView leftStart) (rightView : AppView rightStart)
    (leftInitial : ContextDerivation leftEnv U leftRootSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (leftInsertion : Ctx.Lift' leftMap leftSource displayed)
    (rightInsertion : Ctx.Lift' rightMap rightSource displayed)
    (leftExpression : displayedFunction = leftFunction.lift' leftMap)
    (rightExpression : displayedFunction = rightFunction.lift' rightMap)
    (sameArgument : leftArgument.lift' leftMap = rightArgument.lift' rightMap)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (argumentIH : StateFundamental env registry
      ((Located.appArgument leftView.location).contextDerivation leftInitial) leftView.argument)
    (functionIH : DisplayCoherence env U registry
      (leftView.functionDisplayAs leftInitial leftInsertion leftExpression)
      (rightView.functionDisplayAs rightInitial rightInsertion rightExpression))
    (domainIH : StateFundamental env registry
      (rightView.location.contextDerivation rightInitial) rightView.domain)
    (bodyIH : StateFundamental env registry
      ((Located.appCodomain rightView.location).contextDerivation rightInitial) rightView.codomain)
    {target : List VExpr} {common : Subst} {commonAvailable : Valuation}
    {leftLocals rightLocals : List Nat}
    (closed : commonAvailable.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (leftTail : TailFits leftEnv env U registry target leftSource leftLocals
      (Subst.lift_l leftMap common) (Subst.lift_l leftMap common)
      (fun index => commonAvailable (leftMap.liftVar index)))
    (rightTail : TailFits rightEnv env U registry target rightSource rightLocals
      (Subst.lift_l rightMap common) (Subst.lift_l rightMap common)
      (fun index => commonAvailable (rightMap.liftVar index)))
    (leftSubs : Ctx.SubstEq env U target
      (Subst.lift_l leftMap common) (Subst.lift_l leftMap common) leftSource)
    (rightSubs : Ctx.SubstEq env U target
      (Subst.lift_l rightMap common) (Subst.lift_l rightMap common) rightSource)

include leftInitial rightInitial leftInsertion rightInsertion leftExpression rightExpression
  sameArgument henv hscoped leftBelow rightBelow argumentIH functionIH domainIH bodyIH
  closed hTarget leftTail rightTail leftSubs rightSubs in
theorem AppView.naturalComparison
    {n : Nat} {profile : Profile n} {footprint : Footprint}
    (certificate : CodeCert env U registry target leftLocals (Subst.lift_l leftMap common)
      (leftView.codomainExpression.inst leftArgument) profile footprint)
    (resources : footprint.Available (fun index => commonAvailable (leftMap.liftVar index))) :
    TypeConversion env U target
      ((leftView.codomainExpression.inst leftArgument).subst (Subst.lift_l leftMap common))
      ((rightView.codomainExpression.inst rightArgument).subst (Subst.lift_l rightMap common)) ∧
    Nonempty (CodeTransferResult env U registry target rightLocals
      (Subst.lift_l leftMap common) (Subst.lift_l rightMap common)
      (fun index => commonAvailable (rightMap.liftVar index))
      (leftView.codomainExpression.inst leftArgument)
      (rightView.codomainExpression.inst rightArgument) profile) := by
  have leftClosed : Valuation.AtomClosed (fun index => commonAvailable (leftMap.liftVar index)) := by
    intro index need member atom present
    exact closed _ need member atom present
  have rightClosed : Valuation.AtomClosed (fun index => commonAvailable (rightMap.liftVar index)) := by
    intro index need member atom present
    exact closed _ need member atom present
  let seed : NativeArgumentSeed env U registry target leftLocals (Subst.lift_l leftMap common)
      (fun index => commonAvailable (leftMap.liftVar index)) leftArgument :=
    ⟨0, .empty, [], .empty, by intro i need member; cases member⟩
  obtain ⟨request, _⟩ := OriginalFactorCut.CodeCert.prepareOriginalApplication leftView seed certificate resources
  have argumentTransfer : GradedTransfer env U registry target leftLocals
      (Subst.lift_l leftMap common) (Subst.lift_l leftMap common)
      (fun index => commonAvailable (leftMap.liftVar index))
      leftArgument leftArgument leftView.domainExpression :=
    (argumentIH target leftLocals _ _ _ leftClosed hTarget leftSubs
      (TailPairedFits.diagonal ((Located.appArgument leftView.location).contextDerivation leftInitial)
        leftTail)).1
  obtain ⟨argumentAnswer⟩ := argumentTransfer request.observation request.resources
  let frame := request.complete henv leftBelow hTarget leftSubs argumentAnswer
  let leftFrame := leftView.functionDisplayFits leftInitial leftInsertion leftExpression leftTail leftSubs
  let rightFrame := rightView.functionDisplayFits rightInitial rightInsertion rightExpression rightTail rightSubs
  have comparison := functionIH target common commonAvailable leftLocals rightLocals
    closed hTarget leftFrame rightFrame
  obtain ⟨functionAnswer⟩ := comparison.queries frame.certificate frame.resources
  have path := frame.comparisonPath henv hTarget
    (realized_between_displays sameArgument rfl rfl) functionAnswer
  refine ⟨path, ?_⟩
  exact request.compare rightView henv hscoped leftBelow rightBelow hTarget leftSubs rightSubs
    rightInitial rightTail rightClosed leftMap rightMap common [] rfl rfl sameArgument
    (fun _ => rfl) (fun _ => rfl) argumentAnswer functionAnswer domainIH bodyIH

include leftInitial rightInitial leftInsertion rightInsertion leftExpression rightExpression
  sameArgument henv hscoped leftBelow rightBelow argumentIH functionIH domainIH bodyIH
  closed hTarget leftTail rightTail leftSubs rightSubs in
/-- An empty exact code request still creates a genuine function Pi query,
whose frozen body prototype supplies the support-independent raw path. -/
theorem AppView.naturalPath :
    TypeConversion env U target
      ((leftView.codomainExpression.inst leftArgument).subst (Subst.lift_l leftMap common))
      ((rightView.codomainExpression.inst rightArgument).subst (Subst.lift_l rightMap common)) := by
  have empty : CodeCert env U registry target leftLocals (Subst.lift_l leftMap common)
      (leftView.codomainExpression.inst leftArgument) (Profile.empty : Profile 0) [] :=
    .seed .empty (Profile.HasType.empty (Profile.HasType.sort true).wf_value)
  exact (leftView.naturalComparison rightView leftInitial rightInitial leftInsertion rightInsertion
    leftExpression rightExpression sameArgument henv hscoped leftBelow rightBelow argumentIH functionIH
    domainIH bodyIH closed hTarget leftTail rightTail leftSubs rightSubs empty
    (by intro i need member; cases member)).1

end

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
