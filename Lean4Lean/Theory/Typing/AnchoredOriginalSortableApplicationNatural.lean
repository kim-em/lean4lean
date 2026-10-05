import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationNatural
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableApplicationCoherence

/-! Natural application comparison consumes the actual smaller argument F
and function C hypotheses. Query preparation, original fitted contexts, and
both the raw result path and exact result certificate are constructed here. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

noncomputable def AppView.functionSortableDisplayFits
    {function argument : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (initial : ContextDerivation sourceEnv U rootSource)
    (insertion : Ctx.Lift' map source displayed)
    (function_eq : displayedFunction = function.lift' map)
    (tail : SortableTailFits sourceEnv env U registry target source locals
      (Subst.lift_l map common) (Subst.lift_l map common)
      (fun index => commonAvailable (map.liftVar index)))
    (substitutions : Ctx.SubstEq env U target
      (Subst.lift_l map common) (Subst.lift_l map common) source) :
    SortableDisplayFits env registry target (view.functionDisplayAs initial insertion function_eq)
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
    (argumentIH : StateHereditaryFundamental env registry
      ((Located.appArgument leftView.location).contextDerivation leftInitial) leftView.argument)
    (functionIH : DisplaySortableCoherence env U registry
      (leftView.functionDisplayAs leftInitial leftInsertion leftExpression)
      (rightView.functionDisplayAs rightInitial rightInsertion rightExpression))
    (domainIH : StateSortableFundamental env registry
      (rightView.location.contextDerivation rightInitial) rightView.domain)
    (bodyIH : StateSortableFundamental env registry
      ((Located.appCodomain rightView.location).contextDerivation rightInitial) rightView.codomain)
    {target : List VExpr} {common : Subst} {commonAvailable : Valuation}
    {leftLocals rightLocals : List Nat}
    (closed : commonAvailable.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (leftTail : SortableTailFits leftEnv env U registry target leftSource leftLocals
      (Subst.lift_l leftMap common) (Subst.lift_l leftMap common)
      (fun index => commonAvailable (leftMap.liftVar index)))
    (rightTail : SortableTailFits rightEnv env U registry target rightSource rightLocals
      (Subst.lift_l rightMap common) (Subst.lift_l rightMap common)
      (fun index => commonAvailable (rightMap.liftVar index)))
    (leftSubs : Ctx.SubstEq env U target
      (Subst.lift_l leftMap common) (Subst.lift_l leftMap common) leftSource)
    (rightSubs : Ctx.SubstEq env U target
      (Subst.lift_l rightMap common) (Subst.lift_l rightMap common) rightSource)

include leftInitial rightInitial leftInsertion rightInsertion leftExpression rightExpression
  sameArgument henv hscoped leftBelow rightBelow argumentIH functionIH domainIH bodyIH
  closed hTarget leftTail rightTail leftSubs rightSubs in
theorem AppView.naturalSortableComparison
    {n : Nat} {profile : Profile n} {footprint : Footprint}
    (certificate : SortableCert env U registry target leftLocals (Subst.lift_l leftMap common)
      (leftView.codomainExpression.inst leftArgument) relevant profile footprint)
    (resources : footprint.Available (fun index => commonAvailable (leftMap.liftVar index))) :
    TypeConversion env U target
      ((leftView.codomainExpression.inst leftArgument).subst (Subst.lift_l leftMap common))
      ((rightView.codomainExpression.inst rightArgument).subst (Subst.lift_l rightMap common)) ∧
    Nonempty (SortableTransferResult env U registry target rightLocals
      (Subst.lift_l leftMap common) (Subst.lift_l rightMap common)
      (fun index => commonAvailable (rightMap.liftVar index))
      (leftView.codomainExpression.inst leftArgument)
      (rightView.codomainExpression.inst rightArgument) relevant profile) := by
  have leftClosed : Valuation.AtomClosed (fun index => commonAvailable (leftMap.liftVar index)) := by
    intro index need member atom present
    exact closed _ need member atom present
  have rightClosed : Valuation.AtomClosed (fun index => commonAvailable (rightMap.liftVar index)) := by
    intro index need member atom present
    exact closed _ need member atom present
  obtain ⟨request⟩ := OriginalFactorCut.SortableCert.prepareApplication leftView certificate resources
  obtain ⟨frame⟩ := request.complete leftInitial henv leftBelow leftClosed hTarget leftSubs
    (SortableTailPairedFits.diagonal (leftView.location.contextDerivation leftInitial) leftTail) argumentIH
  let leftFrame := leftView.functionSortableDisplayFits leftInitial leftInsertion leftExpression leftTail leftSubs
  let rightFrame := rightView.functionSortableDisplayFits rightInitial rightInsertion rightExpression rightTail rightSubs
  obtain ⟨functionAnswer⟩ := functionIH target common commonAvailable leftLocals rightLocals
    closed hTarget leftFrame rightFrame frame.certificate frame.resources
  have argumentEq := realized_between_displays sameArgument
    (σ := Subst.lift_l leftMap common) (τ := Subst.lift_l rightMap common) rfl rfl
  have rawArgument : env.HasType U target
      (leftArgument.subst (Subst.lift_l leftMap common))
      (leftView.domainExpression.subst (Subst.lift_l leftMap common)) :=
    frame.guard.path.cast frame.guard.anchor.2.1
  have path := TypeRelated.literalPiBodyPath henv hTarget
    (by simpa only [SortableApplicationFrame.profile, AppView.functionDisplayAs, EndpointDisplay.sourceSubst, subst] using functionAnswer.related) rawArgument
  refine ⟨?_, ?_⟩
  · simpa only [AppView.functionDisplayAs, EndpointDisplay.sourceSubst, subst_inst, argumentEq] using path
  · obtain ⟨answer⟩ := frame.compare rightView request.collected.observation
      request.collected.argumentAvailable henv hscoped leftBelow rightBelow hTarget leftSubs rightSubs
      rightInitial rightTail rightClosed leftMap rightMap common [] rfl rfl sameArgument
      (fun _ => rfl) (fun _ => rfl) functionAnswer domainIH bodyIH
    refine ⟨⟨answer.footprint, answer.certificate.lowerRaised request.collected.bound,
      answer.available, ?_⟩⟩
    have lowered := answer.related.lower henv request.collected.bound
    simpa only [lower_raised] using lowered

include leftInitial rightInitial leftInsertion rightInsertion leftExpression rightExpression
  sameArgument henv hscoped leftBelow rightBelow argumentIH functionIH domainIH bodyIH
  closed hTarget leftTail rightTail leftSubs rightSubs in
/-- The raw path has no nonempty-query prerequisite. The computed singleton
function row retains its body prototype even for an empty result profile. -/
theorem AppView.naturalSortablePath :
    TypeConversion env U target
      ((leftView.codomainExpression.inst leftArgument).subst (Subst.lift_l leftMap common))
      ((rightView.codomainExpression.inst rightArgument).subst (Subst.lift_l rightMap common)) := by
  have empty : SortableCert env U registry target leftLocals (Subst.lift_l leftMap common)
      (leftView.codomainExpression.inst leftArgument) false (Profile.empty : Profile 0) [] :=
    .seed .empty (Profile.HasType.empty (Profile.HasType.sort false).wf_value)
  exact (leftView.naturalSortableComparison rightView leftInitial rightInitial leftInsertion rightInsertion
    leftExpression rightExpression sameArgument henv hscoped leftBelow rightBelow argumentIH functionIH
    domainIH bodyIH closed hTarget leftTail rightTail leftSubs rightSubs empty
    (by intro i need member; cases member)).1

end

end Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor
