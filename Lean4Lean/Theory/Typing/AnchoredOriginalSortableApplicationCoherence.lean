import Lean4Lean.Theory.Typing.AnchoredOriginalSortableCutSupply
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableDisplayTransport

/-! Exact two-context application comparison for hereditary sortable queries.
The finite frame is computed by application preparation; replay uses only the
actual right original domain and codomain formation calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem SortableApplicationFrame.compare
    {leftEnv rightEnv env : VEnv} {U : Nat}
    {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
    {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
    {leftNode : EndpointState leftEnv U leftSource (.app leftFunction leftArgument) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.app rightFunction rightArgument) rightAssigned}
    {leftStart : Located leftRoot leftNode} {rightStart : Located rightRoot rightNode}
    {leftView : AppView leftStart} (rightView : AppView rightStart)
    {registry : CanonicalHead.Registry} {target : List VExpr}
    {leftLocals rightLocals : List Nat} {σ τ : Subst}
    {leftAvailable rightAvailable commonAvailable : Valuation}
    {input result : Profile n}
    (frame : SortableApplicationFrame env U registry target leftLocals σ leftAvailable
      leftView.domainExpression leftView.codomainExpression leftArgument relevant input result)
    (argumentObservation : SortableObs env U registry target leftLocals σ
      leftArgument input argumentFootprint)
    (argumentResources : argumentFootprint.Available leftAvailable)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftLe : leftEnv ≤ env) (rightLe : rightEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (rightFits : SortableTailFits rightEnv env U registry target rightSource rightLocals τ τ rightAvailable)
    (rightClosed : rightAvailable.AtomClosed)
    (leftMap rightMap : Lift) (common : Subst) (commonLocals : List Nat)
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ)
    (sameArgument : leftArgument.lift' leftMap = rightArgument.lift' rightMap)
    (leftAvailableEq : ∀ index, leftAvailable index = commonAvailable (leftMap.liftVar index))
    (rightAvailableEq : ∀ index, rightAvailable index = commonAvailable (rightMap.liftVar index))
    (functionAnswer : SortableTransferResult env U registry target rightLocals σ τ rightAvailable
      (.forallE leftView.domainExpression leftView.codomainExpression)
      (.forallE rightView.domainExpression rightView.codomainExpression)
      relevant frame.profile)
    (rightDomain : StateSortableFundamental env registry
      (rightView.location.contextDerivation rightInitial) rightView.domain)
    (rightBody : StateSortableFundamental env registry
      ((Located.appCodomain rightView.location).contextDerivation rightInitial) rightView.codomain) :
    Nonempty (SortableTransferResult env U registry target rightLocals σ τ rightAvailable
      (leftView.codomainExpression.inst leftArgument)
      (rightView.codomainExpression.inst rightArgument) relevant result) := by
  let originalDomain := Classical.choose rightView.location.originalDomains.1
  have domain_eq : rightView.domain = .ref originalDomain :=
    Classical.choose_spec rightView.location.originalDomains.1
  have domainIH : StateSortableFundamental env registry
      (rightView.location.contextDerivation rightInitial) (.ref originalDomain) := by
    simpa only [domain_eq] using rightDomain
  have bodyIH : StateSortableFundamental env registry
      (.cons (rightView.location.contextDerivation rightInitial) originalDomain) rightView.codomain :=
    rightBody
  have origins := functionAnswer.certificate.piOriginsOriginal henv hscoped rightLe hTarget rightClosed
    (rightView.location.contextDerivation rightInitial) originalDomain rightView.codomain
    rightSubstitutions rightFits domainIH bodyIH functionAnswer.available
  obtain ⟨row⟩ := functionAnswer.certificate.piRowOfOrigins origins
    (List.mem_singleton_self _) (List.mem_singleton_self _)
  have argumentEq := realized_between_displays sameArgument leftRealization rightRealization
  have admitted : Admitted env U registry target frame.key
      (rightArgument.subst τ) (rightArgument.subst τ) := by
    rw [← argumentEq]
    exact frame.guard.anchor
  have admissionCopy := admitted
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := admissionCopy
  have live := Related.live henv hscoped hTarget anchorRelated
  obtain ⟨argumentFootprint, ⟨argumentObservation⟩, argumentResources⟩ :=
    SortableObs.betweenDisplays argumentObservation leftMap rightMap common
      leftRealization rightRealization sameArgument commonLocals rightLocals
      argumentResources leftAvailableEq rightAvailableEq
  let sourceArgument : SortableGradedResult env U registry target rightLocals τ rightAvailable
      rightArgument frame.key.input :=
    { rank := n
      bound := Nat.le_refl _
      raw := input
      footprint := argumentFootprint
      observation := argumentObservation
      adapter := by rw [raiseProfile_self]; exact .refl _
      resources := argumentResources
      live := live }
  obtain ⟨rightCode⟩ := rowInstantiateSortableOriginal henv hscoped rightLe hTarget rightClosed
    (rightView.location.contextDerivation rightInitial) originalDomain rightView.codomain
    rightSubstitutions rightFits domainIH bodyIH row admitted sourceArgument
  have paired := literalPiBody henv hscoped hTarget
    (by simpa only [SortableApplicationFrame.profile, subst] using functionAnswer.related) admitted
  refine ⟨⟨rightCode.footprint, rightCode.certificate, rightCode.resources, ?_⟩⟩
  simpa only [subst_inst, argumentEq] using paired

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
