import Lean4Lean.Theory.Typing.AnchoredOriginalPrefixApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalPairedApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalDisplay
import Lean4Lean.Theory.Typing.AnchoredOriginalDisplayTransport
import Lean4Lean.Theory.Typing.AnchoredOriginalPiReanchor

/-! Application coherence at two actual original source contexts. The
inferred domains may differ. A finite left argument answer builds the exact
Pi query, the actual function comparison answers that query in the right
context, and the right original domain/codomain children replay its row.

Source weakening transports only existing observation syntax. No weakened
raw proof is reified or supplied as an original semantic premise.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor
open OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Consume the genuine two-context application calls. The only argument
semantic premise is the prepared finite answer at the left natural domain.
Right formation clauses belong to the displayed application's fixed original
children and receive their exact captured TailFits contexts. -/
theorem ApplicationPreparation.compare
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
    {result : Profile n} {before : Footprint}
    (request : ApplicationPreparation (env := env) registry target leftLocals σ
      leftAvailable leftView result before)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftLe : leftEnv ≤ env) (rightLe : rightEnv ≤ env)
    (hTarget : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    (rightInitial : ContextDerivation rightEnv U rightRootSource)
    (rightFits : TailFits rightEnv env U registry target rightSource rightLocals τ τ rightAvailable)
    (rightClosed : rightAvailable.AtomClosed)
    (leftMap rightMap : Lift) (common : Subst) (commonLocals : List Nat)
    (leftRealization : Subst.lift_l leftMap common = σ)
    (rightRealization : Subst.lift_l rightMap common = τ)
    (sameArgument : leftArgument.lift' leftMap = rightArgument.lift' rightMap)
    (leftAvailableEq : ∀ index, leftAvailable index = commonAvailable (leftMap.liftVar index))
    (rightAvailableEq : ∀ index, rightAvailable index = commonAvailable (rightMap.liftVar index))
    (argumentAnswer : request.Answer)
    (functionAnswer : CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      (.forallE leftView.domainExpression leftView.codomainExpression)
      (.forallE rightView.domainExpression rightView.codomainExpression)
      (request.complete henv leftLe hTarget leftSubstitutions argumentAnswer).profile)
    (rightDomain : StateFundamental env registry
      (rightView.location.contextDerivation rightInitial) rightView.domain)
    (rightBody : StateFundamental env registry
      ((Located.appCodomain rightView.location).contextDerivation rightInitial) rightView.codomain) :
    Nonempty (CodeTransferResult env U registry target rightLocals σ τ rightAvailable
      (leftView.codomainExpression.inst leftArgument)
      (rightView.codomainExpression.inst rightArgument) result) := by
  let frame := request.complete henv leftLe hTarget leftSubstitutions argumentAnswer
  let originalDomain := Classical.choose rightView.location.originalDomains.1
  have domain_eq : rightView.domain = .ref originalDomain :=
    Classical.choose_spec rightView.location.originalDomains.1
  have domainIH : EndpointFundamental env registry
      (rightView.location.contextDerivation rightInitial) originalDomain := by
    simpa only [domain_eq] using rightDomain
  have bodyIH : StateFundamental env registry
      (.cons (rightView.location.contextDerivation rightInitial) originalDomain) rightView.codomain :=
    rightBody
  have origins := functionAnswer.certificate.piOriginsOriginal henv hscoped rightLe hTarget rightClosed
    (rightView.location.contextDerivation rightInitial) originalDomain rightView.codomain
    rightSubstitutions rightFits domainIH bodyIH functionAnswer.available
  obtain ⟨row⟩ := origins _ (List.mem_singleton_self _) frame.key _ (List.mem_singleton_self _)
  have argumentEq := realized_between_displays sameArgument leftRealization rightRealization
  have admitted : Admitted env U registry target frame.key
      (rightArgument.subst τ) (rightArgument.subst τ) := by
    rw [← argumentEq]
    exact frame.guard.anchor
  have admissionCopy := admitted
  obtain ⟨_, _, _, _, _, _, anchorRelated, _⟩ := admissionCopy
  have live := Related.live henv hscoped hTarget anchorRelated
  obtain ⟨argumentFootprint, ⟨argumentObservation⟩, argumentResources⟩ :=
    Obs.betweenDisplays frame.argumentObservation leftMap rightMap common
      leftRealization rightRealization sameArgument commonLocals rightLocals
      frame.argumentResources leftAvailableEq rightAvailableEq
  let sourceArgument : GradedResult env U registry target rightLocals τ rightAvailable
      rightArgument frame.key.input :=
    { rank := frame.collected.rank
      bound := Nat.le_refl _
      raw := frame.input
      footprint := argumentFootprint
      observation := argumentObservation
      adapter := by rw [raiseProfile_self]; exact .refl _
      resources := argumentResources
      live := live }
  obtain ⟨rightCode⟩ := rowInstantiateOriginal henv hscoped rightLe hTarget rightClosed
    (rightView.location.contextDerivation rightInitial) originalDomain rightView.codomain
    rightSubstitutions rightFits domainIH bodyIH row admitted sourceArgument
  have paired := literalPiBody henv hscoped hTarget
    (by simpa only [SeededApplicationCodeInput.profile, subst] using functionAnswer.related) admitted
  have bound := Nat.le_trans (Nat.le_max_left n frame.seed.rank) frame.collected.bound
  refine ⟨⟨rightCode.footprint, rightCode.certificate.lowerRaised bound, rightCode.resources, ?_⟩⟩
  have lowered := TypeRelated.lower henv bound paired
  change TypeRelated env U registry target _ _ (lowerProfile n bound (raiseProfile frame.collected.rank bound result)) at lowered
  rw [lower_raised] at lowered
  simpa only [subst_inst, argumentEq] using lowered

/-- Every fixed formation/function call uses its actual captured environment.
In particular the codomain retains the original domain-formation closure. -/
theorem app_children_cost_lt
    {root : EndpointRef env U rootSource rootExpression rootType}
    {node : EndpointState env U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start) (initial : List Closure) :
    (Closure.close view.function.origin (view.location.environment initial)).cost <
        (Closure.close node.origin (start.environment initial)).cost ∧
      (Closure.close view.domain.origin (view.location.environment initial)).cost <
        (Closure.close node.origin (start.environment initial)).cost ∧
      (Closure.close view.codomain.origin
        (.close view.domain.origin (view.location.environment initial) ::
          view.location.environment initial)).cost <
        (Closure.close node.origin (start.environment initial)).cost := by
  have functionBound := binder_other_cost (domain := view.domain.origin)
    (bodies := [view.codomain.origin])
    (children := [view.function.origin, view.argument.origin, view.result.origin])
    (child := view.function.origin) (by simp) (view.location.environment initial)
  have domainBound := binder_domain_cost view.domain.origin [view.codomain.origin]
    [view.function.origin, view.argument.origin, view.result.origin]
    (view.location.environment initial)
  have bodyBound := binder_body_cost (domain := view.domain.origin)
    (bodies := [view.codomain.origin])
    (children := [view.function.origin, view.argument.origin, view.result.origin])
    (body := view.codomain.origin) (by simp) (view.location.environment initial)
  exact ⟨Nat.lt_of_lt_of_le functionBound (view.cost_le initial),
    Nat.lt_of_lt_of_le domainBound (view.cost_le initial),
    Nat.lt_of_lt_of_le bodyBound (view.cost_le initial)⟩

/-- The exact function query may grow while both original function endpoints
strictly decrease inside the two-context comparison. -/
theorem application_function_pair_schedule
    {leftRoot : EndpointRef leftEnv U leftRootSource leftRootExpression leftRootType}
    {rightRoot : EndpointRef rightEnv U rightRootSource rightRootExpression rightRootType}
    {leftNode : EndpointState leftEnv U leftSource (.app leftFunction leftArgument) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.app rightFunction rightArgument) rightAssigned}
    {leftStart : Located leftRoot leftNode} {rightStart : Located rightRoot rightNode}
    (leftView : AppView leftStart) (rightView : AppView rightStart)
    (leftInitial rightInitial : List Closure) :
    schedule .coherence
      ((Closure.close leftView.function.origin (leftView.location.environment leftInitial)).cost +
        (Closure.close rightView.function.origin (rightView.location.environment rightInitial)).cost) <
      schedule .coherence
        ((Closure.close leftNode.origin (leftStart.environment leftInitial)).cost +
          (Closure.close rightNode.origin (rightStart.environment rightInitial)).cost) := by
  apply schedule_strict
  exact Nat.add_lt_add (app_children_cost_lt leftView leftInitial).1
    (app_children_cost_lt rightView rightInitial).1

/-- The original cut-versus-argument calls fit inside the local left
application, hence also inside the paired comparison. This uses the result
child's actual factor bound, including its relative source boundary. -/
theorem ApplicationPreparation.paired_cuts_schedule
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} {view : AppView start}
    (request : ApplicationPreparation (env := env) registry target locals σ available view result before)
    (initial : List Closure) (rightCost : Nat) :
    schedule .coherence (request.cuts.cost initial +
      (Closure.close view.argument.origin (view.location.environment initial)).cost) <
      schedule .coherence ((Closure.close node.origin (start.environment initial)).cost + rightCost) := by
  apply schedule_strict
  exact Nat.lt_of_lt_of_le
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right (request.cutsBound initial) _)
      (view.result_argument_cost_lt initial))
    (Nat.le_add_right _ _)

/-- The right replay's two semantic suppliers are fixed original formation
children, each strictly below the paired application call. -/
theorem application_right_formation_schedule
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app function argument) assigned}
    {start : Located root node} (view : AppView start)
    (initial : List Closure) (leftCost : Nat) :
    schedule .fundamental
      (Closure.close view.domain.origin (view.location.environment initial)).cost <
        schedule .coherence (leftCost + (Closure.close node.origin (start.environment initial)).cost) ∧
      schedule .fundamental
        (Closure.close view.codomain.origin
          (.close view.domain.origin (view.location.environment initial) ::
            view.location.environment initial)).cost <
        schedule .coherence (leftCost + (Closure.close node.origin (start.environment initial)).cost) := by
  obtain ⟨_, domainBound, bodyBound⟩ := app_children_cost_lt view initial
  constructor <;> apply schedule_strict
  · exact Nat.lt_of_lt_of_le domainBound (Nat.le_add_left _ _)
  · exact Nat.lt_of_lt_of_le bodyBound (Nat.le_add_left _ _)

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
