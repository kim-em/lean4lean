import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationObservationReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational

/-! Application query reconstruction at arbitrary actual original frames.
Every retained source origin produces strictly smaller calls on its own
function and argument. Full output actions and conversion routes survive. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

open private app_child_costs from Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationTransport

section
variable
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    {leftNode : EndpointState leftEnv U leftSource (.app f a) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.app g b) rightAssigned}
    {leftRoot : EndpointRef leftEnv U leftRootSource lre lrt}
    {rightRoot : EndpointRef rightEnv U rightRootSource rre rrt}

/-- The continuation receives only actual retained child queries and their
strict pair bounds. The result retains destination source syntax, its finite
directional adapter, available resources, and actual raw-profile liveness. -/
theorem OriginalRichFrame.applicationObservationReindexStep
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (leftOrdered : leftEnv.Ordered)
    (rightOrdered : rightEnv.Ordered)
    (leftFrame : OriginalRichFrame leftEnv env U registry target
      leftContext leftLocals σ σ leftAvailable)
    (rightFrame : OriginalRichFrame rightEnv env U registry target
      rightContext rightLocals τ τ rightAvailable)
    (leftLocation : Located leftRoot leftNode)
    (rightLocation : Located rightRoot rightNode)
    (rightClosed : rightAvailable.AtomClosed)
    (argumentEq : a.subst σ = b.subst τ)
    (functionR : ∀ origin : RichAppOrigin leftRoot env registry target leftSource leftLocals σ f a,
      origin.RootedAt leftNode →
      richSchedule .expressionReindex
        ((Closure.close (origin.functionNode.dependencyOrigin leftOrdered)
          (leftFrame.dependencyEnvironment leftOrdered)).cost +
         (Closure.close ((applicationPrefix rightLocation).view.function.dependencyOrigin rightOrdered)
          (rightFrame.dependencyEnvironment rightOrdered)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (leftNode.dependencyOrigin leftOrdered)
          (leftFrame.dependencyEnvironment leftOrdered)).cost +
         (Closure.close (rightNode.dependencyOrigin rightOrdered)
          (rightFrame.dependencyEnvironment rightOrdered)).cost) →
      origin.functionFootprint.Available leftAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target
        (applicationPrefix rightLocation).view.function rightLocals τ rightAvailable
        (Profile.fn origin.key origin.output)))
    (argumentR : ∀ origin : RichAppOrigin leftRoot env registry target leftSource leftLocals σ f a,
      origin.RootedAt leftNode →
      richSchedule .expressionReindex
        ((Closure.close (origin.argumentNode.dependencyOrigin leftOrdered)
          (leftFrame.dependencyEnvironment leftOrdered)).cost +
         (Closure.close ((applicationPrefix rightLocation).view.argument.dependencyOrigin rightOrdered)
          (rightFrame.dependencyEnvironment rightOrdered)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (leftNode.dependencyOrigin leftOrdered)
          (leftFrame.dependencyEnvironment leftOrdered)).cost +
         (Closure.close (rightNode.dependencyOrigin rightOrdered)
          (rightFrame.dependencyEnvironment rightOrdered)).cost) →
      origin.argumentFootprint.Available leftAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target
        (applicationPrefix rightLocation).view.argument rightLocals τ rightAvailable origin.rawInput))
    (query : RichObs leftEnv env U registry target leftNode leftLocals σ profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (RichGradedResult rightEnv env U registry target rightNode rightLocals τ
      rightAvailable profile) := by
  let rightPrefix := applicationPrefix rightLocation
  let leftCaptured := leftFrame.dependencyEnvironment leftOrdered
  let rightCaptured := rightFrame.dependencyEnvironment rightOrdered
  obtain ⟨seeds, rooted⟩ := query.applicationSeedsRooted leftLocation
  have destinationChildren := app_child_costs rightOrdered rightPrefix.view.domain rightPrefix.view.codomain
    rightPrefix.view.function rightPrefix.view.argument rightPrefix.view.result
    rightPrefix.view.domainWF rightPrefix.view.bodyWF rightCaptured
  have destinationParent := rightPrefix.route.dependency_cost_le rightOrdered rightCaptured
  have rightFunctionBound := Nat.lt_of_lt_of_le destinationChildren.1 destinationParent
  have rightArgumentBound := Nat.lt_of_lt_of_le destinationChildren.2 destinationParent
  have collect : ∀ {n} {atoms : List (Atom n)}
      (seeds : RichApplicationSeeds leftRoot env registry target leftSource leftLocals σ f a footprint atoms),
      seeds.RootedAt leftNode → Nonempty (RichApplicationReplies rightPrefix.view.function
        rightPrefix.view.argument rightLocals τ rightAvailable seeds) := by
    intro n atoms seeds rooted
    induction seeds with
    | nil => exact ⟨.nil⟩
    | cons origin path included rest ih =>
      have originalChildren := origin.rooted_child_costs leftOrdered rooted.1 leftCaptured
      have supplied := origin.originalResources included resources
      obtain ⟨fn⟩ := functionR origin rooted.1
        (richSchedule_strict (Nat.add_lt_add originalChildren.1 rightFunctionBound) _ _) supplied.1
      obtain ⟨arg⟩ := argumentR origin rooted.1
        (richSchedule_strict (Nat.add_lt_add originalChildren.2 rightArgumentBound) _ _) supplied.2
      obtain ⟨tail⟩ := ih rooted.2
      exact ⟨.cons fn arg tail⟩
  obtain ⟨replies⟩ := collect seeds rooted
  obtain ⟨answer⟩ := replies.reindexObservation henv hscoped formed rightClosed
    rightPrefix.view.domain rightPrefix.view.codomain rightPrefix.view.result
    rightPrefix.view.domainWF rightPrefix.view.bodyWF argumentEq
  exact ⟨⟨answer.rank, answer.bound, answer.raw, answer.footprint,
    .route rightPrefix.route answer.observation, answer.adapter, answer.resources, answer.live⟩⟩

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
