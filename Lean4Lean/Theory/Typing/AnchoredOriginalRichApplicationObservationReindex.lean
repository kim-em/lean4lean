import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationTransport
import Lean4Lean.Theory.Typing.AnchoredOriginalRichOutputReplay

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem RichObs.applicationSeedsRooted
    {profile : Profile n}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    (query : RichObs sourceEnv env U registry target node locals σ profile footprint)
    (location : Located root node) :
    ∃ seeds : RichApplicationSeeds root env registry target source locals σ f a footprint profile.atoms,
      seeds.RootedAt node := by
  have each := fun atom member => query.applicationOriginRooted location (atom := atom) member
  suffices collect : ∀ atoms : List (Atom n),
      (∀ atom ∈ atoms, ∃ origin : RichAppOrigin root env registry target source locals σ f a,
        Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
        List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
          origin.RootedAt node) →
      ∃ seeds : RichApplicationSeeds root env registry target source locals σ f a footprint atoms,
        seeds.RootedAt node from collect profile.atoms each
  intro atoms
  induction atoms with
  | nil => exact fun _ => ⟨.nil, trivial⟩
  | cons atom atoms ih =>
    intro each
    obtain ⟨origin, ⟨path⟩, included, rooted⟩ := each atom (by simp)
    obtain ⟨rest, rootedRest⟩ := ih (fun a h => each a (by simp [h]))
    exact ⟨.cons origin path included rest, rooted, rootedRest⟩

theorem RichAppOrigin.reindexObservation
    {A B : VExpr} {u v : VLevel}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {rightFunction : EndpointState rightEnv U rightSource rightFn (.forallE A B)}
    {rightArgument : EndpointState rightEnv U rightSource rightArg A}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : rightAvailable.AtomClosed)
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (path : GeneralOutputPath env U registry target origin.output atom)
    (domain : EndpointState rightEnv U rightSource A (.sort u))
    (codomain : EndpointState rightEnv U (A :: rightSource) B (.sort v))
    (result : EndpointState rightEnv U rightSource (B.inst rightArg) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (argumentEq : a.subst σ = rightArg.subst τ)
    (function : RichGradedResult rightEnv env U registry target rightFunction rightLocals τ
      rightAvailable (Profile.fn origin.key origin.output))
    (argument : RichGradedResult rightEnv env U registry target rightArgument rightLocals τ
      rightAvailable origin.rawInput) :
    Nonempty (RichGradedResult rightEnv env U registry target
      (.app hu hv domain codomain rightFunction rightArgument result) rightLocals τ rightAvailable
      (.singleton atom)) := by
  have admitted : Admitted env U registry target origin.key (rightArg.subst τ) (rightArg.subst τ) :=
    argumentEq ▸ origin.admitted
  obtain ⟨application⟩ := RichGradedResult.app henv hscoped formed closed domain codomain result hu hv
    function argument origin.arguments admitted
  exact application.outputPath henv hscoped formed path

theorem RichApplicationReplies.reindexObservation
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {rightFunction : EndpointState rightEnv U rightSource rightFn (.forallE A B)}
    {rightArgument : EndpointState rightEnv U rightSource rightArg A}
    {seeds : RichApplicationSeeds root env registry target source locals σ f a footprint atoms}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : rightAvailable.AtomClosed)
    (replies : RichApplicationReplies rightFunction rightArgument rightLocals τ rightAvailable seeds)
    (domain : EndpointState rightEnv U rightSource A (.sort u))
    (codomain : EndpointState rightEnv U (A :: rightSource) B (.sort v))
    (result : EndpointState rightEnv U rightSource (B.inst rightArg) (.sort v))
    (hu : u.WF U) (hv : v.WF U)
    (argumentEq : a.subst σ = rightArg.subst τ) :
    Nonempty (RichGradedResult rightEnv env U registry target
      (.app hu hv domain codomain rightFunction rightArgument result) rightLocals τ rightAvailable
      (.mk atoms)) := by
  induction replies with
  | nil => exact ⟨.empty⟩
  | cons fn arg tail ih =>
    rename_i footprint atoms origin path included rest
    obtain ⟨head⟩ := origin.reindexObservation henv hscoped formed closed path
      domain codomain result hu hv argumentEq fn arg
    obtain ⟨tail⟩ := ih henv hscoped formed argumentEq
    exact ⟨head.union henv hscoped formed tail⟩

open private app_child_costs from Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationTransport

section
variable
    {leftHeader : EndpointRef leftEnv U [] lhe lht}
    {leftField : EndpointRef leftOwnerEnv U leftOwnerSource lfe lft}
    {leftMajor : EndpointRef leftOwnerEnv U leftOwnerSource lme lmt}
    {rightHeader : EndpointRef rightEnv U [] rhe rht}
    {rightField : EndpointRef rightOwnerEnv U rightOwnerSource rfe rft}
    {rightMajor : EndpointRef rightOwnerEnv U rightOwnerSource rme rmt}
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    {leftNode : EndpointState leftEnv U leftSource (.app f a) leftAssigned}
    {rightNode : EndpointState rightEnv U rightSource (.app g b) rightAssigned}
    {leftRoot : EndpointRef leftEnv U leftRootSource lre lrt}
    {rightRoot : EndpointRef rightEnv U rightRootSource rre rrt}

/-- The continuation receives only actual retained child queries and their
strict pair bounds. The result retains destination source syntax, its finite
directional adapter, available resources, and actual raw-profile liveness. -/
theorem HeaderBinderFrame.applicationObservationReindexStep
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (leftOrdered : leftEnv.Ordered) (leftOwnerOrdered : leftOwnerEnv.Ordered)
    (rightOrdered : rightEnv.Ordered) (rightOwnerOrdered : rightOwnerEnv.Ordered)
    (leftInitial rightInitial : List Closure)
    (leftFrame : HeaderBinderFrame leftHeader leftField leftMajor env registry target
      leftContext leftLocals σ σ leftAvailable)
    (rightFrame : HeaderBinderFrame rightHeader rightField rightMajor env registry target
      rightContext rightLocals τ τ rightAvailable)
    (leftLocation : Located leftRoot leftNode)
    (rightLocation : Located rightRoot rightNode)
    (rightClosed : rightAvailable.AtomClosed)
    (argumentEq : a.subst σ = b.subst τ)
    (functionR : ∀ origin : RichAppOrigin leftRoot env registry target leftSource leftLocals σ f a,
      origin.RootedAt leftNode →
      richSchedule .expressionReindex
        ((Closure.close (origin.functionNode.dependencyOrigin leftOrdered)
          (leftFrame.dependencyEnvironment leftOrdered leftOwnerOrdered leftInitial)).cost +
         (Closure.close ((applicationPrefix rightLocation).view.function.dependencyOrigin rightOrdered)
          (rightFrame.dependencyEnvironment rightOrdered rightOwnerOrdered rightInitial)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (leftNode.dependencyOrigin leftOrdered)
          (leftFrame.dependencyEnvironment leftOrdered leftOwnerOrdered leftInitial)).cost +
         (Closure.close (rightNode.dependencyOrigin rightOrdered)
          (rightFrame.dependencyEnvironment rightOrdered rightOwnerOrdered rightInitial)).cost) →
      origin.functionFootprint.Available leftAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target
        (applicationPrefix rightLocation).view.function rightLocals τ rightAvailable
        (Profile.fn origin.key origin.output)))
    (argumentR : ∀ origin : RichAppOrigin leftRoot env registry target leftSource leftLocals σ f a,
      origin.RootedAt leftNode →
      richSchedule .expressionReindex
        ((Closure.close (origin.argumentNode.dependencyOrigin leftOrdered)
          (leftFrame.dependencyEnvironment leftOrdered leftOwnerOrdered leftInitial)).cost +
         (Closure.close ((applicationPrefix rightLocation).view.argument.dependencyOrigin rightOrdered)
          (rightFrame.dependencyEnvironment rightOrdered rightOwnerOrdered rightInitial)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (leftNode.dependencyOrigin leftOrdered)
          (leftFrame.dependencyEnvironment leftOrdered leftOwnerOrdered leftInitial)).cost +
         (Closure.close (rightNode.dependencyOrigin rightOrdered)
          (rightFrame.dependencyEnvironment rightOrdered rightOwnerOrdered rightInitial)).cost) →
      origin.argumentFootprint.Available leftAvailable →
      Nonempty (RichGradedResult rightEnv env U registry target
        (applicationPrefix rightLocation).view.argument rightLocals τ rightAvailable origin.rawInput))
    (query : RichObs leftEnv env U registry target leftNode leftLocals σ profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (RichGradedResult rightEnv env U registry target rightNode rightLocals τ
      rightAvailable profile) := by
  let rightPrefix := applicationPrefix rightLocation
  let leftCaptured := leftFrame.dependencyEnvironment leftOrdered leftOwnerOrdered leftInitial
  let rightCaptured := rightFrame.dependencyEnvironment rightOrdered rightOwnerOrdered rightInitial
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
