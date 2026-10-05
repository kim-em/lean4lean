import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationReindex
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationSeeding
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiStep

/-! Full application expression-code R step. Source unary F supplies the
actual code semantics. Bounded child R reconstructs the destination query,
including its original conversion prefix. Both budgets use the actual
captured frames, independently of the source location's structural context. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

private theorem app_child_costs
    (ordered : sourceEnv.Ordered)
    (domain : EndpointState sourceEnv U source A (.sort u))
    (body : EndpointState sourceEnv U (A :: source) B (.sort v))
    (fn : EndpointState sourceEnv U source f (.forallE A B))
    (arg : EndpointState sourceEnv U source a A)
    (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
    (hu : u.WF U) (hv : v.WF U) (captured : List Closure) :
    (Closure.close (fn.dependencyOrigin ordered) captured).cost <
      (Closure.close ((EndpointState.app hu hv domain body fn arg result).dependencyOrigin ordered) captured).cost ∧
    (Closure.close (arg.dependencyOrigin ordered) captured).cost <
      (Closure.close ((EndpointState.app hu hv domain body fn arg result).dependencyOrigin ordered) captured).cost := by
  have reserve := application_cost_le_captured (domain.dependencyOrigin ordered) (body.dependencyOrigin ordered)
    (fn.dependencyOrigin ordered) (arg.dependencyOrigin ordered) (result.dependencyOrigin ordered) captured
  exact ⟨Nat.lt_of_lt_of_le (binder_other_cost (by simp) captured) reserve,
    Nat.lt_of_lt_of_le (binder_other_cost (by simp) captured) reserve⟩

theorem RichAppOrigin.rooted_child_costs
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    (ordered : sourceEnv.Ordered)
    (origin : RichAppOrigin root env registry target source locals σ f a)
    (rooted : origin.RootedAt node) (captured : List Closure) :
    (Closure.close (origin.functionNode.dependencyOrigin ordered) captured).cost <
      (Closure.close (node.dependencyOrigin ordered) captured).cost ∧
    (Closure.close (origin.argumentNode.dependencyOrigin ordered) captured).cost <
      (Closure.close (node.dependencyOrigin ordered) captured).cost := by
  obtain ⟨route⟩ := rooted
  have parent := route.dependency_cost_le ordered captured
  have children := app_child_costs ordered origin.domain origin.codomain origin.functionNode
    origin.argumentNode origin.result origin.hu origin.hv captured
  exact ⟨Nat.lt_of_lt_of_le children.1 parent, Nat.lt_of_lt_of_le children.2 parent⟩

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
    {leftNode : EndpointState leftEnv U leftSource (.app f a) (.sort leftLevel)}
    {rightNode : EndpointState rightEnv U rightSource (.app g b) (.sort rightLevel)}
    {leftRoot : EndpointRef leftEnv U leftRootSource lre lrt}
    {rightRoot : EndpointRef rightEnv U rightRootSource rre rrt}

/-- The continuation receives only actual retained child queries and their
strict pair bounds. The complete result includes destination source syntax
and semantic expression transport, not merely a target capability. -/
theorem HeaderBinderFrame.applicationReindexStep
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
    (leftClosed : leftAvailable.AtomClosed) (rightClosed : rightAvailable.AtomClosed)
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (functionEq : f.subst σ = g.subst τ) (argumentEq : a.subst σ = b.subst τ)
    (sourceF : HeaderCodeInductionAt leftHeader leftField leftMajor env registry leftOrdered leftOwnerOrdered
      leftInitial leftContext leftNode
      ((Closure.close (leftNode.dependencyOrigin leftOrdered)
        (leftFrame.dependencyEnvironment leftOrdered leftOwnerOrdered leftInitial)).cost +
       (Closure.close (rightNode.dependencyOrigin rightOrdered)
        (rightFrame.dependencyEnvironment rightOrdered rightOwnerOrdered rightInitial)).cost))
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
    (query : RichCert leftEnv env U registry target leftNode leftLocals σ relevant profile footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (RichCodeTransferResult env U registry target leftNode rightNode rightLocals σ τ
      rightAvailable relevant profile) := by
  let rightPrefix := applicationPrefix rightLocation
  let leftCaptured := leftFrame.dependencyEnvironment leftOrdered leftOwnerOrdered leftInitial
  let rightCaptured := rightFrame.dependencyEnvironment rightOrdered rightOwnerOrdered rightInitial
  have rightPositive := (Closure.close (rightNode.dependencyOrigin rightOrdered) rightCaptured).cost_pos
  obtain ⟨semantics⟩ := sourceF target leftLocals σ σ leftAvailable leftFrame
    (by dsimp [leftCaptured, rightCaptured] at *; omega) leftClosed formed leftSubstitutions query resources
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
  obtain ⟨required, ⟨certificate⟩, available⟩ := replies.reindex henv hscoped formed rightClosed
    query.formed rightPrefix.view.domain rightPrefix.view.codomain rightPrefix.view.result
    rightPrefix.view.domainWF rightPrefix.view.bodyWF argumentEq
  exact ⟨{
    footprint := required
    certificate := .route rightPrefix.route certificate
    resources := available
    related := by simpa only [subst, ← functionEq, ← argumentEq] using semantics.related }⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
