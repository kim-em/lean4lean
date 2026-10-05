import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationReply

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private app_child_costs from Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationTransport
set_option backward.isDefEq.respectTransparency false

/-- Full application source-query replay. Origins are extracted from all
current rich/legacy wrappers. Each child is reconstructed independently
under the original input pair budget, then finite replies are merged with
maximum environment cost. No recursive call sees the merged frame. -/
theorem applicationGeneratedQueryStep
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
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (lf : leftEnv.Ordered) (rf : rightEnv.Ordered)
    (leftFrame : OriginalGeneratedDisplayFrame base
      (applicationGeneratedSourceDisplay leftLocation leftInitial leftGraph leftFunction leftArgument)
      common leftLocals leftAvailable)
    (rightFrame : OriginalGeneratedDisplayFrame base
      (applicationGeneratedSourceDisplay rightLocation rightInitial rightGraph rightFunction rightArgument)
      common rightLocals rightAvailable)
    (leftCapped : CappedCaptureGenerated base commonCaps common common leftGraph leftFrame.capture.frame.raw)
    (rightCapped : CappedCaptureGenerated base commonCaps common common rightGraph rightFrame.capture.frame.raw)
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
      Nonempty (BoundedGeneratedQueryReply base commonCaps
        (applicationGeneratedFunctionSourceDisplay rightLocation rightInitial rightGraph
          (applicationPrefix rightLocation).route rightFunction)
        common common (Profile.fn origin.key origin.output)
        (environmentCost (rightFrame.capture.frame.dependencyEnvironment rf))))
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
      Nonempty (BoundedGeneratedQueryReply base commonCaps
        (applicationGeneratedArgumentSourceDisplay rightLocation rightInitial rightGraph
          (applicationPrefix rightLocation).route rightArgument)
        common common origin.rawInput
        (environmentCost (rightFrame.capture.frame.dependencyEnvironment rf))))
    (query : RichObs leftEnv env U registry target leftNode leftLocals (leftRaw.comp common)
      (profile : Profile n) footprint)
    (resources : footprint.Available leftAvailable) :
    Nonempty (BoundedGeneratedQueryReply base commonCaps
      (applicationGeneratedSourceDisplay rightLocation rightInitial rightGraph rightFunction rightArgument)
      common common profile (environmentCost (rightFrame.capture.frame.dependencyEnvironment rf))) := by
  let rightPrefix := applicationPrefix rightLocation
  let leftCaptured := leftFrame.capture.frame.dependencyEnvironment lf
  let rightCaptured := rightFrame.capture.frame.dependencyEnvironment rf
  obtain ⟨seeds, rooted⟩ := query.applicationSeedsRooted leftLocation
  have destinationChildren := app_child_costs rf rightPrefix.view.domain rightPrefix.view.codomain
    rightPrefix.view.function rightPrefix.view.argument rightPrefix.view.result
    rightPrefix.view.domainWF rightPrefix.view.bodyWF rightCaptured
  have destinationParent := rightPrefix.route.dependency_cost_le rf rightCaptured
  have rightFunctionBound := Nat.lt_of_lt_of_le destinationChildren.1 destinationParent
  have rightArgumentBound := Nat.lt_of_lt_of_le destinationChildren.2 destinationParent
  have same : a.subst (leftRaw.comp common) = b.subst (rightRaw.comp common) := by
    simpa only [subst_subst] using congrArg (fun e => e.subst common) (leftArgument.symm.trans rightArgument)
  have collect : ∀ {m} {atoms : List (Atom m)}
      (seeds : RichApplicationSeeds leftRoot env registry target leftSource leftLocals
        (leftRaw.comp common) f a footprint atoms),
      seeds.RootedAt leftNode → Nonempty (BoundedGeneratedQueryReply base commonCaps
        (applicationGeneratedSourceDisplay rightLocation rightInitial rightGraph rightFunction rightArgument)
        common common (.mk atoms) (environmentCost rightCaptured)) := by
    intro m atoms seeds rooted
    induction seeds with
    | nil =>
      exact ⟨.empty _ rightFrame.capture rightCapped rightClosed (fun _ => Nat.le_refl _)⟩
    | cons origin path included rest ih =>
      have originalChildren := origin.rooted_child_costs lf rooted.1 leftCaptured
      have supplied := origin.originalResources included resources
      obtain ⟨fn⟩ := functionR origin rooted.1
        (richSchedule_strict (Nat.add_lt_add originalChildren.1 rightFunctionBound) _ _) supplied.1
      obtain ⟨arg⟩ := argumentR origin rooted.1
        (richSchedule_strict (Nat.add_lt_add originalChildren.2 rightArgumentBound) _ _) supplied.2
      obtain ⟨head⟩ := boundedGeneratedApplicationReply rightLocation rightInitial rightGraph
        rightPrefix.route rightFunction rightArgument henv hscoped formed fn arg origin.arguments
        (same ▸ origin.admitted)
      obtain ⟨head⟩ := head.outputPath henv hscoped formed path
      obtain ⟨tail⟩ := ih rooted.2
      exact ⟨head.union henv hscoped formed tail⟩
  obtain ⟨answer⟩ := collect seeds rooted
  exact ⟨answer⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
