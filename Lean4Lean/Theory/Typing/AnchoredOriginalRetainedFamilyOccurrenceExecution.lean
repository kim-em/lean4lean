import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyWorldExecution

/-! The actual first retained family history initializes positive occurrence
storage. Only this already coherent initial dictionary is reused; subsequent
compositions keep distinct generations at each annotated position. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private transportWorld from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem retainedFirstFamilyOccurrenceExecution
    {U : Nat} {P : VEnv → Prop} {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {strata : EquationStratification env} {frontier : List (World strata.rules.length)}
    {outer : EndpointState sourceEnv U source (.proj projectedName index displayedMajor) outerType}
    (head : OriginalFactorCut.ProjectionHead outer)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    (majorLocation : Located (.right head.major) (.ref major))
    (initial : ContextDerivation sourceEnv U source)
    (graph : OriginalCaptureMap (common := common) initial raw)
    (frame : OriginalTypeRouteFrame env registry target graph commonLeft commonRight)
    (controls : OriginalWorldControls strata sourceEnv) (below : sourceEnv ≤ env)
    (captured : WorldEnvironmentProvenance strata U
      (frame.realization.frame.dependencyEnvironment controls.ordered))
    (consumed : RetainedRichFamilyConsumption major env registry target locals σ available
      name levels (argument :: arguments) (n := n+1) (.family demand))
    {base : OriginalCaptureBase env U registry target}
    (worldGenerated : WorldGenerated strata P base caps commonLeft commonRight graph frame.realization.frame.raw controls)
    (worldReplayable : worldGenerated.Replayable)
    (worldReady : worldGenerated.Controlled frontier)
    (worldCompatible : worldGenerated.UsesControlPrefix controls.cutoff controls.fuel)
    (worldCovered : Covered (@EquationControlMeasure.Less strata.rules.length) worldGenerated.worlds captured.worlds)
    (headerSource : P consumed.seed.origin.source) :
    ∃ A domains, consumed.seed.signature.domains = A :: domains ∧
      ∃ shape : consumed.seed.info.type.instL consumed.seed.seed =
          .forallE A (wrapForalls domains consumed.seed.signature.result),
      let left := assignedFamilyRouteSide major initial graph 0 rfl
      let right := RetainedHeaderUniverse.nativeSide consumed.seed.origin consumed.seed.seedWF shape common
      ∃ history : OriginalApplyPiHistory env registry target commonLeft commonRight left right,
        history.AmbientGenerated base caps ∧
        history.whole.SourceGenerated P base caps ∧
        SourceCaptureGenerated P base caps commonLeft commonRight right.graph
          history.headerFrame.realization.frame.raw ∧
        history.sourceFrame = assignedFamilyRouteFrame major initial graph 0 rfl frame ∧
        history.final = [] ∧
        right.sourceEnv ≤ env ∧
        right.A = A ∧ right.B = wrapForalls domains consumed.seed.signature.result ∧
        ∃ inputs : history.whole.WorldInputs strata,
          Sponsored [originalCallWorld controls .assignedComparison outer captured]
            (history.whole.worldReserve inputs).worlds ∧
          ∃ sourceEnvironment : history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered =
              frame.realization.frame.dependencyEnvironment controls.ordered,
          ∃ finalWorld : WorldEnvironmentProvenance strata U history.final,
            finalWorld.worlds = [] ∧
            ∃ boundary : history.whole.WorldBoundary inputs controls (controls.atHeader consumed.seed.origin)
              (transportWorld sourceEnvironment.symm captured) finalWorld,
            ∃ frameControls : ∀ position : Fin history.whole.frames.length,
              OriginalWorldControls strata (history.whole.frames[position]).sourceEnv,
            ∃ frameGenerated : ∀ position : Fin history.whole.frames.length,
              WorldGenerated strata P base caps commonLeft commonRight (history.whole.frames[position]).graph
                (history.whole.frames[position]).frame.realization.frame.raw (frameControls position),
              boundary.FrameOccurrenceCoherent frameControls frameGenerated ∧
              ∀ position, (frameGenerated position).Replayable ∧
                Nonempty ((frameGenerated position).Controlled frontier) ∧
                (frameGenerated position).UsesControlPrefix controls.cutoff controls.fuel := by
  obtain ⟨A, domains, domainsEq, shape, history, ambient, generated, headerGenerated,
      sourceFrameEq, finalEq, headerBelow, domainEq, bodyEq, inputs, sponsored,
      sourceEnvironment, finalWorld, finalWorlds, boundary, frameControls,
      frameGenerated, coherent, ready⟩ :=
    retainedFirstFamilyWorldExecution henv hscoped formed head major majorLocation initial graph frame
      controls below captured consumed worldGenerated worldReplayable worldReady worldCompatible
      worldCovered headerSource
  refine ⟨A, domains, domainsEq, shape, history, ambient, generated, headerGenerated,
    sourceFrameEq, finalEq, headerBelow, domainEq, bodyEq, inputs, sponsored,
    sourceEnvironment, finalWorld, finalWorlds, boundary,
    (fun position => frameControls (history.whole.frames[position]) (List.getElem_mem _)),
    (fun position => frameGenerated (history.whole.frames[position]) (List.getElem_mem _)),
    coherent.occurrences, ?_⟩
  intro position
  exact ready (history.whole.frames[position]) (List.getElem_mem _)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
