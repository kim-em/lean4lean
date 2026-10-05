import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyInitialWorldRoute

/-! The first actual family application carries its exact whole-Pi world
reserve. Every reserved source call descends from the actual outer projection;
retained header calls use constant descent, irrespective of proof size. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private transport_sourceGenerated closed_sourceGenerated from
  Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiHistory
open private sameExpression_worldInputs sameExpression_worldReserve trans_worldInputs trans_worldReserve
  environment_worlds_mpr from Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
open private projectionMajor_cost_lt from Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionReindex
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private def transportWorld
    {strata : EquationStratification env} {first second : List Closure}
    (equal : first = second) (world : WorldEnvironmentProvenance strata U first) :
    WorldEnvironmentProvenance strata U second := equal ▸ world

private theorem transportWorld_worlds
    {strata : EquationStratification env} {first second : List Closure}
    (equal : first = second) (world : WorldEnvironmentProvenance strata U first) :
    (transportWorld equal world).worlds = world.worlds := by
  cases equal
  rfl

private theorem transportWorld_call
    {strata : EquationStratification env} {first second : List Closure}
    (equal : first = second) (world : WorldEnvironmentProvenance strata U first)
    (controls : OriginalWorldControls strata sourceEnv) (phase : RichPhase)
    (node : EndpointState sourceEnv U source expression assigned) :
    originalCallWorld controls phase node (transportWorld equal world) =
      originalCallWorld controls phase node world := by
  cases equal
  rfl

private theorem descendant_below
    {outer : EndpointState sourceEnv U source (.proj name index displayed) assigned}
    (head : OriginalFactorCut.ProjectionHead outer)
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (majorLocation : Located (.right head.major) (.ref major))
    {node : EndpointState sourceEnv U source expression type}
    (location : Located major node)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment) (phase parentPhase : RichPhase) :
    WorldBelow strata.rules.length (originalCallWorld controls phase node captured)
      (originalCallWorld controls parentPhase outer captured) := by
  have cost := Nat.le_trans (Located.sameSource_cost_le location controls.ordered environment)
    (Located.sameSource_cost_le majorLocation controls.ordered environment)
  exact original_child (richSchedule_strict
    (Nat.lt_of_le_of_lt cost (projectionMajor_cost_lt head controls.ordered environment))
    phase parentPhase) _ _ _ _ _

private theorem same_worldReserve
    {strata : EquationStratification env}
    (left : OriginalNestedDisplay U common expression leftAssigned)
    (right : OriginalNestedDisplay U common expression rightAssigned)
    (lf : left.sourceEnv.Ordered) (rf : right.sourceEnv.Ordered)
    (initial : List Closure)
    (frame : OriginalTypeRouteFrame env registry target right.graph commonLeft commonRight)
    (leftControls : OriginalWorldControls strata left.sourceEnv)
    (rightControls : OriginalWorldControls strata right.sourceEnv)
    (leftWorld : WorldEnvironmentProvenance strata U initial)
    (rightWorld : WorldEnvironmentProvenance strata U (frame.realization.frame.dependencyEnvironment rf)) :
    ((RawGeneratedTypeRoute.same left right lf rf initial frame).worldReserve
      (leftControls, rightControls, leftWorld, rightWorld)).worlds =
      [originalCallWorld leftControls .expressionReindex left.node leftWorld,
       originalCallWorld rightControls .expressionReindex right.node rightWorld] := by
  simp only [RawGeneratedTypeRoute.worldReserve, RawGeneratedTypeRoute.WorldInputs]
  rw [environment_worlds_mpr (RawGeneratedTypeRoute.reserve.eq_def
    (RawGeneratedTypeRoute.same left right lf rf initial frame))]
  rfl

theorem retainedFirstFamilyApplyPiWorldHistory
    {U : Nat} {P : VEnv → Prop} {demand : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {strata : EquationStratification env}
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
    (generated : SourceCaptureGenerated P base caps commonLeft commonRight graph frame.realization.frame.raw)
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
            Nonempty (history.whole.WorldBoundary inputs controls (controls.atHeader consumed.seed.origin)
              (transportWorld sourceEnvironment.symm captured) finalWorld) := by
  let ordered := controls.ordered
  have saturated := consumed.cursor.saturated henv hscoped formed
  cases domainsEq : consumed.seed.signature.domains with
  | nil => simp only [domainsEq, List.length_nil, List.length_cons] at saturated; omega
  | cons A domains =>
    have shape : consumed.seed.info.type.instL consumed.seed.seed =
        .forallE A (wrapForalls domains consumed.seed.signature.result) := by
      simpa only [domainsEq, wrapForalls, List.foldr_cons] using consumed.seed.signature.type_eq
    let left := assignedFamilyRouteSide major initial graph 0 rfl
    let sourceFrame := assignedFamilyRouteFrame major initial graph 0 rfl frame
    have sourceGenerated : SourceCaptureGenerated P base caps commonLeft commonRight left.graph
        sourceFrame.realization.frame.raw := transport_sourceGenerated _ frame generated
    let sourceWorld := transportWorld
      (assignedFamilyRouteFrame_environment major initial graph 0 rfl frame ordered).symm captured
    obtain ⟨selection, ledger, rootBound, equivalent, initialRoute, initialGenerated, initialInputs, initialWorlds, initialBoundary, _initialFrames⟩ :=
      retainedFamilyInitialWorldRoute left.initial (.appFunction left.location) left.graph sourceFrame controls below
        sourceWorld consumed.seed.origin consumed.seed.seedWF consumed.seed.equivalent caps sourceGenerated headerSource
    let right := RetainedHeaderUniverse.nativeSide consumed.seed.origin consumed.seed.seedWF shape common
    let headerFrame := RetainedHeaderUniverse.nativeFrame consumed.seed.origin consumed.seed.seedWF
      shape common env registry target commonLeft commonRight
    have headerGenerated : SourceCaptureGenerated P base caps commonLeft commonRight right.graph
        headerFrame.realization.frame.raw :=
      closed_sourceGenerated _ common caps commonLeft commonRight
        (consumed.seed.origin.sourceBelow.trans below) headerSource
    let first := RawGeneratedTypeRoute.same left.pi.display
      (OriginalNestedDisplay.ofOccurrence left.initial (.appFunction left.location) left.graph).formationDisplay
      ordered ordered (sourceFrame.realization.frame.dependencyEnvironment ordered) sourceFrame
    have firstGenerated : first.SourceGenerated P base caps := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [RawGeneratedTypeRoute.WellFormed.eq_def]; trivial
      · rw [RawGeneratedTypeRoute.Ambient.eq_def]; exact ⟨below, below⟩
      · rw [RawGeneratedTypeRoute.AllSources.eq_def]
        exact ⟨generated.sources.1.source, generated.sources.1.source, trivial⟩
      · intro boxed member
        rw [RawGeneratedTypeRoute.frames.eq_def, List.mem_singleton] at member
        subst boxed
        exact sourceGenerated
    have rightShape : consumed.seed.info.type.instL consumed.seed.seed =
        (VExpr.forallE right.A right.B).subst right.raw := shape.trans subst_id.symm
    let last := RawGeneratedTypeRoute.sameExpression
      (RetainedHeaderUniverse.display consumed.seed.origin consumed.seed.seedWF common) right.display rightShape
      consumed.seed.origin.ordered consumed.seed.origin.ordered [] headerFrame
    have lastGenerated : last.SourceGenerated P base caps :=
      RetainedHeaderUniverse.sourceGenerated_same _ _ _ _ _ _ _
        (consumed.seed.origin.sourceBelow.trans below) (consumed.seed.origin.sourceBelow.trans below)
        headerSource headerSource headerGenerated
    let selected := piPrefix
      ((Located.here (root := (consumed.seed.origin.familyHeader consumed.seed.seedWF).reference)).castExpression shape)
    let domain := Classical.choose selected.view.location.originalDomains.1
    have domainEq := Classical.choose_spec selected.view.location.originalDomains.1
    let history : OriginalApplyPiHistory env registry target commonLeft commonRight left right :=
      ⟨ordered, consumed.seed.origin.ordered, below, domain, domainEq, sourceFrame, headerFrame,
        first.trans (initialRoute.trans last)⟩
    have wholeGenerated : history.whole.SourceGenerated P base caps :=
      RetainedHeaderUniverse.sourceGenerated_trans firstGenerated
        (RetainedHeaderUniverse.sourceGenerated_trans initialGenerated lastGenerated)
    let firstInputs : first.WorldInputs strata := (controls, controls, sourceWorld, sourceWorld)
    let headerWorld := transportWorld
      (RetainedHeaderUniverse.nativeFrame_environment consumed.seed.origin consumed.seed.seedWF shape common
        env registry target commonLeft commonRight).symm
      (WorldEnvironmentProvenance.nil (strata := strata) (U := U))
    let lastInputs := sameExpression_worldInputs
      (RetainedHeaderUniverse.display consumed.seed.origin consumed.seed.seedWF common) right.display rightShape
      consumed.seed.origin.ordered consumed.seed.origin.ordered [] headerFrame
      (controls.atHeader consumed.seed.origin) (controls.atHeader consumed.seed.origin) .nil headerWorld
    refine ⟨A, domains, rfl, shape, history,
      ⟨sourceGenerated.ambientGenerated, headerGenerated.ambientGenerated, wholeGenerated.ambientGenerated⟩,
      wholeGenerated, headerGenerated, rfl,
      RetainedHeaderUniverse.nativeFrame_environment _ _ _ _ _ _ _ _ _,
      consumed.seed.origin.sourceBelow.trans below, rfl, rfl,
      trans_worldInputs firstInputs (trans_worldInputs initialInputs lastInputs), ?_,
      assignedFamilyRouteFrame_environment major initial graph 0 rfl frame ordered,
      headerWorld, ?_, ⟨?_⟩⟩
    · rw [trans_worldReserve, trans_worldReserve]
      apply Sponsored.merge
      · rw [same_worldReserve]
        simp only [sourceWorld, transportWorld_call]
        intro child member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
            (.appPiFormation left.location) controls captured _ _⟩
        · cases List.mem_singleton.mp member
          exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
            (.assignedFormation (.appFunction left.location)) controls captured _ _⟩
      · apply Sponsored.merge
        · rw [initialWorlds]
          apply Sponsored.merge
          · simp only [sourceWorld, transportWorld_call]
            intro child member
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            rcases member with rfl | rfl | rfl | rfl
            · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
                (.appFunction left.location) controls captured _ _⟩
            · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
                ((constantPrefix _).route.locate (.appFunction left.location)) controls captured _ _⟩
            · exact ⟨_, List.mem_singleton_self _, descendant_below head majorLocation
                (.assignedFormation ((constantPrefix _).route.locate (.appFunction left.location)))
                controls captured _ _⟩
            · exact ⟨_, List.mem_singleton_self _, originalClosedHeader_below controls consumed.seed.origin
                _ outer captured _ _⟩
          · exact RetainedHeaderUniverse.worldReserve_sponsored controls consumed.seed.origin consumed.seed.origin
              selection.seedWF consumed.seed.seedWF equivalent below common registry target
              commonLeft commonRight outer captured .assignedComparison
        · erw [sameExpression_worldReserve]
          simp only [headerWorld, transportWorld_call]
          intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨_, List.mem_singleton_self _, originalClosedHeader_below controls consumed.seed.origin
              _ outer captured _ _⟩
          · cases List.mem_singleton.mp member
            exact ⟨_, List.mem_singleton_self _, originalClosedHeader_below controls consumed.seed.origin
              _ outer captured _ _⟩
    · exact transportWorld_worlds _ _
    · exact .trans (.same _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩)
        (.trans initialBoundary
          (RawGeneratedTypeRoute.sameExpression_worldBoundary _ _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl⟩))



end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
