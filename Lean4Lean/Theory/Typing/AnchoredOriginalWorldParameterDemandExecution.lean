import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterDemandPacking
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationArguments

/-! The enriched projection-parameter request begins with an actual result
certificate. Its backward body query and all argument-owner queries are
computed by strict original calls, before the assigned/value demands are
packed into that same request. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

/-- No body packet or argument-answer supply is a caller obligation. The same
actual lower result-to-body reply supplies every requested argument owner. -/
theorem ProjectionHead.parameterDemandFromResultWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {outer : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {initial : ContextDerivation sourceEnv U rootSource}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source head.fieldType A}
    {result : EndpointState sourceEnv U source (B.inst head.fieldType) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    (majorLocation : Located (.right head.major) (.app hu hv (.ref domain) body function argument result))
    (fieldProvenance : EndpointProvenance (location.contextDerivation initial) head.field)
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (frameReady : generated.Controlled frontier)
    (frameReplayable : generated.Replayable)
    (frameCompatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (frameHereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (other : World strata.rules.length)
    (certificate : RichCert sourceEnv env U registry target result locals
      (raw.comp commonLeft) relevant (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (certificateReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (extraQuery : RichGradedResult sourceEnv env U registry target argument locals
      (raw.comp commonLeft) available (extra : Profile m))
    (extraReady : ControlledStoredQuery controls frontier (.observation extraQuery.observation))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison outer baseline])
    (unaryBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline]))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline])) :
    ∃ output : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
        locals (raw.comp commonLeft) available relevant profile,
      Nonempty (output.Controlled controls frontier) ∧
      assignedSortFlag head.fieldLevel ∈ output.request.support.sortFlags ∧
      ∃ extraBound : extraQuery.rank ≤ output.request.rank,
        ∀ atom ∈ (raiseProfile output.request.rank extraBound extraQuery.raw).atoms,
          atom ∈ output.request.key.input.atoms := by
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated frame.frame generated frameReady
    frameReplayable frameCompatible frameHereditary
  let application := EndpointState.app hu hv (.ref domain) body function argument result
  let parent := originalCallWorld controls .fundamental application generated.environment
  have outerAdmitted := originalCallWorld_boundedNode controls .assignedComparison outer
    generated.environment baseline capacity covered
  have applicationBelow : WorldBelow strata.rules.length parent
      (originalCallWorld controls .assignedComparison outer baseline) :=
    BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans outerAdmitted
      (ProjectionHead.parameter_below head majorLocation controls generated.environment
        .fundamental .assignedComparison)
  have actualDecrease : CallBelow strata.rules.length [parent]
      [other, originalCallWorld controls .assignedComparison outer baseline] := by
    have replace : CallBelow strata.rules.length [other, parent]
        [other, originalCallWorld controls .assignedComparison outer baseline] :=
      (split_call (fun world member => by cases List.mem_singleton.mp member; exact applicationBelow)).cons other
    have drop : CallBelow strata.rules.length [parent] [other, parent] :=
      .single (.head (replacement := []) (by intro world member; cases member))
    exact drop.trans replace
  have decrease : CallBelow strata.rules.length (frontier ++ [parent])
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline]) := by
    have appendDecrease : ∀ inherited : List (World strata.rules.length),
        CallBelow strata.rules.length (inherited ++ [parent])
          (inherited ++ [other, originalCallWorld controls .assignedComparison outer baseline]) := by
      intro inherited
      induction inherited with
      | nil => exact actualDecrease
      | cons world tail ih => exact ih.cons world
    exact appendDecrease frontier
  have appPaid : Sponsored frontier [parent] := by
    intro world member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, below⟩ := paid _ (List.mem_cons_of_mem other (List.mem_singleton_self _))
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans applicationBelow below⟩
  have appUnary : WorldBoundedUnaryCallBank env U registry strata P (frontier ++ [parent]) :=
    fun retained smaller => unaryBank retained (smaller.trans decrease)
  have appReplay : WorldBoundedCallBank env U registry strata P (frontier ++ [parent]) :=
    fun retained smaller => replayBank retained (smaller.trans decrease)
  obtain ⟨packet, supply, supplyReady⟩ :=
    generatedWorldApplicationArguments initial domain body function argument result hu hv location
      frame.frame frame.substitutions controls generated.environment frontier frameData
      generated.environment (Nat.le_refl _) (Covered.refl _) henv hscoped formed closed
      appPaid appReplay certificate resources certificateReady
  have headReady : ∀ query ∈ packet.reply.answer.reply.realization.frame.raw.storedQueries,
      Nonempty (ControlledStoredQuery controls frontier query) :=
    fun query member => packet.controlled.selectStored (packet.generation.storedQueries_in_retained member)
  exact ProjectionHead.parameterDemandPackedWorld head location majorLocation fieldProvenance controls
    frame generated frontier frameReady frameReplayable frameCompatible frameHereditary baseline capacity covered
    other packet.toApplicationBackwardQueries headReady packet.certificateReady supply supplyReady
    extraQuery extraReady henv hscoped formed closed paid unaryBank replayBank

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
