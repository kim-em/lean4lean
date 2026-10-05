import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterDemandExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFunctionPiBody
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCallerFamilyRequest

/-! The actual projection-parameter result demand is replayed backward into
its application body, enriched with the selected parameter demands, and
transferred to the caller function's assigned formation and its actual selected
Pi body is entered. All intermediate
queries and selected frames are produced internally from the outer banks. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

theorem ProjectionHead.parameterFunctionFormationWorld
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
    let side := originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph
    ∃ output : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
        locals (raw.comp commonLeft) available relevant profile,
      Nonempty (output.Controlled controls frontier) ∧
      assignedSortFlag head.fieldLevel ∈ output.request.support.sortFlags ∧
      (∃ extraBound : extraQuery.rank ≤ output.request.rank,
        ∀ atom ∈ (raiseProfile output.request.rank extraBound extraQuery.raw).atoms,
          atom ∈ output.request.key.input.atoms) ∧
      RankedData.RequestAdmission env U (relations env U registry output.request.rank) target
        output.parameterRequest (head.fieldType.subst (raw.comp commonLeft))
          (head.fieldType.subst (raw.comp commonRight)) ∧
      (∃ value : RichSupportedValue sourceEnv env U registry target argument locals
          (raw.comp commonLeft) (raw.comp commonRight) available output.request.key.input,
        value.support = output.request.support ∧
        Nonempty (ControlledStoredQuery controls frontier (.certificate value.certificate))) ∧
      ∃ answer : AmbientBoundedParameterReply base caps
          ((VExpr.forallE A B).subst (raw.comp commonLeft)) side.functionFormationDisplay
          commonLeft commonRight
          (Profile.pi (A.subst (raw.comp commonLeft)) (B.subst (raw.comp commonLeft).lift)
            output.request.support [(output.request.key, raiseProfile output.request.rank output.request.bound profile)])
          (environmentCost (frame.frame.dependencyEnvironment controls.ordered)),
      ∃ answerData : WorldParameterReplyData (P := P) controls generated.environment frontier answer,
        Nonempty (WorldPiPrefixBodyExecution (P := P)
          (piPrefix (.assignedFormation (.appFunction side.location))) controls frontier
          answer.reply.answer.reply.realization.frame.leftDiagonal
          (answer.reply.answer.reply.realization.frame.diagonalWorld controls answerData.generation.environment)
          relevant output.request.key (raiseProfile output.request.rank output.request.bound profile)) := by
  dsimp only
  have below : sourceEnv ≤ env := generated.erase.ambientGenerated.ambient.1.below
  obtain ⟨output, ⟨outputReady⟩, flagPresent, extraBound, extraIncluded⟩ :=
    ProjectionHead.parameterDemandFromResultWorld head location majorLocation fieldProvenance controls
      frame generated frontier frameReady frameReplayable frameCompatible frameHereditary baseline capacity covered
      other certificate resources certificateReady extraQuery extraReady henv hscoped formed closed paid unaryBank replayBank
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
  obtain ⟨value, valueSupport, valueReady, pairedRequest⟩ :=
    output.parameterRequestWorld controls frame generated frontier frameReady frameReplayable frameCompatible
      frameHereditary generated.environment (Nat.le_refl _) (Covered.refl _) henv hscoped formed closed
      outputReady appPaid appUnary appReplay
  let side := originalApplicationTypeRouteSide initial domain body function argument result hu hv location graph
  obtain ⟨answer, answerData, executed⟩ := side.piRequestFunctionBodyWorld controls frame generated frameReplayable
    frontier frameReady frameCompatible frameHereditary generated.environment (Nat.le_refl _) (Covered.refl _)
    henv hscoped below formed closed output.request outputReady.request appPaid appUnary appReplay
  exact ⟨output, ⟨outputReady⟩, flagPresent, ⟨extraBound, extraIncluded⟩, pairedRequest,
    ⟨value, valueSupport, valueReady⟩, answer, answerData, executed⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
