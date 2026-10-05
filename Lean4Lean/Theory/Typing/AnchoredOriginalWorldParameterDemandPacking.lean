import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterAssignedDemand
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationAssignedPacking

/-! Construct the richer parameter request from the actual field sort seed,
actual extra value observer, and original application body packet. Both value
and assigned-code channels are present in the SAME controlled packed query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem raiseProfile_sortFlags {n N : Nat} (bound : n ≤ N) (profile : Profile n) :
    (raiseProfile N bound profile).sortFlags = profile.sortFlags := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n; rw [raiseProfile_self]
    · have previous : n ≤ N := by omega
      rw [raiseProfile_step previous]
      simpa only [Profile.sortFlags, Profile.down_pad] using ih previous

/-- All F/C/R calls are strict children of the actual outer projection pair.
The extra value profile need not agree with the body query's grade, and its
actual raw observer is included explicitly rather than inferred from old
key coverage. -/
theorem ProjectionHead.parameterDemandPackedWorld
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
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location
      frame.frame frame.substitutions controls.ordered relevant (profile : Profile n))
    (headReady : ∀ query ∈ packet.reply.answer.reply.realization.frame.raw.storedQueries,
      Nonempty (ControlledStoredQuery controls frontier query))
    (bodyReady : ControlledStoredQuery controls frontier (.certificate packet.certificate))
    (supply : RichArgumentSupply sourceEnv env U registry target argument locals (raw.comp commonLeft)
      available packet.footprint.localNeeds)
    (supplyReady : supply.Controlled controls frontier)
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
  obtain ⟨seedFootprint, seed, seedResources, seedRelated, seedPath, ⟨seedReady⟩⟩ :=
    ProjectionHead.parameterAssignedSortWorld (n := n) head (.appArgument majorLocation)
      fieldProvenance (.ofLocation (.appArgument location) initial) controls frame generated
      frontier frameReady frameReplayable frameCompatible frameHereditary baseline capacity covered other henv hscoped formed closed paid replayBank
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
  obtain ⟨output, ready, seedBound, seedIncluded, extraBound, extraIncluded, _⟩ :=
    ApplicationBackwardQueries.piRequestAssignedDemandWorld controls frame generated frontier frameReady frameReplayable frameCompatible frameHereditary
      generated.environment (Nat.le_refl _) (Covered.refl _) packet headReady bodyReady supply supplyReady
      henv hscoped formed closed extraQuery extraReady seed seedResources seedReady appPaid appUnary appReplay
  have member : assignedSortFlag head.fieldLevel ∈
      (raiseProfile output.request.rank seedBound
        (Profile.sort (n := n) (assignedSortFlag head.fieldLevel))).sortFlags := by
    rw [raiseProfile_sortFlags, Profile.sortFlags_sort]
    exact List.mem_singleton_self _
  exact ⟨output, ready, Profile.sortFlags_mono (fun _ present => seedIncluded _ present) member,
    extraBound, extraIncluded⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
