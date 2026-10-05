import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPackingData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyCaptureAssembly

/-! The backward application request starts with an actual empty own capture.
Its argument and domain worlds come from the original application children;
empty demands add no query-owned worlds or dormant semantic history. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private realizeWorld from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyCaptureAssembly
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)

theorem emptyWorldApplicationBodyFrame
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata sourceEnv)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph realized.frame.raw controls)
    (replayable : generated.Replayable)
    (frontier : List (World strata.rules.length))
    (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier) :
    ∃ next : OriginalCaptureRealization
        (applicationBodyDisplay initial domain body function argument result hu hv location graph).graph
        env registry target (Locals.push locals) commonLeft commonRight (available.push []),
      ∃ nextGenerated : WorldGenerated strata P base commonCaps commonLeft commonRight
        (applicationBodyDisplay initial domain body function argument result hu hv location graph).graph next.frame.raw controls,
        nextGenerated.Replayable ∧ Nonempty (nextGenerated.Controlled frontier) ∧
        nextGenerated.UsesControlPrefix controls.cutoff controls.fuel ∧
        (∀ ordered : sourceEnv.Ordered,
          next.frame.dependencyEnvironment ordered =
            [Closure.bundle
              (.close (argument.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered))
              (.close (domain.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered))] ++
            Closure.bundle (.close (argument.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered))
              (.close (domain.dependencyOrigin ordered) (realized.frame.dependencyEnvironment ordered)) ::
            realized.frame.dependencyEnvironment ordered) ∧
        nextGenerated.worlds = (ownCaptureWorldEnvironment controls domain argument generated.environment).worlds ∧
        Nonempty (nextGenerated.Hereditary frontier) := by
  let query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft)
      (.empty : Profile 0) [] := .legacy (.legacy .empty)
  let certificate : RichCert sourceEnv env U registry target (.ref domain) locals (raw.comp commonLeft)
      true (.empty : Profile 0) [] :=
    .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true)))
  have resources : Footprint.Available [] available := fun _ _ h => nomatch h
  have typed : (.empty : Profile 0).HasType .empty := Profile.HasType.empty Profile.WF.empty
  have arguments : Related env U registry target (a.subst (raw.comp commonLeft))
      (a.subst (raw.comp commonRight)) (A.subst (raw.comp commonLeft)) (.empty : Profile 0) .empty :=
    Related.of_singletons (fun _ h => nomatch h)
  let activeFrame := realized.frame.capture domain initial argument (.appArgument location) rfl
    query resources certificate resources typed arguments [] (fun _ h => nomatch h) (fun _ h => nomatch h)
  let frame := activeFrame.reserve [Closure.bundle
    (.close (argument.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered))
    (.close (domain.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered))]
  let nextGenerated : WorldGenerated strata P base commonCaps commonLeft commonRight
      (applicationBodyDisplay initial domain body function argument result hu hv location graph).graph frame.raw controls :=
    .capture generated generated.environment (Nat.le_refl _) domain initial argument (.appArgument location) rfl query resources
      (Nat.le_refl _) (by rw [raiseProfile_self]; exact .refl _) certificate resources
      typed arguments [] (fun _ h => nomatch h) (fun _ h => nomatch h)
  have nextReady : nextGenerated.Controlled frontier := by
    refine ⟨.cons (.legacy _ (.legacy _ .empty))
      (.cons (.legacy _ (.seed _ _ .empty)) ready.annotation), ?_, ?_⟩
    · intro control active
      change nextGenerated.retainedDepth _ ≤ _
      rw [← nextGenerated.retainedQueries_depth]
      change StoredOriginalQuery.maximumDepth _
        (.observation query :: .certificate certificate :: generated.retainedQueries) ≤ _
      simp only [StoredOriginalQuery.maximumDepth_cons, StoredOriginalQuery.headDepth,
        query, certificate, RichObs.headDepth, SortableObs.headDepth,
        RichCert.headDepth, SortableCert.headDepth, Obs.headDepth, Nat.zero_max,
        generated.retainedQueries_depth]
      exact ready.within control active
    · change Sponsored frontier ready.annotation.worlds
      exact ready.sponsored
  have nextCompatible : nextGenerated.UsesControlPrefix controls.cutoff controls.fuel := compatible
  have nextReplayable : nextGenerated.Replayable := ⟨replayable, fun world member => ⟨world, member, .inl rfl⟩⟩
  have below := generated.erase.ambientGenerated.ambient.1.below
  have rawPair := (argument.sound.defeq.mono below).substDF henv realized.substitutions.wf formed realized.substitutions
  have substitutions : Ctx.SubstEq env U target
      ((raw.comp commonLeft).cons (a.subst (raw.comp commonLeft)))
      ((raw.comp commonRight).cons (a.subst (raw.comp commonRight))) (A :: source) :=
    .cons realized.substitutions (domain.sound.defeq.mono below) rawPair
  let nextHereditary : nextGenerated.Hereditary frontier :=
    ⟨⟨hereditary.tablesClosed, by intro index need member; cases member⟩, hereditary.bases, hereditary.ready⟩
  obtain ⟨next, final, worlds, finalReady, finalCompatible, environment, finalReplayable, _, finalHereditary⟩ :=
    realizeWorld frame nextGenerated nextReady nextCompatible nextHereditary substitutions
  refine ⟨next, final, finalReplayable.mpr nextReplayable, finalReady, finalCompatible, ?_, ?_, finalHereditary⟩
  · intro ordered
    rw [environment]
    rfl
  · rw [worlds]
    rfl

/-- Both backward R endpoints and the newly captured argument/domain are
proper worlds of this actual application. The captured body keeps the two
real owner worlds instead of replacing them by a scalar capacity claim. -/
theorem applicationBodyWorldChildren
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U environment) :
    let parent := originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) captured
    WorldBelow strata.rules.length
      (originalCallWorld controls .expressionReindex result captured) parent ∧
    WorldBelow strata.rules.length
      (originalCallWorld controls .expressionReindex body
        (ownCaptureWorldEnvironment controls domain argument captured)) parent := by
  have compared := capturedApplication_comparison (domain.dependencyOrigin controls.ordered)
    (body.dependencyOrigin controls.ordered) (function.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (result.dependencyOrigin controls.ordered) environment
  have resultLess := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) compared
  have bodyLess := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) compared
  have enlarged := application_cost_le_captured (domain.dependencyOrigin controls.ordered)
    (body.dependencyOrigin controls.ordered) (function.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (result.dependencyOrigin controls.ordered) environment
  have domainLess := Nat.lt_of_lt_of_le (binder_domain_cost (domain.dependencyOrigin controls.ordered)
    [body.dependencyOrigin controls.ordered]
    [function.dependencyOrigin controls.ordered, argument.dependencyOrigin controls.ordered,
      result.dependencyOrigin controls.ordered] environment) enlarged
  have argumentLess := Nat.lt_of_lt_of_le (binder_other_cost
    (child := argument.dependencyOrigin controls.ordered)
    (domain := domain.dependencyOrigin controls.ordered)
    (bodies := [body.dependencyOrigin controls.ordered])
    (children := [function.dependencyOrigin controls.ordered, argument.dependencyOrigin controls.ordered,
      result.dependencyOrigin controls.ordered]) (by simp) environment) enlarged
  have lower {context expression assigned} (node : EndpointState sourceEnv U context expression assigned)
      (phase : RichPhase)
      (smaller : (Closure.close (node.dependencyOrigin controls.ordered) environment).cost <
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin
          controls.ordered) environment).cost) :
      WorldBelow strata.rules.length (originalCallWorld controls phase node captured)
        (originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) captured) :=
    original_child (richSchedule_strict smaller _ _) _ _ _ _ _
  dsimp only
  refine ⟨lower result .expressionReindex resultLess, ?_⟩
  apply Below.root (EquationControlMeasure.scheduleDecrease (richSchedule_strict (by
    simpa only [EndpointState.dependencyOrigin, Closure.cost, List.cons_append, List.nil_append, environmentCost, ← Nat.max_assoc, Nat.max_self] using bodyLess) _ _) _ _ _ _)
  intro world member
  change world ∈ [captureBundleWorld controls domain argument captured,
    originalCallWorld controls .expressionReindex argument captured,
    originalCallWorld controls .fundamental (.ref domain) captured] ++
    ([originalCallWorld controls .expressionReindex argument captured,
      originalCallWorld controls .fundamental (.ref domain) captured] ++ captured.worlds) at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_cons.mp member with rfl | member
    · exact captureBundleWorld_below_application controls domain body function argument result hu hv captured
    · rcases List.mem_cons.mp member with rfl | member
      · exact lower argument .expressionReindex argumentLess
      · cases List.mem_singleton.mp member
        exact lower (.ref domain) .fundamental domainLess
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_cons.mp member with rfl | member
      · exact lower argument .expressionReindex argumentLess
      · cases List.mem_singleton.mp member
        exact lower (.ref domain) .fundamental domainLess
    · exact .child member

/-- An incoming actual result certificate selects the captured body query
through the qualified original R bank. Every returned annotation belongs
to that same selected reply, including its replayable dormant histories. -/
theorem generatedWorldApplicationBody
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata sourceEnv)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph realized.frame.raw controls)
    (replayable : generated.Replayable)
    (frontier : List (World strata.rules.length))
    (ready : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (closed : available.AtomClosed)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (realized.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (certificate : RichCert sourceEnv env U registry target result locals (raw.comp commonLeft)
      relevant (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (queryReady : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ answer : AmbientBoundedGeneratedQueryReply base commonCaps
      (applicationBodyDisplay initial domain body function argument result hu hv location graph)
      commonLeft commonRight profile
      (environmentCost
        ([Closure.bundle
          (.close (argument.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered))
          (.close (domain.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered))] ++
        (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered))
          (.close (domain.dependencyOrigin controls.ordered) (realized.frame.dependencyEnvironment controls.ordered)) ::
          realized.frame.dependencyEnvironment controls.ordered))),
      Nonempty (WorldGeneratedQueryReplyData (P := P) controls
        (ownCaptureWorldEnvironment controls domain argument generated.environment) frontier answer) := by
  obtain ⟨next, nextGenerated, nextReplayable, ⟨nextReady⟩, nextCompatible, environment, worlds, ⟨nextHereditary⟩⟩ :=
    emptyWorldApplicationBodyFrame initial domain body function argument result hu hv location graph
      controls henv formed realized generated replayable frontier ready compatible hereditary
  let bodyBaseline := ownCaptureWorldEnvironment controls domain argument generated.environment
  let leftDisplay := applicationResultDisplay initial domain body function argument result hu hv location graph
  let rightDisplay := applicationBodyDisplay initial domain body function argument result hu hv location graph
  have nextClosed : (available.push []).AtomClosed := by
    simpa only [List.flatMap_nil, List.nil_append] using Valuation.push_atomized_closed closed []
  have bounded := originalCallWorld_boundedNode controls .fundamental
    (.app hu hv (.ref domain) body function argument result) generated.environment baseline capacity covered
  obtain ⟨leftLess, rightLess⟩ := applicationBodyWorldChildren domain body function argument result hu hv
    controls generated.environment
  let calls := [originalCallWorld controls .expressionReindex result generated.environment,
    originalCallWorld controls .expressionReindex body bodyBaseline]
  have actualChildren : ∀ world ∈ calls, WorldBelow strata.rules.length world
      (originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) generated.environment) := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact leftLess
    · cases List.mem_singleton.mp member
      exact rightLess
  have children : ∀ world ∈ calls, WorldBelow strata.rules.length world
      (originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline) :=
    fun world member => BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans bounded (actualChildren world member)
  have callSponsored : Sponsored frontier calls := bounded.sponsored sponsored actualChildren
  have funded : CallBelow strata.rules.length
      (frontier ++ calls)
      (frontier ++ [originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline]) := by
    have lower := split_call children
    have appendLower : ∀ sponsors : List (World strata.rules.length), CallBelow strata.rules.length
        (sponsors ++ calls)
        (sponsors ++ [originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline]) := by
      intro sponsors
      induction sponsors with
      | nil => exact lower
      | cons world rest ih => exact ih.cons world
    exact appendLower frontier
  let leftData : WorldCallFrameData (P := P) (display := leftDisplay)
      controls generated.environment frontier realized :=
    ⟨generated, replayable, ready, compatible, closed, Nat.le_refl _, Covered.refl _, hereditary⟩
  let rightData : WorldCallFrameData (P := P) (display := rightDisplay)
      controls bodyBaseline frontier next := {
    generation := nextGenerated, hereditary := nextHereditary, replayable := nextReplayable, controlled := nextReady,
    compatible := nextCompatible, closed := nextClosed,
    capacity := by rw [environment]; exact Nat.le_refl _,
    covered := by rw [worlds]; exact Covered.refl _ }
  have observed : ControlledStoredQuery controls frontier (.observation (.code certificate)) := by
    refine ⟨.code queryReady.annotation, ?_, queryReady.sponsored⟩
    simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using queryReady.within
  exact bank.observation _ funded base commonCaps leftDisplay rightDisplay commonLeft commonRight
    controls controls rfl rfl generated.environment bodyBaseline frontier rfl callSponsored
    realized leftData next rightData (.code certificate) resources observed

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
