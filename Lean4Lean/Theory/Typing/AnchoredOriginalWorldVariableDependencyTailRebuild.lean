import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBindReservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureBundle
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureHeadReplyData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistorySelection

/-! Rebuild source-context prefixes around a finite variable dependency.
The actual selected frame is merged with the retained original tail before
reusing its upper domain certificate. Trace leaves keep their individual
grades, and the outer adapter is unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private realizeVariableTail from Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemand
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000


/-- Rebuild the upper binder from the structurally selected tail, before attaching any original variable node. -/
theorem rebuildWorldBinderVariableDependency
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (tail : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph tail.frame.raw controls)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (tail.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (annotation : VExpr) (displayed : A.subst raw = annotation)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals (raw.comp commonLeft)
      true (support : Profile k) domainFootprint)
    (resources : domainFootprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst (raw.comp commonLeft)) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ k)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade k).atoms, atom ∈ input.atoms)
    (substitutions : Ctx.SubstEq env U target ((raw.comp commonLeft).cons x)
      ((raw.comp commonRight).cons y) (A :: source))
    (frontier : List (World strata.rules.length))
    (replayable : (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).Replayable)
    (ready : (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).Controlled frontier)
    (compatible : (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).Hereditary frontier)
    (selected : OriginalCaptureRealization graph env registry target nextLocals commonLeft commonRight nextAvailable)
    (selectedWorld : WorldGenerated strata P base caps commonLeft commonRight graph selected.frame.raw controls)
    (selectedReplayable : selectedWorld.Replayable) (selectedReady : selectedWorld.Controlled frontier)
    (selectedCompatible : selectedWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (selectedHereditary : selectedWorld.Hereditary frontier)
    (selectedCapacity : environmentCost (selected.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (selectedCovered : Covered (@EquationControlMeasure.Less strata.rules.length) selectedWorld.worlds baseline.worlds)
    (demand : WorldVariableDependency env U registry target nextAvailable index requested) :
    Nonempty (WorldVariableDependencyReply P base (caps.push (Need.Fits input))
      (.bind graph domain annotation displayed)
      (commonLeft.cons x) (commonRight.cons y) controls
      (reservedBindWorldEnvironment controls domain baseline generated.environment)
      frontier (index + 1) requested) := by
  have sameLocals : nextLocals = locals := selectedWorld.erase.capped.generated.locals_eq.trans generated.erase.capped.generated.locals_eq.symm
  cases sameLocals
  let merged := selected.frame.merge tail.frame
  let mergedWorld := selectedWorld.merge generated
  have selectedIncluded : ∀ i need, need ∈ nextAvailable i → need ∈ (nextAvailable.append available) i :=
    fun _ _ member => List.mem_append_left _ member
  have oldIncluded : ∀ i need, need ∈ available i → need ∈ (nextAvailable.append available) i :=
    fun _ _ member => List.mem_append_right _ member
  have nextResources : domainFootprint.Available (nextAvailable.append available) :=
    fun i need member => oldIncluded i need (resources i need member)
  have mergedCapacity : environmentCost (merged.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment := by
    rw [OriginalRichFrame.merge_environmentCost]
    exact Nat.max_le.mpr ⟨selectedCapacity, capacity⟩
  have mergedCovered : Covered (@EquationControlMeasure.Less strata.rules.length) mergedWorld.worlds baseline.worlds := by
    rw [WorldGenerated.merge_worlds]
    exact selectedCovered.merge replayable.2
  obtain ⟨tailReady⟩ := ready.selectGeneration generated (fun _ member => List.mem_cons_of_mem _ member) rfl rfl
  obtain ⟨certificateReady⟩ := ready.selectStored (show StoredOriginalQuery.certificate certificate ∈
      (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).retainedQueries from List.mem_cons_self)
  let tailH : generated.Hereditary frontier := ⟨hereditary.tablesClosed.1, hereditary.bases, hereditary.ready⟩
  let mergedH := selectedHereditary.merge tailH
  let mergedReady := selectedReady.merge tailReady
  let nextFrame := (merged.bind domain certificate nextResources typed arguments needs bounded covered).reserve
    [.close (domain.dependencyOrigin controls.ordered) baselineEnvironment]
  let nextWorld := WorldGenerated.bind mergedWorld baseline mergedCapacity domain annotation displayed
    certificate nextResources typed arguments needs bounded covered
  have nextReady : nextWorld.Controlled frontier := {
    annotation := .cons certificateReady.annotation mergedReady.annotation
    within := fun control active => Nat.max_le.mpr ⟨certificateReady.within control active, mergedReady.within control active⟩
    sponsored := certificateReady.sponsored.merge mergedReady.sponsored }
  have nextCompatible : nextWorld.UsesControlPrefix controls.cutoff controls.fuel := ⟨selectedCompatible, compatible⟩
  have nextReplayable : nextWorld.Replayable := ⟨⟨selectedReplayable, replayable.1⟩, mergedCovered⟩
  let nextH : nextWorld.Hereditary frontier :=
    ⟨⟨mergedH.tablesClosed, hereditary.tablesClosed.2⟩, mergedH.bases, mergedH.ready⟩
  obtain ⟨realized, actual, actualReplayable, ⟨actualReady⟩, actualCompatible, ⟨actualH⟩, actualWorlds, actualEnvironment⟩ :=
    realizeVariableTail nextFrame nextWorld substitutions nextReplayable nextReady nextCompatible nextH
  let wanted := (demand.availableMono selectedIncluded).push needs
  have localCapacity (ordered : sourceEnv.Ordered) :
      environmentCost (realized.frame.dependencyEnvironment ordered) ≤
      environmentCost (reservedBindWorldEnvironment controls domain baseline generated.environment).closures := by
    rw [actualEnvironment ordered]
    change environmentCost ([Closure.close (domain.dependencyOrigin controls.ordered) baselineEnvironment] ++
      (Closure.close (domain.dependencyOrigin ordered) (merged.dependencyEnvironment ordered) :: merged.dependencyEnvironment ordered)) ≤ _
    rw [reservedBindWorld_capacity _ _ _ mergedCapacity]
    have originalCapacity := reservedBindWorld_capacity (domain.dependencyOrigin controls.ordered)
      (tail.frame.dependencyEnvironment controls.ordered) baselineEnvironment capacity
    change _ ≤ environmentCost ([Closure.close (domain.dependencyOrigin controls.ordered) baselineEnvironment] ++
      (Closure.close (domain.dependencyOrigin controls.ordered) (tail.frame.dependencyEnvironment controls.ordered) ::
        tail.frame.dependencyEnvironment controls.ordered))
    exact Nat.le_of_eq originalCapacity.symm
  have localCovered : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds
      (reservedBindWorldEnvironment controls domain baseline generated.environment).worlds := by
    rw [actualWorlds]
    exact reservedBindWorld_retained_covered controls domain mergedWorld.environment baseline mergedCapacity mergedCovered _
  exact ⟨{
    locals := Locals.push locals
    available := (nextAvailable.append available).push needs
    realization := realized
    generation := actual
    replayable := actualReplayable
    controlled := actualReady
    compatible := actualCompatible
    hereditary := actualH
    capacity := localCapacity
    covered := localCovered
    dependency := wanted }⟩

/-- Rebuild the upper capture from the structurally selected tail, before attaching any original variable node. -/
theorem rebuildWorldCaptureVariableDependency
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (tail : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph tail.frame.raw controls)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (tail.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument) (lineage : location.contextDerivation initial = context)
    (argumentQuery : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft)
      (rawInput : Profile q) argumentFootprint)
    (queryResources : argumentFootprint.Available available)
    (queryBound : k ≤ q)
    (queryAdapter : GeneralNormalProfileAdapter env U registry target rawInput (raiseProfile q queryBound input))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals (raw.comp commonLeft)
      true (support : Profile k) domainFootprint)
    (resources : domainFootprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target (a.subst (raw.comp commonLeft)) (a.subst (raw.comp commonRight)) (A.subst (raw.comp commonLeft)) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ k)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade k).atoms, atom ∈ input.atoms)
    (substitutions : Ctx.SubstEq env U target ((raw.comp commonLeft).cons (a.subst (raw.comp commonLeft)))
      ((raw.comp commonRight).cons (a.subst (raw.comp commonRight))) (A :: source))
    (frontier : List (World strata.rules.length))
    (replayable : (generated.capture baseline capacity domain initial argument location lineage argumentQuery queryResources queryBound queryAdapter certificate resources typed arguments needs bounded covered).Replayable)
    (ready : (generated.capture baseline capacity domain initial argument location lineage argumentQuery queryResources queryBound queryAdapter certificate resources typed arguments needs bounded covered).Controlled frontier)
    (compatible : (generated.capture baseline capacity domain initial argument location lineage argumentQuery queryResources queryBound queryAdapter certificate resources typed arguments needs bounded covered).UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : (generated.capture baseline capacity domain initial argument location lineage argumentQuery queryResources queryBound queryAdapter certificate resources typed arguments needs bounded covered).Hereditary frontier)
    (selected : OriginalCaptureRealization graph env registry target nextLocals commonLeft commonRight nextAvailable)
    (selectedWorld : WorldGenerated strata P base caps commonLeft commonRight graph selected.frame.raw controls)
    (selectedReplayable : selectedWorld.Replayable) (selectedReady : selectedWorld.Controlled frontier)
    (selectedCompatible : selectedWorld.UsesControlPrefix controls.cutoff controls.fuel)
    (selectedHereditary : selectedWorld.Hereditary frontier)
    (selectedCapacity : environmentCost (selected.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (selectedCovered : Covered (@EquationControlMeasure.Less strata.rules.length) selectedWorld.worlds baseline.worlds)
    (demand : WorldVariableDependency env U registry target nextAvailable index requested) :
    Nonempty (WorldVariableDependencyReply P base caps
      (.capture graph domain graph argument ⟨_, _, _, root, initial, location, lineage.symm⟩)
      commonLeft commonRight controls
      (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment)
      frontier (index + 1) requested) := by
  have sameLocals : nextLocals = locals := selectedWorld.erase.capped.generated.locals_eq.trans generated.erase.capped.generated.locals_eq.symm
  cases sameLocals
  let merged := selected.frame.merge tail.frame
  let mergedWorld := selectedWorld.merge generated
  have selectedIncluded : ∀ i need, need ∈ nextAvailable i → need ∈ (nextAvailable.append available) i :=
    fun _ _ member => List.mem_append_left _ member
  have oldIncluded : ∀ i need, need ∈ available i → need ∈ (nextAvailable.append available) i :=
    fun _ _ member => List.mem_append_right _ member
  have nextResources : domainFootprint.Available (nextAvailable.append available) :=
    fun i need member => oldIncluded i need (resources i need member)
  have mergedCapacity : environmentCost (merged.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment := by
    rw [OriginalRichFrame.merge_environmentCost]
    exact Nat.max_le.mpr ⟨selectedCapacity, capacity⟩
  have mergedCovered : Covered (@EquationControlMeasure.Less strata.rules.length) mergedWorld.worlds baseline.worlds := by
    rw [WorldGenerated.merge_worlds]
    exact selectedCovered.merge replayable.2
  obtain ⟨tailReady⟩ := ready.selectGeneration generated (fun _ member => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)) rfl rfl
  obtain ⟨certificateReady⟩ := ready.selectStored (show StoredOriginalQuery.certificate certificate ∈
      (generated.capture baseline capacity domain initial argument location lineage argumentQuery queryResources queryBound queryAdapter certificate resources typed arguments needs bounded covered).retainedQueries from List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨argumentReady⟩ := ready.selectStored (show StoredOriginalQuery.observation argumentQuery ∈
      (generated.capture baseline capacity domain initial argument location lineage argumentQuery queryResources queryBound queryAdapter certificate resources typed arguments needs bounded covered).retainedQueries from List.mem_cons_self)
  have nextQueryResources : argumentFootprint.Available (nextAvailable.append available) :=
    fun i need member => oldIncluded i need (queryResources i need member)
  let tailH : generated.Hereditary frontier := ⟨hereditary.tablesClosed.1, hereditary.bases, hereditary.ready⟩
  let mergedH := selectedHereditary.merge tailH
  let mergedReady := selectedReady.merge tailReady
  let nextFrame := (merged.capture domain initial argument location lineage argumentQuery nextQueryResources
    certificate nextResources typed arguments needs bounded covered).reserve
      [.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
        (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)]
  let nextWorld := WorldGenerated.capture mergedWorld baseline mergedCapacity domain initial argument location lineage
    argumentQuery nextQueryResources queryBound queryAdapter certificate nextResources typed arguments needs bounded covered
  have nextReady : nextWorld.Controlled frontier := {
    annotation := .cons argumentReady.annotation (.cons certificateReady.annotation mergedReady.annotation)
    within := fun control active => Nat.max_le.mpr ⟨argumentReady.within control active, Nat.max_le.mpr ⟨certificateReady.within control active, mergedReady.within control active⟩⟩
    sponsored := argumentReady.sponsored.merge (certificateReady.sponsored.merge mergedReady.sponsored) }
  have nextCompatible : nextWorld.UsesControlPrefix controls.cutoff controls.fuel := ⟨selectedCompatible, compatible⟩
  have nextReplayable : nextWorld.Replayable := ⟨⟨selectedReplayable, replayable.1⟩, mergedCovered⟩
  let nextH : nextWorld.Hereditary frontier :=
    ⟨⟨mergedH.tablesClosed, hereditary.tablesClosed.2⟩, mergedH.bases, mergedH.ready⟩
  obtain ⟨realized, actual, actualReplayable, ⟨actualReady⟩, actualCompatible, ⟨actualH⟩, actualWorlds, actualEnvironment⟩ :=
    realizeVariableTail nextFrame nextWorld substitutions nextReplayable nextReady nextCompatible nextH
  let wanted := (demand.availableMono selectedIncluded).push needs
  have localCapacity (ordered : sourceEnv.Ordered) :
      environmentCost (realized.frame.dependencyEnvironment ordered) ≤
      environmentCost (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment).closures := by
    rw [actualEnvironment ordered]
    change environmentCost ([Closure.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
      (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)] ++
      (Closure.bundle (.close (argument.dependencyOrigin ordered) (merged.dependencyEnvironment ordered))
        (.close (domain.dependencyOrigin ordered) (merged.dependencyEnvironment ordered)) :: merged.dependencyEnvironment ordered)) ≤ _
    rw [captureBundleWorld_retained_capacity _ _ _ _ mergedCapacity]
    have originalCapacity := captureBundleWorld_retained_capacity (argument.dependencyOrigin controls.ordered)
      (domain.dependencyOrigin controls.ordered) (tail.frame.dependencyEnvironment controls.ordered) baselineEnvironment capacity
    change _ ≤ environmentCost ([Closure.bundle (.close (argument.dependencyOrigin controls.ordered) baselineEnvironment)
      (.close (domain.dependencyOrigin controls.ordered) baselineEnvironment)] ++
      (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) (tail.frame.dependencyEnvironment controls.ordered))
        (.close (domain.dependencyOrigin controls.ordered) (tail.frame.dependencyEnvironment controls.ordered)) ::
        tail.frame.dependencyEnvironment controls.ordered))
    exact Nat.le_of_eq originalCapacity.symm
  have localCovered : Covered (@EquationControlMeasure.Less strata.rules.length) actual.worlds
      (reservedCaptureWorldEnvironment controls domain argument baseline generated.environment).worlds := by
    rw [actualWorlds]
    exact captureBundleWorld_retained_covered controls domain argument mergedWorld.environment baseline mergedCapacity mergedCovered _
  exact ⟨{
    locals := Locals.push locals
    available := (nextAvailable.append available).push needs
    realization := realized
    generation := actual
    replayable := actualReplayable
    controlled := actualReady
    compatible := actualCompatible
    hereditary := actualH
    capacity := localCapacity
    covered := localCovered
    dependency := wanted }⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
