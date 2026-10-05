import Lean4Lean.Theory.Typing.AnchoredOriginalSourceResourceClosure
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistoryWorlds
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldReplayableGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureMergePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistory

/-! Resource closure on the same generated world witness. Closing needs
changes only resource proofs and singleton availability, preserving actual
owner histories, retained queries, and their world annotations. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private closeNeeds_fits historyReserveOfEntries from Lean4Lean.Theory.Typing.AnchoredOriginalCappedResourceClosure
open private retained_worlds_cast from Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

private theorem headerAvailableMono_injective
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {available nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i) :
    Function.Injective (fun entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue => entry.headerAvailableMono included) := by
  intro first second same
  rcases first with ⟨owner₁, ownerLocals₁, ownerLeft₁, ownerRight₁, ownerAvailable₁, initialContext₁, frame₁, substitutions₁, bound₁, depth₁, sourcePrefix₁, sourceEq₁, depthEq₁, expressionEq₁, leftEq₁, rightEq₁, rank₁, input₁, queryRank₁, queryInput₁, queryBound₁, queryAdapter₁, footprint₁, query₁, queryAvailable₁, ⟨value₁, ⟨codeFootprint₁, certificate₁, resources₁, related₁⟩, path₁⟩⟩
  rcases second with ⟨owner₂, ownerLocals₂, ownerLeft₂, ownerRight₂, ownerAvailable₂, initialContext₂, frame₂, substitutions₂, bound₂, depth₂, sourcePrefix₂, sourceEq₂, depthEq₂, expressionEq₂, leftEq₂, rightEq₂, rank₂, input₂, queryRank₂, queryInput₂, queryBound₂, queryAdapter₂, footprint₂, query₂, queryAvailable₂, ⟨value₂, ⟨codeFootprint₂, certificate₂, resources₂, related₂⟩, path₂⟩⟩
  simp only [RichGroupedCaptureEntry.headerAvailableMono, RichGroupedCaptureEntry.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rest⟩
  have rest := eq_of_heq rest
  simp only [HeaderValueAlignment.mk.injEq] at rest
  rcases rest with ⟨rfl, rest⟩
  have rest := eq_of_heq rest
  simp only [RichCodeTransferResult.mk.injEq] at rest
  rcases rest with ⟨rfl, rfl⟩
  rfl



private abbrev EntryWorldPacket
    {P : VEnv → Prop} {common : List VExpr}
    {ownerRaw commonLeft commonRight : Subst} {commonCaps : CaptureCaps}
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue) :=
  Σ scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
      (entry.owner.context entry.initialContext),
    WorldGenerated strata P base scope.caps scope.left scope.right scope.graph entry.frame.raw ownerControls

private theorem mapAttachedPackets
    {α β : Type u} (f : α → β) (injective : Function.Injective f)
    (items : List α) (family : β → Type v) (packets : ∀ a ∈ items, family (f a)) :
    ∃ next : ∀ b ∈ items.map f, family b,
      ∀ a (member : a ∈ items), next (f a) (List.mem_map_of_mem member) = packets a member := by
  let predecessor := fun b (member : b ∈ items.map f) => Classical.choose (List.mem_map.mp member)
  have present : ∀ b member, predecessor b member ∈ items :=
    fun b member => (Classical.choose_spec (List.mem_map.mp member)).1
  have same : ∀ b member, f (predecessor b member) = b :=
    fun b member => (Classical.choose_spec (List.mem_map.mp member)).2
  let next := fun b member => (congrArg family (same b member)).mp (packets (predecessor b member) (present b member))
  refine ⟨next, ?_⟩
  intro a member
  have selected : predecessor (f a) (List.mem_map_of_mem member) = a :=
    injective (same (f a) (List.mem_map_of_mem member))
  apply eq_of_heq
  simp only [next, Eq.mp, eqRec_heq_iff]
  have transport (b : α) (present : b ∈ items) (equal : b = a) :
      HEq (packets b present) (packets a member) := by
    cases equal
    rfl
  exact transport _ _ selected

private theorem headerAvailableMono_packets
    {strata : EquationStratification env} {base : OriginalCaptureBase env U registry target}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i)
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (packets : ∀ entry ∈ entries,
      EntryWorldPacket (P := P) (base := base) (common := common) (ownerRaw := ownerRaw)
        (commonLeft := commonLeft) (commonRight := commonRight) (commonCaps := commonCaps) ownerControls entry) :
    ∃ next : ∀ entry ∈ entries.map (fun selected => selected.headerAvailableMono included),
      EntryWorldPacket (P := P) (base := base) (common := common) (ownerRaw := ownerRaw)
        (commonLeft := commonLeft) (commonRight := commonRight) (commonCaps := commonCaps) ownerControls entry,
      ∀ entry (member : entry ∈ entries),
        next (entry.headerAvailableMono included) (List.mem_map_of_mem member) = packets entry member := by
  exact mapAttachedPackets (fun entry => entry.headerAvailableMono included)
    (headerAvailableMono_injective included) entries
    (fun entry => EntryWorldPacket (P := P) (base := base) (common := common) (ownerRaw := ownerRaw)
      (commonLeft := commonLeft) (commonRight := commonRight) (commonCaps := commonCaps) ownerControls entry)
    packets

private theorem headerAvailableMono_queries
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i) :
    (richGroupedEntriesRaw (entries.headerAvailableMono included)).storedQueries =
      (richGroupedEntriesRaw entries).storedQueries := by
  induction entries with
  | nil =>
    change (richGroupedEntriesRaw ([] : RichGroupedCapture _ _ _ _ _ _ _ _ _ _ _)).storedQueries = _
    simp only [richGroupedEntriesRaw, RawRichGroupEntries.storedQueries]
  | cons entry tail ih =>
    change (richGroupedEntriesRaw ((entry.headerAvailableMono included) ::
      RichGroupedCapture.headerAvailableMono tail included)).storedQueries = _
    simp only [richGroupedEntriesRaw, RawRichGroupEntries.storedQueries]
    rw [ih]
    congr 1
    simp only [RichGroupedCaptureEntry.toRaw, RichGroupedCaptureEntry.headerAvailableMono,
      RawRichGroupEntry.storedQueries, HeaderValueAlignment.storedQueries]

structure WorldResourceClosure
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {controls : OriginalWorldControls strata sourceEnv}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ originalAvailable}
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph original controls)
    (valid : original.Valid) where
  available : Valuation
  frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available
  generation : WorldGenerated strata P base commonCaps commonLeft commonRight graph frame.raw controls
  included : ∀ i need, need ∈ originalAvailable i → need ∈ available i
  closed : available.AtomClosed
  environment : ∀ ordered : sourceEnv.Ordered,
    frame.dependencyEnvironment ordered = original.dependencyEnvironment ordered
  worlds : generation.worlds = generated.worlds
  queries : generation.retainedQueries = generated.retainedQueries
  replayable : generated.Replayable → generation.Replayable
  compatible : ∀ cutoff fuel,
    generated.UsesControlPrefix cutoff fuel → generation.UsesControlPrefix cutoff fuel
  baseUses : generation.baseUses = generated.baseUses
  tablesClosed : generated.TablesClosed → generation.TablesClosed

private theorem call_world_congr
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv) (phase : RichPhase)
    (node : EndpointState sourceEnv U source expression assigned)
    (first : WorldEnvironmentProvenance strata U firstEnvironment)
    (second : WorldEnvironmentProvenance strata U secondEnvironment)
    (same : firstEnvironment = secondEnvironment)
    (worlds : first.worlds = second.worlds) :
    originalCallWorld controls phase node first = originalCallWorld controls phase node second := by
  cases same
  unfold originalCallWorld
  rw [worlds]


private theorem groupEntries_worlds_close
    {strata : EquationStratification env}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i)
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (initialProvenance : WorldEnvironmentProvenance strata U initial)
    (first : WorldEnvironmentProvenance strata U firstEnvironment)
    (second : WorldEnvironmentProvenance strata U secondEnvironment)
    (same : firstEnvironment = secondEnvironment) (worlds : first.worlds = second.worlds) :
    (WorldEnvironmentProvenance.groupEntries ownerControls headerControls initialProvenance first
      (entries.headerAvailableMono included)).worlds =
    (WorldEnvironmentProvenance.groupEntries ownerControls headerControls initialProvenance second entries).worlds := by
  have domainEq := call_world_congr headerControls .fundamental (.ref domain) first second same worlds
  induction entries with
  | nil => exact worlds
  | cons entry tail ih =>
    change ((WorldEnvironmentProvenance.owner ownerControls entry.owner initialProvenance).worlds ++
      [originalCallWorld headerControls .fundamental (.ref domain) first]) ++
      (WorldEnvironmentProvenance.groupEntries ownerControls headerControls initialProvenance first
        (RichGroupedCapture.headerAvailableMono tail included)).worlds = _
    rw [domainEq, ih]
    rfl

private theorem group_worlds_close
    {strata : EquationStratification env}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i)
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (headerControls : OriginalWorldControls strata headerEnv)
    (initialProvenance : WorldEnvironmentProvenance strata U initial)
    (first : WorldEnvironmentProvenance strata U firstEnvironment)
    (second : WorldEnvironmentProvenance strata U secondEnvironment)
    (same : firstEnvironment = secondEnvironment) (worlds : first.worlds = second.worlds) :
    (WorldEnvironmentProvenance.group ownerControls headerControls initialProvenance first
      (entries.headerAvailableMono included)).worlds =
    (WorldEnvironmentProvenance.group ownerControls headerControls initialProvenance second entries).worlds := by
  have domainEq := call_world_congr headerControls .fundamental (.ref domain) first second same worlds
  have entriesEq := groupEntries_worlds_close entries included ownerControls headerControls initialProvenance
    first second same worlds
  change [originalCallWorld headerControls .fundamental (.ref domain) first] ++
    ([originalCallWorld ownerControls .expressionReindex (.ref field) initialProvenance] ++
      [originalCallWorld headerControls .fundamental (.ref domain) first]) ++
    ([originalCallWorld ownerControls .expressionReindex (.ref major) initialProvenance] ++
      [originalCallWorld headerControls .fundamental (.ref domain) first]) ++ _ = _
  rw [domainEq, entriesEq]
  rfl

/-- Closing needs uses the same original query and history payloads. Only
resource proofs and the finite resource tables are rebuilt. -/
theorem WorldGenerated.closeResources
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {controls : OriginalWorldControls strata sourceEnv}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph original controls)
    (valid : original.Valid) (baseClosed : base.available.AtomClosed) :
    Nonempty (WorldResourceClosure generated valid) := by
  induction generated with
  | identity ambient sources controls environment =>
    exact ⟨⟨_, base.frame, .identity ambient sources controls environment, fun _ _ h => h, baseClosed,
      fun _ => rfl, rfl, rfl, id, (fun _ _ => id), rfl, id⟩⟩
  | empty common left right below source controls =>
    exact ⟨⟨_, .nil, .empty common left right below source controls, fun _ _ h => h,
      fun _ _ h => False.elim (List.not_mem_nil h), fun _ => rfl, rfl, rfl, id, (fun _ _ => id), rfl, id⟩⟩
  | merge first second ihl ihr =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨left⟩ := ihl valid.1
    obtain ⟨right⟩ := ihr valid.2
    refine ⟨⟨_, left.frame.merge right.frame, .merge left.generation right.generation, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro i need member
      exact (List.mem_append.mp member).elim
        (fun h => List.mem_append_left _ (left.included i need h))
        (fun h => List.mem_append_right _ (right.included i need h))
    · intro i need member atom present
      exact (List.mem_append.mp member).elim
        (fun h => List.mem_append_left _ (left.closed i need h atom present))
        (fun h => List.mem_append_right _ (right.closed i need h atom present))
    · intro ordered
      change left.frame.dependencyEnvironment ordered ++ right.frame.dependencyEnvironment ordered = _
      rw [left.environment, right.environment]
      rfl
    · rw [WorldGenerated.merge_worlds, WorldGenerated.merge_worlds, left.worlds, right.worlds]
    · change left.generation.retainedQueries ++ right.generation.retainedQueries = first.retainedQueries ++ second.retainedQueries
      rw [left.queries, right.queries]
    · exact fun ready => ⟨left.replayable ready.1, right.replayable ready.2⟩
    · exact fun cutoff fuel ready => ⟨left.compatible cutoff fuel ready.1, right.compatible cutoff fuel ready.2⟩
    · change left.generation.baseUses ++ right.generation.baseUses = first.baseUses ++ second.baseUses
      rw [left.baseUses, right.baseUses]
    · exact fun closed => ⟨left.tablesClosed closed.1, right.tablesClosed closed.2⟩
  | weaken generated insertion leftTail rightTail capsTail ih =>
    obtain ⟨answer⟩ := ih valid
    exact ⟨{ answer with generation := .weaken answer.generation insertion leftTail rightTail capsTail }⟩
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨tail⟩ := ih valid
    have resources' := fun i need member => tail.included i need (resources i need member)
    have fits := closeNeeds_fits _ needs bounded covered
    let activeFrame := tail.frame.bind domain certificate resources' typed arguments
      (needs ++ needs.flatMap Need.singletons) (fun n m => (fits n m).1) (fun n m => (fits n m).2)
    let frame := activeFrame.reserve [.close (domain.dependencyOrigin generated.callControls.ordered) baseline.closures]
    have nextCapacity : environmentCost (tail.frame.dependencyEnvironment generated.callControls.ordered) ≤
        environmentCost baseline.closures := by
      rw [tail.environment]
      exact capacity
    refine ⟨⟨_, frame, .bind tail.generation baseline nextCapacity domain annotation displayed certificate resources' typed arguments
      _ (fun n m => (fits n m).1) (fun n m => (fits n m).2), ?_,
      Valuation.push_atomized_closed tail.closed needs, ?_, ?_, ?_, ?_, tail.compatible,
      tail.baseUses, fun closed => ⟨tail.tablesClosed closed.1, atomizedNeeds_closed needs⟩⟩⟩
    · intro i need member
      cases i with
      | zero => exact List.mem_append_left _ member
      | succ i => exact tail.included i need member
    · intro ordered
      change _ :: Closure.close _ (tail.frame.dependencyEnvironment ordered) :: tail.frame.dependencyEnvironment ordered = _
      rw [tail.environment]
      rfl
    · apply congrArg (fun worlds => [originalCallWorld generated.callControls .expressionReindex (.ref domain) baseline] ++ worlds)
      change [originalCallWorld generated.callControls .fundamental (.ref domain) tail.generation.environment] ++
        tail.generation.worlds = [originalCallWorld generated.callControls .fundamental (.ref domain) generated.environment] ++ generated.worlds
      rw [call_world_congr _ _ _ _ _ (tail.environment _) tail.worlds, tail.worlds]
    · change .certificate certificate :: tail.generation.retainedQueries = .certificate certificate :: generated.retainedQueries
      rw [tail.queries]
    · intro ready
      refine ⟨tail.replayable ready.1, ?_⟩
      rw [tail.worlds]
      exact ready.2
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered ih =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨tail⟩ := ih valid
    have resources' := fun i need member => tail.included i need (resources i need member)
    have queryAvailable' := fun i need member => tail.included i need (queryAvailable i need member)
    have fits := closeNeeds_fits _ needs bounded covered
    let activeFrame := tail.frame.capture domain initial argument location lineage query queryAvailable' certificate
      resources' typed arguments (needs ++ needs.flatMap Need.singletons)
      (fun n m => (fits n m).1) (fun n m => (fits n m).2)
    let frame := activeFrame.reserve [Closure.bundle
      (.close (argument.dependencyOrigin generated.callControls.ordered) baseline.closures)
      (.close (domain.dependencyOrigin generated.callControls.ordered) baseline.closures)]
    have nextCapacity : environmentCost (tail.frame.dependencyEnvironment generated.callControls.ordered) ≤
        environmentCost baseline.closures := by
      rw [tail.environment]
      exact capacity
    refine ⟨⟨_, frame, .capture tail.generation baseline nextCapacity domain initial argument location lineage query queryAvailable'
      queryBound queryAdapter certificate resources' typed arguments _ (fun n m => (fits n m).1) (fun n m => (fits n m).2), ?_,
      Valuation.push_atomized_closed tail.closed needs, ?_, ?_, ?_, ?_, tail.compatible,
      tail.baseUses, fun closed => ⟨tail.tablesClosed closed.1, atomizedNeeds_closed needs⟩⟩⟩
    · intro i need member
      cases i with
      | zero => exact List.mem_append_left _ member
      | succ i => exact tail.included i need member
    · intro ordered
      change _ :: Closure.bundle (Closure.close _ (tail.frame.dependencyEnvironment ordered))
        (Closure.close _ (tail.frame.dependencyEnvironment ordered)) :: tail.frame.dependencyEnvironment ordered = _
      rw [tail.environment]
      rfl
    · apply congrArg (fun worlds => (WorldClosureProvenance.captureBundle generated.callControls domain argument baseline).worlds ++ worlds)
      change ([originalCallWorld generated.callControls .expressionReindex argument tail.generation.environment] ++
        [originalCallWorld generated.callControls .fundamental (.ref domain) tail.generation.environment]) ++
        tail.generation.worlds = ([originalCallWorld generated.callControls .expressionReindex argument generated.environment] ++
        [originalCallWorld generated.callControls .fundamental (.ref domain) generated.environment]) ++ generated.worlds
      rw [call_world_congr _ _ argument _ _ (tail.environment _) tail.worlds,
        call_world_congr _ _ (.ref domain) _ _ (tail.environment _) tail.worlds, tail.worlds]
    · change .observation query :: .certificate certificate :: tail.generation.retainedQueries =
        .observation query :: .certificate certificate :: generated.retainedQueries
      rw [tail.queries]
    · intro ready
      refine ⟨tail.replayable ready.1, ?_⟩
      rw [tail.worlds]
      exact ready.2
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      ih seedIH priorIH historyIH ownerIH =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨tail⟩ := ih valid.1
    let nextEntries := entries.headerAvailableMono tail.included
    let reserve := historyReserveOfEntries entries ownerOrdered headerOrdered
      (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve
    let frame := (tail.frame.group domain ownerOrdered ownerInitial nextEntries).reserve reserve
    obtain ⟨packets, packetsEq⟩ := headerAvailableMono_packets entries tail.included ownerControls
      (fun entry member => ⟨scopes entry member, owners entry member⟩)
    let nextScopes := fun entry member => (packets entry member).1
    let nextOwners := fun entry member => (packets entry member).2
    have nextBound : environmentCost (tail.frame.dependencyEnvironment headerOrdered) ≤
        environmentCost (prior.frame.dependencyEnvironment headerOrdered) := by
      rw [tail.environment]
      exact tailBound
    let nextGenerated := WorldGenerated.historyGroup tail.generation domain ownerGraph nominalGraph nominal provenance displayed
      ownerOrdered headerOrdered ownerInitial seed seedScope seedControls seedGenerated domainProvenance prior history
      priorGenerated initialProvenance baselines routeInputs historyWellFormed historyControls historyGenerated nextBound
      nextEntries nextScopes ownerControls nextOwners ownerAmbient nominalAmbient priorAmbient routeAmbient
      ownerSources nominalSources priorSources routeSources
    refine ⟨⟨_, frame, nextGenerated, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro i need member
      cases i with
      | zero =>
        change need ∈ nextEntries.needs
        rw [show nextEntries.needs = entries.needs from entries.headerAvailableMono_needs tail.included]
        exact member
      | succ i => exact tail.included i need member
    · change (tail.available.push nextEntries.needs).AtomClosed
      rw [show nextEntries.needs = entries.needs from entries.headerAvailableMono_needs tail.included]
      intro i need member atom present
      cases i with
      | succ i => exact tail.closed i need member atom present
      | zero =>
        obtain ⟨entry, member, needed⟩ := List.mem_flatMap.mp member
        apply List.mem_flatMap.mpr
        refine ⟨entry, member, ?_⟩
        exact (Valuation.atomize_closed (fun _ => [⟨entry.rank, entry.input⟩])) 0 need needed atom present
    · intro ordered
      change reserve ++ (tail.frame.group domain ownerOrdered ownerInitial nextEntries).dependencyEnvironment ordered = _
      rw [OriginalRichFrame.group_environment, tail.environment, RichGroupedCapture.headerAvailableMono_environment]
      exact congrArg (reserve ++ ·) (OriginalRichFrame.group_environment ownerOrdered ordered ⟨_, valid.1⟩ entries).symm
    · rw [WorldGenerated.historyGroup_worlds, WorldGenerated.historyGroup_worlds]
      simp only [WorldEnvironmentProvenance.worlds_append]
      congr 1
      exact group_worlds_close entries tail.included ownerControls generated.callControls initialProvenance
        tail.generation.environment generated.environment (tail.environment _) tail.worlds
    · have ownersQueries : nextEntries.attach.flatMap (fun entry => (nextOwners entry.val entry.property).retainedQueries) =
          entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries) := by
        simp only [nextEntries, RichGroupedCapture.headerAvailableMono, List.attach_map, List.flatMap_map]
        congr 1
        funext entry
        change (packets (entry.val.headerAvailableMono tail.included) _).2.retainedQueries = _
        rw [packetsEq]
      change (richGroupedEntriesRaw nextEntries).storedQueries ++ tail.generation.retainedQueries ++
        (.observation seed.query :: seedGenerated.retainedQueries) ++ priorGenerated.retainedQueries ++
        ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).retainedQueries)) ++
        nextEntries.attach.flatMap (fun entry => (nextOwners entry.val entry.property).retainedQueries) = _
      rw [headerAvailableMono_queries, tail.queries, ownersQueries]
      rfl
    · intro replayable
      refine ⟨tail.replayable replayable.1, replayable.2.1, replayable.2.2.1, replayable.2.2.2.1, ?_, ?_,
        replayable.2.2.2.2.2.2.1, replayable.2.2.2.2.2.2.2.1,
        replayable.2.2.2.2.2.2.2.2.1, replayable.2.2.2.2.2.2.2.2.2.1, ?_⟩
      · intro entry member
        obtain ⟨previous, previousMember, rfl⟩ := List.mem_map.mp member
        change (packets (previous.headerAvailableMono tail.included) _).2.Replayable
        rw [packetsEq]
        exact replayable.2.2.2.2.1 previous previousMember
      · intro entry member
        obtain ⟨previous, previousMember, rfl⟩ := List.mem_map.mp member
        change Covered _ (packets (previous.headerAvailableMono tail.included) _).2.worlds _
        rw [packetsEq]
        exact replayable.2.2.2.2.2.1 previous previousMember
      · rw [tail.worlds]
        exact replayable.2.2.2.2.2.2.2.2.2.2
    · intro cutoff fuel compatible
      refine ⟨tail.compatible cutoff fuel compatible.1, compatible.2.1, compatible.2.2.1,
        compatible.2.2.2.1, ?_, compatible.2.2.2.2.2⟩
      intro entry member
      obtain ⟨previous, previousMember, rfl⟩ := List.mem_map.mp member
      change (packets (previous.headerAvailableMono tail.included) _).2.UsesControlPrefix cutoff fuel
      rw [packetsEq]
      exact compatible.2.2.2.2.1 previous previousMember
    · have ownersBases : nextEntries.attach.flatMap (fun entry => (nextOwners entry.val entry.property).baseUses) =
          entries.attach.flatMap (fun entry => (owners entry.val entry.property).baseUses) := by
        simp only [nextEntries, RichGroupedCapture.headerAvailableMono, List.attach_map, List.flatMap_map]
        congr 1
        funext entry
        change (packets (entry.val.headerAvailableMono tail.included) _).2.baseUses = _
        rw [packetsEq]
      change tail.generation.baseUses ++ seedGenerated.baseUses ++ priorGenerated.baseUses ++
        ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).baseUses)) ++
        nextEntries.attach.flatMap (fun entry => (nextOwners entry.val entry.property).baseUses) = _
      rw [tail.baseUses, ownersBases]
      rfl
    · intro closed
      refine ⟨tail.tablesClosed closed.1, closed.2.1, closed.2.2.1, closed.2.2.2.1, ?_⟩
      intro entry member
      obtain ⟨previous, previousMember, rfl⟩ := List.mem_map.mp member
      change (packets (previous.headerAvailableMono tail.included) _).2.TablesClosed
      rw [packetsEq]
      exact closed.2.2.2.2 previous previousMember


/-- Exact retained-query equality transports the same provenance annotation;
closing resources neither creates a query-owned world nor spends extra fuel. -/
theorem WorldResourceClosure.controlled
    {available : Valuation}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {controls : OriginalWorldControls strata sourceEnv}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph original controls}
    {valid : original.Valid} (answer : WorldResourceClosure generated valid)
    {frontier : List (World strata.rules.length)} (ready : generated.Controlled frontier) :
    ∃ nextReady : answer.generation.Controlled frontier,
      nextReady.annotation.worlds = ready.annotation.worlds := by
  let annotation : RetainedQueryProvenance strata answer.generation.retainedQueries :=
    answer.queries.symm ▸ ready.annotation
  have worlds : annotation.worlds = ready.annotation.worlds :=
    retained_worlds_cast answer.queries.symm ready.annotation
  refine ⟨{ annotation := annotation, within := ?_, sponsored := worlds.symm ▸ ready.sponsored }, worlds⟩
  intro control active
  change answer.generation.retainedDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control) ≤ controls.fuel control
  rw [← answer.generation.retainedQueries_depth, answer.queries, generated.retainedQueries_depth]
  exact ready.within control active

/-- Resource closure of an actual selected scope, retaining its paired
substitution, dormant histories and exact query provenance. -/
theorem OriginalCaptureRealization.closeResourcesWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {controls : OriginalWorldControls strata sourceEnv}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (original : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph original.frame.raw controls)
    (baseClosed : base.available.AtomClosed) {frontier : List (World strata.rules.length)}
    (ready : generated.Controlled frontier) :
    ∃ nextAvailable, ∃ next : OriginalCaptureRealization graph env registry target locals commonLeft commonRight nextAvailable,
      ∃ nextGenerated : WorldGenerated strata P base commonCaps commonLeft commonRight graph next.frame.raw controls,
      (∀ i need, need ∈ available i → need ∈ nextAvailable i) ∧
      nextAvailable.AtomClosed ∧
      (∀ ordered : sourceEnv.Ordered,
        next.frame.dependencyEnvironment ordered = original.frame.dependencyEnvironment ordered) ∧
      nextGenerated.worlds = generated.worlds ∧
      nextGenerated.retainedQueries = generated.retainedQueries ∧
      (generated.Replayable → nextGenerated.Replayable) ∧
      (∀ cutoff fuel, generated.UsesControlPrefix cutoff fuel → nextGenerated.UsesControlPrefix cutoff fuel) ∧
      nextGenerated.baseUses = generated.baseUses ∧
      (generated.TablesClosed → nextGenerated.TablesClosed) ∧
      ∃ nextReady : nextGenerated.Controlled frontier,
        nextReady.annotation.worlds = ready.annotation.worlds := by
  obtain ⟨answer⟩ := generated.closeResources original.frame.valid baseClosed
  obtain ⟨nextReady, worlds⟩ := answer.controlled ready
  exact ⟨answer.available, ⟨answer.frame, original.substitutions⟩, answer.generation, answer.included,
    answer.closed, answer.environment, answer.worlds, answer.queries, answer.replayable, answer.compatible,
    answer.baseUses, answer.tablesClosed, nextReady, worlds⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
