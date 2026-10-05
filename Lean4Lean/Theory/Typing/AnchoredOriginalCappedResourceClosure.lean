import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedResourceCaps
import Lean4Lean.Theory.Typing.AnchoredOriginalRichSuffixEnvironment

/-! Close a generated frame's finite needs without changing its original
dependency environment. This permits selecting a branch of a merged
destination without assuming that closure of a union implies closure of
each branch, or combining unrelated groups' reserves. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private raiseProfile_map from Lean4Lean.Theory.Typing.AnchoredSourceSubstitution
open private suffixEnvironment_castLocals from Lean4Lean.Theory.Typing.AnchoredOriginalRichSuffixEnvironment
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def RichGroupedCaptureEntry.headerAvailableMono
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i) :
    RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals σ nextAvailable initial rawCapture leftValue rightValue :=
  { entry with answer := { entry.answer with aligned := { entry.answer.aligned with
      resources := fun i need member => included i need (entry.answer.aligned.resources i need member) } } }

def RichGroupedCapture.headerAvailableMono
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i) :
    RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ nextAvailable initial rawCapture leftValue rightValue :=
  entries.map (fun entry => entry.headerAvailableMono included)

theorem RichGroupedCapture.headerAvailableMono_needs
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i) :
    (entries.headerAvailableMono included).needs = entries.needs := by
  simp only [RichGroupedCapture.headerAvailableMono, RichGroupedCapture.needs, List.flatMap_map]
  rfl

theorem RichGroupedCapture.headerAvailableMono_environment
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered) (previous : List Closure) :
    (entries.headerAvailableMono included).environment ordered headerOrdered initial previous =
      entries.environment ordered headerOrdered initial previous := by
  simp only [RichGroupedCapture.environment, RichGroupedCapture.headerAvailableMono, List.map_map]
  rfl

def PendingRichCapture.headerAvailable
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (seed : PendingRichCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    (nextAvailable : Valuation) :
    PendingRichCapture (field := field) (major := major) domain env registry target
      locals σ nextAvailable initial rawCapture leftValue rightValue :=
  seed.reheader locals σ nextAvailable

theorem RichGroupedCapture.headerAvailableMono_scopes
    {base : OriginalCaptureBase env U registry target}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    {nextAvailable : Valuation}
    (included : ∀ i need, need ∈ available i → need ∈ nextAvailable i)
    (scopes : ∀ entry ∈ entries, CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
      (entry.owner.context entry.initialContext))
    (owners : ∀ entry member, CappedCaptureGenerated base (scopes entry member).caps (scopes entry member).left
      (scopes entry member).right (scopes entry member).graph entry.frame.raw) :
    ∃ nextScopes : ∀ entry ∈ entries.headerAvailableMono included,
      CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext),
      ∀ entry member, CappedCaptureGenerated base (nextScopes entry member).caps (nextScopes entry member).left
        (nextScopes entry member).right (nextScopes entry member).graph entry.frame.raw := by
  have existsScope : ∀ entry ∈ entries.headerAvailableMono included,
      ∃ scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext),
        CappedCaptureGenerated base scope.caps scope.left scope.right scope.graph entry.frame.raw := by
    intro entry member
    obtain ⟨previous, previousMember, rfl⟩ := List.mem_map.mp member
    exact ⟨scopes previous previousMember, owners previous previousMember⟩
  exact ⟨fun entry member => (existsScope entry member).choose,
    fun entry member => (existsScope entry member).choose_spec⟩

private noncomputable def historyReserveOfEntries
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (_entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      locals σ available initial rawCapture leftValue rightValue)
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (previous history : List Closure) : List Closure :=
  groupCaptureHistoryReserve field major domain ordered headerOrdered initial previous history

structure CappedResourceClosure
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ originalAvailable) (valid : original.Valid) where
  available : Valuation
  frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available
  capped : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.raw
  included : ∀ i need, need ∈ originalAvailable i → need ∈ available i
  closed : available.AtomClosed
  suffixEnvironment : ∀ (ordered : sourceEnv.Ordered) (depth : Nat),
    frame.suffixEnvironment ordered depth = (OriginalRichFrame.mk original valid).suffixEnvironment ordered depth

theorem CappedResourceClosure.environment
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ oldAvailable}
    {valid : original.Valid}
    (answer : CappedResourceClosure base commonCaps commonLeft commonRight graph original valid)
    (ordered : sourceEnv.Ordered) :
    answer.frame.dependencyEnvironment ordered = original.dependencyEnvironment ordered := by
  simpa only [OriginalRichFrame.suffixEnvironment_zero, OriginalRichFrame.dependencyEnvironment] using
    answer.suffixEnvironment ordered 0

private theorem closeNeeds_fits
    (input : Profile n) (needs : List Need)
    (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    ∀ need ∈ needs ++ needs.flatMap Need.singletons, Need.Fits input need := by
  intro need member
  rcases List.mem_append.mp member with original | selected
  · exact ⟨bounded need original, covered need original⟩
  · obtain ⟨old, oldMember, selected⟩ := List.mem_flatMap.mp selected
    obtain ⟨atom, present, rfl⟩ := List.mem_map.mp selected
    have bound := bounded old oldMember
    refine ⟨bound, ?_⟩
    intro high highMember
    apply covered old oldMember high
    simp only [Need.atGrade, dif_pos bound] at highMember ⊢
    rw [raiseProfile_singleton] at highMember
    cases List.mem_singleton.mp highMember
    rw [raiseProfile_map]
    exact List.mem_map.mpr ⟨atom, present, rfl⟩

private def cappedRawFrame
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (_generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph original)
    (valid : original.Valid) : OriginalRichFrame sourceEnv env U registry target context locals σ τ available :=
  ⟨original, valid⟩

private theorem capped_castLocals
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph frame.raw)
    {nextLocals : List Nat} (same : locals = nextLocals) :
    CappedCaptureGenerated base commonCaps commonLeft commonRight graph (same ▸ frame).raw := by
  cases same
  exact generated

/-- Each branch can be closed separately at exactly its old original cost.
The base is already closed; fresh heads add only singleton selections of
needs supported by their existing guards. -/
theorem CappedCaptureGenerated.closeResources
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph original)
    (valid : original.Valid) (baseClosed : base.available.AtomClosed) :
    Nonempty (CappedResourceClosure base commonCaps commonLeft commonRight graph original valid) := by
  induction generated with
  | tail generated parentValid ih =>
    obtain ⟨answer⟩ := ih parentValid
    let source := cappedRawFrame generated parentValid
    have same : answer.frame.fullTail.tailLocals = source.fullTail.tailLocals :=
      answer.frame.fullTail_locals.trans source.fullTail_locals.symm
    let frame := same ▸ answer.frame.fullTail.frame
    have generatedTail := CappedCaptureGenerated.tail answer.capped answer.frame.valid
    have capped := capped_castLocals answer.frame.fullTail.frame generatedTail same
    refine ⟨⟨_, frame, capped, fun i need member => answer.included (i + 1) need member,
      fun i need member atom present => answer.closed (i + 1) need member atom present, ?_⟩⟩
    intro ordered depth
    rw [suffixEnvironment_castLocals, OriginalRichFrame.suffixEnvironment_tail]
    exact (answer.suffixEnvironment ordered (depth + 1)).trans
      (OriginalRichFrame.suffixEnvironment_tail source ordered depth).symm
  | reserveCapture generated closures ih =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨answer⟩ := ih valid
    refine ⟨⟨_, answer.frame.reserve closures, .reserveCapture answer.capped closures,
      answer.included, answer.closed, ?_⟩⟩
    intro ordered depth
    cases depth with
    | zero =>
      rw [OriginalRichFrame.suffixEnvironment_zero, OriginalRichFrame.suffixEnvironment_zero]
      change closures ++ answer.frame.dependencyEnvironment ordered = closures ++ _
      rw [answer.environment]
    | succ depth =>
      change (answer.frame.reserve closures).suffixEnvironment ordered (depth + 1) =
        ((OriginalRichFrame.mk _ valid).reserve closures).suffixEnvironment ordered (depth + 1)
      rw [OriginalRichFrame.suffixEnvironment_reserve_succ, OriginalRichFrame.suffixEnvironment_reserve_succ]
      exact answer.suffixEnvironment ordered (depth + 1)
  | reserveBind generated closures ih =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨answer⟩ := ih valid
    refine ⟨⟨_, answer.frame.reserve closures, .reserveBind answer.capped closures,
      answer.included, answer.closed, ?_⟩⟩
    intro ordered depth
    cases depth with
    | zero =>
      rw [OriginalRichFrame.suffixEnvironment_zero, OriginalRichFrame.suffixEnvironment_zero]
      change closures ++ answer.frame.dependencyEnvironment ordered = closures ++ _
      rw [answer.environment]
    | succ depth =>
      change (answer.frame.reserve closures).suffixEnvironment ordered (depth + 1) =
        ((OriginalRichFrame.mk _ valid).reserve closures).suffixEnvironment ordered (depth + 1)
      rw [OriginalRichFrame.suffixEnvironment_reserve_succ, OriginalRichFrame.suffixEnvironment_reserve_succ]
      exact answer.suffixEnvironment ordered (depth + 1)
  | identity => exact ⟨⟨_, base.frame, .identity, fun _ _ h => h, baseClosed, fun _ _ => rfl⟩⟩
  | empty => exact ⟨⟨_, .nil, .empty _ _ _, fun _ _ h => h,
      fun _ _ h => False.elim (List.not_mem_nil h), fun _ _ => rfl⟩⟩
  | merge first second ihl ihr =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨left⟩ := ihl valid.1
    obtain ⟨right⟩ := ihr valid.2
    refine ⟨⟨_, left.frame.merge right.frame, .merge left.capped right.capped, ?_, ?_, ?_⟩⟩
    · intro i need member
      exact (List.mem_append.mp member).elim
        (fun h => List.mem_append_left _ (left.included i need h))
        (fun h => List.mem_append_right _ (right.included i need h))
    · intro i need member atom present
      exact (List.mem_append.mp member).elim
        (fun h => List.mem_append_left _ (left.closed i need h atom present))
        (fun h => List.mem_append_right _ (right.closed i need h atom present))
    · intro ordered depth
      rw [OriginalRichFrame.suffixEnvironment_merge, left.suffixEnvironment, right.suffixEnvironment]
      exact (OriginalRichFrame.suffixEnvironment_merge _ _ ordered depth).symm
  | weaken generated insertion leftTail rightTail capsTail ih =>
    obtain ⟨answer⟩ := ih valid
    exact ⟨{ answer with capped := .weaken answer.capped insertion leftTail rightTail capsTail }⟩
  | bind generated domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨tail⟩ := ih valid
    have resources' := fun i need member => tail.included i need (resources i need member)
    have fits := closeNeeds_fits _ needs bounded covered
    let frame := tail.frame.bind domain certificate resources' typed arguments
      (needs ++ needs.flatMap Need.singletons) (fun n m => (fits n m).1) (fun n m => (fits n m).2)
    refine ⟨⟨_, frame, .bind tail.capped domain annotation displayed certificate resources' typed arguments
      _ (fun n m => (fits n m).1) (fun n m => (fits n m).2), ?_,
      Valuation.push_atomized_closed tail.closed needs, ?_⟩⟩
    · intro i need member
      cases i with
      | zero => exact List.mem_append_left _ member
      | succ i => exact tail.included i need member
    · intro ordered depth
      cases depth with
      | zero =>
        simp only [OriginalRichFrame.suffixEnvironment_zero]
        change Closure.close _ (tail.frame.dependencyEnvironment ordered) :: tail.frame.dependencyEnvironment ordered = _
        rw [tail.environment]
        rfl
      | succ depth =>
        rw [OriginalRichFrame.suffixEnvironment_bind]
        exact (tail.suffixEnvironment ordered depth).trans
          (OriginalRichFrame.suffixEnvironment_bind ⟨_, valid⟩ domain certificate resources typed arguments
            needs bounded covered ordered depth).symm
  | capture generated domain initial argument location lineage query queryAvailable queryBound queryAdapter certificate resources typed arguments needs bounded covered ih =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨tail⟩ := ih valid
    have resources' := fun i need member => tail.included i need (resources i need member)
    have queryAvailable' := fun i need member => tail.included i need (queryAvailable i need member)
    have fits := closeNeeds_fits _ needs bounded covered
    let frame := tail.frame.capture domain initial argument location lineage query queryAvailable' certificate
      resources' typed arguments (needs ++ needs.flatMap Need.singletons)
      (fun n m => (fits n m).1) (fun n m => (fits n m).2)
    refine ⟨⟨_, frame, .capture tail.capped domain initial argument location lineage query queryAvailable'
      queryBound queryAdapter certificate resources' typed arguments _ (fun n m => (fits n m).1) (fun n m => (fits n m).2), ?_,
      Valuation.push_atomized_closed tail.closed needs, ?_⟩⟩
    · intro i need member
      cases i with
      | zero => exact List.mem_append_left _ member
      | succ i => exact tail.included i need member
    · intro ordered depth
      cases depth with
      | zero =>
        simp only [OriginalRichFrame.suffixEnvironment_zero]
        change Closure.bundle (Closure.close _ (tail.frame.dependencyEnvironment ordered))
          (Closure.close _ (tail.frame.dependencyEnvironment ordered)) :: tail.frame.dependencyEnvironment ordered = _
        rw [tail.environment]
        rfl
      | succ depth =>
        rw [OriginalRichFrame.suffixEnvironment_capture]
        exact (tail.suffixEnvironment ordered depth).trans
          (OriginalRichFrame.suffixEnvironment_capture ⟨_, valid⟩ domain initial argument location lineage query queryAvailable
            certificate resources typed arguments needs bounded covered ordered depth).symm
  | group generated domain ownerGenerated nominalGraph nominal provenance displayed ownerOrdered ownerInitial seed seedExtension entries owners ih ownerIH =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨tail⟩ := ih valid.1
    let nextEntries := entries.headerAvailableMono tail.included
    let nextSeed := seed.headerAvailable tail.available
    let frame := tail.frame.group domain ownerOrdered ownerInitial nextEntries
    have capped := CappedCaptureGenerated.group tail.capped domain ownerGenerated nominalGraph nominal provenance displayed
      ownerOrdered ownerInitial nextSeed seedExtension nextEntries (by
        intro entry member
        obtain ⟨previous, previousMember, rfl⟩ := List.mem_map.mp member
        exact owners previous previousMember)
    refine ⟨⟨_, frame, capped, ?_, ?_, ?_⟩⟩
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
    · intro ordered depth
      cases depth with
      | zero =>
        rw [OriginalRichFrame.suffixEnvironment_zero, OriginalRichFrame.suffixEnvironment_zero,
          OriginalRichFrame.group_environment, tail.environment,
          RichGroupedCapture.headerAvailableMono_environment]
        exact (OriginalRichFrame.group_environment ownerOrdered ordered ⟨_, valid.1⟩ entries).symm
      | succ depth =>
        rw [OriginalRichFrame.suffixEnvironment_group]
        exact (tail.suffixEnvironment ordered depth).trans
          (OriginalRichFrame.suffixEnvironment_group ⟨_, valid.1⟩ domain ownerOrdered ownerInitial entries ordered depth).symm

  | scopedGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered ownerInitial
      seed seedScope seedGenerated entries scopes owners ih seedIH ownerIH =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨tail⟩ := ih valid.1
    let nextEntries := entries.headerAvailableMono tail.included
    let nextSeed := seed.headerAvailable tail.available
    let frame := tail.frame.group domain ownerOrdered ownerInitial nextEntries
    obtain ⟨nextScopes, nextOwners⟩ := entries.headerAvailableMono_scopes tail.included scopes owners
    have capped := CappedCaptureGenerated.scopedGroup tail.capped domain ownerGraph nominalGraph nominal provenance displayed
      ownerOrdered ownerInitial nextSeed seedScope seedGenerated nextEntries nextScopes nextOwners
    refine ⟨⟨_, frame, capped, ?_, ?_, ?_⟩⟩
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
    · intro ordered depth
      cases depth with
      | zero =>
        rw [OriginalRichFrame.suffixEnvironment_zero, OriginalRichFrame.suffixEnvironment_zero,
          OriginalRichFrame.group_environment, tail.environment,
          RichGroupedCapture.headerAvailableMono_environment]
        exact (OriginalRichFrame.group_environment ownerOrdered ordered ⟨_, valid.1⟩ entries).symm
      | succ depth =>
        rw [OriginalRichFrame.suffixEnvironment_group]
        exact (tail.suffixEnvironment ordered depth).trans
          (OriginalRichFrame.suffixEnvironment_group ⟨_, valid.1⟩ domain ownerOrdered ownerInitial entries ordered depth).symm
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedGenerated domainProvenance prior history historyWellFormed historyGenerated tailBound
      entries scopes owners ih seedIH historyIH ownerIH =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨tail⟩ := ih valid.1
    let nextEntries := entries.headerAvailableMono tail.included
    let reserve := historyReserveOfEntries entries ownerOrdered headerOrdered
      (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve
    let frame := (tail.frame.group domain ownerOrdered ownerInitial nextEntries).reserve reserve
    obtain ⟨nextScopes, nextOwners⟩ := entries.headerAvailableMono_scopes tail.included scopes owners
    have nextBound : environmentCost (tail.frame.dependencyEnvironment headerOrdered) ≤
        environmentCost (prior.frame.dependencyEnvironment headerOrdered) := by
      rw [tail.environment]
      exact tailBound
    have capped := CappedCaptureGenerated.historyGroup tail.capped domain ownerGraph nominalGraph nominal provenance displayed
      ownerOrdered headerOrdered ownerInitial seed seedScope seedGenerated domainProvenance prior history
      historyWellFormed historyGenerated nextBound nextEntries nextScopes nextOwners
    refine ⟨⟨_, frame, capped, ?_, ?_, ?_⟩⟩
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
    · intro ordered depth
      cases depth with
      | zero =>
        rw [OriginalRichFrame.suffixEnvironment_zero, OriginalRichFrame.suffixEnvironment_zero]
        change reserve ++ (tail.frame.group domain ownerOrdered ownerInitial nextEntries).dependencyEnvironment ordered = _
        rw [OriginalRichFrame.group_environment, tail.environment,
          RichGroupedCapture.headerAvailableMono_environment]
        exact congrArg (fun suffix => reserve ++ suffix)
          (OriginalRichFrame.group_environment ownerOrdered ordered ⟨_, valid.1⟩ entries).symm
      | succ depth =>
        change ((tail.frame.group domain ownerOrdered ownerInitial nextEntries).reserve reserve).suffixEnvironment ordered (depth + 1) = _
        rw [OriginalRichFrame.suffixEnvironment_reserve_succ, OriginalRichFrame.suffixEnvironment_group]
        exact (tail.suffixEnvironment ordered depth).trans (by
          change _ = (((OriginalRichFrame.mk _ valid.1).group domain ownerOrdered ownerInitial entries).reserve reserve).suffixEnvironment ordered (depth + 1)
          rw [OriginalRichFrame.suffixEnvironment_reserve_succ, OriginalRichFrame.suffixEnvironment_group])

/-- Recursive reconstruction can enter a selected generated branch using its
own closed frame and unchanged cost. The semantic substitution is unchanged. -/
theorem OriginalCaptureRealization.closeResources
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (original : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : CappedCaptureGenerated base commonCaps commonLeft commonRight graph original.frame.raw)
    (baseClosed : base.available.AtomClosed) :
    ∃ nextAvailable, ∃ next : OriginalCaptureRealization graph env registry target locals commonLeft commonRight nextAvailable,
      CappedCaptureGenerated base commonCaps commonLeft commonRight graph next.frame.raw ∧
      (∀ i need, need ∈ available i → need ∈ nextAvailable i) ∧
      nextAvailable.AtomClosed ∧
      ∀ ordered : sourceEnv.Ordered,
        next.frame.dependencyEnvironment ordered = original.frame.dependencyEnvironment ordered := by
  obtain ⟨closed⟩ := generated.closeResources original.frame.valid baseClosed
  exact ⟨closed.available, ⟨closed.frame, original.substitutions⟩, closed.capped, closed.included,
    closed.closed, closed.environment⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
