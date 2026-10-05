import Lean4Lean.Theory.Typing.AnchoredOriginalSourceCaptureGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedResourceClosure

/-! Close actual finite resources while retaining positive hereditary source
provenance on the same reconstructed frame and every original history. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private suffixEnvironment_castLocals from Lean4Lean.Theory.Typing.AnchoredOriginalRichSuffixEnvironment
open private closeNeeds_fits historyReserveOfEntries from Lean4Lean.Theory.Typing.AnchoredOriginalCappedResourceClosure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false

theorem RichGroupedCapture.headerAvailableMono_sourceScopes
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
    (owners : ∀ entry member, SourceCaptureGenerated P base (scopes entry member).caps (scopes entry member).left
      (scopes entry member).right (scopes entry member).graph entry.frame.raw) :
    ∃ nextScopes : ∀ entry ∈ entries.headerAvailableMono included,
      CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext),
      ∀ entry member, SourceCaptureGenerated P base (nextScopes entry member).caps (nextScopes entry member).left
        (nextScopes entry member).right (nextScopes entry member).graph entry.frame.raw := by
  have existsScope : ∀ entry ∈ entries.headerAvailableMono included,
      ∃ scope : CappedOwnerScope common ownerRaw commonLeft commonRight commonCaps entry.depth
        (entry.owner.context entry.initialContext),
        SourceCaptureGenerated P base scope.caps scope.left scope.right scope.graph entry.frame.raw := by
    intro entry member
    obtain ⟨previous, previousMember, rfl⟩ := List.mem_map.mp member
    exact ⟨scopes previous previousMember, owners previous previousMember⟩
  exact ⟨fun entry member => (existsScope entry member).choose,
    fun entry member => (existsScope entry member).choose_spec⟩

structure SourceResourceClosure (P : VEnv → Prop)
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (commonLeft commonRight : Subst)
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ originalAvailable) (valid : original.Valid) where
  available : Valuation
  frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available
  generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame.raw
  included : ∀ i need, need ∈ originalAvailable i → need ∈ available i
  closed : available.AtomClosed
  suffixEnvironment : ∀ (ordered : sourceEnv.Ordered) (depth : Nat),
    frame.suffixEnvironment ordered depth = (OriginalRichFrame.mk original valid).suffixEnvironment ordered depth

theorem SourceResourceClosure.environment
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ oldAvailable}
    {valid : original.Valid}
    (answer : SourceResourceClosure P base commonCaps commonLeft commonRight graph original valid)
    (ordered : sourceEnv.Ordered) :
    answer.frame.dependencyEnvironment ordered = original.dependencyEnvironment ordered := by
  simpa only [OriginalRichFrame.suffixEnvironment_zero, OriginalRichFrame.dependencyEnvironment] using
    answer.suffixEnvironment ordered 0

private def sourceRawFrame
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (_generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph original)
    (valid : original.Valid) : OriginalRichFrame sourceEnv env U registry target context locals σ τ available :=
  ⟨original, valid⟩

private theorem source_castLocals
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph frame.raw)
    {nextLocals : List Nat} (same : locals = nextLocals) :
    SourceCaptureGenerated P base commonCaps commonLeft commonRight graph (same ▸ frame).raw := by
  cases same
  exact generated

/-- Each branch can be closed separately at exactly its old original cost.
The base is already closed; fresh heads add only singleton selections of
needs supported by their existing guards. -/
theorem SourceCaptureGenerated.closeResources
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {original : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph original)
    (valid : original.Valid) (baseClosed : base.available.AtomClosed) :
    Nonempty (SourceResourceClosure P base commonCaps commonLeft commonRight graph original valid) := by
  induction generated with
  | tail generated parentValid ih =>
    obtain ⟨answer⟩ := ih parentValid
    let source := sourceRawFrame generated parentValid
    have same : answer.frame.fullTail.tailLocals = source.fullTail.tailLocals :=
      answer.frame.fullTail_locals.trans source.fullTail_locals.symm
    let frame := same ▸ answer.frame.fullTail.frame
    have generatedTail := SourceCaptureGenerated.tail answer.generated answer.frame.valid
    have capped := source_castLocals answer.frame.fullTail.frame generatedTail same
    refine ⟨⟨_, frame, capped, fun i need member => answer.included (i + 1) need member,
      fun i need member atom present => answer.closed (i + 1) need member atom present, ?_⟩⟩
    intro ordered depth
    rw [suffixEnvironment_castLocals, OriginalRichFrame.suffixEnvironment_tail]
    exact (answer.suffixEnvironment ordered (depth + 1)).trans
      (OriginalRichFrame.suffixEnvironment_tail source ordered depth).symm
  | reserveCapture generated closures ih =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨answer⟩ := ih valid
    refine ⟨⟨_, answer.frame.reserve closures, .reserveCapture answer.generated closures,
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
    refine ⟨⟨_, answer.frame.reserve closures, .reserveBind answer.generated closures,
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
  | identity ambient sources => exact ⟨⟨_, base.frame, .identity ambient sources, fun _ _ h => h, baseClosed, fun _ _ => rfl⟩⟩
  | empty common left right below sources => exact ⟨⟨_, .nil, .empty common left right below sources, fun _ _ h => h,
      fun _ _ h => False.elim (List.not_mem_nil h), fun _ _ => rfl⟩⟩
  | merge first second ihl ihr =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨left⟩ := ihl valid.1
    obtain ⟨right⟩ := ihr valid.2
    refine ⟨⟨_, left.frame.merge right.frame, .merge left.generated right.generated, ?_, ?_, ?_⟩⟩
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
    exact ⟨{ answer with generated := .weaken answer.generated insertion leftTail rightTail capsTail }⟩
  | bind generated domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨tail⟩ := ih valid
    have resources' := fun i need member => tail.included i need (resources i need member)
    have fits := closeNeeds_fits _ needs bounded covered
    let frame := tail.frame.bind domain certificate resources' typed arguments
      (needs ++ needs.flatMap Need.singletons) (fun n m => (fits n m).1) (fun n m => (fits n m).2)
    refine ⟨⟨_, frame, .bind tail.generated domain annotation displayed certificate resources' typed arguments
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
    refine ⟨⟨_, frame, .capture tail.generated domain initial argument location lineage query queryAvailable'
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
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedGenerated domainProvenance prior history historyWellFormed historyGenerated tailBound
      entries scopes owners ownerAmbient nominalAmbient priorAmbient routeAmbient
      ownerSources nominalSources priorSources routeSources ih seedIH historyIH ownerIH =>
    simp only [RawOriginalRichFrame.Valid] at valid
    obtain ⟨tail⟩ := ih valid.1
    let nextEntries := entries.headerAvailableMono tail.included
    let reserve := historyReserveOfEntries entries ownerOrdered headerOrdered
      (prior.frame.dependencyEnvironment headerOrdered) history.route.reserve
    let frame := (tail.frame.group domain ownerOrdered ownerInitial nextEntries).reserve reserve
    obtain ⟨nextScopes, nextOwners⟩ := entries.headerAvailableMono_sourceScopes tail.included scopes owners
    have nextBound : environmentCost (tail.frame.dependencyEnvironment headerOrdered) ≤
        environmentCost (prior.frame.dependencyEnvironment headerOrdered) := by
      rw [tail.environment]
      exact tailBound
    have capped := SourceCaptureGenerated.historyGroup tail.generated domain ownerGraph nominalGraph nominal provenance displayed
      ownerOrdered headerOrdered ownerInitial seed seedScope seedGenerated domainProvenance prior history
      historyWellFormed historyGenerated nextBound nextEntries nextScopes nextOwners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
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
theorem OriginalCaptureRealization.closeResourcesSource
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (original : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : SourceCaptureGenerated P base commonCaps commonLeft commonRight graph original.frame.raw)
    (baseClosed : base.available.AtomClosed) :
    ∃ nextAvailable, ∃ next : OriginalCaptureRealization graph env registry target locals commonLeft commonRight nextAvailable,
      SourceCaptureGenerated P base commonCaps commonLeft commonRight graph next.frame.raw ∧
      (∀ i need, need ∈ available i → need ∈ nextAvailable i) ∧
      nextAvailable.AtomClosed ∧
      ∀ ordered : sourceEnv.Ordered,
        next.frame.dependencyEnvironment ordered = original.frame.dependencyEnvironment ordered := by
  obtain ⟨closed⟩ := generated.closeResources original.frame.valid baseClosed
  exact ⟨closed.available, ⟨closed.frame, original.substitutions⟩, closed.generated, closed.included,
    closed.closed, closed.environment⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
