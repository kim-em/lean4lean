import Lean4Lean.Theory.Typing.AnchoredOriginalWorldArgumentSupplyControl
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySandbox
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory

/-! Concrete family capture traces retain the actual source argument.
At depth zero the recorded binder extension is necessarily empty. This
fact, rather than a bound on environment cost, recovers the original caller
resource table for every selected demand. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private needAdapter from Lean4Lean.Theory.Typing.AnchoredOriginalCapturedQuerySelection
open private descendant_below from Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyApplyPiWorldHistory
open private from_left from Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

theorem OriginalFrameExtension.sameSourceFrame
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    {context : ContextDerivation sourceEnv U source}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (extension : OriginalFrameExtension base frame)
    (sameLength : source.length = baseSource.length) :
    source = baseSource ∧ locals = baseLocals ∧ σ = baseLeft ∧ τ = baseRight ∧
      available = baseAvailable ∧ HEq frame base := by
  have empty : extension.length = 0 := by
    have lengths := congrArg List.length extension.source_eq
    rw [List.length_append, extension.prefix_length] at lengths
    omega
  cases extension with
  | refl => exact ⟨rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩
  | bind previous domain certificate resources typed arguments needs bounded covered =>
    simp only [OriginalFrameExtension.length] at empty
    omega

/-- Selecting any finite need from an actually completed family capture
retains the original source locals, substitutions, and resource table. -/
theorem GeneratedArgumentCaptureTrace.sourceFrame
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    {entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    (trace : GeneratedArgumentCaptureTrace frame pending input entries)
    (depthZero : pending.depth = 0)
    {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    (member : entry ∈ entries) :
    entry.owner.source = source ∧ entry.ownerLocals = locals ∧ entry.ownerLeft = σ ∧ entry.ownerRight = τ ∧
      entry.ownerAvailable = available ∧ HEq entry.frame.raw frame.raw := by
  have ownerEq := trace.owners entry member
  have pendingSource : pending.owner.source = source := by
    have prefixEmpty : pending.sourcePrefix = [] := by
      apply List.length_eq_zero_iff.mp
      have depthEq := pending.depth_eq
      omega
    simpa only [prefixEmpty, List.nil_append] using pending.source_eq
  obtain ⟨extension⟩ := trace.extensions entry member
  exact extension.sameSourceFrame (by rw [ownerEq, pendingSource])


private theorem transportArgumentObserver
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {argument : EndpointState sourceEnv U source expression assigned}
    (location : Located major argument)
    (owner : HeaderOwner field major)
    (ownerEq : owner = .inr ⟨source, expression, assigned, argument, location⟩)
    (query : RichObs sourceEnv env U registry target owner.node oldLocals oldLeft profile footprint)
    (resources : footprint.Available oldAvailable)
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (localsEq : oldLocals = locals) (leftEq : oldLeft = σ) (availableEq : oldAvailable = available) :
    ∃ actual : RichObs sourceEnv env U registry target argument locals σ profile footprint,
      HEq actual query ∧ footprint.Available available ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation actual)) := by
  cases ownerEq
  cases localsEq
  cases leftEq
  cases availableEq
  exact ⟨query, HEq.rfl, resources, ⟨ready⟩⟩

/-- The actual completed capture supplies a richer observer at the original
argument. Every selected entry is traced back to the same source frame;
controls are selected from the concrete group's retained query list. -/
theorem GeneratedArgumentCaptureTrace.controlledHead
    {base : OriginalCaptureBase env U registry target}
    {strata : EquationStratification env}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    {entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    (trace : GeneratedArgumentCaptureTrace frame pending input entries)
    (depthZero : pending.depth = 0)
    {argument : EndpointState sourceEnv U source expression assigned}
    (location : Located major argument)
    (ownerEq : pending.owner = .inr ⟨source, expression, assigned, argument, location⟩)
    {headerContext : ContextDerivation headerEnv U headerSource}
    {tail : RawOriginalRichFrame headerEnv env U registry target headerContext headerLocals
      declaredLeft declaredRight headerAvailable}
    {graph : OriginalCaptureMap (common := common) (.cons headerContext domain) raw}
    (ownerOrdered : sourceEnv.Ordered)
    {headerControls : OriginalWorldControls strata headerEnv}
    (controls : OriginalWorldControls strata sourceEnv)
    {frontier : List (World strata.rules.length)}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph
      (.reserve (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries)) reserve) headerControls)
    (ready : generated.Controlled frontier)
    (sameCutoff : headerControls.cutoff = controls.cutoff)
    (sameFuel : headerControls.fuel = controls.fuel)
    (need : Need) (member : need ∈ entries.needs) :
    ∃ rank, ∃ bound : need.rank ≤ rank, ∃ profile : Profile rank, ∃ footprint,
    ∃ query : RichObs sourceEnv env U registry target argument locals σ profile footprint,
      footprint.Available available ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation query)) ∧
      Nonempty (GeneralNormalProfileAdapter env U registry target profile (raiseProfile rank bound need.profile)) := by
  obtain ⟨entry, present, requested⟩ := List.mem_flatMap.mp member
  have queryMember : .observation entry.query ∈ generated.retainedQueries := by
    apply generated.storedQueries_in_retained
    simp only [RawOriginalRichFrame.storedQueries]
    exact List.mem_append_left _ (RichGroupedCapture.query_mem_storedQueries entries present)
  obtain ⟨queryReady⟩ := ready.selectStored queryMember
  let sourceReady := queryReady.recontrol controls sameCutoff sameFuel
  obtain ⟨_, localsEq, leftEq, _, availableEq, _⟩ := trace.sourceFrame depthZero present
  obtain ⟨actual, sameQuery, resources, ⟨actualReady⟩⟩ :=
    transportArgumentObserver location entry.owner ((trace.owners entry present).trans ownerEq)
      entry.query entry.queryAvailable sourceReady localsEq leftEq availableEq
  have bounded := (captureNeeds_covered entry.input need requested).1
  have covered := (captureNeeds_covered entry.input need requested).2
  exact ⟨entry.queryRank, Nat.le_trans bounded entry.queryBound, entry.queryInput, entry.footprint,
    actual, resources, ⟨actualReady⟩, ⟨needAdapter entry.queryBound entry.queryAdapter bounded covered⟩⟩


/-- A genuinely richer demand from an earlier captured slot is replayed at
the independently retained source argument. The source query is selected
from this exact capture trace; both original R endpoints are proper
descendants of the actual projection major, and the destination identity
sandbox is chosen here from the whole caller frame. -/
theorem GeneratedArgumentCaptureTrace.replayAtArgument
    {base : OriginalCaptureBase env U registry target}
    {strata : EquationStratification env}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    {entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    (trace : GeneratedArgumentCaptureTrace frame pending input entries)
    (depthZero : pending.depth = 0)
    {argument : EndpointState sourceEnv U source expression assigned}
    (location : Located major argument)
    (ownerEq : pending.owner = .inr ⟨source, expression, assigned, argument, location⟩)
    {headerContext : ContextDerivation headerEnv U headerSource}
    {tail : RawOriginalRichFrame headerEnv env U registry target headerContext headerLocals
      declaredLeft declaredRight headerAvailable}
    {graph : OriginalCaptureMap (common := common) (.cons headerContext domain) raw}
    (ownerOrdered : sourceEnv.Ordered)
    {headerControls : OriginalWorldControls strata headerEnv}
    (controls : OriginalWorldControls strata sourceEnv)
    {frontier : List (World strata.rules.length)}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph
      (.reserve (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries)) reserve) headerControls)
    (ready : generated.Controlled frontier)
    (sameCutoff : headerControls.cutoff = controls.cutoff)
    (sameFuel : headerControls.fuel = controls.fuel)

    {outer : EndpointState sourceEnv U source (.proj projectionName projectionIndex displayedMajor) outerType}
    (outerHead : ProjectionHead outer)
    (majorLocation : Located (.right outerHead.major) (.ref major))
    {destination : EndpointState sourceEnv U source expression destinationType}
    (destinationLocation : Located major destination)
    (destinationProvenance : EndpointProvenance context destination)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (other : World strata.rules.length)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (reindex :
      CallBelow strata.rules.length
        (frontier ++ [originalCallWorld controls .expressionReindex argument captured,
          originalCallWorld controls .expressionReindex destination captured])
        (frontier ++ [originalCallWorld controls .assignedComparison outer captured, other]) →
      ∀ {n : Nat} {profile : Profile n} {footprint : Footprint}
        (query : RichObs sourceEnv env U registry target argument locals σ profile footprint),
      footprint.Available available →
      ControlledStoredQuery controls frontier (.observation query) →
      ∃ reply : CappedGeneratedQueryReply (frame.captureBase substitutions)
        (frame.captureBase substitutions).initialCaps
        (OriginalNestedDisplay.identity (frame.captureBase substitutions) destination destinationProvenance)
        σ τ profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation reply.reply.query.observation)))
    (need : Need) (member : need ∈ entries.needs) :
    ∃ result : RichGradedResult sourceEnv env U registry target destination locals σ available need.profile,
      Nonempty (ControlledStoredQuery controls frontier (.observation result.observation)) := by
  obtain ⟨rank, bound, profile, footprint, query, resources, ⟨queryReady⟩, ⟨adapter⟩⟩ :=
    trace.controlledHead depthZero location ownerEq ownerOrdered controls generated ready sameCutoff sameFuel need member
  have proper : CallBelow strata.rules.length
      [originalCallWorld controls .expressionReindex argument captured,
       originalCallWorld controls .expressionReindex destination captured]
      [originalCallWorld controls .assignedComparison outer captured, other] := by
    apply from_left
    intro call member
    rcases List.mem_cons.mp member with rfl | member
    · exact descendant_below outerHead majorLocation location controls captured _ _
    · cases List.mem_singleton.mp member
      exact descendant_below outerHead majorLocation destinationLocation controls captured _ _
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .expressionReindex argument captured,
        originalCallWorld controls .expressionReindex destination captured])
      (frontier ++ [originalCallWorld controls .assignedComparison outer captured, other]) := by
    clear ready queryReady reindex
    induction frontier with
    | nil => exact proper
    | cons sponsor rest ih => exact ih.cons sponsor
  obtain ⟨reply, ⟨replyReady⟩⟩ := reindex funded query resources queryReady
  obtain ⟨frozenReady⟩ := reply.freezeBase_controlled replyReady
  exact ⟨reply.freezeBase.adaptRequest henv hscoped formed bound adapter, ⟨frozenReady⟩⟩


/-- Consume any finite newly requested list at this actual prefix slot.
The list recursion runs no semantic call on a generated header node: every
R call is the exact pair of proper source-argument occurrences above. -/
theorem GeneratedArgumentCaptureTrace.supplyAtArgument
    {base : OriginalCaptureBase env U registry target}
    {strata : EquationStratification env}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {context : ContextDerivation sourceEnv U source}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    {entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    (trace : GeneratedArgumentCaptureTrace frame pending input entries)
    (depthZero : pending.depth = 0)
    {argument : EndpointState sourceEnv U source expression assigned}
    (location : Located major argument)
    (ownerEq : pending.owner = .inr ⟨source, expression, assigned, argument, location⟩)
    {headerContext : ContextDerivation headerEnv U headerSource}
    {tail : RawOriginalRichFrame headerEnv env U registry target headerContext headerLocals
      declaredLeft declaredRight headerAvailable}
    {graph : OriginalCaptureMap (common := common) (.cons headerContext domain) raw}
    (ownerOrdered : sourceEnv.Ordered)
    {headerControls : OriginalWorldControls strata headerEnv}
    (controls : OriginalWorldControls strata sourceEnv)
    {frontier : List (World strata.rules.length)}
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph
      (.reserve (.group tail domain ownerOrdered ownerInitial (richGroupedEntriesRaw entries)) reserve) headerControls)
    (ready : generated.Controlled frontier)
    (sameCutoff : headerControls.cutoff = controls.cutoff)
    (sameFuel : headerControls.fuel = controls.fuel)

    {outer : EndpointState sourceEnv U source (.proj projectionName projectionIndex displayedMajor) outerType}
    (outerHead : ProjectionHead outer)
    (majorLocation : Located (.right outerHead.major) (.ref major))
    {destination : EndpointState sourceEnv U source expression destinationType}
    (destinationLocation : Located major destination)
    (destinationProvenance : EndpointProvenance context destination)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (other : World strata.rules.length)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (reindex :
      CallBelow strata.rules.length
        (frontier ++ [originalCallWorld controls .expressionReindex argument captured,
          originalCallWorld controls .expressionReindex destination captured])
        (frontier ++ [originalCallWorld controls .assignedComparison outer captured, other]) →
      ∀ {n : Nat} {profile : Profile n} {footprint : Footprint}
        (query : RichObs sourceEnv env U registry target argument locals σ profile footprint),
      footprint.Available available →
      ControlledStoredQuery controls frontier (.observation query) →
      ∃ reply : CappedGeneratedQueryReply (frame.captureBase substitutions)
        (frame.captureBase substitutions).initialCaps
        (OriginalNestedDisplay.identity (frame.captureBase substitutions) destination destinationProvenance)
        σ τ profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation reply.reply.query.observation)))
    (needs : List Need) (members : ∀ need ∈ needs, need ∈ entries.needs) :
    ∃ supply : RichArgumentSupply sourceEnv env U registry target destination locals σ available needs,
      supply.Controlled controls frontier := by
  induction needs with
  | nil => exact ⟨.nil, trivial⟩
  | cons need needs ih =>
    obtain ⟨query, ready⟩ := trace.replayAtArgument depthZero location ownerEq ownerOrdered controls
      generated ready sameCutoff sameFuel outerHead majorLocation destinationLocation destinationProvenance
      substitutions captured other henv hscoped formed reindex need (members need List.mem_cons_self)
    obtain ⟨tail, tailReady⟩ := ih (fun need member => members need (List.mem_cons_of_mem _ member))
    exact ⟨.cons query tail, ready, tailReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
