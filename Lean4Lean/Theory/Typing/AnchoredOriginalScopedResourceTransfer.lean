import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientCapturedArgumentSupply
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth

/-! Finite resource transfer out of a genuinely selected scoped capture.
Each need retains its own selected destination frame: footprints with different
local tables are not concatenated and advertised in an unrelated frame.

This is the resource-producing component, conditional on the actual smaller
original bank. Its ambient generation is not a replacement for WorldGenerated,
Replayable, or controlled retained-query annotations. Those stronger witnesses
must be preserved by the same scoped replay, not reconstructed from this data.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 1200000

/-- Both ends are actual retained witnesses. `selected` retains the owner,
its scoped original frame, its raw query, and its adapter. `returned` retains
the actual unweakened destination frame and the adapted query in that frame.
No relation between the owner's assigned type and a declaration is postulated. -/
structure ScopedResourceTransfer
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (commonLeft commonRight : Subst)
    (destination : OriginalNestedDisplay U common expression assigned)
    (need : Need) (ownerCapacity destinationCapacity : Nat) where
  selected : AmbientCapturedHeadQuery base caps common commonLeft commonRight expression need ownerCapacity
  returned : AmbientBoundedGeneratedQueryReply base caps destination commonLeft commonRight
    need.profile destinationCapacity

/-- The resource map for one selected need is the returned query's actual
finite footprint, at the returned local table and availability. -/
def ScopedResourceTransfer.footprint
    (transfer : ScopedResourceTransfer base caps commonLeft commonRight destination need ownerCapacity destinationCapacity) :
    Footprint := transfer.returned.answer.reply.query.footprint

theorem ScopedResourceTransfer.available
    (transfer : ScopedResourceTransfer base caps commonLeft commonRight destination need ownerCapacity destinationCapacity) :
    transfer.footprint.Available transfer.returned.answer.reply.available :=
  transfer.returned.answer.reply.query.resources

/-- A sorted requested need yields its certificate by interpreting the
actual returned adapter, not by identifying the owner's assigned type with
the declared binder domain. The chosen output frame is unchanged. -/
theorem ScopedResourceTransfer.code
    {base : OriginalCaptureBase env U registry target}
    {destination : OriginalNestedDisplay U common expression assigned}
    (transfer : ScopedResourceTransfer base caps commonLeft commonRight destination need ownerCapacity destinationCapacity)
    (henv : env.Ordered) (formed : need.profile.HasType (.sort relevant)) :
    ∃ footprint, ∃ certificate : RichCert destination.sourceEnv env U registry target destination.node
      transfer.returned.answer.reply.locals (destination.raw.comp commonLeft) relevant need.profile footprint,
      footprint.Available transfer.returned.answer.reply.available ∧
      ∀ policy, certificate.headDepth policy ≤ transfer.returned.answer.reply.query.observation.headDepth policy :=
  transfer.returned.answer.reply.query.code_headDepth henv formed

/-- Duplicates and independently selected destination frames are retained.
A later common-frame compiler must perform a checked merge/replay; this finite
spine does not silently identify the locals or valuations of its entries. -/
inductive ScopedResourceTransfers
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (commonLeft commonRight : Subst)
    (destination : OriginalNestedDisplay U common expression assigned)
    (ownerCapacity destinationCapacity : Nat) : List Need → Type where
  | nil : ScopedResourceTransfers base caps commonLeft commonRight destination ownerCapacity destinationCapacity []
  | cons (head : ScopedResourceTransfer base caps commonLeft commonRight destination need ownerCapacity destinationCapacity)
      (tail : ScopedResourceTransfers base caps commonLeft commonRight destination ownerCapacity destinationCapacity needs) :
      ScopedResourceTransfers base caps commonLeft commonRight destination ownerCapacity destinationCapacity (need :: needs)

/-- The source variable's positive original weight pays the selected owner
capacity strictly, including when the capture belongs to a heterogeneous group.
The destination contribution is unchanged. -/
theorem captureResource_schedule
    (origin : Origin) (environment : List Closure) (destinationCost : Nat) :
    richSchedule .expressionReindex (environmentCost environment + destinationCost) <
      richSchedule .expressionReindex ((Closure.close origin environment).cost + destinationCost) := by
  have positive := origin.weight_pos
  have step : environmentCost environment < (Closure.close origin environment).cost := by
    have lower : 1 + environmentCost environment ≤ origin.weight * (1 + environmentCost environment) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (1 + environmentCost environment) positive
    change _ < origin.weight * (1 + environmentCost environment)
    omega
  exact richSchedule_strict (Nat.add_lt_add_right step _) _ _

/-- Actual heterogeneous head production. Selection comes from the positive
capture witness (which includes groups and merges), and the only semantic
call is the strictly smaller owner R computed by `head.replay`. That producer
closes resources, enters the actual owner scope, adapts its returned query,
and unweakens the SAME generated answer. -/
theorem AmbientCaptureGenerated.transferHead
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {owner : EndpointState ownerEnv U ownerSource argument ownerAssigned}
    {provenance : EndpointProvenance ownerContext owner}
    {frame : RawOriginalRichFrame headerEnv env U registry target (.cons context domain) locals σ τ available}
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain ownerGraph owner provenance) frame)
    (valid : frame.Valid) (substitutions : Ctx.SubstEq env U target σ τ (A :: headerSource))
    (ordered : headerEnv.Ordered)
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (need : Need) (member : need ∈ available 0)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (baseClosed : base.available.AtomClosed)
    (destination : OriginalNestedDisplay U common (argument.subst ownerRaw) assigned)
    (destinationOrdered : destination.sourceEnv.Ordered)
    (destinationFrame : OriginalCaptureRealization destination.graph env registry target
      destinationLocals commonLeft commonRight destinationAvailable)
    (destinationGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight
      destination.graph destinationFrame.frame.raw)
    (destinationClosed : destinationAvailable.AtomClosed)
    (bank : OriginalLowerCallBank env U registry
      (richSchedule .expressionReindex
        ((Closure.close (variableNode.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost +
         (Closure.close (destination.node.dependencyOrigin destinationOrdered)
           (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost))) :
    Nonempty (ScopedResourceTransfer base commonCaps commonLeft commonRight destination need
      (environmentCost (frame.dependencyEnvironment ordered))
      (environmentCost (destinationFrame.frame.dependencyEnvironment destinationOrdered))) := by
  obtain ⟨head⟩ := generated.headQuery valid substitutions ordered need member
  obtain ⟨answer⟩ := head.replay henv hscoped formed baseClosed destination destinationOrdered
    destinationFrame destinationGenerated destinationClosed
    (captureResource_schedule (variableNode.dependencyOrigin ordered) _ _) bank
  exact ⟨⟨head, answer⟩⟩

/-- Replay exactly the finite demanded needs, preserving multiplicities and
each chosen output frame. Every call uses the same strict variable-parent
budget proved above; no completed per-need transfer is assumed. -/
theorem AmbientCaptureGenerated.transferNeeds
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {owner : EndpointState ownerEnv U ownerSource argument ownerAssigned}
    {provenance : EndpointProvenance ownerContext owner}
    {frame : RawOriginalRichFrame headerEnv env U registry target (.cons context domain) locals σ τ available}
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain ownerGraph owner provenance) frame)
    (valid : frame.Valid) (substitutions : Ctx.SubstEq env U target σ τ (A :: headerSource))
    (ordered : headerEnv.Ordered)
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (needs : List Need) (resources : ∀ need ∈ needs, need ∈ available 0)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (baseClosed : base.available.AtomClosed)
    (destination : OriginalNestedDisplay U common (argument.subst ownerRaw) assigned)
    (destinationOrdered : destination.sourceEnv.Ordered)
    (destinationFrame : OriginalCaptureRealization destination.graph env registry target
      destinationLocals commonLeft commonRight destinationAvailable)
    (destinationGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight
      destination.graph destinationFrame.frame.raw)
    (destinationClosed : destinationAvailable.AtomClosed)
    (bank : OriginalLowerCallBank env U registry
      (richSchedule .expressionReindex
        ((Closure.close (variableNode.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost +
         (Closure.close (destination.node.dependencyOrigin destinationOrdered)
           (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost))) :
    Nonempty (ScopedResourceTransfers base commonCaps commonLeft commonRight destination
      (environmentCost (frame.dependencyEnvironment ordered))
      (environmentCost (destinationFrame.frame.dependencyEnvironment destinationOrdered)) needs) := by
  induction needs with
  | nil => exact ⟨.nil⟩
  | cons need needs ih =>
    obtain ⟨head⟩ := generated.transferHead valid substitutions ordered variableNode need
      (resources need List.mem_cons_self) henv hscoped formed baseClosed destination destinationOrdered
      destinationFrame destinationGenerated destinationClosed bank
    obtain ⟨tail⟩ := ih (fun need member => resources need (List.mem_cons_of_mem _ member))
    exact ⟨.cons head tail⟩

/-- Availability transport leaves every finite argument observation and
adapter untouched; it changes only proofs of resource membership. -/
noncomputable def RichArgumentSupply.availableMono
    {available next : Valuation}
    (supply : RichArgumentSupply sourceEnv env U registry target node locals σ available needs)
    (included : ∀ index need, need ∈ available index → need ∈ next index) :
    RichArgumentSupply sourceEnv env U registry target node locals σ next needs := by
  induction supply with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.availableMono included) ih

/-- A finite transfer compiled into ONE actual generated destination frame.
The actual frame stores both branch ledgers; its capacity is their maximum. -/
structure ScopedResourceSupply
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (commonLeft commonRight : Subst)
    (destination : OriginalNestedDisplay U common expression assigned)
    (capacity : Nat) (needs : List Need) where
  locals : List Nat
  available : Valuation
  realization : OriginalCaptureRealization destination.graph env registry target locals commonLeft commonRight available
  generated : AmbientCaptureGenerated base caps commonLeft commonRight destination.graph realization.frame.raw
  closed : available.AtomClosed
  bounded : ∀ ordered : destination.sourceEnv.Ordered,
    environmentCost (realization.frame.dependencyEnvironment ordered) ≤ capacity
  supply : RichArgumentSupply destination.sourceEnv env U registry target destination.node locals
    (destination.raw.comp commonLeft) available needs

/-- Merge one genuinely returned scoped answer with an already compiled
finite tail. Local equality follows from the shared generated graph; it is
not an additional premise or a syntactic identification of foreign owners. -/
noncomputable def ScopedResourceSupply.cons
    {base : OriginalCaptureBase env U registry target}
    {destination : OriginalNestedDisplay U common expression assigned}
    (head : AmbientBoundedGeneratedQueryReply base caps destination commonLeft commonRight need.profile capacity)
    (tail : ScopedResourceSupply base caps commonLeft commonRight destination capacity needs) :
    ScopedResourceSupply base caps commonLeft commonRight destination capacity (need :: needs) := by
  rcases head with ⟨⟨⟨⟨headLocals, headAvailable, headFrame, headScoped, headQuery, headClosed⟩,
    headCapped⟩, headBound⟩, headGenerated⟩
  rcases tail with ⟨tailLocals, tailAvailable, tailFrame, tailGenerated, tailClosed, tailBound, tailSupply⟩
  have localEq : headLocals = tailLocals :=
    headScoped.locals_eq.trans tailGenerated.capped.generated.locals_eq.symm
  cases localEq
  have leftIncluded : ∀ i n, n ∈ headAvailable i → n ∈ (headAvailable.append tailAvailable) i :=
    fun _ _ h => List.mem_append_left _ h
  have rightIncluded : ∀ i n, n ∈ tailAvailable i → n ∈ (headAvailable.append tailAvailable) i :=
    fun _ _ h => List.mem_append_right _ h
  refine ⟨headLocals, headAvailable.append tailAvailable,
    ⟨headFrame.frame.merge tailFrame.frame, headFrame.substitutions⟩,
    .merge headGenerated tailGenerated, ?_, ?_,
    .cons (headQuery.availableMono leftIncluded) (tailSupply.availableMono rightIncluded)⟩
  · intro index need member selected present
    rcases List.mem_append.mp member with member | member
    · exact List.mem_append_left _ (headClosed index need member selected present)
    · exact List.mem_append_right _ (tailClosed index need member selected present)
  · intro ordered
    rw [OriginalRichFrame.merge_environmentCost]
    exact Nat.max_le.mpr ⟨headBound ordered, tailBound ordered⟩

/-- The finite spine is compiled using only actual merges. No further F/R
call occurs at the larger resource table, and no need is silently dropped. -/
noncomputable def ScopedResourceTransfers.compile
    {base : OriginalCaptureBase env U registry target}
    {destination : OriginalNestedDisplay U common expression assigned}
    (transfers : ScopedResourceTransfers base caps commonLeft commonRight destination ownerCapacity capacity needs)
    (initial : OriginalCaptureRealization destination.graph env registry target initialLocals commonLeft commonRight initialAvailable)
    (generated : AmbientCaptureGenerated base caps commonLeft commonRight destination.graph initial.frame.raw)
    (closed : initialAvailable.AtomClosed)
    (bounded : ∀ ordered : destination.sourceEnv.Ordered,
      environmentCost (initial.frame.dependencyEnvironment ordered) ≤ capacity) :
    ScopedResourceSupply base caps commonLeft commonRight destination capacity needs := by
  induction transfers with
  | nil => exact ⟨initialLocals, initialAvailable, initial, generated, closed, bounded, .nil⟩
  | cons head _ ih => exact .cons head.returned ih

/-- Connected finite producer: select and replay actual scoped owners, then
compile all returned needs in one generated destination frame. -/
theorem AmbientCaptureGenerated.transferSupply
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {ownerContext : ContextDerivation ownerEnv U ownerSource}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    {owner : EndpointState ownerEnv U ownerSource argument ownerAssigned}
    {provenance : EndpointProvenance ownerContext owner}
    {frame : RawOriginalRichFrame headerEnv env U registry target (.cons context domain) locals σ τ available}
    (generated : AmbientCaptureGenerated base commonCaps commonLeft commonRight
      (.capture graph domain ownerGraph owner provenance) frame)
    (valid : frame.Valid) (substitutions : Ctx.SubstEq env U target σ τ (A :: headerSource))
    (ordered : headerEnv.Ordered)
    (variableNode : EndpointState headerEnv U (A :: headerSource) (.bvar 0) variableType)
    (needs : List Need) (resources : ∀ need ∈ needs, need ∈ available 0)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (baseClosed : base.available.AtomClosed)
    (destination : OriginalNestedDisplay U common (argument.subst ownerRaw) assigned)
    (destinationOrdered : destination.sourceEnv.Ordered)
    (destinationFrame : OriginalCaptureRealization destination.graph env registry target
      destinationLocals commonLeft commonRight destinationAvailable)
    (destinationGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight
      destination.graph destinationFrame.frame.raw)
    (destinationClosed : destinationAvailable.AtomClosed)
    (bank : OriginalLowerCallBank env U registry
      (richSchedule .expressionReindex
        ((Closure.close (variableNode.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost +
         (Closure.close (destination.node.dependencyOrigin destinationOrdered)
           (destinationFrame.frame.dependencyEnvironment destinationOrdered)).cost))) :
    Nonempty (ScopedResourceSupply base commonCaps commonLeft commonRight destination
      (environmentCost (destinationFrame.frame.dependencyEnvironment destinationOrdered)) needs) := by
  obtain ⟨transfers⟩ := generated.transferNeeds valid substitutions ordered variableNode needs resources
    henv hscoped formed baseClosed destination destinationOrdered destinationFrame destinationGenerated
    destinationClosed bank
  exact ⟨transfers.compile destinationFrame destinationGenerated destinationClosed (fun _ => Nat.le_refl _)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
