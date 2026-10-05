import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichProjectedDomain
import Lean4Lean.Theory.Typing.AnchoredOriginalGroupedHeaderReserve

/-! Whole-cut queries before their declared-domain alignment is produced.
The frame and source lineage are retained, but no alignment answer occurs in
this data or in the reserve used to interpret the query. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

structure PendingRichCapture
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (ownerInitial : List Closure) (rawCapture leftValue rightValue : VExpr) where
  owner : HeaderOwner field major
  ownerLocals : List Nat
  ownerLeft : Subst
  ownerRight : Subst
  ownerAvailable : Valuation
  ownerClosed : ownerAvailable.AtomClosed
  initialContext : ContextDerivation sourceEnv U source
  frame : OriginalRichFrame sourceEnv env U registry target
    (owner.context initialContext) ownerLocals ownerLeft ownerRight ownerAvailable
  substitutions : Ctx.SubstEq env U target ownerLeft ownerRight owner.source
  frame_environment_le : ∀ ordered : sourceEnv.Ordered,
    environmentCost (frame.dependencyEnvironment ordered) ≤
      environmentCost (owner.dependencyEnvironment ordered ownerInitial)
  depth : Nat
  sourcePrefix : List VExpr
  source_eq : owner.source = sourcePrefix ++ source
  depth_eq : depth = sourcePrefix.length
  expression_eq : owner.expression = rawCapture.lift' (.skipN .refl depth)
  left_eq : owner.expression.subst ownerLeft = leftValue
  right_eq : owner.expression.subst ownerRight = rightValue
  rank : Nat
  input : Profile rank
  footprint : Footprint
  query : RichObs sourceEnv env U registry target owner.node ownerLocals ownerLeft input footprint
  queryAvailable : footprint.Available ownerAvailable

/-- Changing the declaration-side resource table retains the entire original
whole query, its actual semantic frame, and its binder-dependent metadata. -/
def PendingRichCapture.reheader
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (nextLocals : List Nat) (nextLeft : Subst) (nextAvailable : Valuation) :
    PendingRichCapture (field := field) (major := major) domain env registry target
      nextLocals nextLeft nextAvailable ownerInitial rawCapture leftValue rightValue where
  owner := pending.owner
  ownerLocals := pending.ownerLocals
  ownerLeft := pending.ownerLeft
  ownerRight := pending.ownerRight
  ownerAvailable := pending.ownerAvailable
  ownerClosed := pending.ownerClosed
  initialContext := pending.initialContext
  frame := pending.frame
  substitutions := pending.substitutions
  frame_environment_le := pending.frame_environment_le
  depth := pending.depth
  sourcePrefix := pending.sourcePrefix
  source_eq := pending.source_eq
  depth_eq := pending.depth_eq
  expression_eq := pending.expression_eq
  left_eq := pending.left_eq
  right_eq := pending.right_eq
  rank := pending.rank
  input := pending.input
  footprint := pending.footprint
  query := pending.query
  queryAvailable := pending.queryAvailable

variable {sourceEnv headerEnv env : VEnv} {U : Nat} {source headerSource target : List VExpr}
variable {fieldExpression fieldType majorExpression majorType A : VExpr} {level : VLevel}
variable {field : EndpointRef sourceEnv U source fieldExpression fieldType}
variable {major : EndpointRef sourceEnv U source majorExpression majorType}
variable {domain : EndpointRef headerEnv U headerSource A (.sort level)}
variable {registry : CanonicalHead.Registry} {headerLocals : List Nat} {declaredLeft : Subst}
variable {headerAvailable : Valuation} {ownerInitial : List Closure} {rawCapture leftValue rightValue : VExpr}

noncomputable def PendingRichCapture.complete
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (answer : HeaderValueAlignment pending.owner domain env registry target pending.ownerLocals headerLocals
      pending.ownerLeft pending.ownerRight declaredLeft pending.ownerAvailable headerAvailable pending.input) :
    RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue := {
  owner := pending.owner
  ownerLocals := pending.ownerLocals
  ownerLeft := pending.ownerLeft
  ownerRight := pending.ownerRight
  ownerAvailable := pending.ownerAvailable
  initialContext := pending.initialContext
  frame := pending.frame
  substitutions := pending.substitutions
  frame_environment_le := pending.frame_environment_le
  depth := pending.depth
  sourcePrefix := pending.sourcePrefix
  source_eq := pending.source_eq
  depth_eq := pending.depth_eq
  expression_eq := pending.expression_eq
  left_eq := pending.left_eq
  right_eq := pending.right_eq
  rank := pending.rank
  input := pending.input
  queryRank := pending.rank
  queryInput := pending.input
  queryBound := Nat.le_refl _
  queryAdapter := by rw [raiseProfile_self]; exact .refl _
  footprint := pending.footprint
  query := pending.query
  queryAvailable := pending.queryAvailable
  answer := answer }

/-- The raw original query survives directional input adaptation. The declared
value and its support are proved separately at the advertised input. -/
noncomputable def PendingRichCapture.completeAdapted
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (input : Profile n)
    (bound : n ≤ pending.rank)
    (adapter : GeneralNormalProfileAdapter env U registry target pending.input
      (raiseProfile pending.rank bound input))
    (answer : HeaderValueAlignment pending.owner domain env registry target pending.ownerLocals headerLocals
      pending.ownerLeft pending.ownerRight declaredLeft pending.ownerAvailable headerAvailable input) :
    RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue := {
  owner := pending.owner
  ownerLocals := pending.ownerLocals
  ownerLeft := pending.ownerLeft
  ownerRight := pending.ownerRight
  ownerAvailable := pending.ownerAvailable
  initialContext := pending.initialContext
  frame := pending.frame
  substitutions := pending.substitutions
  frame_environment_le := pending.frame_environment_le
  depth := pending.depth
  sourcePrefix := pending.sourcePrefix
  source_eq := pending.source_eq
  depth_eq := pending.depth_eq
  expression_eq := pending.expression_eq
  left_eq := pending.left_eq
  right_eq := pending.right_eq
  rank := n
  input := input
  queryRank := pending.rank
  queryInput := pending.input
  queryBound := bound
  queryAdapter := adapter
  footprint := pending.footprint
  query := pending.query
  queryAvailable := pending.queryAvailable
  answer := answer }

noncomputable def PendingRichCapture.measureOwner
    (ordered : sourceEnv.Ordered)
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    Sum (Dependency.LocatedOrigin ordered field) (Dependency.LocatedOrigin ordered major) :=
  pending.owner.map (Dependency.measureLocated ordered) (Dependency.measureLocated ordered)

theorem PendingRichCapture.owner_cost_le
    (ordered : sourceEnv.Ordered)
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    (Closure.close (pending.owner.node.dependencyOrigin ordered)
      (pending.frame.dependencyEnvironment ordered)).cost ≤
    (Dependency.groupedOwnerClosure (pending.measureOwner ordered) ownerInitial).cost := by
  have bound := Nat.mul_le_mul_left (pending.owner.node.dependencyOrigin ordered).weight
    (Nat.add_le_add_left (pending.frame_environment_le ordered) 1)
  have equation : ∀ owner : HeaderOwner field major,
      Closure.close (owner.node.dependencyOrigin ordered) (owner.dependencyEnvironment ordered ownerInitial) =
      Dependency.groupedOwnerClosure
        (owner.map (Dependency.measureLocated ordered) (Dependency.measureLocated ordered)) ownerInitial := by
    intro owner
    cases owner <;> rfl
  change _ ≤ (Dependency.groupedOwnerClosure
    (pending.owner.map (Dependency.measureLocated ordered) (Dependency.measureLocated ordered)) ownerInitial).cost
  rw [← equation]
  exact bound

/-- A newly discovered whole cut is scheduled against the existing destination
slot, including an empty group. Its actual semantic owner frame is retained;
no completed alignment or membership in the old group is required. -/
theorem PendingRichCapture.group_owner_activation_bound
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {context : ContextDerivation headerEnv U headerSource}
    (tail : OriginalRichFrame headerEnv env U registry target context
      headerLocals declaredLeft declaredRight headerAvailable)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (lookupOrigin : Origin) :
    (Closure.close (pending.owner.node.dependencyOrigin ordered)
      (pending.frame.dependencyEnvironment ordered)).cost +
      (Closure.close (domain.dependencyOrigin headerOrdered)
        (tail.dependencyEnvironment headerOrdered)).cost <
      (Closure.close lookupOrigin
        ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost := by
  rw [OriginalRichFrame.group_environment]
  apply Nat.lt_of_le_of_lt _ (entries.pending_owner_bound ordered headerOrdered pending.owner
    ownerInitial (tail.dependencyEnvironment headerOrdered) lookupOrigin)
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (pending.frame_environment_le ordered) _)


/-- A newly discovered whole cut is scheduled against the existing destination
slot, including an empty group. Its actual semantic owner frame is retained;
no completed alignment or membership in the old group is required. -/
theorem PendingRichCapture.group_activation_bound
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {context : ContextDerivation headerEnv U headerSource}
    (tail : OriginalRichFrame headerEnv env U registry target context
      headerLocals declaredLeft declaredRight headerAvailable)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (lookupOrigin : Origin) :
    (Closure.close (pending.owner.node.typeFormation.node.dependencyOrigin ordered)
      (pending.frame.dependencyEnvironment ordered)).cost +
      (Closure.close (domain.dependencyOrigin headerOrdered)
        (tail.dependencyEnvironment headerOrdered)).cost <
      (Closure.close lookupOrigin
        ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost := by
  rw [OriginalRichFrame.group_environment]
  apply Nat.lt_of_le_of_lt _ (entries.pending_alignment_bound ordered headerOrdered pending.owner
    ownerInitial (tail.dependencyEnvironment headerOrdered) lookupOrigin)
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (pending.frame_environment_le ordered) _)

/-- Interpreting a retained whole query is paid by the original projection
before any declaration-side frame or alignment answer is constructed. -/
theorem PendingRichCapture.projection_owner_schedule
    (sourceOrdered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
    (major : Derivation sourceEnv U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (pending : PendingRichCapture (field := field) (major := .left major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    richSchedule .fundamental
      (Closure.close (pending.owner.node.dependencyOrigin sourceOrdered)
        (pending.frame.dependencyEnvironment sourceOrdered)).cost <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin sourceOrdered) ownerInitial).cost := by
  apply richSchedule_strict
  apply Nat.lt_of_le_of_lt (pending.owner_cost_le sourceOrdered)
  apply Nat.lt_of_le_of_lt (Dependency.groupedOwner_bound (pending.measureOwner sourceOrdered) ownerInitial)
  change _ < _ * (1 + environmentCost ownerInitial)
  apply Nat.mul_lt_mul_of_pos_right _ (by omega)
  simp only [EndpointState.dependencyOrigin, EndpointRef.dependencyOrigin, Origin.weight,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, reserveOrigin_weight]
  omega

/-- Once owner interpretation has determined the required record demand,
replay the earlier prefix and complete the capture at its actual projected
declared domain. No declared-domain comparison callback is used here. -/
noncomputable def PendingRichCapture.completeProjected
    {context : ContextDerivation headerEnv U headerSource}
    {domainX : EndpointRef headerEnv U headerSource (.proj name index (.bvar slot)) (.sort xLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (frame : OriginalRichFrame headerEnv env U registry target context headerLocals declaredLeft declaredRight headerAvailable)
    (lookup : Lookup headerSource slot S)
    (head : ProjectionHead (.ref domainX))
    (sortField : head.fieldType = .sort sortLevel) (sortRelevant : Relevant sortLevel true)
    (pending : PendingRichCapture (field := field) (major := major) domainX env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (value : RichBinderValue sourceEnv env U registry target pending.owner.node pending.ownerLocals
      pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input)
    (family : FamilyData (Profile pending.rank)) (familyName : family.name = name)
    (familyRelevant : family.relevant = true)
    (same : pending.owner.assigned.subst pending.ownerLeft = .proj name index (declaredLeft slot))
    (needed : majorNeed (fieldRecord family familyRelevant index
      (fieldRequest head declaredLeft value.support (.sort true))) ∈ headerAvailable slot) :
    RichGroupedCaptureEntry (field := field) (major := major) domainX env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue :=
  pending.complete (Classical.choice (frame.projectedDomainAlignment henv hscoped formed lookup head
    sortField sortRelevant pending.owner value family familyName familyRelevant same needed))

/-- A finite result spine contains concrete answers, never an alignment
supplier. Its pre-alignment index retains all original whole queries. -/
inductive CompletedRichCaptureBatch :
    List (PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) → Type where
  | nil : CompletedRichCaptureBatch []
  | cons (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
      (answer : HeaderValueAlignment pending.owner domain env registry target pending.ownerLocals headerLocals
        pending.ownerLeft pending.ownerRight declaredLeft pending.ownerAvailable headerAvailable pending.input)
      (rest : CompletedRichCaptureBatch tail) : CompletedRichCaptureBatch (pending :: tail)

noncomputable def CompletedRichCaptureBatch.entries
    (batch : CompletedRichCaptureBatch (field := field) (major := major) (domain := domain)
      (env := env) (registry := registry) (target := target) (headerLocals := headerLocals)
      (declaredLeft := declaredLeft) (headerAvailable := headerAvailable) (ownerInitial := ownerInitial)
      (rawCapture := rawCapture) (leftValue := leftValue) (rightValue := rightValue) pending) :
    RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue :=
  match batch with
  | .nil => []
  | .cons query answer rest => query.complete answer :: rest.entries

theorem CompletedRichCaptureBatch.ownerClosures
    (ordered : sourceEnv.Ordered) (declared : Closure)
    (batch : CompletedRichCaptureBatch (field := field) (major := major) (domain := domain)
      (env := env) (registry := registry) (target := target) (headerLocals := headerLocals)
      (declaredLeft := declaredLeft) (headerAvailable := headerAvailable) (ownerInitial := ownerInitial)
      (rawCapture := rawCapture) (leftValue := leftValue) (rightValue := rightValue) pending) :
    batch.entries.map (fun entry => Closure.bundle (entry.owner.dependencyClosure ordered ownerInitial) declared) =
    pending.map (fun query => Closure.bundle
      (Dependency.groupedOwnerClosure (query.measureOwner ordered) ownerInitial) declared) := by
  induction batch with
  | nil => rfl
  | cons query answer rest ih =>
    simp only [entries, List.map_cons, PendingRichCapture.complete, ih]
    congr 2
    unfold PendingRichCapture.measureOwner
    cases query.owner <;> rfl

/-- Completing pending calls does not enlarge or change the reserve: the
resulting semantic group has exactly the environment planned beforehand. -/
theorem CompletedRichCaptureBatch.group_environment
    {header : EndpointRef headerEnv U headerRootSource headerExpression headerType}
    {context : ContextDerivation headerEnv U headerSource}
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (domainLocation : Located header (.ref domain))
    (previous : List (Dependency.GroupedHeaderStep headerOrdered ordered header field major))
    (tail : OriginalRichFrame headerEnv env U registry target context headerLocals declaredLeft declaredRight headerAvailable)
    (tail_environment : tail.dependencyEnvironment headerOrdered = Dependency.groupedHeaderEnvironment previous ownerInitial)
    (batch : CompletedRichCaptureBatch (field := field) (major := major) (domain := domain)
      (env := env) (registry := registry) (target := target) (headerLocals := headerLocals)
      (declaredLeft := declaredLeft) (headerAvailable := headerAvailable) (ownerInitial := ownerInitial)
      (rawCapture := rawCapture) (leftValue := leftValue) (rightValue := rightValue) pending) :
    (tail.group domain ordered ownerInitial batch.entries).dependencyEnvironment headerOrdered =
    Dependency.groupedHeaderEnvironment
      (⟨⟨headerSource, A, .sort level, .ref domain, domainLocation⟩,
        .inl ⟨_, _, _, .ref field, .here⟩ :: .inr ⟨_, _, _, .ref major, .here⟩ ::
          pending.map (fun query => query.measureOwner ordered)⟩ :: previous) ownerInitial := by
  rw [OriginalRichFrame.group_environment]
  simp only [RichGroupedCapture.environment, tail_environment, Dependency.groupedHeaderEnvironment,
    batch.ownerClosures, List.map_cons, List.map_map, Function.comp_def, EndpointState.dependencyOrigin,
    Dependency.groupedOwnerClosure, Dependency.LocatedOrigin.closure, Located.dependencyEnvironment]

theorem PendingRichCapture.projection_alignment_schedule
    (sourceOrdered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
    (major : Derivation sourceEnv U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (domain : EndpointRef
      (selectOriginalHeader sourceOrdered (sourceOrdered.projectionConstructor registered) levelsWF).source
      U headerSource A (.sort level))
    (domainLocation : Located
      (.left (selectOriginalHeader sourceOrdered (sourceOrdered.projectionConstructor registered) levelsWF).original)
      (.ref domain))
    {context : ContextDerivation
      (selectOriginalHeader sourceOrdered (sourceOrdered.projectionConstructor registered) levelsWF).source U headerSource}
    (tail : OriginalRichFrame _ env U registry target context headerLocals declaredLeft declaredRight headerAvailable)
    (previous : List (Dependency.GroupedHeaderStep
      (selectOriginalHeader sourceOrdered (sourceOrdered.projectionConstructor registered) levelsWF).ordered sourceOrdered
      (.left (selectOriginalHeader sourceOrdered (sourceOrdered.projectionConstructor registered) levelsWF).original)
      field (.left major)))
    (prefixLength : previous.length ≤
      (params ++ (List.range index).map (fun j => VExpr.proj name j sourceMajor)).length)
    (tail_environment : tail.dependencyEnvironment
      (selectOriginalHeader sourceOrdered (sourceOrdered.projectionConstructor registered) levelsWF).ordered =
      Dependency.groupedHeaderEnvironment previous ownerInitial)
    (pending : PendingRichCapture (field := field) (major := .left major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    richSchedule .expressionReindex
      ((Closure.close (pending.owner.node.typeFormation.node.dependencyOrigin sourceOrdered)
        (pending.frame.dependencyEnvironment sourceOrdered)).cost +
       (Closure.close (domain.dependencyOrigin
          (selectOriginalHeader sourceOrdered (sourceOrdered.projectionConstructor registered) levelsWF).ordered)
         (tail.dependencyEnvironment
           (selectOriginalHeader sourceOrdered (sourceOrdered.projectionConstructor registered) levelsWF).ordered)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin sourceOrdered) ownerInitial).cost := by
  have pair := Dependency.grouped_projection_prefix_schedule sourceOrdered registered levelsWF levelCount
    parameterCount indexCount selected fieldWF field major closed allowed previous prefixLength
    ⟨headerSource, A, .sort level, .ref domain, domainLocation⟩
    (pending.measureOwner sourceOrdered) ownerInitial
  have ownerBound := Nat.le_trans
    (pending.owner.node.typeFormation_dependency_cost_le sourceOrdered (pending.frame.dependencyEnvironment sourceOrdered))
    (pending.owner_cost_le sourceOrdered)
  rw [tail_environment]
  change richSchedule .expressionReindex _ < _ at pair
  simp only [richSchedule, RichPhase.code, EndpointState.dependencyOrigin] at pair ⊢
  omega

theorem CompletedRichCaptureBatch.needs
    (batch : CompletedRichCaptureBatch (field := field) (major := major) (domain := domain)
      (env := env) (registry := registry) (target := target) (headerLocals := headerLocals)
      (declaredLeft := declaredLeft) (headerAvailable := headerAvailable) (ownerInitial := ownerInitial)
      (rawCapture := rawCapture) (leftValue := leftValue) (rightValue := rightValue) pending)
    {query} (member : query ∈ pending) (needed : need ∈ captureNeeds query.input) :
    need ∈ batch.entries.needs := by
  induction batch with
  | nil => cases member
  | cons first answer rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_append_left _ needed
    · exact List.mem_append_right _ (ih member)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
