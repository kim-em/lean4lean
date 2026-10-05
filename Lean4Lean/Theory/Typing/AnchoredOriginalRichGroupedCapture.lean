import Lean4Lean.Theory.Typing.AnchoredOriginalRichCaptureActivation
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericRichFrame

/-! A single declaration slot can collect whole queries from several actual
original occurrences, including occurrences under different source binders.
Each entry retains its own original frame and its concrete declared-domain
alignment. Query multiplicity is not charged as extra declaration slots. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
set_option backward.isDefEq.respectTransparency false

abbrev RichGroupedCapture
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (ownerInitial : List Closure) (rawCapture leftValue rightValue : VExpr) :=
  List (RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
    headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)

def RichGroupedCapture.needs
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) : List Need :=
  entries.flatMap (fun entry => captureNeeds entry.input)

/-- Lookup selects a concrete original query and its actual aligned rich
certificate. Different needs may select different original source contexts. -/
theorem RichGroupedCapture.lookup
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (member : need ∈ entries.needs) :
    ∃ entry, entry ∈ entries ∧ ∃ support footprint,
      Nonempty (RichCert headerEnv env U registry target (.ref domain) headerLocals declaredLeft
        true (support : Profile need.rank) footprint) ∧
      footprint.Available headerAvailable ∧ need.profile.HasType support ∧
      Related env U registry target leftValue rightValue (A.subst declaredLeft) need.profile support := by
  obtain ⟨entry, entryMember, member⟩ := List.mem_flatMap.mp member
  have bounded := (captureNeeds_covered entry.input need member).1
  have covered := (captureNeeds_covered entry.input need member).2
  simp only [Need.atGrade, dif_pos bounded] at covered
  have typed := lowerProfile.hasType bounded (typed_subset covered entry.answer.value.typed)
  have related : Related env U registry target (entry.owner.expression.subst entry.ownerLeft)
      (entry.owner.expression.subst entry.ownerRight) (A.subst declaredLeft)
      (raiseProfile entry.rank bounded need.profile) entry.answer.value.support :=
    Related.of_singletons (fun atom hm => (entry.answer.related henv).singleton_of_mem (covered atom hm))
  have lowered := lowerProfile.related bounded henv formed related
  rw [entry.left_eq, entry.right_eq] at lowered
  exact ⟨entry, entryMember, _, entry.answer.aligned.footprint,
    ⟨entry.answer.aligned.certificate.lower need.rank bounded⟩,
    entry.answer.aligned.resources, typed, lowered⟩

variable {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
variable {field : EndpointRef sourceEnv U source fieldExpression fieldType}
variable {major : EndpointRef sourceEnv U source majorExpression majorType}

noncomputable def RichGroupedCapture.environment
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (initial previous : List Closure) : List Closure :=
  let declared := Closure.close (domain.dependencyOrigin headerOrdered) previous
  declared ::
    Closure.bundle (.close (field.dependencyOrigin ordered) initial) declared ::
    Closure.bundle (.close (major.dependencyOrigin ordered) initial) declared ::
    (entries.map (fun entry => Closure.bundle
    (entry.owner.dependencyClosure ordered initial) declared)) ++ previous

/-- The semantic frame charges exactly the finite owner ledger, including each
owner's retained original environment. -/
theorem OriginalRichFrame.group_environment
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (tail : OriginalRichFrame headerEnv env U registry target context
      headerLocals declaredLeft declaredRight headerAvailable)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    (tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered =
      entries.environment ordered headerOrdered ownerInitial (tail.dependencyEnvironment headerOrdered) := by
  have owners : ∀ declared : Closure,
      (richGroupedEntriesRaw entries).ownerClosures ordered declared =
      entries.map (fun entry => Closure.bundle
        (entry.owner.dependencyClosure ordered ownerInitial) declared) := by
    induction entries with
    | nil => intro declared; rfl
    | cons entry entries ih =>
      intro declared
      simp only [richGroupedEntriesRaw, RawRichGroupEntries.ownerClosures,
        RichGroupedCaptureEntry.toRaw, RawRichGroupEntry.owner, List.map_cons, ih]
  simp only [OriginalRichFrame.group, OriginalRichFrame.dependencyEnvironment,
    RawOriginalRichFrame.dependencyEnvironment, owners, RichGroupedCapture.environment]

/-- Every queried owner and its declared domain are an ACTUAL member of the
measured environment. The original whole-query owner is the lookup witness. -/
theorem RichGroupedCapture.lookup_member
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    (member : entry ∈ entries) (initial previous : List Closure) :
    Closure.bundle (entry.owner.dependencyClosure ordered initial)
      (.close (domain.dependencyOrigin headerOrdered) previous) ∈
      entries.environment ordered headerOrdered initial previous := by
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_append_left _ (List.mem_map_of_mem member))))

private theorem environmentCost_le_of_members {environment : List Closure}
    (bound : ∀ closure ∈ environment, closure.cost ≤ maximum) : environmentCost environment ≤ maximum := by
  induction environment with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
    exact Nat.max_le.mpr ⟨bound head List.mem_cons_self,
      ih (fun closure member => bound closure (List.mem_cons_of_mem _ member))⟩

private theorem owner_dependency_bound
    (ordered : sourceEnv.Ordered) (owner : HeaderOwner field major) (initial : List Closure) :
    (owner.dependencyClosure ordered initial).cost ≤
      ((field.dependencyOrigin ordered).weight + (major.dependencyOrigin ordered).weight) *
        (1 + environmentCost initial) := by
  cases owner with
  | inl owner =>
    exact Nat.le_trans (owner.location.dependency_cost_le ordered initial)
      (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  | inr owner =>
    exact Nat.le_trans (owner.location.dependency_cost_le ordered initial)
      (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))

/-- The reserve depends on original owner roots, not the number of queries
stored for this one source slot. In particular arbitrarily many Pi rows do
not consume arbitrarily many declaration slots. -/
theorem RichGroupedCapture.environment_bound
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (initial previous : List Closure) :
    environmentCost (entries.environment ordered headerOrdered initial previous) ≤
      max ((((field.dependencyOrigin ordered).weight + (major.dependencyOrigin ordered).weight) *
        (1 + environmentCost initial)) + (Closure.close (domain.dependencyOrigin headerOrdered) previous).cost)
        (environmentCost previous) := by
  apply environmentCost_le_of_members
  intro closure member
  rcases List.mem_cons.mp member with rfl | member
  · exact Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_left _ _)
  · rcases List.mem_cons.mp member with rfl | member
    · apply Nat.le_trans _ (Nat.le_max_left _ _)
      change _ + _ ≤ _ + _
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _
    rcases List.mem_cons.mp member with rfl | member
    · apply Nat.le_trans _ (Nat.le_max_left _ _)
      change _ + _ ≤ _ + _
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)) _
    rcases List.mem_append.mp member with member | member
    · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
      exact Nat.le_trans (Nat.add_le_add_right (owner_dependency_bound ordered entry.owner initial) _)
        (Nat.le_max_left _ _)
    · exact Nat.le_trans (environment_entry member) (Nat.le_max_right _ _)

/-- The concrete selected whole-query occurrence pays for its own formation
and the distinct declared-domain formation, using the actual grouped slot. -/
theorem RichGroupedCapture.lookup_alignment_bound
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    (member : entry ∈ entries) (initial previous : List Closure) (lookupOrigin : Origin) :
    (Closure.close (entry.owner.node.typeFormation.node.dependencyOrigin ordered)
      (entry.owner.dependencyEnvironment ordered initial)).cost +
      (Closure.close (domain.dependencyOrigin headerOrdered) previous).cost <
      (Closure.close lookupOrigin (entries.environment ordered headerOrdered initial previous)).cost := by
  apply Nat.lt_of_le_of_lt
    (Nat.add_le_add_right (entry.owner.node.typeFormation_dependency_cost_le ordered _) _)
  exact variable_lookup lookupOrigin (entries.lookup_member ordered headerOrdered member initial previous)

/-- Even an empty semantic group pays every prospective actual field/major
occurrence. This bound is available BEFORE interpreting a newly discovered
query or constructing its alignment entry. -/
theorem RichGroupedCapture.pending_owner_bound
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (owner : HeaderOwner field major) (initial previous : List Closure) (lookupOrigin : Origin) :
    (Closure.close (owner.node.dependencyOrigin ordered)
      (owner.dependencyEnvironment ordered initial)).cost +
      (Closure.close (domain.dependencyOrigin headerOrdered) previous).cost <
      (Closure.close lookupOrigin (entries.environment ordered headerOrdered initial previous)).cost := by
  cases owner with
  | inl occurrence =>
    apply Nat.lt_of_le_of_lt (Nat.add_le_add_right (occurrence.location.dependency_cost_le ordered initial) _)
    exact variable_lookup lookupOrigin (show Closure.bundle (.close (field.dependencyOrigin ordered) initial)
      (.close (domain.dependencyOrigin headerOrdered) previous) ∈ entries.environment ordered headerOrdered initial previous from
      List.mem_cons_of_mem _ List.mem_cons_self)
  | inr occurrence =>
    apply Nat.lt_of_le_of_lt (Nat.add_le_add_right (occurrence.location.dependency_cost_le ordered initial) _)
    exact variable_lookup lookupOrigin (show Closure.bundle (.close (major.dependencyOrigin ordered) initial)
      (.close (domain.dependencyOrigin headerOrdered) previous) ∈ entries.environment ordered headerOrdered initial previous from
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))


/-- Even an empty semantic group pays every prospective actual field/major
occurrence. This bound is available BEFORE interpreting a newly discovered
query or constructing its alignment entry. -/
theorem RichGroupedCapture.pending_alignment_bound
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (owner : HeaderOwner field major) (initial previous : List Closure) (lookupOrigin : Origin) :
    (Closure.close (owner.node.typeFormation.node.dependencyOrigin ordered)
      (owner.dependencyEnvironment ordered initial)).cost +
      (Closure.close (domain.dependencyOrigin headerOrdered) previous).cost <
      (Closure.close lookupOrigin (entries.environment ordered headerOrdered initial previous)).cost := by
  apply Nat.lt_of_le_of_lt
    (Nat.add_le_add_right (owner.node.typeFormation_dependency_cost_le ordered _) _)
  cases owner with
  | inl occurrence =>
    apply Nat.lt_of_le_of_lt (Nat.add_le_add_right (occurrence.location.dependency_cost_le ordered initial) _)
    exact variable_lookup lookupOrigin (show Closure.bundle (.close (field.dependencyOrigin ordered) initial)
      (.close (domain.dependencyOrigin headerOrdered) previous) ∈ entries.environment ordered headerOrdered initial previous from
      List.mem_cons_of_mem _ List.mem_cons_self)
  | inr occurrence =>
    apply Nat.lt_of_le_of_lt (Nat.add_le_add_right (occurrence.location.dependency_cost_le ordered initial) _)
    exact variable_lookup lookupOrigin (show Closure.bundle (.close (major.dependencyOrigin ordered) initial)
      (.close (domain.dependencyOrigin headerOrdered) previous) ∈ entries.environment ordered headerOrdered initial previous from
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- The actual grouped F frame pays the selected owner's formation query
in its retained semantic frame, together with the original declared domain. -/
theorem RichGroupedCapture.group_alignment_bound
    (ordered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (tail : OriginalRichFrame headerEnv env U registry target context
      headerLocals declaredLeft declaredRight headerAvailable)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}
    (member : entry ∈ entries) (lookupOrigin : Origin) :
    (Closure.close (entry.owner.node.typeFormation.node.dependencyOrigin ordered)
      (entry.frame.dependencyEnvironment ordered)).cost +
      (Closure.close (domain.dependencyOrigin headerOrdered)
        (tail.dependencyEnvironment headerOrdered)).cost <
      (Closure.close lookupOrigin
        ((tail.group domain ordered ownerInitial entries).dependencyEnvironment headerOrdered)).cost := by
  rw [OriginalRichFrame.group_environment]
  apply Nat.lt_of_le_of_lt _ (entries.lookup_alignment_bound ordered headerOrdered member
    ownerInitial (tail.dependencyEnvironment headerOrdered) lookupOrigin)
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (entry.frame_environment_le ordered) _)

/-- Form a ledger entry from an ACTUAL whole cut in the field tree. The
owner frame is the one constructed while traversing the original location;
it can contain fresh Pi binders and their rich metadata. -/
noncomputable def RichGroupedCaptureEntry.ofFieldOccurrence
    {initialContext : ContextDerivation sourceEnv U source}
    {ownerLocals : List Nat} {ownerLeft ownerRight : Subst} {ownerAvailable : Valuation}
    {n : Nat} {input : Profile n} {footprint : Footprint}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    (location : Located field node)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target ownerLocals
      ownerLeft ownerRight ownerAvailable ordered ownerInitial)
    (expressionEq : expression = rawCapture.lift' (.skipN .refl location.binderPrefix.length))
    (leftEq : expression.subst ownerLeft = leftValue)
    (rightEq : expression.subst ownerRight = rightValue)
    (query : RichObs sourceEnv env U registry target node ownerLocals ownerLeft (input : Profile n) footprint)
    (queryAvailable : footprint.Available ownerAvailable)
    (answer : HeaderValueAlignment
      (field := field) (major := major) (.inl ⟨_, _, _, node, location⟩) domain env registry target
      ownerLocals headerLocals ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) :
    RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue := by
  exact {
    owner := .inl ⟨_, _, _, node, location⟩
    ownerLocals := ownerLocals, ownerLeft := ownerLeft, ownerRight := ownerRight, ownerAvailable := ownerAvailable
    initialContext := initialContext
    frame := occurrence.frame
    substitutions := occurrence.substitutions
    frame_environment_le := fun _ => occurrence.environment_le
    depth := location.binderPrefix.length
    sourcePrefix := location.binderPrefix
    source_eq := location.context_eq
    depth_eq := rfl
    expression_eq := expressionEq
    left_eq := leftEq, right_eq := rightEq
    rank := n, input := input, queryRank := n, queryInput := input,
    queryBound := Nat.le_refl _, queryAdapter := by rw [raiseProfile_self]; exact .refl _
    footprint := footprint
    query := query, queryAvailable := queryAvailable, answer := answer }

noncomputable def RichGroupedCaptureEntry.ofMajorOccurrence
    {initialContext : ContextDerivation sourceEnv U source}
    {ownerLocals : List Nat} {ownerLeft ownerRight : Subst} {ownerAvailable : Valuation}
    {n : Nat} {input : Profile n} {footprint : Footprint}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {node : EndpointState sourceEnv U occurrenceSource expression assigned}
    (location : Located major node)
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target ownerLocals
      ownerLeft ownerRight ownerAvailable ordered ownerInitial)
    (expressionEq : expression = rawCapture.lift' (.skipN .refl location.binderPrefix.length))
    (leftEq : expression.subst ownerLeft = leftValue)
    (rightEq : expression.subst ownerRight = rightValue)
    (query : RichObs sourceEnv env U registry target node ownerLocals ownerLeft (input : Profile n) footprint)
    (queryAvailable : footprint.Available ownerAvailable)
    (answer : HeaderValueAlignment
      (field := field) (major := major) (.inr ⟨_, _, _, node, location⟩) domain env registry target
      ownerLocals headerLocals ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) :
    RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue := by
  exact {
    owner := .inr ⟨_, _, _, node, location⟩
    ownerLocals := ownerLocals, ownerLeft := ownerLeft, ownerRight := ownerRight, ownerAvailable := ownerAvailable
    initialContext := initialContext
    frame := occurrence.frame
    substitutions := occurrence.substitutions
    frame_environment_le := fun _ => occurrence.environment_le
    depth := location.binderPrefix.length
    sourcePrefix := location.binderPrefix
    source_eq := location.context_eq
    depth_eq := rfl
    expression_eq := expressionEq
    left_eq := leftEq, right_eq := rightEq
    rank := n, input := input, queryRank := n, queryInput := input,
    queryBound := Nat.le_refl _, queryAdapter := by rw [raiseProfile_self]; exact .refl _
    footprint := footprint
    query := query, queryAvailable := queryAvailable, answer := answer }

/-- The actual owner F frame is bounded by the same original roots as its
whole cut; the resource ledger does not hide an unrelated semantic frame. -/
theorem RichGroupedCaptureEntry.frame_cost_bound
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (ordered : sourceEnv.Ordered) :
    (Closure.close (entry.owner.node.dependencyOrigin ordered)
      (entry.frame.dependencyEnvironment ordered)).cost ≤
      ((field.dependencyOrigin ordered).weight + (major.dependencyOrigin ordered).weight) *
        (1 + environmentCost ownerInitial) := by
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (entry.frame_environment_le ordered) _))
    (owner_dependency_bound ordered entry.owner ownerInitial)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
