import Lean4Lean.Theory.Typing.AnchoredOriginalGenericPiReanchor
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecordExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure

/-! Advance an actual declaration prefix using its retained rich Pi row.
The local resource ledger is computed by restricting the actual captured
owner query, retaining the owner's original frame and declared alignment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
set_option backward.isDefEq.respectTransparency false

private theorem RichObs.selectQuery
    (query : RichObs sourceEnv env U registry target node locals σ (input : Profile n) footprint)
    (resources : footprint.Available available) (requested : Profile n)
    (included : ∀ atom ∈ requested.atoms, atom ∈ input.atoms) :
    ∃ required, Nonempty (RichObs sourceEnv env U registry target node locals σ requested required) ∧
      required.Available available := by
  induction requested using List.rec with
  | nil => exact ⟨[], ⟨.legacy (.legacy .empty)⟩, fun _ _ h => nomatch h⟩
  | cons atom atoms ih =>
      obtain ⟨required, ⟨rest⟩, availableRest⟩ := ih (fun a h => included a (List.mem_cons_of_mem _ h))
      exact ⟨footprint ++ required,
        ⟨.union (.select query (included atom List.mem_cons_self)) rest⟩,
        fun i need h => (List.mem_append.mp h).elim (resources i need) (availableRest i need)⟩

/-- Lower a finite local need using the SAME original owner and the SAME
captured frame. The outgoing query and both rich type certificates are
constructed; no fresh owner answer or retyping premise is introduced. -/
theorem RichGroupedCaptureEntry.forNeed
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (need : Need) (bounded : need.rank ≤ entry.rank)
    (covered : ∀ atom ∈ (need.atGrade entry.rank).atoms, atom ∈ entry.input.atoms) :
    ∃ selected : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue,
      (⟨selected.rank, selected.input⟩ : Need) = need ∧ selected.owner = entry.owner := by
  have included : ∀ atom ∈ (raiseProfile entry.rank bounded need.profile).atoms, atom ∈ entry.input.atoms := by
    simpa only [Need.atGrade, dif_pos bounded] using covered
  have adapter : GeneralNormalProfileAdapter env U registry target entry.queryInput
      (raiseProfile entry.queryRank (Nat.le_trans bounded entry.queryBound) need.profile) := by
    have selected : GeneralNormalProfileAdapter env U registry target
        (raiseProfile entry.queryRank entry.queryBound entry.input)
        (raiseProfile entry.queryRank entry.queryBound (raiseProfile entry.rank bounded need.profile)) :=
      GeneralProfileAdapter.select (by
        intro atom member
        obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
        exact List.mem_map.mpr ⟨old, raiseProfile_subset entry.queryBound included old present, rfl⟩)
    simpa only [raiseProfile_trans] using entry.queryAdapter.comp selected
  have selectedRelated : Related env U registry target (entry.owner.expression.subst entry.ownerLeft)
      (entry.owner.expression.subst entry.ownerRight) (entry.owner.assigned.subst entry.ownerLeft)
      (raiseProfile entry.rank bounded need.profile) entry.answer.value.support :=
    Related.of_singletons (fun atom member => entry.answer.value.related.singleton_of_mem (included atom member))
  let answer : HeaderValueAlignment entry.owner domain env registry target entry.ownerLocals headerLocals
      entry.ownerLeft entry.ownerRight declaredLeft entry.ownerAvailable headerAvailable need.profile := {
    value := {
      support := lowerProfile need.rank bounded entry.answer.value.support
      footprint := entry.answer.value.footprint
      certificate := entry.answer.value.certificate.lower need.rank bounded
      resources := entry.answer.value.resources
      typed := lowerProfile.hasType bounded (typed_subset included entry.answer.value.typed)
      related := lowerProfile.related bounded henv formed selectedRelated }
    aligned := {
      footprint := entry.answer.aligned.footprint
      certificate := entry.answer.aligned.certificate.lower need.rank bounded
      resources := entry.answer.aligned.resources
      related := entry.answer.aligned.related.lower henv bounded }
    path := entry.answer.path }
  exact ⟨{ entry with
    rank := need.rank
    input := need.profile
    queryBound := Nat.le_trans bounded entry.queryBound
    queryAdapter := adapter
    answer := answer }, rfl, rfl⟩

/-- One finite whole owner answer supplies every local need of the selected
row. Multiplicity changes the query ledger, never the number of slots or
the original owner roots used by the capture reserve. -/
theorem RichGroupedCaptureEntry.coverNeeds
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ entry.rank)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade entry.rank).atoms, atom ∈ entry.input.atoms) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue,
      (∀ need ∈ needs, need ∈ entries.needs) ∧
      (∀ selected ∈ entries, selected.owner = entry.owner) := by
  induction needs with
  | nil => exact ⟨[], by simp [RichGroupedCapture.needs], by simp⟩
  | cons need needs ih =>
    obtain ⟨selected, exactNeed, ownerEq⟩ := entry.forNeed henv formed need
      (bounded need List.mem_cons_self) (covered need List.mem_cons_self)
    obtain ⟨entries, coverage, owners⟩ := ih
      (fun need member => bounded need (List.mem_cons_of_mem _ member))
      (fun need member => covered need (List.mem_cons_of_mem _ member))
    refine ⟨selected :: entries, ?_, ?_⟩
    · intro requested member
      rcases List.mem_cons.mp member with rfl | member
      · change requested ∈ captureNeeds selected.input ++ entries.needs
        apply List.mem_append_left
        rw [← exactNeed]
        exact List.mem_append_left _ (List.mem_singleton_self _)
      · exact List.mem_append_right _ (coverage requested member)
    · intro chosen member
      rcases List.mem_cons.mp member with rfl | member
      · exact ownerEq
      · exact owners chosen member

/-- The computed grouped ledger is closed under the literal singleton
queries used by source pruning. -/
theorem RichGroupedCapture.closed
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (closed : headerAvailable.AtomClosed) :
    (headerAvailable.push entries.needs).AtomClosed := by
  intro index need member selected singleton
  cases index with
  | zero =>
    obtain ⟨entry, present, member⟩ := List.mem_flatMap.mp member
    exact List.mem_flatMap.mpr ⟨entry, present,
      (Valuation.push_atomized_closed closed [⟨entry.rank, entry.input⟩]) 0 need member selected singleton⟩
  | succ index => exact closed index need member selected singleton

private theorem needCoverage_cast {need first last : Need} (same : first = last)
    (covered : ∀ atom ∈ (need.atGrade last.rank).atoms, atom ∈ last.profile.atoms) :
    ∀ atom ∈ (need.atGrade first.rank).atoms, atom ∈ first.profile.atoms := by
  cases same
  exact covered

/-- Enter the actual next header binder. The source certificate is the
selected original row body, and all of its local resources are constructed
from the actual captured owner. Even an empty body retains the whole owner
query, so subsequent dependent rows can inspect the captured slot. -/
theorem RichPiRowCertificate.captureSuccessor
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    {domain : EndpointRef headerEnv U headerSource A (.sort u)}
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (sourceOrdered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (tail : OriginalRichFrame headerEnv env U registry target context
      headerLocals declaredLeft declaredRight headerAvailable)
    (key : Key n) (result : Profile n)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture key.anchor rightValue)
    (input : (⟨entry.rank, entry.input⟩ : Need) = ⟨n, key.input⟩)
    (row : RichPiRowCertificate env U registry target headerLocals declaredLeft headerAvailable
      relevant (.ref domain) body key result)
    (closed : headerAvailable.AtomClosed) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        headerLocals declaredLeft headerAvailable ownerInitial rawCapture key.anchor rightValue,
      ∃ nextFrame : OriginalRichFrame headerEnv env U registry target (.cons context domain)
        (Locals.push headerLocals) (declaredLeft.cons key.anchor) (declaredRight.cons rightValue)
        (headerAvailable.push entries.needs),
      nextFrame.dependencyEnvironment headerOrdered = entries.environment sourceOrdered headerOrdered
        ownerInitial (tail.dependencyEnvironment headerOrdered) ∧
      Nonempty (RichCert headerEnv env U registry target body (Locals.push headerLocals)
        (declaredLeft.cons key.anchor) relevant result row.bodyFootprint) ∧
      row.bodyFootprint.Available (headerAvailable.push entries.needs) ∧
      (headerAvailable.push entries.needs).AtomClosed ∧
      (∀ need ∈ row.bodyFootprint.localNeeds, need ∈ entries.needs) ∧
      (⟨entry.rank, entry.input⟩ : Need) ∈ entries.needs ∧
      (∀ selected ∈ entries, selected.owner = entry.owner) ∧
      environmentCost (entries.environment sourceOrdered headerOrdered ownerInitial
        (tail.dependencyEnvironment headerOrdered)) ≤
        max ((((field.dependencyOrigin sourceOrdered).weight + (major.dependencyOrigin sourceOrdered).weight) *
          (1 + environmentCost ownerInitial)) +
          (Closure.close (domain.dependencyOrigin headerOrdered) (tail.dependencyEnvironment headerOrdered)).cost)
          (environmentCost (tail.dependencyEnvironment headerOrdered)) := by
  let needs := row.bodyFootprint.localNeeds ++ [Need.mk entry.rank entry.input]
  have bounded : ∀ need ∈ needs, need.rank ≤ entry.rank := by
    intro need member
    rcases List.mem_append.mp member with member | member
    · have rankEq : entry.rank = n := congrArg Need.rank input
      rw [rankEq]
      exact (row.pack.localNeeds need member).1
    · cases List.mem_singleton.mp member; exact Nat.le_refl _
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade entry.rank).atoms, atom ∈ entry.input.atoms := by
    intro need member atom atomMember
    rcases List.mem_append.mp member with member | member
    · exact needCoverage_cast input (fun a present => row.covered a
        ((row.pack.localNeeds need member).2 a present)) atom atomMember
    · cases List.mem_singleton.mp member
      simpa only [Need.atGrade, dif_pos (Nat.le_refl _), raiseProfile_self] using atomMember
  obtain ⟨entries, coverage, owners⟩ := entry.coverNeeds henv formed needs bounded covered
  have bodyResources := row.pack.available row.outsideAvailable
  refine ⟨entries, tail.group domain sourceOrdered ownerInitial entries,
    tail.group_environment sourceOrdered headerOrdered entries, ⟨row.body⟩, ?_, entries.closed closed,
    (fun need member => coverage need (List.mem_append_left _ member)),
    coverage _ (List.mem_append_right _ (List.mem_singleton_self _)), owners,
    entries.environment_bound sourceOrdered headerOrdered ownerInitial (tail.dependencyEnvironment headerOrdered)⟩
  intro index need member
  cases index with
  | zero => exact coverage need (List.mem_append_left _ (Footprint.mem_localNeeds.mpr member))
  | succ index => exact bodyResources (index + 1) need member

private theorem located_castNode_context
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {first last : EndpointState sourceEnv U source expression assigned}
    (same : first = last) (location : Located root first)
    (initial : ContextDerivation sourceEnv U rootSource) :
    (same ▸ location).contextDerivation initial = location.contextDerivation initial := by
  cases same
  rfl

private theorem OriginalCodeInductionAt.castNode
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {first last : EndpointState sourceEnv U source expression (.sort level)}
    (same : first = last) (location : Located root first)
    {initial : ContextDerivation sourceEnv U rootSource}
    (induction : OriginalCodeInductionAt env registry ordered initial location limit) :
    OriginalCodeInductionAt env registry ordered initial (same ▸ location) limit := by
  cases same
  exact induction

private theorem frame_castContext_environment
    {first last : ContextDerivation sourceEnv U source} (same : first = last)
    (frame : OriginalRichFrame sourceEnv env U registry target first locals σ τ available)
    (ordered : sourceEnv.Ordered) :
    ((same ▸ frame) : OriginalRichFrame sourceEnv env U registry target last locals σ τ available).dependencyEnvironment ordered =
      frame.dependencyEnvironment ordered := by
  cases same
  rfl

private def RichCert.castExpression
    {node : EndpointState sourceEnv U source expression assigned}
    (same : expression = nextExpression)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
    RichCert sourceEnv env U registry target (node.cast same rfl) locals σ relevant profile footprint := by
  cases same
  exact certificate

/-- A rich row retains BOTH declaration children and their actual paths.
The next residual is the original body occurrence, not a reified typing. -/
structure OriginalRichFamilyRowSelection
    (header : OriginalFamilyHeader headerEnv U declaredType)
    (signature : ConstantTelescope declaredType) (count : Nat)
    (cursor : OriginalFamilyPrefix header signature count)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (seed : Subst) (available : Valuation)
    (domainExpression : VExpr) (key : Key n) (result : Profile n) where
  domainLevel : VLevel
  original : EndpointRef headerEnv U (signature.domains.take count).reverse domainExpression (.sort domainLevel)
  domainLocation : Located header.reference (.ref original)
  domainContext : domainLocation.contextDerivation .nil = cursor.location.contextDerivation .nil
  bodyLevel : VLevel
  body : EndpointState headerEnv U (domainExpression :: (signature.domains.take count).reverse)
    (wrapForalls (signature.domains.drop (count + 1)) signature.result) (.sort bodyLevel)
  bodyLocation : Located header.reference body
  bodyContext : bodyLocation.contextDerivation .nil = .cons (cursor.location.contextDerivation .nil) original
  row : RichPiRowCertificate env U registry target locals seed available true (.ref original) body key result

/- Rich row selection is performed by the deferred resolver with the actual
interpreted Pi and admitted request. The selection record below still retains
the exact declaration children and their paths. -/

private def castSourceNode (same : source = nextSource)
    (node : EndpointState sourceEnv U source expression assigned) :
    EndpointState sourceEnv U nextSource expression assigned := same ▸ node

private def castSourceLocation (same : source = nextSource)
    {node : EndpointState sourceEnv U source expression assigned} (location : Located root node) :
    Located root (castSourceNode same node) := by
  cases same
  exact location

private theorem castSourceLocation_context
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (same : source = nextSource)
    {node : EndpointState sourceEnv U source expression assigned} (location : Located root node)
    (initial : ContextDerivation sourceEnv U rootSource) :
    (castSourceLocation same location).contextDerivation initial = same ▸ location.contextDerivation initial := by
  cases same
  rfl

private def castSourceCertificate (same : source = nextSource)
    {node : EndpointState sourceEnv U source expression assigned}
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
    RichCert sourceEnv env U registry target (castSourceNode same node) locals σ relevant profile footprint := by
  cases same
  exact certificate

private def castSourceFrame (same : source = nextSource)
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available) :
    OriginalRichFrame sourceEnv env U registry target (same ▸ context) locals σ τ available := by
  cases same
  exact frame

private theorem castSourceFrame_environment (same : source = nextSource)
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (ordered : sourceEnv.Ordered) :
    (castSourceFrame same frame).dependencyEnvironment ordered = frame.dependencyEnvironment ordered := by
  cases same
  rfl

noncomputable def OriginalRichFamilyRowSelection.next
    {header : OriginalFamilyHeader headerEnv U declaredType}
    {signature : ConstantTelescope declaredType} {cursor : OriginalFamilyPrefix header signature count}
    (selected : OriginalRichFamilyRowSelection header signature count cursor env registry target
      locals seed available domainExpression key result)
    (domainAt : signature.domains[count]? = some domainExpression) :
    OriginalFamilyPrefix header signature (count + 1) :=
  ⟨.sort selected.bodyLevel,
    castSourceNode (signature.prefixContext_cons domainAt).symm selected.body,
    castSourceLocation (signature.prefixContext_cons domainAt).symm selected.bodyLocation⟩

/-- The true dependent successor: the next cursor, frame and certificate all
name the retained original header body. Its grouped slot contains concrete
restricted owner queries, including the full original input. -/
theorem OriginalRichFamilyRowSelection.advance
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {header : OriginalFamilyHeader headerEnv U declaredType}
    {signature : ConstantTelescope declaredType} {cursor : OriginalFamilyPrefix header signature count}
    {key : Key n} {result : Profile n}
    (selected : OriginalRichFamilyRowSelection header signature count cursor env registry target
      locals seed available domainExpression key result)
    (domainAt : signature.domains[count]? = some domainExpression)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (sourceOrdered : sourceEnv.Ordered) (headerOrdered : headerEnv.Ordered)
    (frame : OriginalRichFrame headerEnv env U registry target
      (cursor.location.contextDerivation .nil) locals seed seed available)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) selected.original env registry target
      locals seed available ownerInitial rawCapture key.anchor key.anchor)
    (exactInput : (⟨entry.rank, entry.input⟩ : Need) = ⟨n, key.input⟩)
    (closed : available.AtomClosed) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) selected.original env registry target
        locals seed available ownerInitial rawCapture key.anchor key.anchor,
      ∃ nextFrame : OriginalRichFrame headerEnv env U registry target
        ((selected.next domainAt).location.contextDerivation .nil) (Locals.push locals)
        (seed.cons key.anchor) (seed.cons key.anchor) (available.push entries.needs),
      nextFrame.dependencyEnvironment headerOrdered = entries.environment sourceOrdered headerOrdered
        ownerInitial (frame.dependencyEnvironment headerOrdered) ∧
      Nonempty (RichCert headerEnv env U registry target (selected.next domainAt).node (Locals.push locals)
        (seed.cons key.anchor) true result selected.row.bodyFootprint) ∧
      selected.row.bodyFootprint.Available (available.push entries.needs) ∧
      (available.push entries.needs).AtomClosed ∧
      (⟨n, key.input⟩ : Need) ∈ entries.needs ∧
      (∀ current ∈ entries, current.owner = entry.owner) := by
  obtain ⟨entries, nextFrame, environmentEq, ⟨certificate⟩, resources, nextClosed, coverage, whole, owners, reserve⟩ :=
    selected.row.captureSuccessor henv formed sourceOrdered headerOrdered frame key result entry exactInput closed
  let converted := castSourceFrame (signature.prefixContext_cons domainAt).symm nextFrame
  have nextContext : (selected.next domainAt).location.contextDerivation .nil =
      (signature.prefixContext_cons domainAt).symm ▸
        ContextDerivation.cons (cursor.location.contextDerivation .nil) selected.original := by
    change (castSourceLocation (signature.prefixContext_cons domainAt).symm selected.bodyLocation).contextDerivation .nil = _
    rw [castSourceLocation_context, selected.bodyContext]
  let actualFrame : OriginalRichFrame headerEnv env U registry target
      ((selected.next domainAt).location.contextDerivation .nil) (Locals.push locals)
      (seed.cons key.anchor) (seed.cons key.anchor) (available.push entries.needs) := nextContext.symm ▸ converted
  refine ⟨entries, actualFrame, ?_,
    ⟨castSourceCertificate (signature.prefixContext_cons domainAt).symm certificate⟩,
    resources, nextClosed, ?_, owners⟩
  · exact (frame_castContext_environment nextContext.symm converted headerOrdered).trans
      ((castSourceFrame_environment (signature.prefixContext_cons domainAt).symm nextFrame headerOrdered).trans environmentEq)
  · simpa only [exactInput] using whole

/-- The previous actual Pi transfer supplies the raw codomain path even
when the selected result profile is empty. This is target transport only;
the source result remains the original header body returned by `advance`. -/
theorem OriginalRichFamilyRowSelection.residualRelated
    {header : OriginalFamilyHeader headerEnv U declaredType}
    {signature : ConstantTelescope declaredType} {cursor : OriginalFamilyPrefix header signature count}
    {key : Key n} {result : Profile n}
    (selected : OriginalRichFamilyRowSelection header signature count cursor env registry target
      locals seed available domainExpression key result)
    (domainAt : signature.domains[count]? = some domainExpression)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (previous : TypeRelated env U registry target
      ((VExpr.forallE A B).subst σ)
      ((wrapForalls (signature.domains.drop count) signature.result).subst seed)
      (Profile.pi protoDomain protoBody support [(key, result)]))
    (anchor : key.anchor = argument.subst σ) :
    TypeConversion env U target ((B.inst argument).subst σ)
      ((wrapForalls (signature.domains.drop (count + 1)) signature.result).subst (seed.cons key.anchor)) ∧
    TypeRelated env U registry target ((B.inst argument).subst σ)
      ((wrapForalls (signature.domains.drop (count + 1)) signature.result).subst (seed.cons key.anchor)) result := by
  rw [signature.prefixResidual_cons domainAt] at previous
  have pair := previous.literalPiBody_pair henv hscoped formed (List.mem_singleton_self _) selected.row.anchor
  simpa only [inst_lift_cons, subst_inst, anchor] using pair

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
