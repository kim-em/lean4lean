import Lean4Lean.Theory.Typing.AnchoredOriginalScopedCaptureGeneration

/-! Concrete finite restriction of a generated original owner preserves its
actual binder-extension trace. The next declaration frame is constructed by
`.group`, rather than inferred from an equal semantic environment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
open private needCoverage_cast from Lean4Lean.Theory.Typing.AnchoredOriginalGenericFamilyDeclaredPrefix
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


theorem RichGroupedCaptureEntry.forNeedGenerated
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base entry.frame.raw)
    (need : Need) (bounded : need.rank ≤ entry.rank)
    (covered : ∀ atom ∈ (need.atGrade entry.rank).atoms, atom ∈ entry.input.atoms) :
    ∃ selected : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue,
      (⟨selected.rank, selected.input⟩ : Need) = need ∧ selected.owner = entry.owner ∧
      Nonempty (OriginalFrameExtension base selected.frame.raw) := by
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
    answer := answer }, rfl, rfl, ⟨extension⟩⟩


theorem RichGroupedCaptureEntry.coverNeedsGenerated
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {base : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension base entry.frame.raw)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ entry.rank)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade entry.rank).atoms, atom ∈ entry.input.atoms) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue,
      (∀ need ∈ needs, need ∈ entries.needs) ∧
      (∀ selected ∈ entries, selected.owner = entry.owner) ∧
      (∀ selected ∈ entries, Nonempty (OriginalFrameExtension base selected.frame.raw)) := by
  induction needs with
  | nil => exact ⟨[], by simp [RichGroupedCapture.needs], by simp, by simp⟩
  | cons need needs ih =>
    obtain ⟨selected, exactNeed, ownerEq, selectedExtension⟩ := entry.forNeedGenerated henv formed extension need
      (bounded need List.mem_cons_self) (covered need List.mem_cons_self)
    obtain ⟨entries, coverage, owners, extensions⟩ := ih
      (fun need member => bounded need (List.mem_cons_of_mem _ member))
      (fun need member => covered need (List.mem_cons_of_mem _ member))
    refine ⟨selected :: entries, ?_, ?_, ?_⟩
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

    · intro chosen member
      rcases List.mem_cons.mp member with rfl | member
      · exact selectedExtension
      · exact extensions chosen member



/-- A complete generated dependent successor. The row's finite needs are
answered by restrictions of its actual owner query. Both captured values
are derived from that owner's original source extension, and the outgoing
frame is the concrete `.group` constructor. -/
theorem RichPiRowCertificate.captureGenerated
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation headerEnv U headerSource}
    {graph : OriginalCaptureMap (common := common) context raw}
    (tail : OriginalRichFrame headerEnv env U registry target context locals σ τ available)
    (generated : ScopedCaptureGenerated base commonLeft commonRight graph tail.raw)
    (domain : EndpointRef headerEnv U headerSource A (.sort u))
    {body : EndpointState headerEnv U (A :: headerSource) B (.sort v)}
    {ownerContext : ContextDerivation sourceEnv U source}
    {ownerGraph : OriginalCaptureMap (common := common) ownerContext ownerRaw}
    (ownerFrame : OriginalRichFrame sourceEnv env U registry target ownerContext ownerLocals ownerLeft ownerRight ownerAvailable)
    (ownerGenerated : ScopedCaptureGenerated base commonLeft commonRight ownerGraph ownerFrame.raw)
    {nominalContext : ContextDerivation nominalEnv U nominalSource}
    (nominalGraph : OriginalCaptureMap (common := common) nominalContext nominalRaw)
    (nominal : EndpointState nominalEnv U nominalSource argument assigned)
    (provenance : EndpointProvenance nominalContext nominal)
    (displayed : rawCapture.subst ownerRaw = argument.subst nominalRaw)
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      locals σ available ownerInitial rawCapture key.anchor rightValue)
    (extension : OriginalFrameExtension ownerFrame.raw entry.frame.raw)
    (input : (⟨entry.rank, entry.input⟩ : Need) = ⟨n, key.input⟩)
    (row : RichPiRowCertificate env U registry target locals σ available relevant
      (.ref domain) body (key : Key n) result)
    (closed : available.AtomClosed) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        locals σ available ownerInitial rawCapture key.anchor rightValue,
      ScopedCaptureGenerated base commonLeft commonRight
        (.capture graph domain nominalGraph nominal provenance)
        ((tail.group domain ordered ownerInitial entries).raw) ∧
      Nonempty (RichCert headerEnv env U registry target body (Locals.push locals)
        (σ.cons key.anchor) relevant result row.bodyFootprint) ∧
      row.bodyFootprint.Available (available.push entries.needs) ∧
      (available.push entries.needs).AtomClosed ∧
      (⟨entry.rank, entry.input⟩ : Need) ∈ entries.needs ∧
      (∀ selected ∈ entries, selected.owner = entry.owner) ∧
      (∀ selected ∈ entries, Nonempty (OriginalFrameExtension ownerFrame.raw selected.frame.raw)) := by
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
  obtain ⟨entries, coverage, owners, extensions⟩ :=
    entry.coverNeedsGenerated henv formed extension needs bounded covered
  have values := entry.extensionRealizations extension
  have bodyResources := row.pack.available row.outsideAvailable
  refine ⟨entries, ?_, ⟨row.body⟩, ?_, entries.closed closed,
    coverage _ (List.mem_append_right _ (List.mem_singleton_self _)), owners, extensions⟩
  · exact ScopedCaptureGenerated.groupOfValues generated domain ownerGenerated nominalGraph nominal
      provenance displayed ordered ownerInitial entries extensions values.2.2.2.1 values.2.2.2.2
  · intro index need member
    cases index with
    | zero => exact coverage need (List.mem_append_left _ (Footprint.mem_localNeeds.mpr member))
    | succ index => exact bodyResources (index + 1) need member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
