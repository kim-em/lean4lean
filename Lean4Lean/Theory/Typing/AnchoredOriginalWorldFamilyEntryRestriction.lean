import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldReplayableGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistoryPreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedFamilyCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySandbox
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCaptureDepth

/-! Restrict the actual captured entry while preserving its owner generation,
raw observer and both original certificates. The only changes to a request
are its finite adapter and actual certificate lowering. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
open private lowerProfile_sortFlags from Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCaptureDepth
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private noncomputable def certificateCast
    {strata : EquationStratification env} {first second : Profile n}
    (same : first = second)
    {query : RichCert sourceEnv env U registry target node locals σ relevant first footprint}
    (annotation : WorldCertProvenance strata query) :
    WorldCertProvenance strata ((congrArg
      (fun profile => RichCert sourceEnv env U registry target node locals σ relevant profile footprint) same).mp query) := by
  cases same
  exact annotation

private theorem certificateCast_worlds
    {strata : EquationStratification env} {first second : Profile n}
    (same : first = second)
    {query : RichCert sourceEnv env U registry target node locals σ relevant first footprint}
    (annotation : WorldCertProvenance strata query) :
    (certificateCast same annotation).worlds = annotation.worlds := by
  cases same
  rfl

theorem RichCert.lower_worlds_depth
    {strata : EquationStratification env} {profile : Profile N}
    (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (annotation : WorldCertProvenance strata query) (n : Nat) (bound : n ≤ N) :
    ∃ output : WorldCertProvenance strata (query.lower n bound),
      output.worlds = annotation.worlds ∧
      ∀ policy, (query.lower n bound).headDepth policy = query.headDepth policy := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact ⟨annotation, rfl, fun _ => rfl⟩
  | succ N ih =>
    by_cases equal : n = N+1
    · subst n
      simp only [RichCert.lower, Nat.recAux]
      rw [dif_pos rfl]
      refine ⟨certificateCast (lowerProfile_self ..).symm annotation, certificateCast_worlds _ _, ?_⟩
      intro policy
      exact RichCert.headDepth_mpr policy rfl rfl (lowerProfile_self ..).symm rfl
        (congrArg (fun p => RichCert sourceEnv env U registry target node locals σ relevant p footprint)
          (lowerProfile_self profile)) query
    · have previous : n ≤ N := by omega
      obtain ⟨output, worlds, depth⟩ := ih query.down (.down annotation) previous
      simp only [RichCert.lower, Nat.recAux]
      rw [dif_neg equal]
      refine ⟨certificateCast (lowerProfile_step previous profile).symm output, (certificateCast_worlds _ _).trans worlds, ?_⟩
      intro policy
      exact (RichCert.headDepth_mpr policy rfl rfl (lowerProfile_step previous profile).symm rfl _
        (query.down.lower n previous)).trans (by simpa only [RichCert.headDepth] using depth policy)

theorem ControlledStoredQuery.lower
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {query : RichCert sourceEnv env U registry target node locals σ relevant (profile : Profile N) footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query)) (n : Nat) (bound : n ≤ N) :
    Nonempty (ControlledStoredQuery controls frontier (.certificate (query.lower n bound))) := by
  obtain ⟨annotation, worlds, depth⟩ := query.lower_worlds_depth ready.annotation n bound
  refine ⟨⟨annotation, ?_, ?_⟩⟩
  · intro control active
    change (query.lower n bound).headDepth _ ≤ _
    rw [depth]
    exact ready.within control active
  · change Sponsored frontier annotation.worlds
    rw [worlds]
    exact ready.sponsored

/-- The same entry owns its scoped generation and controlled raw payloads. -/
structure WorldFamilyEntry
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (P : VEnv → Prop) (common : List VExpr) (ownerRaw commonLeft commonRight : Subst) (caps : CaptureCaps)
    (controls : OriginalWorldControls strata headerEnv)
    (ownerControls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) where
  scope : CappedOwnerScope common ownerRaw commonLeft commonRight caps entry.depth
    (entry.owner.context entry.initialContext)
  generation : WorldGenerated strata P base scope.caps scope.left scope.right scope.graph entry.frame.raw ownerControls
  replayable : generation.Replayable
  ready : generation.Controlled frontier
  compatible : generation.UsesControlPrefix controls.cutoff controls.fuel
  queryReady : ControlledStoredQuery controls frontier (.observation entry.query)
  valueReady : ControlledStoredQuery controls frontier (.certificate entry.answer.value.certificate)
  declaredReady : ControlledStoredQuery controls frontier (.certificate entry.answer.aligned.certificate)
  hereditary : generation.Hereditary frontier

section
variable
    {strata : EquationStratification env}
    {base : OriginalCaptureBase env U registry target}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {controls : OriginalWorldControls strata headerEnv}
    {ownerControls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {entry : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue}

theorem WorldFamilyEntry.storedReady
    (packet : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps controls ownerControls frontier entry)
    (same : ownerControls.HasPrefix controls.cutoff controls.fuel) :
    ∀ query ∈ entry.toRaw.storedQueries, Nonempty (ControlledStoredQuery controls frontier query) := by
  intro query member
  simp only [RichGroupedCaptureEntry.toRaw, RawRichGroupEntry.storedQueries,
    HeaderValueAlignment.storedQueries] at member
  rcases List.mem_append.mp member with member | member
  · obtain ⟨ready⟩ := packet.ready.selectStored (packet.generation.storedQueries_in_retained member)
    exact ⟨ready.recontrol controls same.1 same.2⟩
  · rcases List.mem_cons.mp member with rfl | member
    · exact ⟨packet.queryReady⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨packet.valueReady⟩
    cases List.mem_singleton.mp member
    exact ⟨packet.declaredReady⟩

/-- Actual finite restriction, retaining the exact scoped owner generation. -/
theorem WorldFamilyEntry.forNeedWorlds
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (packet : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps controls ownerControls frontier entry)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {ownerBase : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension ownerBase entry.frame.raw)
    (need : Need) (bounded : need.rank ≤ entry.rank)
    (covered : ∀ atom ∈ (need.atGrade entry.rank).atoms, atom ∈ entry.input.atoms) :
    ∃ selected : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
        headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue,
      (⟨selected.rank, selected.input⟩ : Need) = need ∧ selected.owner = entry.owner ∧
      Nonempty (OriginalFrameExtension ownerBase selected.frame.raw) ∧
      ∃ output : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps controls ownerControls frontier selected,
        output.generation.worlds = packet.generation.worlds ∧
        selected.answer.value.support.sortFlags = entry.answer.value.support.sortFlags := by
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
  let selected := { entry with
    rank := need.rank
    input := need.profile
    queryBound := Nat.le_trans bounded entry.queryBound
    queryAdapter := adapter
    answer := answer }
  obtain ⟨valueReady⟩ := packet.valueReady.lower need.rank bounded
  obtain ⟨declaredReady⟩ := packet.declaredReady.lower need.rank bounded
  exact ⟨selected, rfl, rfl, ⟨extension⟩,
    ⟨packet.scope, packet.generation, packet.replayable, packet.ready, packet.compatible, packet.queryReady, valueReady, declaredReady, packet.hereditary⟩, rfl, lowerProfile_sortFlags bounded _⟩

theorem WorldFamilyEntry.forNeed
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (packet : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps controls ownerControls frontier entry)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {ownerBase : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension ownerBase entry.frame.raw)
    (need : Need) (bounded : need.rank ≤ entry.rank)
    (covered : ∀ atom ∈ (need.atGrade entry.rank).atoms, atom ∈ entry.input.atoms) :
    ∃ selected : RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
        headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue,
      (⟨selected.rank, selected.input⟩ : Need) = need ∧ selected.owner = entry.owner ∧
      Nonempty (OriginalFrameExtension ownerBase selected.frame.raw) ∧
      Nonempty (WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps controls ownerControls frontier selected) := by
  obtain ⟨selected, exactNeed, ownerEq, extension, output, worlds, supports⟩ :=
    packet.forNeedWorlds henv formed extension need bounded covered
  exact ⟨selected, exactNeed, ownerEq, extension, ⟨output⟩⟩

theorem WorldFamilyEntry.coverNeedsWorlds
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (packet : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps controls ownerControls frontier entry)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {ownerBase : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension ownerBase entry.frame.raw)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ entry.rank)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade entry.rank).atoms, atom ∈ entry.input.atoms) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue,
      (∀ need ∈ needs, need ∈ entries.needs) ∧
      (∀ selected ∈ entries, selected.owner = entry.owner) ∧
      (∀ selected ∈ entries, Nonempty (OriginalFrameExtension ownerBase selected.frame.raw)) ∧
      (∀ selected ∈ entries, ∃ output : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps controls ownerControls frontier selected,
        output.generation.worlds = packet.generation.worlds ∧
        selected.answer.value.support.sortFlags = entry.answer.value.support.sortFlags) := by
  induction needs with
  | nil => exact ⟨[], by simp [RichGroupedCapture.needs], by simp, by simp, by simp⟩
  | cons need needs ih =>
    obtain ⟨selected, exactNeed, ownerEq, selectedExtension, selectedPacket, selectedWorlds, selectedSupport⟩ := packet.forNeedWorlds henv formed extension need
      (bounded need List.mem_cons_self) (covered need List.mem_cons_self)
    obtain ⟨entries, coverage, owners, extensions, packets⟩ := ih
      (fun need member => bounded need (List.mem_cons_of_mem _ member))
      (fun need member => covered need (List.mem_cons_of_mem _ member))
    refine ⟨selected :: entries, ?_, ?_, ?_, ?_⟩
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
    · intro chosen member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨selectedPacket, selectedWorlds, selectedSupport⟩
      · exact packets chosen member
theorem WorldFamilyEntry.coverNeeds
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (packet : WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps controls ownerControls frontier entry)
    {baseContext : ContextDerivation sourceEnv U baseSource}
    {ownerBase : RawOriginalRichFrame sourceEnv env U registry target baseContext baseLocals baseLeft baseRight baseAvailable}
    (extension : OriginalFrameExtension ownerBase entry.frame.raw)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ entry.rank)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade entry.rank).atoms, atom ∈ entry.input.atoms) :
    ∃ entries : RichGroupedCapture (field := field) (major := major) domain env registry target
        headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue,
      (∀ need ∈ needs, need ∈ entries.needs) ∧
      (∀ selected ∈ entries, selected.owner = entry.owner) ∧
      (∀ selected ∈ entries, Nonempty (OriginalFrameExtension ownerBase selected.frame.raw)) ∧
      (∀ selected ∈ entries, Nonempty (WorldFamilyEntry (base := base) P common ownerRaw commonLeft commonRight caps controls ownerControls frontier selected)) := by
  obtain ⟨entries, coverage, owners, extensions, packets⟩ :=
    packet.coverNeedsWorlds henv formed extension needs bounded covered
  exact ⟨entries, coverage, owners, extensions, fun selected member =>
    let ⟨output, _, _⟩ := packets selected member
    ⟨output⟩⟩

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
