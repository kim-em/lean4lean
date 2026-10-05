import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyEntryRestriction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameHead

/-! Actual head lookup selects its stored declared-domain certificate and
lowers that same query together with its world annotation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
open private lowerHead from Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameHead
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
variable {strata : EquationStratification env}
  {controls : OriginalWorldControls strata controlSource}
  {frontier : List (World strata.rules.length)}

private theorem lowerHeadControlled
    {right : Subst}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals left true
      (support : Profile n) footprint)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (resources : footprint.Available available) (typed : input.HasType support)
    (related : Related env U registry target x y (A.subst left) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms)
    (member : need ∈ needs) :
    ∃ answer : OriginalRichHeadCode (env := env) (registry := registry) (target := target)
      domain locals (left.cons x) (right.cons y) (available.push needs) need,
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  exact ⟨lowerHead henv formed certificate resources typed related needs bounded covered member,
    ready.lower need.rank (bounded need member)⟩

 theorem RawRichGroupEntries.lookup_controlled
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs)
    (ready : ∀ query ∈ entries.storedQueries, Nonempty (ControlledStoredQuery controls frontier query))
    (member : need ∈ needs) :
    ∃ support footprint,
      ∃ certificate : RichCert headerEnv env U registry target (.ref domain) headerLocals declaredLeft
        true (support : Profile need.rank) footprint,
      footprint.Available headerAvailable ∧ need.profile.HasType support ∧
      Related env U registry target leftValue rightValue (A.subst declaredLeft) need.profile support ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate certificate)) := by
  match entries with
  | .nil => cases member
  | .cons (input := input) entry tail =>
    simp only [RawRichGroupEntries.storedQueries] at ready
    rcases List.mem_append.mp member with member | member
    · have bounded := (captureNeeds_covered input need member).1
      have covered := (captureNeeds_covered input need member).2
      simp only [Need.atGrade, dif_pos bounded] at covered
      have typed := lowerProfile.hasType bounded (typed_subset covered entry.answer.value.typed)
      have related : Related env U registry target (entry.owner.expression.subst entry.ownerLeft)
          (entry.owner.expression.subst entry.ownerRight) (A.subst declaredLeft)
          (raiseProfile _ bounded need.profile) entry.answer.value.support :=
        Related.of_singletons (fun atom hm => (entry.answer.related henv).singleton_of_mem (covered atom hm))
      have lowered := lowerProfile.related bounded henv formed related
      rw [entry.left_eq, entry.right_eq] at lowered
      have stored : .certificate entry.answer.aligned.certificate ∈ entry.storedQueries := by
        cases entry
        simp only [RawRichGroupEntry.storedQueries, HeaderValueAlignment.storedQueries]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      obtain ⟨declaredReady⟩ := ready (.certificate entry.answer.aligned.certificate)
        (List.mem_append_left _ stored)
      exact ⟨_, entry.answer.aligned.footprint, entry.answer.aligned.certificate.lower need.rank bounded,
        entry.answer.aligned.resources, typed, lowered, declaredReady.lower need.rank bounded⟩
    · exact tail.lookup_controlled henv formed
        (fun query member => ready query (List.mem_append_right _ member)) member
termination_by sizeOf entries

private theorem headerHeadControlled
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    {header : EndpointRef sourceEnv U [] he ht}
    {field : EndpointRef capturedEnv U capturedSource fe ft}
    {major : EndpointRef capturedEnv U capturedSource me majorType}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (frame : HeaderBinderFrame header field major env registry target
      (.cons context domain) locals left right available)
    (ready : ∀ query ∈ frame.storedQueries, Nonempty (ControlledStoredQuery controls frontier query))
    (member : need ∈ available 0) :
    ∃ tailLocals, Locals.push tailLocals = locals ∧
      ∃ answer : OriginalRichHeadCode (env := env) (registry := registry) (target := target)
        domain tailLocals left right available need,
        Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  cases frame with
  | bind tail domain location lineage certificate resources typed arguments needs bounded covered =>
    obtain ⟨certificateReady⟩ := ready (.certificate certificate) List.mem_cons_self
    obtain ⟨answer, answerReady⟩ := lowerHeadControlled henv formed certificate certificateReady resources typed arguments needs bounded covered member
    exact ⟨_, rfl, answer, answerReady⟩
  | captured tail =>
    cases tail with
    | skip tail domain location lineage arguments => cases member
    | push tail domain location lineage owner answer arguments needs bounded covered =>
      obtain ⟨certificateReady⟩ := ready (.certificate answer.aligned.certificate) (by
        simp only [HeaderBinderFrame.storedQueries, HeaderRichTail.storedQueries, HeaderValueAlignment.storedQueries]
        exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
      obtain ⟨value, valueReady⟩ := lowerHeadControlled henv formed answer.aligned.certificate certificateReady
        answer.aligned.resources answer.value.typed arguments needs bounded covered member
      exact ⟨_, rfl, value, valueReady⟩

private theorem RawOriginalRichFrame.headCodeControlled
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (frame : RawOriginalRichFrame sourceEnv env U registry target
      (.cons context domain) locals left right available)
    (ready : ∀ query ∈ frame.storedQueries, Nonempty (ControlledStoredQuery controls frontier query))
    (member : need ∈ available 0) :
    ∃ tailLocals, Locals.push tailLocals = locals ∧
      ∃ answer : OriginalRichHeadCode (env := env) (registry := registry) (target := target)
        domain tailLocals left right available need,
        Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  match frame with
  | .reserve inner _ =>
    simp only [RawOriginalRichFrame.storedQueries] at ready
    exact inner.headCodeControlled henv formed ready member
  | .header _ _ headerFrame =>
    simp only [RawOriginalRichFrame.storedQueries] at ready
    exact headerHeadControlled henv formed headerFrame ready member
  | .bind tail domain certificate resources typed arguments needs bounded covered =>
    simp only [RawOriginalRichFrame.storedQueries] at ready
    obtain ⟨certificateReady⟩ := ready (.certificate certificate) List.mem_cons_self
    obtain ⟨answer, answerReady⟩ := lowerHeadControlled henv formed certificate certificateReady resources typed arguments needs bounded covered member
    exact ⟨_, rfl, answer, answerReady⟩
  | .capture tail domain _ _ _ _ _ _ certificate resources typed arguments needs bounded covered =>
    simp only [RawOriginalRichFrame.storedQueries] at ready
    obtain ⟨certificateReady⟩ := ready (.certificate certificate) (List.mem_cons_of_mem _ List.mem_cons_self)
    obtain ⟨answer, answerReady⟩ := lowerHeadControlled henv formed certificate certificateReady resources typed arguments needs bounded covered member
    exact ⟨_, rfl, answer, answerReady⟩
  | .group tail domain ordered initial entries =>
    simp only [RawOriginalRichFrame.storedQueries] at ready
    obtain ⟨support, fp, certificate, resources, typed, related, certificateReady⟩ :=
      entries.lookup_controlled henv formed
        (fun query member => ready query (List.mem_append_left _ member)) member
    exact ⟨_, rfl, ⟨support, fp, certificate, resources, typed, related⟩, certificateReady⟩
  | .merge first second =>
    simp only [RawOriginalRichFrame.storedQueries] at ready
    rcases List.mem_append.mp member with member | member
    · obtain ⟨tailLocals, positions, answer, answerReady⟩ := first.headCodeControlled henv formed
        (fun query member => ready query (List.mem_append_left _ member)) member
      exact ⟨tailLocals, positions, { answer with
        resources := fun i need hm => List.mem_append_left _ (answer.resources i need hm) }, answerReady⟩
    · obtain ⟨tailLocals, positions, answer, answerReady⟩ := second.headCodeControlled henv formed
        (fun query member => ready query (List.mem_append_right _ member)) member
      exact ⟨tailLocals, positions, { answer with
        resources := fun i need hm => List.mem_append_right _ (answer.resources i need hm) }, answerReady⟩
termination_by sizeOf frame
decreasing_by all_goals simp_wf <;> omega

 theorem OriginalRichFrame.headCode_controlled
    {context : ContextDerivation sourceEnv U source}
    {domain : EndpointRef sourceEnv U source A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (frame : OriginalRichFrame sourceEnv env U registry target
      (.cons context domain) locals left right available)
    (ready : ∀ query ∈ frame.raw.storedQueries, Nonempty (ControlledStoredQuery controls frontier query))
    (member : need ∈ available 0) :
    ∃ answer : OriginalRichHeadCode (env := env) (registry := registry) (target := target)
      domain frame.peel.tailLocals left right available need,
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  obtain ⟨tailLocals, positions, answer, answerReady⟩ := frame.raw.headCodeControlled henv formed ready member
  have same : tailLocals = frame.peel.tailLocals :=
    (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp
      (List.cons.inj (positions.trans frame.peel.positions.symm)).2
  cases same
  exact ⟨answer, answerReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
