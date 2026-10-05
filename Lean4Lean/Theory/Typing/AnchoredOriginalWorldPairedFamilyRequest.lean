import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyApplication

/-! The request extracted from an actual captured history retains its paired
argument relation. The selected certificate, support flags, and world control
are those of the same stored entry; no field comparison is assumed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
open private lowerProfile_sortFlags from Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCaptureDepth
open private binderWorld literalSortWorld from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyTerminalEnrichment
open private oneDomain_eq from Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyTerminalEnrichment
open private ofCastWorld from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem RichGroupedCapture.completePairedRequestWorld
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    {domain : EndpointRef headerEnv U headerSource C (.sort cu)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (ready : ∀ entry ∈ entries, Nonempty (ControlledStoredQuery controls frontier
      (.certificate entry.answer.aligned.certificate)))
    (present : (⟨n, input⟩ : Need) ∈ entries.needs) :
    ∃ support footprint,
      ∃ certificate : RichCert headerEnv env U registry target (.ref domain)
        headerLocals declaredLeft true (support : Profile n) footprint,
      footprint.Available headerAvailable ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate certificate)) ∧
      RankedData.RequestAdmission env U (relations env U registry n) target
        (⟨⟨C.subst declaredLeft, leftValue, input⟩, support⟩ : DataRequest (Profile n))
        leftValue rightValue ∧
      ∃ entry ∈ entries, support.sortFlags = entry.answer.value.support.sortFlags := by
  obtain ⟨entry, member, needMember⟩ := List.mem_flatMap.mp present
  have bounded := (captureNeeds_covered entry.input (⟨n, input⟩ : Need) needMember).1
  have covered := (captureNeeds_covered entry.input (⟨n, input⟩ : Need) needMember).2
  simp only [Need.atGrade, dif_pos bounded] at covered
  have typed := lowerProfile.hasType bounded (typed_subset covered entry.answer.value.typed)
  have related : Related env U registry target (entry.owner.expression.subst entry.ownerLeft)
      (entry.owner.expression.subst entry.ownerRight) (C.subst declaredLeft)
      (raiseProfile entry.rank bounded input) entry.answer.value.support :=
    Related.of_singletons (fun atom hm => (entry.answer.related henv).singleton_of_mem (covered atom hm))
  have lowered := lowerProfile.related bounded henv formed related
  rw [entry.left_eq, entry.right_eq] at lowered
  have code := ((entry.answer.aligned.related.symm henv
    entry.answer.value.typed.wf_type).left_diagonal).lower henv bounded
  have raw := entry.answer.path.cast
    ((entry.owner.node.sound.defeq.mono below).substDF henv entry.substitutions.wf formed entry.substitutions)
  rw [entry.left_eq, entry.right_eq] at raw
  obtain ⟨entryReady⟩ := ready entry member
  obtain ⟨lowerReady⟩ := entryReady.lower n bounded
  exact ⟨_, _, entry.answer.aligned.certificate.lower n bounded,
    entry.answer.aligned.resources, ⟨lowerReady⟩,
    ⟨raw.hasType.1, raw, typed, (entry.answer.aligned.certificate.lower n bounded).formed,
      code, lowered.left_diagonal, lowered⟩,
    entry, member, lowerProfile_sortFlags bounded _⟩

/-- Build the enriched header plan while retaining the actual paired request.
The plan uses the left anchor; its returned admission also reaches the right
argument of the same selected history entry. -/
theorem RichGroupedCapture.oneParameterPairedPlanWorld
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {domain : EndpointRef headerEnv U [] C (.sort cu)}
    {body : EndpointState headerEnv U [C] signature.result (.sort dv)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (hcu : cu.WF U) (hdv : dv.WF U)
    (domains : signature.domains = [C])
    (resultSort : signature.result = .sort level) (relevance : Relevant level relevant)
    (location : Located header (.ref domain))
    (lineage : location.contextDerivation .nil = .nil)
    (entries : RichGroupedCapture (field := field) (major := major) domain env registry target
      [] realization (fun _ => []) ownerInitial rawCapture leftValue rightValue)
    (ready : ∀ entry ∈ entries, Nonempty (ControlledStoredQuery controls frontier
      (.certificate entry.answer.aligned.certificate)))
    (present : (⟨n, input⟩ : Need) ∈ entries.needs) :
    ∃ request : DataRequest (Profile n),
      request.input = input ∧ request.anchor = leftValue ∧
      (∃ entry ∈ entries, request.support.sortFlags = entry.answer.value.support.sortFlags) ∧
      RankedData.RequestAdmission env U (relations env U registry n) target request leftValue rightValue ∧
      ∃ plan : RichFamilyPlanResult env U registry target header name levels signature
        .nil (.pi hcu hdv (.ref domain) body) realization [] (fun _ => [])
        (n := n+2) (.fn (Key.pad request.toKeyData) (.family ⟨name, levels, relevant, [request]⟩)),
        Nonempty (plan.WorldControlled controls frontier) := by
  obtain ⟨support, footprint, certificate, resources, ⟨certificateReady⟩, admission, retainedSupport⟩ :=
    entries.completePairedRequestWorld controls frontier henv below formed ready present
  have pairedAdmission := admission
  have admission : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨C.subst realization, leftValue, input⟩, support⟩ : DataRequest (Profile n))
      leftValue leftValue :=
    ⟨admission.1, admission.1, admission.2.2.1, admission.2.2.2.1,
      admission.2.2.2.2.1, admission.2.2.2.2.2.1, admission.2.2.2.2.2.1⟩
  let request : DataRequest (Profile n) := ⟨⟨C.subst realization, leftValue, input⟩, support⟩
  have anchor : Admitted env U registry target request.toKeyData leftValue leftValue :=
    ⟨admission.1, admission.2.1, support, admission.2.2.1, admission.2.2.2.1,
      admission.2.2.2.2.1, admission.2.2.2.2.2.1, admission.2.2.2.2.2.2⟩
  have guard : LambdaGuard env U registry target realization C request.toKeyData support :=
    ⟨admission.2.2.1, admission.2.2.2.1, .refl, admission.2.2.2.2.1, anchor⟩
  let needs : List Need := [⟨n, input⟩]
  let captures : FamilyCaptures env U registry target [C] [0]
      (realization.cons leftValue) [.bvar 0] [request] [(0, ⟨n, input⟩)] :=
    .cons .zero (.var [0] (realization.cons leftValue) 0 input) (.refl _)
      (by simpa only [lift_subst_cons] using
        (DomainChain.refl (env := env) (U := U) (registry := registry) (Γ := target) (input := input) (C.subst realization)))
      admission .nil
  let capturesAnnotation : WorldFamilyCapturesProvenance strata captures :=
    .cons .zero _ _ _ admission .nil (.var _ _ _ _) .nil
  have capturesAvailable : Footprint.Available [(0, ⟨n, input⟩)]
      (Valuation.push needs (fun _ => [])) := by
    intro i need member
    cases List.mem_singleton.mp member
    exact List.mem_singleton_self _
  have saturated : [leftValue].length = signature.domains.length := by
    simp only [List.length_singleton, domains]
  obtain ⟨terminalCode, ⟨terminalCodeReady⟩⟩ := literalSortWorld controls frontier
    (node := body) (locals := [0]) (σ := realization.cons leftValue) (n := n+1) resultSort relevance
  let terminal : RichFamilyPlanResult env U registry target header name levels signature
      (ContextDerivation.cons .nil domain) body (realization.cons leftValue) [leftValue]
      (Valuation.push needs (fun _ => [])) (n := n+1) (.family ⟨name, levels, relevant, [request]⟩) := {
    footprint := [(0, ⟨n, input⟩)]
    plan := .terminal saturated resultSort relevance captures
    resources := capturesAvailable
    support := .sort relevant
    typeFootprint := []
    certificate := terminalCode
    typeResources := fun _ _ member => nomatch member
    typed := captures.familyTyped relevant }
  let terminalReady : terminal.WorldControlled controls frontier := {
    plan := .terminal saturated resultSort relevance captures capturesAnnotation
    planWithin := by
      intro control active
      simp only [terminal, RichFamilyPlan.headDepth, captures, FamilyCaptures.headDepth, Obs.headDepth.eq_def, Nat.max_self]
      exact Nat.zero_le _
    planSponsored := fun _ member => nomatch member
    code := terminalCodeReady }
  have bounded : ∀ need ∈ needs, need.rank ≤ n+1 := by
    intro need member
    cases List.mem_singleton.mp member
    exact Nat.le_succ _
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade (n+1)).atoms,
      atom ∈ (Key.pad request.toKeyData).input.atoms := by
    intro need member atom atomMember
    cases List.mem_singleton.mp member
    simpa only [Need.atGrade, dif_pos (Nat.le_succ n),
      raiseProfile_step (Nat.le_refl n), raiseProfile_self, Key.pad, request] using atomMember
  have raisedGuard := guard.raise henv (Nat.le_succ n)
  simp only [raiseKey_step (Nat.le_refl n), raiseKey_self,
    raiseProfile_step (Nat.le_refl n), raiseProfile_self] at raisedGuard
  let paddedReady : ControlledStoredQuery controls frontier (.certificate certificate.pad) := {
    annotation := .pad certificateReady.annotation
    within := by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using certificateReady.within
    sponsored := certificateReady.sponsored }
  obtain ⟨plan, planReady⟩ := binderWorld controls frontier (header := header) (signature := signature)
    (arguments := []) hcu hdv (by simp only [List.length_nil, domains, List.getElem?_cons_zero])
    location lineage certificate.pad resources paddedReady raisedGuard needs bounded covered terminal terminalReady
  exact ⟨request, rfl, rfl, retainedSupport, pairedAdmission, plan, planReady⟩

/-- Restore the selected enriched one-domain plan to its actual original
header. This changes only the finite prefix and its endpoint cast; the exact
header controls and recursive query annotations are preserved. -/
theorem RichFamilyPlanResult.restoreSingleHeaderControlled
    {strata : EquationStratification env}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {domain : EndpointRef headerEnv U [] C (.sort cu)}
    {body : EndpointState headerEnv U [C] signature.result (.sort dv)}
    {hcu : cu.WF U} {hdv : dv.WF U}
    (domains : signature.domains = [C])
    (route : PrefixRoute headerEnv U [] (.forallE C signature.result)
      ((EndpointState.ref header).cast (oneDomain_eq signature domains) rfl)
      (.pi hcu hdv (.ref domain) body))
    (plan : RichFamilyPlanResult env U registry target header name levels signature
      .nil (.pi hcu hdv (.ref domain) body) realization [] (fun _ => []) atom)
    (ready : plan.WorldControlled controls frontier) :
    ∃ actual : RichFamilyPlanResult env U registry target header name levels signature
        .nil (.ref header) realization [] (fun _ => []) atom,
      Nonempty (actual.WorldControlled controls frontier) := by
  let original := plan.restoreRoute route
  let restored : original.WorldControlled controls frontier := {
    plan := ready.plan
    planWithin := ready.planWithin
    planSponsored := ready.planSponsored
    code := {
      annotation := .route route ready.code.annotation
      within := by simpa only [original, RichFamilyPlanResult.restoreRoute,
        StoredOriginalQuery.headDepth, RichCert.headDepth] using ready.code.within
      sponsored := ready.code.sponsored } }
  let actual : RichFamilyPlanResult env U registry target header name levels signature
      .nil (.ref header) realization [] (fun _ => []) atom :=
    { original with certificate := RichCert.ofCast (oneDomain_eq signature domains) rfl original.certificate }
  exact ⟨actual, ⟨⟨restored.plan, restored.planWithin, restored.planSponsored,
    ofCastWorld (oneDomain_eq signature domains) rfl restored.code⟩⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
