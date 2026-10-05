import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedFamilyTerminalEnrichment
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyEntryRestriction

/-! The rebuilt family descriptor retains the exact controlled declared
certificate selected from the operative capture. Empty value demands do
not erase independently requested assigned-type information. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
open private lowerProfile_sortFlags from Lean4Lean.Theory.Typing.AnchoredOriginalRichGroupedCaptureDepth
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

/-- Both actual trees retain their annotations under the caller's controls. -/
structure RichFamilyPlanResult.WorldControlled
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    (result : RichFamilyPlanResult env U registry target header name levels signature
      context node realization arguments available atom) where
  plan : WorldFamilyPlanProvenance strata result.plan
  planWithin : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
    (fun control => result.plan.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
  planSponsored : Sponsored frontier plan.worlds
  code : ControlledStoredQuery controls frontier (.certificate result.certificate)

/-- Select and lower the very captured certificate whose support is retained
in the request. The annotation follows that same finite lowering. -/
theorem RichGroupedCapture.completeRequestWorld
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
        leftValue leftValue ∧
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
    ⟨raw.hasType.1, raw.hasType.1, typed, (entry.answer.aligned.certificate.lower n bounded).formed,
      code, lowered.left_diagonal, lowered.left_diagonal⟩,
    entry, member, lowerProfile_sortFlags bounded _⟩

private theorem binderWorld
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {context : ContextDerivation headerEnv U source}
    {domain : EndpointRef headerEnv U source A (.sort u)}
    {body : EndpointState headerEnv U (A :: source) B (.sort v)}
    (hu : u.WF U) (hv : v.WF U)
    (domainAt : signature.domains[arguments.length]? = some A)
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (domainCode : RichCert headerEnv env U registry target (.ref domain) (List.range arguments.length)
      σ true (domainSupport : Profile n) domainFootprint)
    (domainAvailable : domainFootprint.Available available)
    (domainReady : ControlledStoredQuery controls frontier (.certificate domainCode))
    (guard : LambdaGuard env U registry target σ A key domainSupport)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
    (child : RichFamilyPlanResult env U registry target header name levels signature (.cons context domain)
      body (σ.cons key.anchor) (arguments ++ [key.anchor]) (available.push needs) (output : Atom n))
    (childReady : child.WorldControlled controls frontier) :
    ∃ result : RichFamilyPlanResult env U registry target header name levels signature context
      (.pi hu hv (.ref domain) body) σ arguments available (n := n + 1) (.fn key output),
      Nonempty (result.WorldControlled controls frontier) := by
  obtain ⟨packed, outside, pack, coverage, outsideAvailable⟩ :=
    Footprint.pack_available child.resources bounded covered
  obtain ⟨typePacked, typeOutside, typePack, typeCoverage, typeOutsideAvailable⟩ :=
    Footprint.pack_available child.typeResources bounded covered
  obtain ⟨bodyCode, ⟨bodyReady⟩⟩ : ∃ bodyCode : RichCert headerEnv env U registry target body
      (Locals.push (List.range arguments.length)) (σ.cons key.anchor) true child.support child.typeFootprint,
      Nonempty (ControlledStoredQuery controls frontier (.certificate bodyCode)) := by
    have localsEq : List.range (arguments ++ [key.anchor]).length =
        Locals.push (List.range arguments.length) := by
      simp only [List.length_append, List.length_singleton, List.range_succ_eq_map, Locals.push]
    rw [← localsEq]
    exact ⟨child.certificate, ⟨childReady.code⟩⟩
  let result : RichFamilyPlanResult env U registry target header name levels signature context
      (.pi hu hv (.ref domain) body) σ arguments available (n := n+1) (.fn key output) := {
    footprint := domainFootprint ++ outside
    plan := .binder domainAt domain location lineage domainCode guard child.plan pack coverage
    resources := fun i need member => (List.mem_append.mp member).elim
      (domainAvailable i need) (outsideAvailable i need)
    support := .pi (A.subst σ) (B.subst σ.lift) domainSupport [(key, child.support)]
    typeFootprint := domainFootprint ++ (typeOutside ++ [])
    certificate := RichCert.pi hu hv domainCode PiGuard.literal (RichRows.cons guard bodyCode typePack typeCoverage .nil)
    typeResources := by
      intro i need member
      simp only [List.append_nil] at member
      exact (List.mem_append.mp member).elim (domainAvailable i need) (typeOutsideAvailable i need)
    typed := by
      apply Profile.HasType.fn _ (List.mem_singleton_self _) child.typed
      refine Profile.WF.pi_iff.mpr ⟨domainCode.formed, ?_⟩
      intro k r member
      cases List.mem_singleton.mp member
      exact ⟨guard.inputTyped, child.typed.wf_type⟩ }
  let planAnnotation : WorldFamilyPlanProvenance strata result.plan :=
    .binder domainAt domain location lineage domainCode guard child.plan pack coverage domainReady.annotation childReady.plan
  have certificateReady : ControlledStoredQuery controls frontier (.certificate result.certificate) := by
    let annotation : WorldCertProvenance strata
        (RichCert.pi hu hv domainCode PiGuard.literal (RichRows.cons guard bodyCode typePack typeCoverage .nil)) :=
      .pi hu hv domainCode PiGuard.literal _ domainReady.annotation
        (.cons guard bodyCode typePack typeCoverage .nil bodyReady.annotation .nil)
    have ready : ControlledStoredQuery controls frontier (.certificate
        (RichCert.pi hu hv domainCode PiGuard.literal (RichRows.cons guard bodyCode typePack typeCoverage .nil))) := {
      annotation := annotation
      within := by
        intro control active
        simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth, RichRows.headDepth, Nat.max_zero]
          using Nat.max_le.mpr ⟨domainReady.within control active, bodyReady.within control active⟩
      sponsored := by
        change Sponsored frontier (domainReady.annotation.worlds ++ (bodyReady.annotation.worlds ++ []))
        rw [List.append_nil]
        exact domainReady.sponsored.merge bodyReady.sponsored }
    exact ready
  exact ⟨result, ⟨{
    plan := planAnnotation
    planWithin := by
      intro control active
      simpa only [result, RichFamilyPlan.headDepth, StoredOriginalQuery.headDepth] using
        Nat.max_le.mpr ⟨domainReady.within control active, childReady.planWithin control active⟩
    planSponsored := domainReady.sponsored.merge childReady.planSponsored
    code := certificateReady }⟩⟩

private theorem literalSortWorld
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    {node : EndpointState sourceEnv U source expression assigned}
    (shape : expression = .sort level) (relevance : Relevant level relevant) :
    ∃ code : RichCert sourceEnv env U registry target node locals σ true
        (Profile.sort (n := n) relevant) [],
      Nonempty (ControlledStoredQuery controls frontier (.certificate code)) := by
  cases shape
  let code : RichCert sourceEnv env U registry target node locals σ true
      (Profile.sort (n := n) relevant) [] := .legacy (.seed (.sort relevance) (.sort relevant))
  exact ⟨code, ⟨{
    annotation := .legacy _ (.seed _ _ (.sort _))
    within := by
      intro control active
      simp only [StoredOriginalQuery.headDepth, code, RichCert.headDepth,
        SortableCert.headDepth, Obs.headDepth.eq_def]
      exact Nat.zero_le _
    sponsored := fun _ member => nomatch member }⟩⟩

/-- The actual enlarged entry builds a native one-parameter terminal and
its Pi certificate under the SAME controls. The selected support is never
replaced by an empty profile, including when the value input is empty. -/
theorem RichGroupedCapture.oneParameterPlanWorld
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
      RankedData.RequestAdmission env U (relations env U registry n) target request leftValue leftValue ∧
      ∃ plan : RichFamilyPlanResult env U registry target header name levels signature
        .nil (.pi hcu hdv (.ref domain) body) realization [] (fun _ => [])
        (n := n+2) (.fn (Key.pad request.toKeyData) (.family ⟨name, levels, relevant, [request]⟩)),
        Nonempty (plan.WorldControlled controls frontier) := by
  obtain ⟨support, footprint, certificate, resources, ⟨certificateReady⟩, admission, retainedSupport⟩ :=
    entries.completeRequestWorld controls frontier henv below formed ready present
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
  exact ⟨request, rfl, rfl, retainedSupport, admission, plan, planReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
