import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPairedFamilyRequest

/-! Construct the enriched family plan from the actual freshly chosen
header-domain certificate. Its paired request is an explicit result of the
caller argument and declared-domain calls, not an inferred header alignment. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private binderWorld literalSortWorld from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyTerminalEnrichment
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- The exact full input becomes the terminal parameter capture even when
an independently selected native row did not demand it. The support of that
same request is retained by the original declared-domain code and binder. -/
theorem oneParameterHeaderPlanWorld
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {domain : EndpointRef headerEnv U [] C (.sort cu)}
    {body : EndpointState headerEnv U [C] signature.result (.sort dv)}
    (henv : env.Ordered)
    (hcu : cu.WF U) (hdv : dv.WF U)
    (domains : signature.domains = [C])
    (resultSort : signature.result = .sort level) (relevance : Relevant level relevant)
    (location : Located header (.ref domain))
    (lineage : location.contextDerivation .nil = .nil)
    {input support : Profile n}
    (certificate : RichCert headerEnv env U registry target (.ref domain) [] realization
      true support footprint)
    (resources : footprint.Available (fun _ => []))
    (certificateReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (admission : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨C.subst realization, leftValue, input⟩, support⟩ : DataRequest (Profile n)) leftValue rightValue) :
    let request : DataRequest (Profile n) := ⟨⟨C.subst realization, leftValue, input⟩, support⟩
    ∃ plan : RichFamilyPlanResult env U registry target header name levels signature
        .nil (.pi hcu hdv (.ref domain) body) realization [] (fun _ => [])
        (n := n+2) (.fn (Key.pad request.toKeyData) (.family ⟨name, levels, relevant, [request]⟩)),
      Nonempty (plan.WorldControlled controls frontier) := by
  dsimp only
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
  exact ⟨plan, planReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
