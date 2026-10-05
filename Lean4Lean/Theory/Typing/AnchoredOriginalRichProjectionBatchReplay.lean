import Lean4Lean.Theory.Typing.AnchoredOriginalRichProjectionDemandReplay

/-! All discovered projection atoms share one actual prior-slot group. Its
valuation is fixed only after every concrete earlier-slot answer is collected;
individual field calls and code reconstruction then use that shared frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem unionCodes (atoms : List (Atom n))
    (one : ∀ atom ∈ atoms, ∃ fp,
      Nonempty (RichCert sourceEnv env U registry target node locals σ relevant (.singleton atom) fp) ∧
      fp.Available available) :
    ∃ fp, Nonempty (RichCert sourceEnv env U registry target node locals σ relevant (.mk atoms) fp) ∧
      fp.Available available := by
  induction atoms with
  | nil => exact ⟨[], ⟨.legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort relevant)))⟩,
      fun _ _ h => nomatch h⟩
  | cons atom rest ih =>
    obtain ⟨headFP, ⟨head⟩, headResources⟩ := one atom List.mem_cons_self
    obtain ⟨tailFP, ⟨tail⟩, tailResources⟩ := ih (fun a ha => one a (List.mem_cons_of_mem _ ha))
    exact ⟨headFP ++ tailFP, ⟨.union head tail⟩,
      fun i need h => (List.mem_append.mp h).elim (headResources i need) (tailResources i need)⟩

theorem RichProjectionDemands.captureReplay
    {field : EndpointRef sourceEnv U rootSource fieldExpression fieldType}
    {major : EndpointRef sourceEnv U rootSource majorExpression majorType}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
    {location : Located field node} {rawCapture : VExpr}
    (occurrence : OriginalRichOccurrenceFrame location initialContext env registry target locals σ τ available
      ordered initialEnvironment)
    (sourceTail : RichSourceTail location σ τ rootLeft rootRight) (closed : available.AtomClosed)
    (demands : RichProjectionDemands (node := node) (env := env) (registry := registry)
      (target := target) locals σ available (atoms : List (Atom n)))
    {context : ContextDerivation headerEnv U headerSource}
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (headerLocals : List Nat) (declaredLeft : Subst) (headerAvailable : Valuation)
    (expressionEq : value = rawCapture.lift' (.skipN .refl location.binderPrefix.length))
    (batch : CompletedRichCaptureBatch (demands.requests.map (fun request =>
      request.2.priorPending (major := major) occurrence sourceTail closed domain headerLocals declaredLeft headerAvailable expressionEq)))
    (headerOrdered : headerEnv.Ordered)
    (base : OriginalRichFrame headerEnv env U registry target context headerLocals declaredLeft declaredRight headerAvailable)
    {domainX : EndpointRef headerEnv U (A :: headerSource) (.proj name index (.bvar 0)) (.sort xLevel)}
    (rightHead : ProjectionHead (.ref domainX))
    (sorted : (Profile.mk atoms).HasType (.sort relevant)) :
    let nextAvailable := headerAvailable.push batch.entries.needs
    let nextLeft := declaredLeft.cons (rawCapture.subst rootLeft)
    let nextRight := declaredRight.cons (rawCapture.subst rootRight)
    let rightFrame := base.group domain ordered initialEnvironment batch.entries
    (∀ request ∈ demands.requests,
      RichCert sourceEnv env U registry target request.2.origin.head.field locals σ true
        request.2.origin.support request.2.origin.fieldFootprint →
      request.2.origin.fieldFootprint.Available available →
      richSchedule .assignedComparison
        ((Closure.close ((projectionNatural request.2.origin.head).dependencyOrigin ordered)
          (occurrence.frame.dependencyEnvironment ordered)).cost +
         (Closure.close ((projectionNatural rightHead).dependencyOrigin headerOrdered)
          (rightFrame.dependencyEnvironment headerOrdered)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (node.dependencyOrigin ordered) (occurrence.frame.dependencyEnvironment ordered)).cost +
         (Closure.close ((EndpointState.ref domainX).dependencyOrigin headerOrdered)
          (rightFrame.dependencyEnvironment headerOrdered)).cost) →
      Nonempty (RichProjectionAssignedReply request.2.origin.head rightHead env registry target
        (Locals.push headerLocals) σ nextLeft nextAvailable request.2.origin.support)) →
    ∃ frame : OriginalRichFrame headerEnv env U registry target (.cons context domain)
      (Locals.push headerLocals) nextLeft nextRight nextAvailable,
      frame = rightFrame ∧ ∃ footprint,
        Nonempty (RichCert headerEnv env U registry target (.ref domainX) (Locals.push headerLocals)
          nextLeft relevant (.mk atoms) footprint) ∧ footprint.Available nextAvailable := by
  dsimp only
  intro assignedC
  let rightFrame := base.group domain ordered initialEnvironment batch.entries
  have one : ∀ request ∈ demands.requests,
      ∃ fp, Nonempty (RichCert headerEnv env U registry target (.ref domainX) (Locals.push headerLocals)
        (declaredLeft.cons (rawCapture.subst rootLeft)) relevant (.singleton request.1) fp) ∧
        fp.Available (headerAvailable.push batch.entries.needs) := by
    intro request member
    have pendingMember : request.2.priorPending (major := major) occurrence sourceTail closed domain
        headerLocals declaredLeft headerAvailable expressionEq ∈
        demands.requests.map (fun r => r.2.priorPending (major := major) occurrence sourceTail closed
          domain headerLocals declaredLeft headerAvailable expressionEq) := List.mem_map_of_mem member
    have needed : majorNeed request.2.origin.record ∈ batch.entries.needs :=
      batch.needs pendingMember (List.mem_append_left _ (List.mem_singleton_self _))
    have leftBound := request.2.route.dependency_cost_le ordered (occurrence.frame.dependencyEnvironment ordered)
    have rightBound := rightHead.route.dependency_cost_le headerOrdered (rightFrame.dependencyEnvironment headerOrdered)
    have schedule : richSchedule .assignedComparison
        ((Closure.close ((projectionNatural request.2.origin.head).dependencyOrigin ordered)
          (occurrence.frame.dependencyEnvironment ordered)).cost +
         (Closure.close ((projectionNatural rightHead).dependencyOrigin headerOrdered)
          (rightFrame.dependencyEnvironment headerOrdered)).cost) <
      richSchedule .expressionReindex
        ((Closure.close (node.dependencyOrigin ordered) (occurrence.frame.dependencyEnvironment ordered)).cost +
         (Closure.close ((EndpointState.ref domainX).dependencyOrigin headerOrdered)
          (rightFrame.dependencyEnvironment headerOrdered)).cost) := by
      simp only [richSchedule, RichPhase.code, projectionNatural] at *
      omega
    obtain ⟨reply⟩ := assignedC request member request.2.origin.fieldCode request.2.fieldResources schedule
    let majorQuery : RichObs headerEnv env U registry target (.ref (.right rightHead.major))
        (Locals.push headerLocals) (declaredLeft.cons (rawCapture.subst rootLeft))
        (Profile.singleton (n := request.2.origin.rank + 1) (.record request.2.origin.record))
        [(0, majorNeed request.2.origin.record)] := .legacy (.legacy (.var _ _ 0 _))
    have resources : Footprint.Available [(0, majorNeed request.2.origin.record)]
        (headerAvailable.push batch.entries.needs) := by
      intro i need h
      cases List.mem_singleton.mp h
      exact needed
    have memberAtom : request.1 ∈ atoms := by
      rw [← demands.requests_atoms]
      exact List.mem_map_of_mem member
    exact request.2.rebuild rightHead majorQuery resources reply (sorted.singleton_of_mem memberAtom)
  refine ⟨rightFrame, rfl, unionCodes atoms ?_⟩
  intro atom member
  rw [← demands.requests_atoms] at member
  obtain ⟨request, present, rfl⟩ := List.mem_map.mp member
  exact one request present

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
