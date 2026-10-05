import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHeaderFamilyPlan

/-! A dependent two-parameter family plan retains both full requests.  The
second declared-domain certificate uses the same first anchor and the actual
first row's resource table; neither parameter is replaced by an empty demand. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private binderWorld literalSortWorld from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyTerminalEnrichment
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private theorem requestDiagonal
    (admission : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨domain, left, input⟩, support⟩ : DataRequest (Profile n)) left right) :
    RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨domain, left, input⟩, support⟩ : DataRequest (Profile n)) left left :=
  ⟨admission.1, admission.1, admission.2.2.1, admission.2.2.2.1,
    admission.2.2.2.2.1, admission.2.2.2.2.2.1, admission.2.2.2.2.2.1⟩

private theorem requestAdmitted
    (admission : RankedData.RequestAdmission env U (relations env U registry n) target
      (request : DataRequest (Profile n)) left right) :
    Admitted env U registry target request.toKeyData left right :=
  ⟨admission.1, admission.2.1, request.support, admission.2.2.1, admission.2.2.2.1,
    admission.2.2.2.2.1, admission.2.2.2.2.2.1, admission.2.2.2.2.2.2⟩

/-- `firstNeeds` is the retained first-row table, enlarged with the full
first request. Its actual coverage closes every dependency of the second
header domain. Both paired admissions and both support profiles are retained
unchanged in the two terminal requests. -/
theorem twoParameterHeaderPlanWorld
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (World strata.rules.length))
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {firstDomain : EndpointRef headerEnv U [] C (.sort cu)}
    {secondDomain : EndpointRef headerEnv U [C] D (.sort dv)}
    {body : EndpointState headerEnv U [D, C] signature.result (.sort w)}
    {firstBody : EndpointState headerEnv U [C] (.forallE D signature.result) (.sort firstV)}
    (henv : env.Ordered) (hcu : cu.WF U) (hdv : dv.WF U) (hw : w.WF U)
    (firstVWF : firstV.WF U)
    (innerRoute : PrefixRoute headerEnv U [C] (.forallE D signature.result) firstBody
      (.pi hdv hw (.ref secondDomain) body))
    (domains : signature.domains = [C, D])
    (resultSort : signature.result = .sort level) (relevance : Relevant level relevant)
    (firstLocation : Located header (.ref firstDomain))
    (firstLineage : firstLocation.contextDerivation .nil = .nil)
    (secondLocation : Located header (.ref secondDomain))
    (secondLineage : secondLocation.contextDerivation .nil = .cons .nil firstDomain)
    {firstInput firstSupport secondInput secondSupport : Profile n}
    (firstCode : RichCert headerEnv env U registry target (.ref firstDomain) [] realization
      true firstSupport firstFootprint)
    (firstResources : firstFootprint.Available (fun _ => []))
    (firstReady : ControlledStoredQuery controls frontier (.certificate firstCode))
    (firstAdmission : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨C.subst realization, firstLeft, firstInput⟩, firstSupport⟩ : DataRequest (Profile n))
      firstLeft firstRight)
    (firstNeeds : List Need)
    (firstPresent : (⟨n, firstInput⟩ : Need) ∈ firstNeeds)
    (firstBounded : ∀ need ∈ firstNeeds, need.rank ≤ n)
    (firstCovered : ∀ need ∈ firstNeeds, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ firstInput.atoms)
    (secondCode : RichCert headerEnv env U registry target (.ref secondDomain) [0]
      (realization.cons firstLeft) true secondSupport secondFootprint)
    (secondResources : secondFootprint.Available (Valuation.push firstNeeds (fun _ => [])))
    (secondReady : ControlledStoredQuery controls frontier (.certificate secondCode))
    (secondAdmission : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨D.subst (realization.cons firstLeft), secondLeft, secondInput⟩, secondSupport⟩ : DataRequest (Profile n))
      secondLeft secondRight) :
    let firstRequest : DataRequest (Profile n) :=
      ⟨⟨C.subst realization, firstLeft, firstInput⟩, firstSupport⟩
    let secondRequest : DataRequest (Profile n) :=
      ⟨⟨D.subst (realization.cons firstLeft), secondLeft, secondInput⟩, secondSupport⟩
    ∃ plan : RichFamilyPlanResult env U registry target header name levels signature .nil
        (.pi hcu firstVWF (.ref firstDomain) firstBody) realization [] (fun _ => [])
        (n := n+3) (.fn (Key.pad (Key.pad firstRequest.toKeyData))
          (.fn (Key.pad secondRequest.toKeyData)
            (.family ⟨name, levels, relevant, [firstRequest, secondRequest]⟩))),
      Nonempty (plan.WorldControlled controls frontier) := by
  dsimp only
  let firstRequest : DataRequest (Profile n) :=
    ⟨⟨C.subst realization, firstLeft, firstInput⟩, firstSupport⟩
  let secondRequest : DataRequest (Profile n) :=
    ⟨⟨D.subst (realization.cons firstLeft), secondLeft, secondInput⟩, secondSupport⟩
  have firstDiagonal := requestDiagonal firstAdmission
  have secondDiagonal := requestDiagonal secondAdmission
  have firstGuard : LambdaGuard env U registry target realization C firstRequest.toKeyData firstSupport :=
    ⟨firstAdmission.2.2.1, firstAdmission.2.2.2.1, .refl,
      firstAdmission.2.2.2.2.1, requestAdmitted firstDiagonal⟩
  have secondGuard : LambdaGuard env U registry target (realization.cons firstLeft) D
      secondRequest.toKeyData secondSupport :=
    ⟨secondAdmission.2.2.1, secondAdmission.2.2.2.1, .refl,
      secondAdmission.2.2.2.2.1, requestAdmitted secondDiagonal⟩
  let finalSubst := (realization.cons firstLeft).cons secondLeft
  let firstObservation : Obs env U registry target [0, 1] finalSubst (.bvar 1) firstInput [(1, ⟨n, firstInput⟩)] :=
    .var [0, 1] finalSubst 1 firstInput
  let secondObservation : Obs env U registry target [0, 1] finalSubst (.bvar 0) secondInput [(0, ⟨n, secondInput⟩)] :=
    .var [0, 1] finalSubst 0 secondInput
  have firstAlignment : DomainChain env U registry target firstInput
      firstRequest.domain (C.lift.lift.subst finalSubst) := by
    simp only [finalSubst, lift_subst_cons]
    exact .refl _
  have secondAlignment : DomainChain env U registry target secondInput
      secondRequest.domain (D.lift.subst finalSubst) := by
    simp only [finalSubst, lift_subst_cons]
    exact .refl _
  let captures : FamilyCaptures env U registry target [D, C] [0, 1] finalSubst
      [.bvar 1, .bvar 0] [firstRequest, secondRequest]
      [(1, ⟨n, firstInput⟩), (0, ⟨n, secondInput⟩)] :=
    .cons (.succ .zero) firstObservation (.refl _) firstAlignment firstDiagonal
      (.cons .zero secondObservation (.refl _) secondAlignment secondDiagonal .nil)
  let capturesAnnotation : WorldFamilyCapturesProvenance strata captures :=
    .cons (.succ .zero) _ _ _ firstDiagonal _ (.var _ _ _ _)
      (.cons .zero _ _ _ secondDiagonal .nil (.var _ _ _ _) .nil)
  let secondNeeds : List Need := [⟨n, secondInput⟩]
  have capturesAvailable : Footprint.Available [(1, ⟨n, firstInput⟩), (0, ⟨n, secondInput⟩)]
      (Valuation.push secondNeeds (Valuation.push firstNeeds (fun _ => []))) := by
    intro index need member
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      exact firstPresent
    · cases List.mem_singleton.mp member
      exact List.mem_singleton_self _
  have saturated : [firstLeft, secondLeft].length = signature.domains.length := by simp [domains]
  obtain ⟨terminalCode, ⟨terminalCodeReady⟩⟩ := literalSortWorld controls frontier
    (node := body) (locals := [0, 1]) (σ := finalSubst) (n := n+1) resultSort relevance
  let terminal : RichFamilyPlanResult env U registry target header name levels signature
      (.cons (.cons .nil firstDomain) secondDomain) body finalSubst [firstLeft, secondLeft]
      (Valuation.push secondNeeds (Valuation.push firstNeeds (fun _ => [])))
      (n := n+1) (.family ⟨name, levels, relevant, [firstRequest, secondRequest]⟩) := {
    footprint := [(1, ⟨n, firstInput⟩), (0, ⟨n, secondInput⟩)]
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
      simp only [terminal, RichFamilyPlan.headDepth, captures, FamilyCaptures.headDepth,
        firstObservation, secondObservation, Obs.headDepth.eq_def, Nat.max_self]
      exact Nat.zero_le _
    planSponsored := fun _ member => nomatch member
    code := terminalCodeReady }
  have secondBounded : ∀ need ∈ secondNeeds, need.rank ≤ n+1 := by
    intro need member
    cases List.mem_singleton.mp member
    exact Nat.le_succ _
  have secondCovered : ∀ need ∈ secondNeeds, ∀ atom ∈ (need.atGrade (n+1)).atoms,
      atom ∈ (Key.pad secondRequest.toKeyData).input.atoms := by
    intro need member atom present
    cases List.mem_singleton.mp member
    simpa only [Need.atGrade, dif_pos (Nat.le_succ n),
      raiseProfile_step (Nat.le_refl n), raiseProfile_self, Key.pad, secondRequest] using present
  have secondGuardRaised := secondGuard.raise henv (Nat.le_succ n)
  simp only [raiseKey_step (Nat.le_refl n), raiseKey_self,
    raiseProfile_step (Nat.le_refl n), raiseProfile_self] at secondGuardRaised
  let secondPaddedReady : ControlledStoredQuery controls frontier (.certificate secondCode.pad) := {
    annotation := .pad secondReady.annotation
    within := by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using secondReady.within
    sponsored := secondReady.sponsored }
  obtain ⟨inner, ⟨innerReady⟩⟩ := binderWorld controls frontier (header := header) (signature := signature)
    (arguments := [firstLeft]) hdv hw (by simp [domains]) secondLocation secondLineage
    secondCode.pad secondResources secondPaddedReady secondGuardRaised secondNeeds secondBounded secondCovered
    terminal terminalReady
  let restored := inner.restoreRoute innerRoute
  have restoredReady : restored.WorldControlled controls frontier := {
    plan := innerReady.plan
    planWithin := innerReady.planWithin
    planSponsored := innerReady.planSponsored
    code := {
      annotation := .route innerRoute innerReady.code.annotation
      within := by
        simpa only [restored, RichFamilyPlanResult.restoreRoute, StoredOriginalQuery.headDepth,
          RichCert.headDepth] using innerReady.code.within
      sponsored := innerReady.code.sponsored } }
  have firstBoundedHigh : ∀ need ∈ firstNeeds, need.rank ≤ n+2 := by
    intro need member
    exact Nat.le_trans (firstBounded need member) (by omega)
  have firstCoveredHigh : ∀ need ∈ firstNeeds, ∀ atom ∈ (need.atGrade (n+2)).atoms,
      atom ∈ (Key.pad (Key.pad firstRequest.toKeyData)).input.atoms := by
    intro need member atom present
    have covered := firstCovered need member
    have bounded := firstBounded need member
    simp only [Need.atGrade, dif_pos bounded] at covered
    simp only [Need.atGrade, dif_pos (firstBoundedHigh need member)] at present
    have raised := raiseProfile_subset (show n ≤ n+2 by omega) covered
    rw [raiseProfile_trans] at raised
    simpa only [raiseProfile_step (show n ≤ n+1 by omega),
      raiseProfile_step (Nat.le_refl n), raiseProfile_self, Key.pad, firstRequest] using raised atom present
  have firstGuardRaised := (firstGuard.raise henv (Nat.le_succ n)).raise henv (Nat.le_succ (n+1))
  simp only [raiseKey_step (Nat.le_refl _), raiseKey_self,
    raiseProfile_step (Nat.le_refl _), raiseProfile_self] at firstGuardRaised
  let firstPaddedReady : ControlledStoredQuery controls frontier (.certificate firstCode.pad.pad) := {
    annotation := .pad (.pad firstReady.annotation)
    within := by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using firstReady.within
    sponsored := firstReady.sponsored }
  obtain ⟨outer, outerReady⟩ := binderWorld controls frontier (header := header) (signature := signature)
    (arguments := []) hcu firstVWF (by simp [domains]) firstLocation firstLineage
    firstCode.pad.pad firstResources firstPaddedReady firstGuardRaised firstNeeds firstBoundedHigh firstCoveredHigh
    restored restoredReady
  exact ⟨outer, outerReady⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
