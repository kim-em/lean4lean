import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTwoParameterHeaderRequest
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationPack

/-! Rank-independent assembly from the actual intermediate caller comparison.
The first row may wrap the second Pi in arbitrary finite padding. Its SAME
body certificate is lowered before domain extraction; the resulting request
is then raised to the terminal family grade. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private rowAtCast from Lean4Lean.Theory.Typing.AnchoredOriginalWorldTwoParameterHeaderRequest
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private ofCastWorld from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyApplication
open private lower_raised from Lean4Lean.Theory.Typing.AnchoredFamilyArgumentGrades
open private raiseCertificateControlled from Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationPack
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

theorem AmbientBoundedParameterReply.twoParameterHeaderPlanFromReplyWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (controls : OriginalWorldControls strata origin.source)
    (frontier : List (World strata.rules.length))
    (signature : ConstantTelescope (info.type.instL levels))
    (domains : signature.domains = [C, D])
    (resultSort : signature.result = .sort level) (relevance : Relevant level familyRelevant)
    {firstKey : Key N} {firstSupport : Profile N} {secondInput secondSupport : Profile n}
    {innerRows : List (Key n × Profile n)}
    (bodyBound : n+1 ≤ N)
    (incoming : AmbientBoundedParameterReply base caps (.forallE A B)
      (RetainedHeaderUniverse.display origin levelsWF common) commonLeft commonRight
      (Profile.pi firstPrototypeDomain firstPrototypeBody firstSupport
        [(firstKey,
          raiseProfile N bodyBound
            (Profile.pi secondPrototypeDomain secondPrototypeBody secondSupport innerRows))])
      (environmentCost ([] : List Closure)))
    (incomingData : WorldParameterReplyData (P := P) controls .nil frontier incoming)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi firstPrototypeDomain firstPrototypeBody firstSupport
        [(firstKey,
          raiseProfile N bodyBound
            (Profile.pi secondPrototypeDomain secondPrototypeBody secondSupport innerRows))]).HasType (.sort flag))
    (firstAdmission : RankedData.RequestAdmission env U (relations env U registry N) target
      (⟨⟨A, firstKey.anchor, firstKey.input⟩, firstSupport⟩ : DataRequest (Profile N)) firstKey.anchor firstRight)
    (firstAdmitted : Admitted env U registry target firstKey firstKey.anchor firstKey.anchor)
    {bodyBase : OriginalCaptureBase env U registry target}
    {bodyDisplay : OriginalNestedDisplay U bodyCommon bodyExpression bodyAssigned}
    {bodyControls : OriginalWorldControls strata bodyDisplay.sourceEnv}
    {bodyBaseline : WorldEnvironmentProvenance strata U bodyEnvironment}
    (bodyReply : AmbientBoundedParameterReply bodyBase bodyCaps (.forallE E F) bodyDisplay bodyLeft bodyRight
      (Profile.pi secondPrototypeDomain secondPrototypeBody secondSupport innerRows)
      (environmentCost bodyEnvironment))
    (bodyData : WorldParameterReplyData (P := P) bodyControls bodyBaseline frontier bodyReply)
    (bodyDisplayed : bodyExpression.subst bodyLeft = B.inst firstKey.anchor)
    (secondAdmission : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨E, secondLeft, secondInput⟩, secondSupport⟩ : DataRequest (Profile n)) secondLeft secondRight)
    (paid : Sponsored frontier [originalCallWorld controls .expressionReindex
      (.ref (origin.familyHeader levelsWF).reference) .nil])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .expressionReindex
        (.ref (origin.familyHeader levelsWF).reference) .nil])) :
    let firstRequest : DataRequest (Profile N) :=
      ⟨⟨C.subst commonLeft, firstKey.anchor, firstKey.input⟩, firstSupport⟩
    let secondRequest : DataRequest (Profile N) :=
      ⟨⟨D.subst (commonLeft.cons firstKey.anchor), secondLeft, raiseProfile N (Nat.le_trans (Nat.le_succ n) bodyBound) secondInput⟩, raiseProfile N (Nat.le_trans (Nat.le_succ n) bodyBound) secondSupport⟩
    RankedData.RequestAdmission env U (relations env U registry N) target firstRequest firstKey.anchor firstRight ∧
    RankedData.RequestAdmission env U (relations env U registry N) target secondRequest secondLeft secondRight ∧
    ∃ plan : RichFamilyPlanResult env U registry target (origin.familyHeader levelsWF).reference
        name levels signature .nil (.ref (origin.familyHeader levelsWF).reference) commonLeft [] (fun _ => [])
        (n := N+3) (.fn (Key.pad (Key.pad firstRequest.toKeyData))
          (.fn (Key.pad secondRequest.toKeyData)
            (.family ⟨name, levels, familyRelevant, [firstRequest, secondRequest]⟩))),
      Nonempty (plan.WorldControlled controls frontier) := by
  let selected := origin.doublePiSyntax levelsWF signature domains
  let declared := doubleHeaderDomain_eq signature domains
  obtain ⟨firstCode, ⟨firstReady⟩, firstDeclared⟩ := incoming.headerDomainRequestWorld origin levelsWF
    controls frontier declared selected.hcu selected.firstVWF selected.outerRoute incomingData henv hscoped
    formed sorted firstAdmission
  let innerProfile : Profile (n+1) := .pi secondPrototypeDomain secondPrototypeBody secondSupport innerRows
  have whole : TypeRelated env U registry target (.forallE A B)
      (.forallE (C.subst commonLeft)
        ((VExpr.forallE D signature.result).subst commonLeft.lift))
      (Profile.pi firstPrototypeDomain firstPrototypeBody firstSupport [(firstKey, raiseProfile N bodyBound innerProfile)]) := by
    have whole := incoming.related
    change TypeRelated env U registry target (.forallE A B) ((info.type.instL levels).subst commonLeft) _ at whole
    rw [declared] at whole
    exact whole
  have diagonal := (whole.symm henv sorted.wf_value).left_diagonal
  have cost := selected.outerRoute.dependency_cost_le controls.ordered ([] : List Closure)
  simp only [EndpointState.dependencyOrigin_cast] at cost
  have nativeBelow : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental
        (.pi selected.hcu selected.firstVWF (.ref selected.firstDomain) selected.firstBody) .nil)
      (originalCallWorld controls .expressionReindex (.ref (origin.familyHeader levelsWF).reference) .nil) := by
    refine original_child ?_ _ _ _ _ _
    simp only [richSchedule, RichPhase.code]
    omega
  have nativePaid := singletonSponsoredBelow paid nativeBelow
  have nativeFunding : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental
        (.pi selected.hcu selected.firstVWF (.ref selected.firstDomain) selected.firstBody) .nil])
      (frontier ++ [originalCallWorld controls .expressionReindex (.ref (origin.familyHeader levelsWF).reference) .nil]) := by
    have lower := split_call (fun world member => by cases List.mem_singleton.mp member; exact nativeBelow)
    clear firstCode firstReady firstDeclared bank paid incomingData nativePaid bodyData
    induction frontier with
    | nil => exact lower
    | cons sponsor rest ih => exact ih.cons sponsor
  have nativeBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.pi selected.hcu selected.firstVWF (.ref selected.firstDomain) selected.firstBody) .nil]) := by
    intro retained lower
    exact bank retained (lower.trans nativeFunding)
  let prior := incoming.reply.answer.reply
  obtain ⟨footprint, certificate, certificateReady, resources, _⟩ :=
    prior.query.code_controlled henv controls incomingData.query sorted
  obtain ⟨data⟩ := WorldUnaryFrameData.ofGenerated prior.realization.frame
    incomingData.generation incomingData.controlled incomingData.replayable incomingData.compatible incomingData.hereditary
  have capacity : environmentCost (prior.realization.frame.leftDiagonal.dependencyEnvironment controls.ordered) ≤
      environmentCost [] := by
    simpa only [OriginalRichFrame.dependencyEnvironment_leftDiagonal] using incoming.reply.bounded controls.ordered
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      (prior.realization.frame.diagonalWorld controls incomingData.generation.environment).worlds [] := by
    simpa only [OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds, WorldEnvironmentProvenance.worlds] using incomingData.covered
  have extracted := rowAtCast controls frontier declared selected.hcu selected.firstVWF selected.outerRoute
    selected.firstLocation selected.firstLineage selected.bodyLocation selected.bodyLineage henv hscoped
    (origin.sourceBelow.trans below) formed prior.realization.frame.leftDiagonal
    (prior.realization.frame.diagonalWorld controls incomingData.generation.environment) data.leftDiagonal
    capacity covered prior.closed prior.realization.substitutions.left certificate resources certificateReady
    diagonal firstAdmitted nativePaid nativeBank
  have localsEq : prior.locals = [] := prior.locals_eq
  have availableEq : prior.available = (fun _ => []) := incomingData.generation.emptyAvailable
  change ∃ row : RichPiRowCertificate env U registry target prior.locals commonLeft prior.available flag
      (.ref selected.firstDomain) selected.firstBody firstKey (raiseProfile N bodyBound innerProfile),
    Nonempty (row.Controlled controls frontier) at extracted
  rw [localsEq, availableEq] at extracted
  obtain ⟨row, ⟨rowReady⟩⟩ := extracted
  let firstNeeds : List Need :=
    (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons) ++ [⟨N, firstKey.input⟩]
  have firstPresent : (⟨N, firstKey.input⟩ : Need) ∈ firstNeeds := List.mem_append_right _ (List.mem_singleton_self _)
  have firstBounded : ∀ need ∈ firstNeeds, need.rank ≤ N := by
    intro need member
    rcases List.mem_append.mp member with old | full
    · exact (row.pack.atomized_localNeeds need old).1
    · cases List.mem_singleton.mp full
      exact Nat.le_refl _
  have firstCovered : ∀ need ∈ firstNeeds, ∀ atom ∈ (need.atGrade N).atoms, atom ∈ firstKey.input.atoms := by
    intro need member atom present
    rcases List.mem_append.mp member with old | full
    · exact row.covered atom ((row.pack.atomized_localNeeds need old).2 atom present)
    · cases List.mem_singleton.mp full
      simpa only [Need.atGrade, dif_pos (Nat.le_refl N), raiseProfile_self] using present
  have bodyResources : row.bodyFootprint.Available (Valuation.push firstNeeds (fun _ => [])) := by
    have old := row.pack.available_atomized_localNeeds row.outsideAvailable
    intro index need member
    have included := old index need member
    cases index with
    | zero => exact List.mem_append_left _ included
    | succ index => exact included
  obtain ⟨lowerReady⟩ := rowReady.body.lower (n+1) bodyBound
  have lowerExists : ∃ lowerCode : RichCert origin.source env U registry target selected.firstBody [0]
      (commonLeft.cons firstKey.anchor) flag innerProfile row.bodyFootprint,
      Nonempty (ControlledStoredQuery controls frontier (.certificate lowerCode)) := by
    let predicate (profile : Profile (n+1)) : Prop :=
      ∃ lowerCode : RichCert origin.source env U registry target selected.firstBody [0]
          (commonLeft.cons firstKey.anchor) flag profile row.bodyFootprint,
        Nonempty (ControlledStoredQuery controls frontier (.certificate lowerCode))
    exact (congrArg predicate (lower_raised bodyBound innerProfile)).mp
      ⟨row.body.lower (n+1) bodyBound, ⟨lowerReady⟩⟩
  obtain ⟨lowerCode, ⟨lowerCodeReady⟩⟩ := lowerExists
  obtain ⟨secondCode, secondReady, _, _⟩ := lowerCode.piDomain_controlled selected.hdv selected.hw
    selected.innerRoute bodyResources lowerCodeReady
  have bodies := TypeRelated.literalPiBody_pair henv hscoped formed whole (List.mem_singleton_self _) firstAdmitted
  have innerWhole : TypeRelated env U registry target (.forallE E F)
      (.forallE (D.subst (commonLeft.cons firstKey.anchor))
        (signature.result.subst (commonLeft.cons firstKey.anchor).lift)) innerProfile := by
    have bodyCode := bodies.2.lower henv bodyBound
    simp only [lower_raised bodyBound innerProfile] at bodyCode
    have prefixCode := bodyReply.related
    rw [bodyDisplayed] at prefixCode
    have combined := prefixCode.trans henv bodyCode
    rw [inst_lift_cons] at combined
    exact combined
  have secondBridge := TypeRelated.literalPiDomain henv hscoped formed innerWhole
  have secondPath := TypeRelated.literalPiDomainPath henv formed innerWhole
  have secondDeclared : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨D.subst (commonLeft.cons firstKey.anchor), secondLeft, secondInput⟩, secondSupport⟩ : DataRequest (Profile n))
      secondLeft secondRight := by
    obtain ⟨anchor, pair, typed, formation, _domain, first, second⟩ := secondAdmission
    exact ⟨secondPath.cast anchor, secondPath.cast pair, typed, formation,
      (secondBridge.symm henv typed.wf_type).left_diagonal,
      Related.convert henv typed secondBridge first, Related.convert henv typed secondBridge second⟩
  have secondRaised : RankedData.RequestAdmission env U (relations env U registry N) target
      (⟨⟨D.subst (commonLeft.cons firstKey.anchor), secondLeft, raiseProfile N (Nat.le_trans (Nat.le_succ n) bodyBound) secondInput⟩, raiseProfile N (Nat.le_trans (Nat.le_succ n) bodyBound) secondSupport⟩ : DataRequest (Profile N))
      secondLeft secondRight := by
    exact RankedData.RequestAdmission.raiseFamily henv
      (Nat.le_trans (Nat.le_succ n) bodyBound) secondDeclared
  obtain ⟨secondRaisedCode, ⟨secondRaisedReady⟩⟩ := raiseCertificateControlled secondReady
    (Nat.le_trans (Nat.le_succ n) bodyBound)
  obtain ⟨plan, ⟨planReady⟩⟩ := OriginalRecordSource.twoParameterHeaderPlanWorld (name := name) (levels := levels) controls frontier
    henv selected.hcu selected.hdv selected.hw selected.firstVWF selected.innerRoute domains resultSort relevance
    selected.firstLocation selected.firstLineage selected.secondLocation selected.secondLineage
    firstCode.certificate firstCode.resources firstReady firstDeclared firstNeeds firstPresent firstBounded firstCovered
    secondRaisedCode secondCode.resources secondRaisedReady secondRaised
  let restored := plan.restoreRoute selected.outerRoute
  have restoredReady : restored.WorldControlled controls frontier := {
    plan := planReady.plan
    planWithin := planReady.planWithin
    planSponsored := planReady.planSponsored
    code := {
      annotation := .route selected.outerRoute planReady.code.annotation
      within := by simpa only [restored, RichFamilyPlanResult.restoreRoute,
        StoredOriginalQuery.headDepth, RichCert.headDepth] using planReady.code.within
      sponsored := planReady.code.sponsored } }
  let actual : RichFamilyPlanResult env U registry target (origin.familyHeader levelsWF).reference
      name levels signature .nil (.ref (origin.familyHeader levelsWF).reference) commonLeft [] (fun _ => []) _ :=
    { restored with certificate := RichCert.ofCast declared rfl restored.certificate }
  exact ⟨firstDeclared, secondRaised, actual, ⟨{
    plan := restoredReady.plan
    planWithin := restoredReady.planWithin
    planSponsored := restoredReady.planSponsored
    code := ofCastWorld declared rfl restoredReady.code }⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
