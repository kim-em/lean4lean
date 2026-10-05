import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderDoublePi
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldTwoParameterHeaderPlan
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHeaderDomainRequest
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFunctionPiBody

/-! Consume one actual nested whole-header reply. The first selected row is
reanchored by genuine lower original calls; its body supplies the exact second
domain support. Both declared requests are derived from the same whole-Pi
relation, at the same first anchor. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private recontextUnary from Lean4Lean.Theory.Typing.AnchoredOriginalWorldFunctionPiBody
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
open private ofCastWorld from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

private theorem rowAtCast
    {strata : EquationStratification env} {P : VEnv → Prop}
    {header : EndpointRef headerEnv U [] expression (.sort headerLevel)}
    {domain : EndpointRef headerEnv U [] C (.sort cu)}
    {body : EndpointState headerEnv U [C] D (.sort dv)}
    (controls : OriginalWorldControls strata headerEnv)
    (frontier : List (World strata.rules.length))
    (declared : expression = .forallE C D) (hcu : cu.WF U) (hdv : dv.WF U)
    (route : PrefixRoute headerEnv U [] (.forallE C D) ((EndpointState.ref header).cast declared rfl)
      (.pi hcu hdv (.ref domain) body))
    (domainLocation : Located header (.ref domain))
    (domainLineage : domainLocation.contextDerivation .nil = .nil)
    (bodyLocation : Located header body)
    (bodyLineage : bodyLocation.contextDerivation .nil = .cons .nil domain)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (frame : OriginalRichFrame headerEnv env U registry target .nil locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost [])
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds [])
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ σ [])
    (certificate : RichCert headerEnv env U registry target (.ref header) locals σ flag
      (Profile.pi prototypeDomain prototypeBody support [(key, result)]) footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (whole : TypeRelated env U registry target
      (.forallE (C.subst σ) (D.subst σ.lift)) (.forallE (C.subst σ) (D.subst σ.lift))
      (Profile.pi prototypeDomain prototypeBody support [(key, result)]))
    (admitted : Admitted env U registry target key key.anchor key.anchor)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental (.pi hcu hdv (.ref domain) body) .nil])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hcu hdv (.ref domain) body) .nil])) :
    ∃ row : RichPiRowCertificate env U registry target locals σ available flag (.ref domain) body key result,
      Nonempty (row.Controlled controls frontier) := by
  obtain ⟨parent, parentWorld, parentEq, parentWorldEq, environmentEq, worldsEq, ⟨parentData⟩⟩ :=
    recontextUnary domainLineage.symm controls frontier frame captured data
  have parentCapacity : environmentCost (parent.dependencyEnvironment controls.ordered) ≤ environmentCost [] := by
    rw [environmentEq]
    exact capacity
  have parentCovered : Covered (@EquationControlMeasure.Less strata.rules.length) parentWorld.worlds [] := by
    rw [worldsEq]
    exact covered
  have bodyContext : bodyLocation.contextDerivation .nil =
      .cons (domainLocation.contextDerivation .nil) domain := by
    rw [domainLineage]
    exact bodyLineage
  cases declared
  exact certificate.piRow_controlled henv hscoped formed closed
    (fun row rowReady admission => row.reanchorWorldAt .nil henv hscoped below controls
      domain domainLocation body bodyLocation bodyContext hcu hdv parent parentWorld .nil
      parentCapacity parentCovered frontier parentData bank paid closed formed substitutions rowReady admission)
    hcu hdv route resources ready (List.mem_singleton_self _) (List.mem_singleton_self _) whole admitted

/-- No row, domain certificate, domain conversion or final family relation
is a premise. The paired argument admissions are the actual application-pack
outputs; the only semantic induction input is the lower header unary bank. -/
theorem AmbientBoundedParameterReply.twoParameterHeaderPlanWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (controls : OriginalWorldControls strata origin.source)
    (frontier : List (World strata.rules.length))
    (signature : ConstantTelescope (info.type.instL levels))
    (domains : signature.domains = [C, D])
    (resultSort : signature.result = .sort level) (relevance : Relevant level familyRelevant)
    {firstKey : Key (n+1)} {firstSupport : Profile (n+1)} {secondInput secondSupport : Profile n}
    {innerRows : List (Key n × Profile n)}
    (incoming : AmbientBoundedParameterReply base caps (.forallE A B)
      (RetainedHeaderUniverse.display origin levelsWF common) commonLeft commonRight
      (Profile.pi firstPrototypeDomain firstPrototypeBody firstSupport
        [(firstKey,
          Profile.pi secondPrototypeDomain secondPrototypeBody secondSupport innerRows)])
      (environmentCost ([] : List Closure)))
    (incomingData : WorldParameterReplyData (P := P) controls .nil frontier incoming)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi firstPrototypeDomain firstPrototypeBody firstSupport
        [(firstKey,
          Profile.pi secondPrototypeDomain secondPrototypeBody secondSupport innerRows)]).HasType (.sort true))
    (firstAdmission : RankedData.RequestAdmission env U (relations env U registry (n+1)) target
      (⟨⟨A, firstKey.anchor, firstKey.input⟩, firstSupport⟩ : DataRequest (Profile (n+1))) firstKey.anchor firstRight)
    (firstAdmitted : Admitted env U registry target firstKey firstKey.anchor firstKey.anchor)
    (bodyShape : B.inst firstKey.anchor = .forallE E F)
    (secondAdmission : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨E, secondLeft, secondInput⟩, secondSupport⟩ : DataRequest (Profile n)) secondLeft secondRight)
    (paid : Sponsored frontier [originalCallWorld controls .expressionReindex
      (.ref (origin.familyHeader levelsWF).reference) .nil])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .expressionReindex
        (.ref (origin.familyHeader levelsWF).reference) .nil])) :
    let firstRequest : DataRequest (Profile (n+1)) :=
      ⟨⟨C.subst commonLeft, firstKey.anchor, firstKey.input⟩, firstSupport⟩
    let secondRequest : DataRequest (Profile (n+1)) :=
      ⟨⟨D.subst (commonLeft.cons firstKey.anchor), secondLeft, secondInput.pad⟩, secondSupport.pad⟩
    RankedData.RequestAdmission env U (relations env U registry (n+1)) target firstRequest firstKey.anchor firstRight ∧
    RankedData.RequestAdmission env U (relations env U registry (n+1)) target secondRequest secondLeft secondRight ∧
    ∃ plan : RichFamilyPlanResult env U registry target (origin.familyHeader levelsWF).reference
        name levels signature .nil (.ref (origin.familyHeader levelsWF).reference) commonLeft [] (fun _ => [])
        (n := n+4) (.fn (Key.pad (Key.pad firstRequest.toKeyData))
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
      (Profile.pi firstPrototypeDomain firstPrototypeBody firstSupport [(firstKey, innerProfile)]) := by
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
    clear firstCode firstReady firstDeclared bank paid incomingData nativePaid
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
  change ∃ row : RichPiRowCertificate env U registry target prior.locals commonLeft prior.available true
      (.ref selected.firstDomain) selected.firstBody firstKey innerProfile,
    Nonempty (row.Controlled controls frontier) at extracted
  rw [localsEq, availableEq] at extracted
  obtain ⟨row, ⟨rowReady⟩⟩ := extracted
  let firstNeeds : List Need :=
    (row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons) ++ [⟨n+1, firstKey.input⟩]
  have firstPresent : (⟨n+1, firstKey.input⟩ : Need) ∈ firstNeeds := List.mem_append_right _ (List.mem_singleton_self _)
  have firstBounded : ∀ need ∈ firstNeeds, need.rank ≤ n+1 := by
    intro need member
    rcases List.mem_append.mp member with old | full
    · exact (row.pack.atomized_localNeeds need old).1
    · cases List.mem_singleton.mp full
      exact Nat.le_refl _
  have firstCovered : ∀ need ∈ firstNeeds, ∀ atom ∈ (need.atGrade (n+1)).atoms, atom ∈ firstKey.input.atoms := by
    intro need member atom present
    rcases List.mem_append.mp member with old | full
    · exact row.covered atom ((row.pack.atomized_localNeeds need old).2 atom present)
    · cases List.mem_singleton.mp full
      simpa only [Need.atGrade, dif_pos (Nat.le_refl (n+1)), raiseProfile_self] using present
  have bodyResources : row.bodyFootprint.Available (Valuation.push firstNeeds (fun _ => [])) := by
    have old := row.pack.available_atomized_localNeeds row.outsideAvailable
    intro index need member
    have included := old index need member
    cases index with
    | zero => exact List.mem_append_left _ included
    | succ index => exact included
  obtain ⟨secondCode, secondReady, _, _⟩ := row.body.piDomain_controlled selected.hdv selected.hw
    selected.innerRoute bodyResources rowReady.body
  have bodies := TypeRelated.literalPiBody_pair henv hscoped formed whole (List.mem_singleton_self _) firstAdmitted
  have innerWhole : TypeRelated env U registry target (.forallE E F)
      (.forallE (D.subst (commonLeft.cons firstKey.anchor))
        (signature.result.subst (commonLeft.cons firstKey.anchor).lift)) innerProfile := by
    have code := bodies.2
    rw [bodyShape, inst_lift_cons] at code
    exact code
  have secondBridge := TypeRelated.literalPiDomain henv hscoped formed innerWhole
  have secondPath := TypeRelated.literalPiDomainPath henv formed innerWhole
  have secondDeclared : RankedData.RequestAdmission env U (relations env U registry n) target
      (⟨⟨D.subst (commonLeft.cons firstKey.anchor), secondLeft, secondInput⟩, secondSupport⟩ : DataRequest (Profile n))
      secondLeft secondRight := by
    obtain ⟨anchor, pair, typed, formation, _domain, first, second⟩ := secondAdmission
    exact ⟨secondPath.cast anchor, secondPath.cast pair, typed, formation,
      (secondBridge.symm henv typed.wf_type).left_diagonal,
      Related.convert henv typed secondBridge first, Related.convert henv typed secondBridge second⟩
  have secondRaised : RankedData.RequestAdmission env U (relations env U registry (n+1)) target
      (⟨⟨D.subst (commonLeft.cons firstKey.anchor), secondLeft, secondInput.pad⟩, secondSupport.pad⟩ : DataRequest (Profile (n+1)))
      secondLeft secondRight := by
    simpa only [raiseDataRequest, raiseKey_step (Nat.le_refl n), raiseKey_self,
      raiseProfile_step (Nat.le_refl n), raiseProfile_self, Key.pad] using
      (RankedData.RequestAdmission.raiseFamily henv (Nat.le_succ n) secondDeclared)
  have secondPaddedReady : ControlledStoredQuery controls frontier (.certificate secondCode.certificate.pad) := {
    annotation := .pad secondReady.annotation
    within := by simpa only [StoredOriginalQuery.headDepth, RichCert.headDepth] using secondReady.within
    sponsored := secondReady.sponsored }
  obtain ⟨plan, ⟨planReady⟩⟩ := OriginalRecordSource.twoParameterHeaderPlanWorld (name := name) (levels := levels) controls frontier
    henv selected.hcu selected.hdv selected.hw selected.firstVWF selected.innerRoute domains resultSort relevance
    selected.firstLocation selected.firstLineage selected.secondLocation selected.secondLineage
    firstCode.certificate firstCode.resources firstReady firstDeclared firstNeeds firstPresent firstBounded firstCovered
    secondCode.certificate.pad secondCode.resources secondPaddedReady secondRaised
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
