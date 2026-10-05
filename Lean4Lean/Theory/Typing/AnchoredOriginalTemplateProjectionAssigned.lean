import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateProjection
import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionFieldTemplate
import Lean4Lean.Theory.Typing.AnchoredFamilyLiteralArguments
import Lean4Lean.Theory.Typing.AnchoredDataAnchors
import Lean4Lean.Theory.Typing.AnchoredDataIntrinsic
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientArgumentValue
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiReplay

/-! Assigned-family requests of the productive projection interpreter.
The query below is selected from the actual major answer, not supplied as
an arbitrary observation. Its chosen right frame is retained unchanged.

This gate recovers exactly the frozen family argument demands. It does not
assert that an unrelated, richer parameter demand in a field certificate
is covered by those requests. That extra-request producer is a separate
obligation of the sparse field interpreter. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private major_below from_both from
  Lean4Lean.Theory.Typing.AnchoredOriginalProjectionTemplateWorldCalls
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The record request itself selects the actual retained family code at
its major's assigned formation. Its footprint and all policy depths are
unchanged. -/
def RichSupportedValue.recordAssignedQuery
    {record : RecordData (Profile n)}
    (answer : RichSupportedValue sourceEnv env U registry target owner locals σ σ available
      (Profile.singleton (n := n + 1) (.record record))) :
    RichCert sourceEnv env U registry target owner.typeFormation.node locals σ true
      (Profile.singleton (n := n + 1) (.family record.family)) answer.footprint :=
  .select answer.certificate answer.typed.record_family_mem

theorem RichSupportedValue.recordAssignedQuery_headDepth
    {record : RecordData (Profile n)}
    (answer : RichSupportedValue sourceEnv env U registry target owner locals σ σ available
      (Profile.singleton (n := n + 1) (.record record))) (policy : Name → Nat → Nat) :
    answer.recordAssignedQuery.headDepth policy = answer.certificate.headDepth policy := by
  simp only [recordAssignedQuery, RichCert.headDepth]

/-- Literal family heads extract both exact seed packets and the admissions
at the frozen requests. No conversion at arbitrary stronger support follows
from this statement. -/
theorem TypeRelated.templateFamilyArguments
    {family : FamilyData (Profile n)}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (wf : (Profile.singleton (n := n + 1) (.family family)).WF)
    (code : TypeRelated env U registry target
      (mkApps (.const family.name leftLevels) leftArguments)
      (mkApps (.const family.name rightLevels) rightArguments)
      (Profile.singleton (n := n + 1) (.family family))) :
    List.Forall₂ (· ≈ ·) leftLevels rightLevels ∧
    RankedData.Arguments env U (relations env U registry n) target family.arguments
      leftArguments rightArguments := by
  have leftRelation := code.familyRelation (List.mem_singleton_self _)
  have rightRelation := (code.symm henv wf).familyRelation (List.mem_singleton_self _)
  obtain ⟨_, _, _, leftLevelsEq⟩ := leftRelation.literalFormation henv hscoped formed
  obtain ⟨_, _, _, rightLevelsEq⟩ := rightRelation.literalFormation henv hscoped formed
  refine ⟨?_, (leftRelation.literalArguments henv hscoped formed).joinAnchors
    ((rankLaws henv n).lowerEquality henv) hscoped
    (rightRelation.literalArguments henv hscoped formed)⟩
  exact Lean4Lean.List.Forall₂.trans (T := (· ≈ ·)) (fun _ _ _ first second => first.trans second)
    (Lean4Lean.List.Forall₂.imp (fun _ _ equal => equal.symm)
      (Lean4Lean.List.Forall₂.flip leftLevelsEq)) rightLevelsEq

/-- The right frame and actual right family certificate returned by the
proper-major assigned interpreter. This deliberately makes no unsupported
claim that its resources fit the initial destination frame. -/
structure ProjectionAssignedFamilyReply
    (leftHead : ProjectionHead (left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType))
    (rightHead : ProjectionHead (right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightType))
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (rightContext : ContextDerivation rightEnv U rightSource)
    (σ τ : Subst) (family : FamilyData (Profile n)) where
  locals : List Nat
  available : Valuation
  frame : OriginalRichFrame rightEnv env U registry target rightContext locals τ τ available
  code : TemplateCodeResult env U registry target
    (EndpointState.ref (.right leftHead.major)).typeFormation.node
    (EndpointState.ref (.right rightHead.major)).typeFormation.node
    locals σ τ available true (Profile.singleton (n := n + 1) (.family family))

/-- The derived family and source-major bridges retain the actual raw
constructor template and the exact query-selected destination packet. -/
structure ProjectionAssignedFamilyBridge
    (leftHead : ProjectionHead (left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType))
    (rightHead : ProjectionHead (right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightType))
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (rightContext : ContextDerivation rightEnv U rightSource)
    (σ τ : Subst) (family : FamilyData (Profile n)) where
  reply : ProjectionAssignedFamilyReply leftHead rightHead env registry target rightContext σ τ family
  template : SharedProjectionFieldTemplate leftHead rightHead
  universes : List.Forall₂ (· ≈ ·) leftHead.levels rightHead.levels
  arguments : RankedData.Arguments env U (relations env U registry n) target family.arguments
    ((leftHead.parameters ++ leftHead.indices).map (VExpr.subst · σ))
    ((rightHead.parameters ++ rightHead.indices).map (VExpr.subst · τ))
  sourceMajors : env.IsDefEq U target (leftHead.sourceMajor.subst σ) (rightHead.sourceMajor.subst τ)
    ((mkApps (.const name leftHead.levels) (leftHead.parameters ++ leftHead.indices)).subst σ)

/-- Call the productive assigned mode only at the proper major subtemplate.
The incoming code query is computed from the real major answer. The output
contains the SAME selected frame, a raw hidden-major bridge, shared raw
field-template syntax, and the finite frozen parameter admissions. -/
theorem projectionAssignedFamilyStep
    {left : EndpointState leftEnv U leftSource (.proj name index leftValue) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightValue) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (leftBelow : leftEnv ≤ env) (rightBelow : rightEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (leftSubstitutions : Ctx.SubstEq env U target σ σ leftSource)
    (rightSubstitutions : Ctx.SubstEq env U target τ τ rightSource)
    (leftControls : OriginalWorldControls strata leftEnv)
    (rightControls : OriginalWorldControls strata rightEnv)
    {leftContext : ContextDerivation leftEnv U leftSource}
    {rightContext : ContextDerivation rightEnv U rightSource}
    (leftFrame : OriginalRichFrame leftEnv env U registry target leftContext leftLocals σ σ leftAvailable)
    (rightFrame : OriginalRichFrame rightEnv env U registry target rightContext rightLocals τ τ rightAvailable)
    (leftCaptured : WorldEnvironmentProvenance strata U (leftFrame.dependencyEnvironment leftControls.ordered))
    (rightCaptured : WorldEnvironmentProvenance strata U (rightFrame.dependencyEnvironment rightControls.ordered))
    {record : RecordData (Profile n)}
    (nameEq : record.family.name = name)
    (majorAnswer : TemplateComparisonResult env U registry target
      (.ref (.right leftHead.major)) (.ref (.right rightHead.major)) leftLocals rightLocals
      σ τ leftAvailable rightAvailable (Profile.singleton (n := n + 1) (.record record)))
    (majorAssigned : ∀ {footprint},
      RichCert leftEnv env U registry target (EndpointState.ref (.right leftHead.major)).typeFormation.node
        leftLocals σ true (Profile.singleton (n := n + 1) (.family record.family)) footprint →
      footprint.Available leftAvailable →
      CallBelow strata.rules.length
        [originalCallWorld leftControls .assignedComparison (.ref (.right leftHead.major)) leftCaptured,
         originalCallWorld rightControls .assignedComparison (.ref (.right rightHead.major)) rightCaptured]
        [originalCallWorld leftControls .assignedComparison left leftCaptured,
         originalCallWorld rightControls .assignedComparison right rightCaptured] →
      Nonempty (ProjectionAssignedFamilyReply leftHead rightHead env registry target rightContext σ τ record.family)) :
    Nonempty (ProjectionAssignedFamilyBridge leftHead rightHead env registry target rightContext σ τ record.family) := by
  have funding := from_both (major_below leftHead leftControls leftCaptured
      .assignedComparison .assignedComparison)
    (major_below rightHead rightControls rightCaptured .assignedComparison .assignedComparison)
  obtain ⟨reply⟩ := majorAssigned majorAnswer.source.recordAssignedQuery majorAnswer.source.resources funding
  have code : TypeRelated env U registry target
      (mkApps (.const record.family.name leftHead.levels)
        ((leftHead.parameters ++ leftHead.indices).map (VExpr.subst · σ)))
      (mkApps (.const record.family.name rightHead.levels)
        ((rightHead.parameters ++ rightHead.indices).map (VExpr.subst · τ)))
      (Profile.singleton (n := n + 1) (.family record.family)) := by
    simpa only [nameEq, subst_mkApps, subst_const] using reply.code.related
  obtain ⟨universes, arguments⟩ := TypeRelated.templateFamilyArguments henv hscoped formed
    reply.code.certificate.formed.wf_value code
  have leftRaw := (leftHead.major.forget.defeq.mono leftBelow).substDF henv
    leftSubstitutions.wf formed leftSubstitutions
  have rightRaw := (rightHead.major.forget.defeq.mono rightBelow).substDF henv
    rightSubstitutions.wf formed rightSubstitutions
  exact ⟨{
    reply := reply
    template := leftHead.sharedFieldTemplate rightHead leftControls.ordered henv leftBelow rightBelow
    universes := universes
    arguments := arguments
    sourceMajors := (leftRaw.trans majorAnswer.raw).trans (reply.code.path.symm.cast rightRaw.symm) }⟩


section ExtraArgument
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {function : EndpointState sourceEnv U source f (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}
  {ordered : sourceEnv.Ordered}

/-- Add one actual parameter observation to the application's inverse
body requests. The advertised input is their finite union at the maximum
grade. Its domain code comes from the actual original argument F followed
by same-expression formation R, while the body's exact binder pack and
external footprint remain unchanged. -/
theorem ApplicationBackwardQueries.piRequestExtraArgumentAmbient
    {n m : Nat} {profile : Profile n} {extra : Profile m}
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location frame substitutions ordered relevant profile)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (ambient : frame.Ambient)
    (bank : OriginalLowerCallBank env U registry limit)
    (budget : applicationReplayLimit initial domain body function argument result hu hv location frame ordered ≤ limit)
    (supply : RichArgumentSupply sourceEnv env U registry target argument locals σ available packet.footprint.localNeeds)
    (extraQuery : RichObs sourceEnv env U registry target argument locals σ extra extraFootprint)
    (extraResources : extraFootprint.Available available) :
    ∃ output : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile,
      ∃ extraBound : m ≤ output.request.rank,
        ∀ atom ∈ (raiseProfile output.request.rank extraBound extra).atoms,
          atom ∈ output.request.key.input.atoms := by
  obtain ⟨packed⟩ := packet.typedPackAmbient (n := n) henv hscoped formed closed ambient bank budget
  obtain ⟨oldArgument⟩ := binderPackArgumentQuery henv hscoped formed packed.pack supply
  have reserve := application_cost_le_captured (domain.dependencyOrigin ordered) (body.dependencyOrigin ordered)
    (function.dependencyOrigin ordered) (argument.dependencyOrigin ordered) (result.dependencyOrigin ordered)
    (frame.dependencyEnvironment ordered)
  have smaller : (Closure.close (argument.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost <
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin ordered)
        (frame.dependencyEnvironment ordered)).cost :=
    Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) reserve
  have scheduled := Nat.lt_of_lt_of_le (richSchedule_strict smaller .fundamental .fundamental) budget
  obtain ⟨extraValue⟩ := bank.computational ordered ambient.below initial (.appArgument location)
    target locals σ τ available frame ambient scheduled closed formed substitutions extraQuery extraResources
  let diagonal := frame.leftDiagonal
  let base := diagonal.captureBase substitutions.left
  have formationSchedule : richSchedule .expressionReindex
      ((Closure.close (argument.typeFormation.node.dependencyOrigin ordered)
          (diagonal.dependencyEnvironment ordered)).cost +
       (Closure.close (domain.dependencyOrigin ordered) (diagonal.dependencyEnvironment ordered)).cost) < limit := by
    rw [OriginalRichFrame.dependencyEnvironment_leftDiagonal, Nat.add_comm]
    exact Nat.lt_of_lt_of_le (applicationArgumentFormation_schedule (frame := frame)) budget
  obtain ⟨domainReply⟩ := bank.observation base base.initialCaps
    (applicationArgumentFormationDisplay (frame := diagonal) (substitutions := substitutions.left))
    (applicationDomainDisplay (frame := diagonal) (substitutions := substitutions.left))
    σ σ ordered ordered base.identityRealization (.identity ambient.leftDiagonal) closed
    base.identityRealization (.identity ambient.leftDiagonal) closed formationSchedule
    (.code extraValue.certificate) extraValue.resources
  obtain ⟨extraDomainFootprint, ⟨extraDomain⟩, extraDomainResources⟩ :=
    domainReply.answer.freezeBase.code henv extraValue.certificate.formed
  let N := max packed.rank m
  have oldBound : packed.rank ≤ N := Nat.le_max_left _ _
  have extraBound : m ≤ N := Nat.le_max_right _ _
  have outputBound : n ≤ N := Nat.le_trans packed.bound oldBound
  let input := (raiseProfile N oldBound packed.input).union (raiseProfile N extraBound extra)
  let support := (raiseProfile N oldBound packed.support).union (raiseProfile N extraBound extraValue.support)
  have oldTyped := Profile.HasType.raise oldBound packed.typed
  have extraTyped := Profile.HasType.raise extraBound extraValue.typed
  have supportWF := oldTyped.wf_type.union extraTyped.wf_type
  have oldTyped' := oldTyped.enlarge (Profile.le_union_left _ _) supportWF
  have extraTyped' := extraTyped.enlarge (Profile.le_union_right _ _) supportWF
  have typed : input.HasType support := oldTyped'.union extraTyped'
  have code : TypeRelated env U registry target (A.subst σ) (A.subst σ) support := by
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => (packed.code.raise henv oldBound).singleton h)
      (fun h => (extraValue.typeCode.raise henv extraBound).singleton h)
  have related : Related env U registry target (a.subst σ) (a.subst τ) (A.subst σ) input support :=
    (Related.retag henv oldTyped' code (packed.related.raise henv oldBound)).union
      (Related.retag henv extraTyped' code (extraValue.related.raise henv extraBound))
  let domainCertificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true support
      (packed.footprint ++ extraDomainFootprint) :=
    .union (packed.certificate.raise oldBound) (extraDomain.raise extraBound)
  have domainResources : (packed.footprint ++ extraDomainFootprint).Available available :=
    fun i need member => (List.mem_append.mp member).elim
      (packed.resources i need) (extraDomainResources i need)
  let extraArgument : RichGradedResult sourceEnv env U registry target argument locals σ available extra := {
    rank := m, bound := Nat.le_refl _, raw := extra, footprint := extraFootprint,
    observation := extraQuery,
    adapter := by rw [raiseProfile_self]; exact .refl _,
    resources := extraResources, live := extraValue.related.live henv hscoped formed }
  let argumentQuery := (oldArgument.raiseRequest henv hscoped formed oldBound).union henv hscoped formed
    (extraArgument.raiseRequest henv hscoped formed extraBound)
  let key : Key N := ⟨A.subst σ, a.subst σ, input⟩
  have raw := (argument.sound.defeq.mono ambient.below).substDF henv substitutions.wf formed substitutions.left
  have guard : LambdaGuard env U registry target σ A key support :=
    ⟨typed, domainCertificate.formed, .refl, code,
      ⟨raw, raw, support, typed, domainCertificate.formed, code, related.left_diagonal, related.left_diagonal⟩⟩
  have bodyCode : RichCert sourceEnv env U registry target body (Locals.push locals)
      (σ.cons (a.subst σ)) relevant (raiseProfile N outputBound profile) packet.footprint := by
    have positions := packet.reply.answer.reply.locals_eq
    change packet.reply.answer.reply.locals = Locals.push locals at positions
    have realization : (Subst.id.cons (a.subst .id)).comp σ = σ.cons (a.subst σ) := by
      funext i; cases i <;> simp only [Subst.comp, Subst.cons, subst_id] <;> rfl
    simpa only [positions, realization] using packet.certificate.raise outputBound
  let rows : RichRows sourceEnv env U registry target (.ref domain) body locals σ relevant support
      [(key, raiseProfile N outputBound profile)] (packed.outside ++ []) :=
    .cons guard bodyCode (packed.pack.raise oldBound)
      (fun _ member => List.mem_append_left _ member) .nil
  let request : GeneratedApplicationPiRequest domain body hu hv env registry target locals σ available a relevant profile :=
    ⟨N, outputBound, key, support, (packed.footprint ++ extraDomainFootprint) ++ (packed.outside ++ []),
      .pi hu hv domainCertificate PiGuard.literal rows,
      (fun i need member => (List.mem_append.mp member).elim
        (domainResources i need)
        (fun member => packed.external i need (by simpa only [List.append_nil] using member))),
      guard.anchor, rfl⟩
  let output : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile :=
    ⟨request, argumentQuery, _, domainCertificate, domainResources, typed, code⟩
  exact ⟨output, extraBound, fun _ member => List.mem_append_right _ member⟩

end ExtraArgument

/-! The enlarged request is now consumed by the operative history replay.
The returned group therefore stores the actual stronger argument query and
its assigned/domain history; it is not only an isolated Pi certificate. -/
section
variable
  {field : EndpointRef sourceEnv U source fieldExpression fieldType}
  {major : EndpointRef sourceEnv U source majorExpression majorType}
  (initial : ContextDerivation sourceEnv U source)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located major (.app hu hv (.ref domain) body function argument result))
  (sourceGraph : OriginalCaptureMap (common := common) (location.contextDerivation initial) sourceRaw)
  {headerRoot : EndpointRef headerEnv U headerRootSource headerExpression headerType}
  (headerInitial : ContextDerivation headerEnv U headerRootSource)
  (headerDomain : EndpointRef headerEnv U headerSource C (.sort cu))
  (headerBody : EndpointState headerEnv U (C :: headerSource) D (.sort dv))
  (hcu : cu.WF U) (hdv : dv.WF U)
  (headerLocation : Located headerRoot (.pi hcu hdv (.ref headerDomain) headerBody))
  (headerGraph : OriginalCaptureMap (common := common) (headerLocation.contextDerivation headerInitial) headerRaw)

local notation "sourceSide" => originalApplicationTypeRouteSide initial domain body function argument result hu hv location sourceGraph
local notation "headerSide" => originalNativePiRouteSide headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph

theorem OriginalApplyPiHistory.replayApplicationExtraArgumentAmbientStep
    {n : Nat} {profile : Profile n}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight sourceSide headerSide)
    {base : OriginalCaptureBase env U registry target}
    (generated : history.AmbientGenerated base commonCaps)
    (selected : OriginalTypeRouteFrame env registry target sourceGraph commonLeft commonRight)
    (selectedGenerated : AmbientCaptureGenerated base commonCaps commonLeft commonRight sourceGraph selected.realization.frame.raw)
    (selectedBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (selected.realization.frame.dependencyEnvironment ordered) ≤
        environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered))
    (noBinders : location.binderPrefix = [])
    (sourceBound : ∀ ordered : sourceEnv.Ordered,
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (location.dependencyEnvironment ordered ownerInitial))
    (henv : env.Ordered) (hscoped : registry.Scoped) (headerBelow : headerEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (bank : OriginalLowerCallBank env U registry limit)
    (wholeReplay : history.whole.schedule < limit →
      ∀ {queryRank : Nat} {start : VExpr} {queryProfile : Profile queryRank},
        AmbientBoundedParameterReply base commonCaps start (sourceSide).pi.display commonLeft commonRight queryProfile
          (environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)) →
        queryProfile.HasType (.sort true) →
        Nonempty (AmbientBoundedParameterReply base commonCaps start (headerSide).display commonLeft commonRight
          queryProfile (environmentCost history.final)))
    (scheduled : history.schedule < limit)
    (certificate : RichCert sourceEnv env U registry target result selected.locals
      (sourceRaw.comp commonLeft) true (profile : Profile n) footprint)
    (resources : footprint.Available selected.available)
    {extraRank : Nat} {extra : Profile extraRank}
    (extraQuery : RichObs sourceEnv env U registry target argument selected.locals
      (sourceRaw.comp commonLeft) extra extraFootprint)
    (extraResources : extraFootprint.Available selected.available) :
    ∃ answer : AmbientApplyPiReplayResult history field major ownerInitial base commonCaps profile,
      ∃ extraBound : extraRank ≤ answer.packed.request.rank,
        ∀ atom ∈ (raiseProfile answer.packed.request.rank extraBound extra).atoms,
          atom ∈ answer.packed.request.key.input.atoms := by
  have selectedCostBound :
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (selected.realization.frame.dependencyEnvironment history.leftOrdered)).cost ≤
      (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
        (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (selectedBound history.leftOrdered) 1)
  have selectedLimit : applicationReplayLimit initial domain body function argument result hu hv location
      selected.realization.frame history.leftOrdered ≤ limit := by
    have parent : richSchedule .fundamental
        (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
          (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost ≤ history.schedule :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have phase : applicationReplayLimit initial domain body function argument result hu hv location
        selected.realization.frame history.leftOrdered ≤ richSchedule .fundamental
          (Closure.close ((sourceSide).node.dependencyOrigin history.leftOrdered)
            (history.sourceFrame.realization.frame.dependencyEnvironment history.leftOrdered)).cost := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 selectedCostBound) 0
    exact Nat.le_trans phase (Nat.le_of_lt (Nat.lt_of_le_of_lt parent scheduled))
  obtain ⟨packet, ⟨supply⟩⟩ := generatedAmbientApplicationArguments initial domain body function argument result hu hv location
    selected.realization.frame selected.realization.substitutions history.leftOrdered
    henv hscoped formed selected.closed selectedGenerated.ambient.2 bank selectedLimit certificate resources
  obtain ⟨packed, extraBound, extraCovered⟩ := packet.toApplicationBackwardQueries.piRequestExtraArgumentAmbient
    henv hscoped formed selected.closed selectedGenerated.ambient.2 bank selectedLimit supply
    extraQuery extraResources
  obtain ⟨answer, selectedEq, packedEq⟩ := history.replayApplicationPackedAmbientStep (field := field)
    initial domain body function argument result hu hv location sourceGraph
    headerInitial headerDomain headerBody hcu hdv headerLocation headerGraph
    generated selected selectedGenerated selectedBound noBinders sourceBound
    henv hscoped headerBelow formed bank wholeReplay scheduled packed
  refine ⟨answer, ?_⟩
  cases selectedEq
  cases eq_of_heq packedEq
  exact ⟨extraBound, extraCovered⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
