import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalDeltaBodyReanchor
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericApplicationStep
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedApplicationBody
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedArgumentPack

/-! Assigned application comparison uses a real whole-Pi row, including for
an empty requested result. The two actual applications may have independently
assigned domains and codomains. Raw body conversion comes from the Pi witness,
not injectivity of arbitrary type conversion. -/
namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

/-- The raw body path is present independently of the selected output atoms.
The paired substitution uses the actual argument equality at the left domain. -/
theorem TypeRelated.literalPiRowPathFromBinder
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (whole : TypeRelated env U registry target (.forallE A B) (.forallE C D)
      (Profile.pi prototypeDomain prototypeBody ambient rows))
    (raw : env.IsDefEq U target x y A) :
    TypeConversion env U target (B.inst x) (D.inst y) := by
  have base := whole target .refl (.refl formed)
  simp only [lift'_refl, Profile.rename_refl] at base
  obtain ⟨witness⟩ := base (.pi prototypeDomain prototypeBody ambient rows)
    (List.mem_singleton_self _)
  have insertion := witness.leftExposure.insertion henv
  have hTarget := witness.leftExposure.targetWF henv
  have raw' := insertion.eq henv raw
  rw [← witness.leftExposure.literalPi_components.1] at raw'
  obtain ⟨level, domainTyped⟩ := witness.leftDomainType
  have substitutions : Ctx.SubstEq env U witness.context
      (Subst.id.cons (x.lift' witness.map)) (Subst.id.cons (y.lift' witness.map))
      (witness.leftDomain :: witness.context) := by
    refine .cons (Ctx.SubstEq.id henv hTarget) domainTyped ?_
    simpa only [Subst.cons_tail, Subst.head, Subst.cons, subst_id] using raw'
  obtain ⟨bodyLevel, bodyTyped⟩ := witness.leftBodyType
  have changed := bodyTyped.substDF henv substitutions.wf hTarget substitutions
  have path := (TypeConversion.single (by simpa only [subst_sort] using changed)).trans
    (witness.bodies.substTarget henv hTarget (substitutions.right henv hTarget))
  apply insertion.pathBack henv
  simpa only [← inst_eq, witness.leftExposure.literalPi_components.2,
    witness.rightExposure.literalPi_components.2, lift'_inst_hi] using path

end Lean4Lean.AnchoredSemantics

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

section RightResult
variable
  {root : EndpointRef rightEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation rightEnv U rootSource)
  (domain : EndpointRef rightEnv U source C (.sort u))
  (body : EndpointState rightEnv U (C :: source) E (.sort v))
  (function : EndpointState rightEnv U source g (.forallE C E))
  (argument : EndpointState rightEnv U source b C)
  (result : EndpointState rightEnv U source (E.inst b) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (frame : OriginalRichFrame rightEnv env U registry target
    (location.contextDerivation initial) locals τ τ available)
  (substitutions : Ctx.SubstEq env U target τ τ source)
  (ordered : rightEnv.Ordered)
local notation "appNode" => EndpointState.app hu hv (.ref domain) body function argument result
local notation "cost" => (Closure.close ((appNode).dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost
local notation "base" => frame.captureBase substitutions
noncomputable def templateApplicationBodyDisplay : OriginalNestedDisplay U source (E.inst b) (.sort v) := {
  sourceEnv := rightEnv, source := C :: source, sourceExpression := E, sourceType := .sort v
  context := .cons (location.contextDerivation initial) domain, node := body
  provenance := (applicationBodyDisplay initial domain body function argument result hu hv location
    (OriginalCaptureMap.identity (location.contextDerivation initial))).provenance
  raw := Subst.id.cons (b.subst Subst.id)
  graph := .capture (.identity (location.contextDerivation initial)) domain
    (.identity (location.contextDerivation initial)) argument (.ofLocation (.appArgument location) initial)
  expression_eq := by simp only [subst_id]; exact inst_eq E b
  type_eq := rfl }
local notation "bodyDisplay" => templateApplicationBodyDisplay initial domain body function argument result hu hv location
local notation "resultDisplay" => OriginalNestedDisplay.identity base result (.ofLocation (.appResult location) initial)

/-- Reconstruct the right result certificate from its actual native row and
argument query. The result R call chooses its frame; identity caps then prove
that its SAME returned query is available in the original right frame. -/
theorem RichPiRowCertificate.templateApplicationResult
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : rightEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (row : RichPiRowCertificate env U registry target locals τ available relevant (.ref domain) body (key : Key n) output)
    (argumentQuery : RichGradedResult rightEnv env U registry target argument locals τ available key.input)
    (admitted : Admitted env U registry target key (b.subst τ) (b.subst τ))
    (domainF : OriginalCodeInductionAt env registry ordered initial (.appDomain location) cost)
    (bodyF : OriginalCodeInductionAt env registry ordered initial (.appCodomain location) cost)
    (resultR : GeneratedObservationCall base (base).initialCaps bodyDisplay resultDisplay τ τ ordered ordered
      (richSchedule .fundamental cost)) :
    ∃ footprint, ∃ certificate : RichCert rightEnv env U registry target result locals τ relevant output footprint,
      footprint.Available available := by
  let needs := row.bodyFootprint.localNeeds ++ row.bodyFootprint.localNeeds.flatMap Need.singletons
  have bounded : ∀ need ∈ needs, need.rank ≤ n := fun need member => (row.pack.atomized_localNeeds need member).1
  have covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms :=
    fun need member atom present => row.covered atom ((row.pack.atomized_localNeeds need member).2 atom present)
  have domainBound : (Closure.close (domain.dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered)).cost < cost :=
    Nat.lt_of_lt_of_le (binder_domain_cost _ [_] [_ , _, _] _)
      (application_cost_le_captured _ _ _ _ _ _)
  obtain ⟨domainAnswer⟩ := domainF target locals τ τ available frame domainBound closed formed substitutions
    row.domain row.domainAvailable
  have aligned := row.alignment.admission henv admitted
  obtain ⟨rawPair, rawArgument, _, _, _, _, pair, self⟩ := aligned
  let pairedFrame := OriginalRichFrame.capture frame domain initial argument (.appArgument location) rfl
    argumentQuery.observation argumentQuery.resources row.domain row.domainAvailable
    row.inputTyped (Related.retag henv row.inputTyped domainAnswer.related pair) needs bounded covered
  have pairedSubstitutions : Ctx.SubstEq env U target (τ.cons key.anchor) (τ.cons (b.subst τ)) (C :: source) :=
    .cons substitutions (domain.sound.defeq.mono below) rawPair
  have bodyClosed : (available.push needs).AtomClosed := Valuation.push_atomized_closed closed _
  have bodyBound : (Closure.close (body.dependencyOrigin ordered)
      (pairedFrame.dependencyEnvironment ordered)).cost < cost :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (capturedApplication_comparison _ _ _ _ _ _)
  have bodyContext : (Located.appCodomain location).contextDerivation initial =
      .cons (location.contextDerivation initial) domain := by
    change ContextDerivation.cons (location.contextDerivation initial) (Classical.choose location.originalDomains.1) = _
    exact congrArg (ContextDerivation.cons (location.contextDerivation initial))
      (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
  have bodyF' := bodyF
  unfold OriginalCodeInductionAt at bodyF'
  rw [bodyContext] at bodyF'
  obtain ⟨answer⟩ := bodyF' target (Locals.push locals) (τ.cons key.anchor) (τ.cons (b.subst τ))
    (available.push needs) pairedFrame bodyBound bodyClosed formed pairedSubstitutions row.body
    (row.pack.available_atomized_localNeeds row.outsideAvailable)
  let actualFrame := OriginalRichFrame.capture frame domain initial argument (.appArgument location) rfl
    argumentQuery.observation argumentQuery.resources row.domain row.domainAvailable
    row.inputTyped (Related.retag henv row.inputTyped domainAnswer.related self) needs bounded covered
  have actualSubstitutions : Ctx.SubstEq env U target (τ.cons (b.subst τ)) (τ.cons (b.subst τ)) (C :: source) :=
    .cons substitutions (domain.sound.defeq.mono below) rawArgument
  have actualCapped : CappedCaptureGenerated base (base).initialCaps τ τ (bodyDisplay).graph actualFrame.raw :=
    .capture (base).identityCapped domain initial argument (.appArgument location) rfl
      argumentQuery.observation argumentQuery.resources argumentQuery.bound argumentQuery.adapter
      row.domain row.domainAvailable row.inputTyped
      (Related.retag henv row.inputTyped domainAnswer.related self) needs bounded covered
  have realizationEq : (Subst.id.cons (b.subst .id)).comp τ = τ.cons (b.subst τ) := by
    funext i; cases i <;> simp only [Subst.comp, Subst.cons, subst_id] <;> rfl
  obtain ⟨realized, realizedCapped, realizedEnvironment⟩ := actualCapped.realize actualFrame actualSubstitutions
  have schedule : richSchedule .expressionReindex
      ((Closure.close (body.dependencyOrigin ordered) (actualFrame.dependencyEnvironment ordered)).cost +
       (Closure.close (result.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost) <
      richSchedule .fundamental cost := by
    apply richSchedule_strict
    rw [Nat.add_comm]
    exact capturedApplication_comparison _ _ _ _ _ _
  have sourceQuery : RichObs (bodyDisplay).sourceEnv env U registry target (bodyDisplay).node
      (Locals.push locals) ((bodyDisplay).raw.comp τ) output answer.footprint := by
    simpa only [templateApplicationBodyDisplay, realizationEq] using RichObs.code answer.certificate
  obtain ⟨returned⟩ := resultR realized realizedCapped bodyClosed (base).identityRealization (base).identityCapped
    closed (by rw [realizedEnvironment ordered]; exact schedule) sourceQuery answer.resources
  let frozen := returned.answer.freezeBase
  obtain ⟨footprint, ⟨certificate⟩, resources⟩ := frozen.code henv row.body.formed
  exact ⟨footprint, certificate, resources⟩

local notation "piDisplay" => OriginalNestedDisplay.identity (base) (.pi hu hv (.ref domain) body)
  (.ofLocation (.appPiFormation location) initial)
local notation "functionDisplay" => OriginalNestedDisplay.identity (base) function.typeFormation.node
  (.ofLocation (.assignedFormation (.appFunction location)) initial)

/-- Assigned-mode application from the actual seeded function/argument child
answers. The right frame is the concrete frame in which BOTH returned child
queries are available (and may already be a merge); only the final identity
replay is frozen to that frame. The Pi query always contains its single row,
including when `profile` is empty. -/
theorem templateApplicationAssignedOfSeed
    {leftDomain : EndpointRef leftEnv U leftSource A (.sort lu)}
    {leftBody : EndpointState leftEnv U (A :: leftSource) B (.sort lv)}
    {leftFunction : EndpointState leftEnv U leftSource f (.forallE A B)}
    {leftArgument : EndpointState leftEnv U leftSource a A}
    (leftResult : EndpointState leftEnv U leftSource (B.inst a) (.sort lv))
    {lhu : lu.WF U} {lhv : lv.WF U}
    (packed : GeneratedApplicationPackedRequest leftDomain leftBody leftArgument lhu lhv
      env registry target leftLocals σ leftAvailable relevant (profile : Profile m))
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : rightEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (functionAnswer : TemplateAssignedResult env U registry target leftFunction function locals σ τ available relevant
      (.pi (A.subst σ) (B.subst σ.lift) packed.request.support
        [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)]))
    (argumentAnswer : TemplateComparisonResult env U registry target leftArgument argument
      leftLocals locals σ τ leftAvailable available packed.argumentQuery.raw)
    (domainF : OriginalCodeInductionAt env registry ordered initial (.appDomain location) cost)
    (bodyF : OriginalCodeInductionAt env registry ordered initial (.appCodomain location) cost)
    (formationR : GeneratedObservationCall (base) (base).initialCaps functionDisplay piDisplay τ τ ordered ordered
      (richSchedule .fundamental cost))
    (resultR : GeneratedObservationCall (base) (base).initialCaps bodyDisplay resultDisplay τ τ ordered ordered
      (richSchedule .fundamental cost)) :
    Nonempty (TemplateAssignedResult env U registry target
      (.app lhu lhv (.ref leftDomain) leftBody leftFunction leftArgument leftResult)
      (.app hu hv (.ref domain) body function argument result) locals σ τ available relevant profile) := by
  have whole : TypeRelated env U registry target
      (.forallE (A.subst σ) (B.subst σ.lift)) (.forallE (C.subst τ) (E.subst τ.lift))
      (.pi (A.subst σ) (B.subst σ.lift) packed.request.support
        [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)]) := by
    simpa only [subst] using functionAnswer.related
  have adapted := packed.argumentQuery.adapter.termMap henv hscoped formed
    (Profile.HasType.raise packed.argumentQuery.bound packed.inputTyped)
    (packed.domainRelated.raise henv packed.argumentQuery.bound) argumentAnswer.related
  have arguments := lowerProfile.related packed.argumentQuery.bound henv formed adapted
  rw [OriginalFactorCut.lower_raised] at arguments
  let rightArgument := argumentAnswer.rightQuery.adaptRequest henv hscoped formed
    packed.argumentQuery.bound packed.argumentQuery.adapter
  have admitted := whole.literalPiRightAdmissionFromBinder henv hscoped formed
    (List.mem_singleton_self _) packed.request.anchor_eq argumentAnswer.raw arguments
  have semantics := whole.literalPiRowPairFromBinder henv hscoped formed
    (List.mem_singleton_self _) packed.request.anchor_eq argumentAnswer.raw arguments
  have path := whole.literalPiRowPathFromBinder henv formed argumentAnswer.raw
  obtain ⟨piReply⟩ := formationR (base).identityRealization (base).identityCapped closed
    (base).identityRealization (base).identityCapped closed
    (EndpointState.application_function_type_reindex_schedule ordered hu hv (.ref domain) body function argument result
      (frame.dependencyEnvironment ordered)) (.code functionAnswer.certificate) functionAnswer.resources
  obtain ⟨piFootprint, ⟨piCertificate⟩, piResources⟩ :=
    piReply.answer.freezeBase.code henv functionAnswer.certificate.formed
  have bodyContext : (Located.appCodomain location).contextDerivation initial =
      .cons (location.contextDerivation initial) domain := by
    change ContextDerivation.cons (location.contextDerivation initial) (Classical.choose location.originalDomains.1) = _
    exact congrArg (ContextDerivation.cons (location.contextDerivation initial))
      (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
  have piBound : (Closure.close (.binder (domain.dependencyOrigin ordered) [body.dependencyOrigin ordered] [])
      (frame.dependencyEnvironment ordered)).cost ≤ cost := by
    apply Nat.le_trans _ (application_cost_le_captured (domain.dependencyOrigin ordered) (body.dependencyOrigin ordered)
      (function.dependencyOrigin ordered) (argument.dependencyOrigin ordered) (result.dependencyOrigin ordered)
      (frame.dependencyEnvironment ordered))
    apply Nat.mul_le_mul_right
    simp only [applicationOrigin, Origin.weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  have origins := piCertificate.piOriginsWith henv hscoped formed closed
    (fun row admission => row.reanchorGeneric initial henv below ordered domain (.appDomain location) body
      (.appCodomain location) bodyContext domainF bodyF frame piBound closed formed substitutions admission)
    hu hv (.done _) piResources
  obtain ⟨row⟩ := piCertificate.piRowOfOrigins origins (List.mem_singleton_self _) (List.mem_singleton_self _)
  obtain ⟨footprint, certificate, resources⟩ := row.templateApplicationResult initial domain body function argument result
    hu hv location frame substitutions ordered henv hscoped below formed closed rightArgument admitted domainF bodyF resultR
  have related := TypeRelated.lower henv packed.request.bound semantics
  rw [OriginalFactorCut.lower_raised] at related
  exact ⟨{
    footprint := footprint
    certificate := certificate.lowerRaised packed.request.bound
    resources := resources
    related := by simpa only [inst_lift_cons, subst_inst] using related
    path := by simpa only [inst_lift_cons, subst_inst] using path }⟩

end RightResult
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
