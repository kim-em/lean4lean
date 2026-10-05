import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantDispatch
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyArgumentAlignment
import Lean4Lean.Theory.Typing.AnchoredOriginalRichApplicationDomainBridge

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def assignedFirstFamilyFunction
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments))) :
    EndpointState sourceEnv U source (.const name levels)
      (.forallE (assignedFamilyApplication major 0 rfl).view.domainExpression
        (assignedFamilyApplication major 0 rfl).view.codomainExpression) :=
  (assignedFamilyApplication major 0 rfl).view.function

noncomputable def assignedFirstFamilyFunctionLocation
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments))) :
    Located major (assignedFirstFamilyFunction major) :=
  .appFunction (assignedFamilyApplication major 0 rfl).view.location

/-- Index zero, packet selection, direct-prefix eligibility and primitive
header selection are all computed from the major's assigned formation. -/
theorem assignedFirstFamilyTransfer
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (captured : List Closure)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    (prefixCalls : ∀ route : DirectPrefixRoute sourceEnv U source (.const name levels)
        (assignedFirstFamilyFunction major) (.ref (constantPrefix (assignedFirstFamilyFunction major)).reference),
      route.PeelCalls env registry target ordered captured locals σ available)
    (headerCalls : PrimitiveHeaderCalls env registry target ordered captured
      (constantPrefix (assignedFirstFamilyFunction major)).reference locals σ headerRealization available) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      RichCodeTransfer env U registry target (assignedFirstFamilyFunction major).typeFormation.node
        (.ref (.left selection.header.original)) locals [] σ headerRealization available (fun _ => []) :=
  locatedConstantTransfer henv ordered captured (assignedFirstFamilyFunctionLocation major) prefixCalls headerCalls

/-- Consume a finite domain-only Pi answer, including an explicitly retained
source shape equality for the selected earlier header. No new Pi coherence
supplier is introduced by domain extraction. -/
theorem RichCodeTransferResult.domainAnswer
    {left : EndpointState leftEnv U leftSource (.forallE A B) (.sort leftLevel)}
    {right : EndpointState rightEnv U rightSource rightExpression (.sort rightLevel)}
    {domain : EndpointState rightEnv U rightSource C (.sort u)}
    {body : EndpointState rightEnv U (C :: rightSource) D (.sort v)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (hu : u.WF U) (hv : v.WF U)
    (shape : rightExpression = .forallE C D)
    (route : PrefixRoute rightEnv U rightSource (.forallE C D) (right.cast shape rfl)
      (.pi hu hv domain body))
    (answer : RichCodeTransferResult env U registry target left right rightLocals σ τ rightAvailable true
      (Profile.pi (A.subst σ) (B.subst σ.lift) (support : Profile n) [])) :
    ∃ footprint,
      Nonempty (RichCert rightEnv env U registry target domain rightLocals τ true support footprint) ∧
      footprint.Available rightAvailable ∧
      TypeRelated env U registry target (A.subst σ) (C.subst τ) support ∧
      TypeConversion env U target (A.subst σ) (C.subst τ) := by
  cases shape
  obtain ⟨domain⟩ := answer.certificate.piDomain hu hv route answer.resources
  exact ⟨domain.footprint, ⟨domain.certificate⟩, domain.resources,
    TypeRelated.literalPiDomain henv hscoped formed (by simpa only [subst] using answer.related),
    TypeRelated.literalPiDomainPath henv formed (by simpa only [subst] using answer.related)⟩

/-- The complete first-slot alignment computes its current application,
function prefix and selected earlier header. The only remaining inputs are
strict original induction calls and the actual selected-header Pi route. -/
theorem assignedFirstFamilyAlignment
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    {initialContext : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target
      ((assignedFamilyApplication major 0 rfl).argument.location.contextDerivation initialContext)
      locals σ τ available) :
    let captured := frame.dependencyEnvironment ordered
    let application := assignedFamilyApplication major 0 rfl
    let pi := piPrefix (Located.assignedFormation (Located.appFunction application.view.location))
    ∀ value : RichBinderValue sourceEnv env U registry target application.view.argument
      locals σ τ available (input : Profile n),
    FormationRestoreCall env U registry target ordered captured
      ((EndpointState.app application.view.domainWF application.view.bodyWF application.view.domain
        application.view.codomain application.view.function application.view.argument application.view.result).dependencyOrigin ordered)
      application.view.argument.typeFormation.node application.view.domain locals σ available →
    FormationRestoreCall env U registry target ordered captured (application.node.dependencyOrigin ordered)
      application.view.domain pi.view.domain locals σ available →
    (∀ route : DirectPrefixRoute sourceEnv U source (.const name levels)
        (assignedFirstFamilyFunction major) (.ref (constantPrefix (assignedFirstFamilyFunction major)).reference),
      route.PeelCalls env registry target ordered captured locals σ available) →
    PrimitiveHeaderCalls env registry target ordered captured
      (constantPrefix (assignedFirstFamilyFunction major)).reference locals σ headerRealization available →
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∀ {C D : VExpr} {u v : VLevel}
        (domain : EndpointRef selection.header.source U [] C (.sort u))
        (body : EndpointState selection.header.source U [C] D (.sort v))
        (hu : u.WF U) (hv : v.WF U)
        (shape : selection.info.type.instL selection.seed = .forallE C D)
        (_route : PrefixRoute selection.header.source U [] (.forallE C D)
          ((EndpointState.ref (.left selection.header.original)).cast shape rfl) (.pi hu hv (.ref domain) body)),
      ∃ answer : HeaderValueAlignment (application.headerOwner (field := field)) domain env registry target
        locals [] σ τ headerRealization available (fun _ => []) input, answer.value = value := by
  dsimp only
  intro value argumentR domainR prefixCalls headerCalls
  let captured := frame.dependencyEnvironment ordered
  let application := assignedFamilyApplication major 0 rfl
  let pi := piPrefix (Located.assignedFormation (Located.appFunction application.view.location))
  obtain ⟨natural⟩ := argumentR
    (EndpointState.application_argument_type_reindex_schedule ordered
      application.view.domainWF application.view.bodyWF application.view.domain application.view.codomain
      application.view.function application.view.argument application.view.result captured)
    value.certificate value.resources
  obtain ⟨fp, ⟨query⟩, resources⟩ := AppView.seedFunctionPi ordered application.selected pi captured
    natural.certificate natural.resources domainR
  obtain ⟨selection, transfer⟩ := assignedFirstFamilyTransfer henv ordered captured major prefixCalls headerCalls
  obtain ⟨reply⟩ := transfer query resources
  refine ⟨selection, ?_⟩
  intro C D u v domain body hu hv shape route
  obtain ⟨fp, ⟨certificate⟩, resources, related, path⟩ :=
    reply.domainAnswer henv hscoped formed hu hv shape route
  exact ⟨{
    value := value
    aligned := {
      footprint := fp
      certificate := certificate
      resources := resources
      related := natural.related.trans henv related }
    path := path }, rfl⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
