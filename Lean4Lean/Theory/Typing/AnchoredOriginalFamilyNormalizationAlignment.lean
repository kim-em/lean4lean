import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationDispatch

/-! The first actual family argument is aligned to the domain of the
retained normalized declaration. The raw family header need not be a Pi. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem assignedFirstFamilyAlignmentNormalized_retained
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info) (nonempty : 0 < info.nparams)
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
      (constantPrefix (assignedFirstFamilyFunction major)).reference locals σ seed available →
    PrimitiveFamilyNormalizationCalls env registry target ordered captured
      (constantPrefix (assignedFirstFamilyFunction major)).reference seed →
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (major.dependencyOrigin ordered).weight ∧
      let normalized := normalizedFamilyPrefix (selectProjectionParameters ordered registered selection.seedWF) nonempty
      ∃ answer : HeaderValueAlignment (application.headerOwner (field := field)) normalized.domainOriginal
        env registry target locals [] σ τ seed available (fun _ => []) input,
        answer.value = value := by
  dsimp only
  intro value argumentR domainR prefixCalls headerCalls normalizationCalls
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
  obtain ⟨selection, ledger, bounded, transfer⟩ := locatedNormalizedHeaderTransfer_retained henv hscoped formed ordered captured
    registered nonempty (assignedFirstFamilyFunctionLocation major) prefixCalls headerCalls normalizationCalls
  obtain ⟨reply⟩ := transfer query resources
  let normalized := normalizedFamilyPrefix (selectProjectionParameters ordered registered selection.seedWF) nonempty
  obtain ⟨domain⟩ := reply.certificate.piDomain normalized.selected.view.domainWF
    normalized.selected.view.bodyWF (.done _) reply.resources
  rcases domain with ⟨domainFootprint, certificate, domainResources⟩
  rw [normalized.domain_eq] at certificate
  have piRelated : TypeRelated env U registry target
      (.forallE (application.view.domainExpression.subst σ) (application.view.codomainExpression.subst σ.lift))
      (.forallE (normalized.domainExpression.subst seed) (normalized.bodyExpression.subst seed.lift))
      (Profile.pi (application.view.domainExpression.subst σ) (application.view.codomainExpression.subst σ.lift)
        value.support []) := by
    simpa only [subst] using reply.related
  have related := TypeRelated.literalPiDomain henv hscoped formed piRelated
  have path := TypeRelated.literalPiDomainPath henv formed piRelated
  refine ⟨selection, ledger, Nat.le_trans bounded
    ((assignedFirstFamilyFunctionLocation major).dependency_weight_le ordered), ?_⟩
  exact ⟨{
    value := value
    aligned := {
      footprint := domainFootprint
      certificate := certificate
      resources := domainResources
      related := natural.related.trans henv related }
    path := path }, rfl⟩

theorem assignedFirstFamilyAlignmentNormalized
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info) (nonempty : 0 < info.nparams)
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
      (constantPrefix (assignedFirstFamilyFunction major)).reference locals σ seed available →
    PrimitiveFamilyNormalizationCalls env registry target ordered captured
      (constantPrefix (assignedFirstFamilyFunction major)).reference seed →
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      let normalized := normalizedFamilyPrefix (selectProjectionParameters ordered registered selection.seedWF) nonempty
      ∃ answer : HeaderValueAlignment (application.headerOwner (field := field)) normalized.domainOriginal
        env registry target locals [] σ τ seed available (fun _ => []) input,
        answer.value = value := by
  dsimp only
  intro value argumentR domainR prefixCalls headerCalls normalizationCalls
  obtain ⟨selection, _, _, alignment⟩ := assignedFirstFamilyAlignmentNormalized_retained
    (field := field) henv hscoped formed ordered registered nonempty major frame value
    argumentR domainR prefixCalls headerCalls normalizationCalls
  exact ⟨selection, alignment⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
