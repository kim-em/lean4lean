import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantBounds
import Lean4Lean.Theory.Typing.AnchoredOriginalGroupedFamilyReserve
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture

/-! Family-header reserve evidence stays attached to the actual replay
selection. The declared family and constructor headers remain distinct. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

structure SelectedFamilyHeader (ordered : sourceEnv.Ordered)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments)) where
  selection : RichHeaderSelection sourceEnv U name levels ordered
  retained : (selection.header.original.dependencyOrigin selection.header.ordered).weight ≤
    (major.dependencyOrigin ordered).weight

noncomputable abbrev SelectedFamilyHeader.header
    {ordered : sourceEnv.Ordered}
    {major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) arguments)}
    (selected : SelectedFamilyHeader ordered major) := selected.selection.header

/-- Actual constant replay constructs the selection and its reserve together. -/
theorem assignedFirstFamilyTransfer_reserved
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (captured : List Closure)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    (prefixCalls : ∀ route : DirectPrefixRoute sourceEnv U source (.const name levels)
        (assignedFirstFamilyFunction major) (.ref (constantPrefix (assignedFirstFamilyFunction major)).reference),
      route.PeelCalls env registry target ordered captured locals σ available)
    (headerCalls : PrimitiveHeaderCalls env registry target ordered captured
      (constantPrefix (assignedFirstFamilyFunction major)).reference locals σ headerRealization available) :
    ∃ selected : SelectedFamilyHeader ordered major,
      RichCodeTransfer env U registry target (assignedFirstFamilyFunction major).typeFormation.node
        (.ref (.left selected.header.original)) locals [] σ headerRealization available (fun _ => []) := by
  obtain ⟨selection, bounded, transfer⟩ := assignedFirstFamilyTransfer_bounded henv ordered captured
    major prefixCalls headerCalls
  exact ⟨⟨selection, bounded⟩, transfer⟩

/-- Exact first-domain alignment keeps the reserve for that very header. -/
theorem assignedFirstFamilyAlignment_reserved
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
    ∃ selected : SelectedFamilyHeader ordered major,
      ∀ {C D : VExpr} {u v : VLevel}
        (domain : EndpointRef selected.header.source U [] C (.sort u))
        (body : EndpointState selected.header.source U [C] D (.sort v))
        (hu : u.WF U) (hv : v.WF U)
        (shape : selected.selection.info.type.instL selected.selection.seed = .forallE C D)
        (_route : PrefixRoute selected.header.source U [] (.forallE C D)
          ((EndpointState.ref (.left selected.header.original)).cast shape rfl) (.pi hu hv (.ref domain) body)),
      ∃ answer : HeaderValueAlignment (application.headerOwner (field := field)) domain env registry target
        locals [] σ τ headerRealization available (fun _ => []) input, answer.value = value := by
  dsimp only
  intro value argumentR domainR prefixCalls headerCalls
  obtain ⟨selection, bounded, aligned⟩ := assignedFirstFamilyAlignment_bounded
    (field := field) henv hscoped formed ordered major frame value argumentR domainR prefixCalls headerCalls
  exact ⟨⟨selection, bounded⟩, aligned⟩

/-- The actual pending-owner frame and the actual declared-family frame fit
below the projection. Header weight is taken from the selected replay packet,
not from an independent numerical premise. -/
theorem SelectedFamilyHeader.projection_alignment_schedule
    (sourceOrdered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
    (major : Derivation sourceEnv U source sourceMajor majorExpression
      (mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (family : SelectedFamilyHeader sourceOrdered (.left major))
    (domain : EndpointRef family.header.source U headerSource A (.sort level))
    (domainLocation : Located (.left family.header.original) (.ref domain))
    {context : ContextDerivation family.header.source U headerSource}
    (tail : OriginalRichFrame _ env U registry target context headerLocals declaredLeft declaredRight headerAvailable)
    (previous : List (Dependency.GroupedHeaderStep family.header.ordered sourceOrdered
      (.left family.header.original) field (.left major)))
    (prefixLength : previous.length ≤ (params ++ indices).length)
    (tail_environment : tail.dependencyEnvironment family.header.ordered =
      Dependency.groupedHeaderEnvironment previous ownerInitial)
    (pending : PendingRichCapture (field := field) (major := .left major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue) :
    richSchedule .expressionReindex
      ((Closure.close (pending.owner.node.typeFormation.node.dependencyOrigin sourceOrdered)
        (pending.frame.dependencyEnvironment sourceOrdered)).cost +
       (Closure.close (domain.dependencyOrigin family.header.ordered)
         (tail.dependencyEnvironment family.header.ordered)).cost) <
    richSchedule .fundamental
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin sourceOrdered) ownerInitial).cost := by
  have pair := Dependency.grouped_projection_family_prefix_schedule sourceOrdered registered levelsWF levelCount
    parameterCount indexCount selected fieldWF field major closed allowed family.header.ordered
    (.left family.header.original) family.retained previous prefixLength
    ⟨headerSource, A, .sort level, .ref domain, domainLocation⟩
    (pending.measureOwner sourceOrdered) ownerInitial
  have ownerBound := Nat.le_trans
    (pending.owner.node.typeFormation_dependency_cost_le sourceOrdered (pending.frame.dependencyEnvironment sourceOrdered))
    (pending.owner_cost_le sourceOrdered)
  rw [tail_environment]
  change richSchedule .expressionReindex _ < _ at pair
  simp only [richSchedule, RichPhase.code, EndpointState.dependencyOrigin] at pair ⊢
  omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
