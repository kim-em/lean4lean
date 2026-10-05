import Lean4Lean.Theory.Typing.AnchoredOriginalRichAssignedFirstFamily
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure

/-! The concrete header chosen by constant replay is bounded by that actual
constant occurrence. In particular a family header reached through a major's
assigned formation is paid by the major, independently of a constructor
header selected for projection computation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem primitiveHeaderTransfer_bounded
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels) (primitive : reference.Primitive)
    (calls : PrimitiveHeaderCalls env registry target ordered captured reference locals σ headerRealization available) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      (selection.header.original.dependencyOrigin selection.header.ordered).weight ≤
        (reference.dependencyOrigin ordered).weight ∧
      RichCodeTransfer env U registry target reference.typeFormation.node
        (.ref (.left selection.header.original)) locals [] σ headerRealization available (fun _ => []) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl otherWF levelWF lookup wf count equiv closed ambient =>
      refine ⟨⟨_, lookup, _, wf, Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl)⟩, ?_, ?_⟩
      · simp only [RichHeaderSelection.header, EndpointRef.dependencyOrigin]
        conv => rhs; rw [Derivation.dependencyOrigin.eq_def]
        exact Nat.le_of_lt (Origin.rule_child (by simp))
      · intro relevant n profile footprint certificate resources
        exact replayConstantHeader ordered lookup wf otherWF count equiv levelWF closed ambient
          captured certificate resources calls
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl wf count levelWF lookup otherWF equiv closed ambient =>
      refine ⟨⟨_, lookup, _, wf, equiv⟩, ?_, ?_⟩
      · simp only [RichHeaderSelection.header, EndpointRef.dependencyOrigin]
        conv => rhs; rw [Derivation.dependencyOrigin.eq_def]
        exact Nat.le_of_lt (Origin.rule_child (by simp))
      · intro relevant n profile footprint certificate resources
        exact replayConstantHeader ordered lookup wf otherWF count equiv levelWF closed ambient
          captured certificate resources calls

/-- The selected header and its bound are returned together with the very
same replay witness, including the original seed on a right constant side. -/
theorem locatedConstantTransfer_bounded
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (captured : List Closure)
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node)
    (prefixCalls : ∀ route : DirectPrefixRoute sourceEnv U source (.const name levels) node
        (.ref (constantPrefix node).reference),
      route.PeelCalls env registry target ordered captured locals σ available)
    (headerCalls : PrimitiveHeaderCalls env registry target ordered captured
      (constantPrefix node).reference locals σ headerRealization available) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      (selection.header.original.dependencyOrigin selection.header.ordered).weight ≤
        (node.dependencyOrigin ordered).weight ∧
      RichCodeTransfer env U registry target node.typeFormation.node
        (.ref (.left selection.header.original)) locals [] σ headerRealization available (fun _ => []) := by
  let packet := constantPrefix node
  obtain ⟨route⟩ := packet.directLocated location
  obtain ⟨selection, bounded, finish⟩ := primitiveHeaderTransfer_bounded ordered captured packet.reference
    rfl packet.primitive headerCalls
  exact ⟨selection, Nat.le_trans bounded (packet.route.dependency_weight_le ordered),
    route.peelCode henv ordered captured (prefixCalls route) finish⟩

theorem _root_.Lean4Lean.AnchoredSource.Adapted.OriginalEndpointFactor.Located.dependency_weight_le
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U context expression assigned}
    (location : Located root node) (ordered : sourceEnv.Ordered) :
    (node.dependencyOrigin ordered).weight ≤ (root.dependencyOrigin ordered).weight := by
  have bounded := location.dependency_cost_le ordered []
  change (node.dependencyOrigin ordered).weight *
      (1 + environmentCost (location.dependencyEnvironment ordered [])) ≤
    (root.dependencyOrigin ordered).weight * (1 + environmentCost []) at bounded
  simp only [environmentCost, Nat.add_zero, Nat.mul_one] at bounded
  exact Nat.le_trans (Nat.le_mul_of_pos_right _ (by omega)) bounded

/-- The family header reserve is controlled by the actual major lineage;
it need not equal the constructor header used elsewhere by projection. -/
theorem assignedFirstFamilyTransfer_bounded
    (henv : env.Ordered) (ordered : sourceEnv.Ordered) (captured : List Closure)
    (major : EndpointRef sourceEnv U source majorExpression
      (mkApps (.const name levels) (argument :: arguments)))
    (prefixCalls : ∀ route : DirectPrefixRoute sourceEnv U source (.const name levels)
        (assignedFirstFamilyFunction major) (.ref (constantPrefix (assignedFirstFamilyFunction major)).reference),
      route.PeelCalls env registry target ordered captured locals σ available)
    (headerCalls : PrimitiveHeaderCalls env registry target ordered captured
      (constantPrefix (assignedFirstFamilyFunction major)).reference locals σ headerRealization available) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      (selection.header.original.dependencyOrigin selection.header.ordered).weight ≤
        (major.dependencyOrigin ordered).weight ∧
      RichCodeTransfer env U registry target (assignedFirstFamilyFunction major).typeFormation.node
        (.ref (.left selection.header.original)) locals [] σ headerRealization available (fun _ => []) := by
  obtain ⟨selection, bounded, transfer⟩ := locatedConstantTransfer_bounded henv ordered captured
    (assignedFirstFamilyFunctionLocation major) prefixCalls headerCalls
  exact ⟨selection, Nat.le_trans bounded
    ((assignedFirstFamilyFunctionLocation major).dependency_weight_le ordered), transfer⟩

/-- First-slot alignment returns the cost evidence for the same concrete
header that supplies its declared-domain certificate. -/
theorem assignedFirstFamilyAlignment_bounded
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
      (selection.header.original.dependencyOrigin selection.header.ordered).weight ≤
        (major.dependencyOrigin ordered).weight ∧
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
  obtain ⟨selection, bound, transfer⟩ := assignedFirstFamilyTransfer_bounded henv ordered captured major prefixCalls headerCalls
  obtain ⟨reply⟩ := transfer query resources
  refine ⟨selection, bound, ?_⟩
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
