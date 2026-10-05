import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyParameterLedger
import Lean4Lean.Theory.Typing.AnchoredOriginalFamilyNormalizationTransfer
import Lean4Lean.Theory.Typing.AnchoredOriginalRichConstantBounds

/-! The normalization obligations are attached to the actual primitive
constant reference before prefix replay forgets its constructor fields. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

def FamilyNormalizationCalls
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {sourceEnv : VEnv} {U : Nat} {name : Name} {levels : List VLevel}
    {ordered : sourceEnv.Ordered}
    (selection : RichHeaderSelection sourceEnv U name levels ordered)
    (registered : sourceEnv.projections name info) (seed : Subst) (limit : Nat) : Prop :=
  let packet := selectProjectionParameters ordered registered selection.seedWF
  let normalizationCost := (Closure.close
    (packet.instantiated.normalization.dependencyOrigin packet.origin.baseOrdered) []).cost
  (richSchedule .expressionReindex
      ((Closure.close (selection.header.original.dependencyOrigin selection.header.ordered) []).cost +
        normalizationCost) < limit →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs selection.header.source env U registry target (.ref (.left selection.header.original))
      [] seed profile footprint → footprint.Available (fun _ => []) →
    Nonempty (RichGradedResult packet.origin.base env U registry target
      (.ref (.left packet.instantiated.normalization)) [] seed (fun _ => []) profile)) ∧
  (richSchedule .fundamental normalizationCost < limit →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs packet.origin.base env U registry target (.ref (.left packet.instantiated.normalization))
      [] seed profile footprint → footprint.Available (fun _ => []) →
    Nonempty (OriginalEqualityQueryResult packet.instantiated.normalization env registry target
      [] seed seed (fun _ => []) profile))

def PrimitiveFamilyNormalizationCalls
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (seed : Subst) : Prop :=
  match reference with
  | .left (.constDF lookup wf otherWF count equiv levelWF closed ambient) =>
    ∀ (info : VProjectionInfo) (registered : sourceEnv.projections _ info),
    FamilyNormalizationCalls (ordered := ordered) env registry target
      ⟨_, lookup, _, wf, Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl)⟩ registered seed
      (richSchedule .fundamental (Closure.close
        ((Derivation.constDF lookup wf otherWF count equiv levelWF closed ambient).dependencyOrigin ordered) captured).cost)
  | .right (.constDF lookup wf otherWF count equiv levelWF closed ambient) =>
    ∀ (info : VProjectionInfo) (registered : sourceEnv.projections _ info),
    FamilyNormalizationCalls (ordered := ordered) env registry target ⟨_, lookup, _, wf, equiv⟩ registered seed
      (richSchedule .fundamental (Closure.close
        ((Derivation.constDF lookup wf otherWF count equiv levelWF closed ambient).dependencyOrigin ordered) captured).cost)
  | _ => True

private theorem FamilyNormalizationCalls.normalizeAnswer
    {ordered : sourceEnv.Ordered}
    {selection : RichHeaderSelection sourceEnv U name levels ordered}
    {registered : sourceEnv.projections name info}
    {left : EndpointState leftEnv U leftSource expression (.sort leftLevel)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (nonempty : 0 < info.nparams)
    (calls : FamilyNormalizationCalls env registry target selection registered seed limit)
    (pairBound : richSchedule .expressionReindex
      ((Closure.close (selection.header.original.dependencyOrigin selection.header.ordered) []).cost +
       (Closure.close ((selectProjectionParameters ordered registered selection.seedWF).instantiated.normalization.dependencyOrigin
         (selectProjectionParameters ordered registered selection.seedWF).origin.baseOrdered) []).cost) < limit)
    (singleBound : richSchedule .fundamental
       (Closure.close ((selectProjectionParameters ordered registered selection.seedWF).instantiated.normalization.dependencyOrigin
         (selectProjectionParameters ordered registered selection.seedWF).origin.baseOrdered) []).cost < limit)
    (answer : RichCodeTransferResult env U registry target left (.ref (.left selection.header.original))
      [] σ seed (fun _ => []) relevant profile) :
    let head := normalizedFamilyPrefix (selectProjectionParameters ordered registered selection.seedWF) nonempty
    Nonempty (RichCodeTransferResult env U registry target left
      (.pi head.selected.view.domainWF head.selected.view.bodyWF head.selected.view.domain head.selected.view.body)
      [] σ seed (fun _ => []) relevant profile) := by
  have infoEq : selection.info = (selectProjectionParameters ordered registered selection.seedWF).origin.family.toVConstant :=
    Option.some.inj (selection.lookup.symm.trans
      (selectProjectionParameters ordered registered selection.seedWF).origin.familyPresent)
  have same : selection.info.type.instL selection.seed =
      (selectProjectionParameters ordered registered selection.seedWF).origin.family.type.instL selection.seed := by
    rw [infoEq]
  exact answer.normalizedPiAnswer henv hscoped formed
    (selectProjectionParameters ordered registered selection.seedWF) nonempty same
    (calls.1 pairBound) (calls.2 singleBound)

/-- Full profile replay is completed while the actual constDF is still
available. The selected normalization includes its exact original seed. -/
theorem primitiveNormalizedHeaderTransfer_retained
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    (registered : sourceEnv.projections name info) (nonempty : 0 < info.nparams)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels) (primitive : reference.Primitive)
    (headerCalls : PrimitiveHeaderCalls env registry target ordered captured reference locals σ seed available)
    (normalizationCalls : PrimitiveFamilyNormalizationCalls env registry target ordered captured reference seed) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight < (reference.dependencyOrigin ordered).weight ∧
      let head := normalizedFamilyPrefix (selectProjectionParameters ordered registered selection.seedWF) nonempty
      RichCodeTransfer env U registry target reference.typeFormation.node
        (.pi head.selected.view.domainWF head.selected.view.bodyWF head.selected.view.domain head.selected.view.body)
        locals [] σ seed available (fun _ => []) := by
  cases reference with
  | left original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl otherWF levelWF lookup wf count equiv closed ambient =>
      let selection : RichHeaderSelection sourceEnv U name levels ordered :=
        ⟨_, lookup, _, wf, Lean4Lean.List.Forall₂.rfl (fun _ _ => by rfl)⟩
      let ledger : FamilyParameterLedger selection := ⟨_, otherWF, equiv, Or.inl rfl⟩
      refine ⟨selection, ledger, ?_, ?_⟩
      · exact Derivation.constantParameters_header_twice_weight_lt ordered lookup wf otherWF count equiv levelWF closed ambient
      dsimp only
      intro relevant n profile footprint certificate resources
      obtain ⟨answer⟩ := replayConstantHeader ordered lookup wf otherWF count equiv levelWF closed ambient
        captured certificate resources headerCalls
      have pair := Derivation.constantNormalization_pair_lt ordered lookup registered wf otherWF count equiv
        levelWF closed ambient captured
      have single := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) pair
      exact FamilyNormalizationCalls.normalizeAnswer (selection := selection) henv hscoped formed nonempty
        (normalizationCalls info registered) (richSchedule_strict pair _ _) (richSchedule_strict single _ _) answer
  | right original =>
    cases original <;> simp only [EndpointRef.Primitive, Derivation.PrimitiveHead] at primitive
    all_goals try contradiction
    all_goals try cases expressionEq
    case constDF.refl wf count levelWF lookup otherWF equiv closed ambient =>
      let selection : RichHeaderSelection sourceEnv U name levels ordered := ⟨_, lookup, _, wf, equiv⟩
      let ledger : FamilyParameterLedger selection := ⟨_, otherWF, equiv, Or.inr rfl⟩
      refine ⟨selection, ledger, ?_, ?_⟩
      · exact Derivation.constantParameters_header_twice_weight_lt ordered lookup wf otherWF count equiv levelWF closed ambient
      dsimp only
      intro relevant n profile footprint certificate resources
      obtain ⟨answer⟩ := replayConstantHeader ordered lookup wf otherWF count equiv levelWF closed ambient
        captured certificate resources headerCalls
      have pair := Derivation.constantNormalization_pair_lt ordered lookup registered wf otherWF count equiv
        levelWF closed ambient captured
      have single := Nat.lt_of_le_of_lt (Nat.le_add_left _ _) pair
      exact FamilyNormalizationCalls.normalizeAnswer (selection := selection) henv hscoped formed nonempty
        (normalizationCalls info registered) (richSchedule_strict pair _ _) (richSchedule_strict single _ _) answer

theorem primitiveNormalizedHeaderTransfer
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    (registered : sourceEnv.projections name info) (nonempty : 0 < info.nparams)
    (reference : EndpointRef sourceEnv U source expression assigned)
    (expressionEq : expression = .const name levels) (primitive : reference.Primitive)
    (headerCalls : PrimitiveHeaderCalls env registry target ordered captured reference locals σ seed available)
    (normalizationCalls : PrimitiveFamilyNormalizationCalls env registry target ordered captured reference seed) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      let head := normalizedFamilyPrefix (selectProjectionParameters ordered registered selection.seedWF) nonempty
      RichCodeTransfer env U registry target reference.typeFormation.node
        (.pi head.selected.view.domainWF head.selected.view.bodyWF head.selected.view.domain head.selected.view.body)
        locals [] σ seed available (fun _ => []) := by
  obtain ⟨selection, _, _, transfer⟩ := primitiveNormalizedHeaderTransfer_retained
    henv hscoped formed ordered captured registered nonempty reference expressionEq primitive headerCalls normalizationCalls
  exact ⟨selection, transfer⟩

/-- Conversion prefixes replay into the already normalized primitive
answer. They cannot replace its retained normalization proof or seed. -/
theorem locatedNormalizedHeaderTransfer_retained
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    (registered : sourceEnv.projections name info) (nonempty : 0 < info.nparams)
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node)
    (prefixCalls : ∀ route : DirectPrefixRoute sourceEnv U source (.const name levels) node
        (.ref (constantPrefix node).reference),
      route.PeelCalls env registry target ordered captured locals σ available)
    (headerCalls : PrimitiveHeaderCalls env registry target ordered captured
      (constantPrefix node).reference locals σ seed available)
    (normalizationCalls : PrimitiveFamilyNormalizationCalls env registry target ordered captured
      (constantPrefix node).reference seed) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      ∃ ledger : FamilyParameterLedger selection,
      ledger.pairWeight ≤ (node.dependencyOrigin ordered).weight ∧
      let head := normalizedFamilyPrefix (selectProjectionParameters ordered registered selection.seedWF) nonempty
      RichCodeTransfer env U registry target node.typeFormation.node
        (.pi head.selected.view.domainWF head.selected.view.bodyWF head.selected.view.domain head.selected.view.body)
        locals [] σ seed available (fun _ => []) := by
  let packet := constantPrefix node
  obtain ⟨route⟩ := packet.directLocated location
  obtain ⟨selection, ledger, bounded, finish⟩ := primitiveNormalizedHeaderTransfer_retained henv hscoped formed ordered captured registered
    nonempty packet.reference rfl packet.primitive headerCalls normalizationCalls
  exact ⟨selection, ledger, Nat.le_trans (Nat.le_of_lt bounded) (packet.route.dependency_weight_le ordered),
    route.peelCode henv ordered captured (prefixCalls route) finish⟩

theorem locatedNormalizedHeaderTransfer
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (captured : List Closure)
    (registered : sourceEnv.projections name info) (nonempty : 0 < info.nparams)
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node)
    (prefixCalls : ∀ route : DirectPrefixRoute sourceEnv U source (.const name levels) node
        (.ref (constantPrefix node).reference),
      route.PeelCalls env registry target ordered captured locals σ available)
    (headerCalls : PrimitiveHeaderCalls env registry target ordered captured
      (constantPrefix node).reference locals σ seed available)
    (normalizationCalls : PrimitiveFamilyNormalizationCalls env registry target ordered captured
      (constantPrefix node).reference seed) :
    ∃ selection : RichHeaderSelection sourceEnv U name levels ordered,
      let head := normalizedFamilyPrefix (selectProjectionParameters ordered registered selection.seedWF) nonempty
      RichCodeTransfer env U registry target node.typeFormation.node
        (.pi head.selected.view.domainWF head.selected.view.bodyWF head.selected.view.domain head.selected.view.body)
        locals [] σ seed available (fun _ => []) := by
  obtain ⟨selection, _, _, transfer⟩ := locatedNormalizedHeaderTransfer_retained
    henv hscoped formed ordered captured registered nonempty location prefixCalls headerCalls normalizationCalls
  exact ⟨selection, transfer⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
