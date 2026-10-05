import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilySeedConsumption
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyDemand
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstOrigin

/-! Recover the exact retained family leaf from a constant observation. Code
wrappers are inverted through their finite origin programs; no registered
header is assumed to be a literal telescope. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem constantSourceHeader
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (node : EndpointState sourceEnv U source (.const name levels) assigned)
    (found : env.constants name = some info) :
    Nonempty (ConstantHeaderOrigin sourceEnv name info) := by
  let head := constantPrefix node
  obtain ⟨selection⟩ := EndpointRef.closedPrimitiveConstant head.reference rfl head.primitive
  have same := below.constants selection.lookup
  rw [found] at same
  cases Option.some.inj same
  exact ordered.constantHeaderOrigin selection.lookup

private theorem familyCodeOrigin
    (action : SortableCodeAction env U registry target relevant p next q)
    (formed : p.HasType (.sort relevant))
    (origins : ∀ a ∈ p.atoms, FamilyEndDemand a →
      ∃ seed : RetainedRichFamilySeed root env registry target name levels,
        Nonempty (GeneralOutputPath env U registry target seed.atom a))
    (member : b ∈ q.atoms) (ends : FamilyEndDemand b) :
    ∃ seed : RetainedRichFamilySeed root env registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.atom b) := by
  obtain ⟨a, ha, ⟨leaf⟩⟩ := action.atom member
  obtain ⟨seed, ⟨path⟩⟩ := origins a ha (ends.codeBack leaf (formed.singleton_of_mem ha))
  exact ⟨seed, ⟨.code path leaf (formed.singleton_of_mem ha)⟩⟩

mutual
theorem _root_.Lean4Lean.AnchoredSource.Adapted.Obs.familyConstantOrigin
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node)
    {demand : Profile n}
    (source : Obs env U registry target locals σ (.const name levels) demand footprint)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom) :
    ∃ seed : RetainedRichFamilySeed root env registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.atom atom) := by
  match n, demand, footprint, source with
  | _, _, _, .family found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    have singleton := tree.singleton_of_mem member
    rw [singleton] at tree typed
    obtain ⟨origin⟩ := constantSourceHeader ordered below node found
    let seed := RetainedRichFamilySeed.ofSortable location origin found noDefinition noNative noQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed (.ofCode certificate certificate.formed) typed tree.toSortable
    exact ⟨seed, ⟨.refl⟩⟩
  | _, _, _, .delta lookup .. => rw [notDefinition] at lookup; contradiction
  | _, _, _, .native lookup .. => rw [notNative] at lookup; contradiction
  | _, _, _, .constructor _ _ _ _ _ _ _ _ _ _ _ _ tree =>
    exact (OriginalRecordSource.ConstructorPlan.not_familyEnd henv hscoped formed tree member ends).elim
  | _, _, _, .empty => cases member
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path⟩ := left.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
    · obtain ⟨origin, path⟩ := right.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
  | _, _, _, .pad source =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location ha ends
    exact ⟨origin, ⟨.pad path⟩⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_map.mpr ⟨_, member, rfl⟩) ends
    exact ⟨origin, ⟨.unpad path⟩⟩
  | _, _, _, .view source change =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_singleton_self _)
      (ends.normalAdapterBack ((AtomAction.view change).toGeneralAdapter henv hscoped formed))
    exact ⟨origin, ⟨.action path (.view change)⟩⟩
  | _, _, _, .rowShift source =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_singleton_self _)
      ends
    exact ⟨origin, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩⟩
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

theorem _root_.Lean4Lean.AnchoredSource.Adapted.CodeCert.familyConstantOrigin
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node)
    {demand : Profile n}
    (source : CodeCert env U registry target locals σ (.const name levels) demand footprint)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom) :
    ∃ seed : RetainedRichFamilySeed root env registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.atom atom) := by
  match n, demand, footprint, source with
  | _, _, _, .seed source _ => exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location member ends
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path⟩ := left.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
    · obtain ⟨origin, path⟩ := right.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
  | _, _, _, .pad source =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location ha ends
    exact ⟨origin, ⟨.pad path⟩⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_map.mpr ⟨_, member, rfl⟩) ends
    exact ⟨origin, ⟨.unpad path⟩⟩
  | _, _, _, .familyPad source => exact familyCodeOrigin .familyPad source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, .down source => exact familyCodeOrigin .down source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, .map v source => exact familyCodeOrigin (.map v) source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, .select source selected => exact familyCodeOrigin (.select selected) source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, .focusMinimal source minimal bound => exact familyCodeOrigin (.focusMinimal minimal bound) source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableObs.familyConstantOrigin
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node)
    {demand : Profile n}
    (source : SortableObs env U registry target locals σ (.const name levels) demand footprint)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom) :
    ∃ seed : RetainedRichFamilySeed root env registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.atom atom) := by
  match n, demand, footprint, source with
  | _, _, _, .family found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    have singleton := tree.singleton_of_mem member
    rw [singleton] at tree typed
    obtain ⟨origin⟩ := constantSourceHeader ordered below node found
    let seed := RetainedRichFamilySeed.ofSortable location origin found noDefinition noNative noQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree
    exact ⟨seed, ⟨.refl⟩⟩
  | _, _, _, .legacy source => exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location member ends
  | _, _, _, .code _ source => exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location member ends
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path⟩ := left.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
    · obtain ⟨origin, path⟩ := right.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
  | _, _, _, .pad source =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location ha ends
    exact ⟨origin, ⟨.pad path⟩⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_map.mpr ⟨_, member, rfl⟩) ends
    exact ⟨origin, ⟨.unpad path⟩⟩
  | _, _, _, .view source change =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_singleton_self _)
      (ends.normalAdapterBack ((AtomAction.view change).toGeneralAdapter henv hscoped formed))
    exact ⟨origin, ⟨.action path (.view change)⟩⟩
  | _, _, _, .action source change =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_singleton_self _)
      (ends.normalAdapterBack (change.toGeneralAdapter henv hscoped formed))
    exact ⟨origin, ⟨.action path change⟩⟩
  | _, _, _, .rowShift source =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_singleton_self _)
      ends
    exact ⟨origin, ⟨.action (.pad path) (.view (.commutePadFn _ _))⟩⟩
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

theorem _root_.Lean4Lean.AnchoredSource.Adapted.SortableCert.familyConstantOrigin
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    (location : Located root node)
    {demand : Profile n}
    (source : SortableCert env U registry target locals σ (.const name levels) relevant demand footprint)
    (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom) :
    ∃ seed : RetainedRichFamilySeed root env registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.atom atom) := by
  match n, demand, footprint, source with
  | _, _, _, .ofCode source _ => exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location member ends
  | _, _, _, .observe source _ => exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location member ends
  | _, _, _, .seed source _ => exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location member ends
  | _, _, _, .union left right =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path⟩ := left.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
    · obtain ⟨origin, path⟩ := right.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
  | _, _, _, .pad source =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location ha ends
    exact ⟨origin, ⟨.pad path⟩⟩
  | _, _, _, .unpad source =>
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_map.mpr ⟨_, member, rfl⟩) ends
    exact ⟨origin, ⟨.unpad path⟩⟩
  | _, _, _, .familyPad source => exact familyCodeOrigin .familyPad source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, .down source => exact familyCodeOrigin .down source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, .map v source => exact familyCodeOrigin (.map v) source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, .select source selected => exact familyCodeOrigin (.select selected) source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, .focusMinimal source minimal bound => exact familyCodeOrigin (.focusMinimal minimal bound) source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, .sortPad source => exact familyCodeOrigin .sortPad source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, .support action source => exact familyCodeOrigin (.support action) source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
termination_by sizeOf source
decreasing_by all_goals (simp_wf <;> omega)

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
