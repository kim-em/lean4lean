import Lean4Lean.Theory.Typing.AnchoredOriginalLegacyFamilyConstantOrigin

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private familyCodeOrigin from Lean4Lean.Theory.Typing.AnchoredOriginalLegacyFamilyConstantOrigin
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

mutual
theorem RichObs.familyConstantOrigin
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    {demand : Profile n}
    (query : RichObs sourceEnv env U registry target node locals σ demand footprint)
    (location : Located root node) (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom) :
    ∃ seed : RetainedRichFamilySeed root env registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.atom atom) := by
  match n, demand, footprint, assigned, node, query, location with
  | _, _, _, _, _, .family origin found noDefinition noNative noQuotient seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree, location =>
    have singleton := tree.singleton_of_mem member
    rw [singleton] at tree typed
    let seed := RetainedRichFamilySeed.ofNative location origin found noDefinition noNative noQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree
    exact ⟨seed, ⟨.refl⟩⟩
  | _, _, _, _, _, .constructor _ _ _ _ _ _ _ _ _ _ _ _ _ tree, _ =>
    exact (RichConstructorPlan.not_familyEnd henv hscoped formed tree member ends).elim
  | _, _, _, _, _, .delta _ lookup .., _ => rw [notDefinition] at lookup; contradiction
  | _, _, _, _, _, .legacy source, location =>
    exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location member ends
  | _, _, _, _, _, .code source, location => exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location member ends
  | _, _, _, _, _, .route path source, location => exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative (path.locate location) member ends
  | _, _, _, _, _, .union left right, location =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path⟩ := left.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
    · obtain ⟨origin, path⟩ := right.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
  | _, _, _, _, _, .pad source, location =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location ha ends
    exact ⟨origin, ⟨.pad path⟩⟩
  | _, _, _, _, _, .unpad source, location =>
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_map.mpr ⟨_, member, rfl⟩) ends
    exact ⟨origin, ⟨.unpad path⟩⟩
  | _, _, _, _, _, .view source change, location =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_singleton_self _)
      (ends.normalAdapterBack ((AtomAction.view change).toGeneralAdapter henv hscoped formed))
    exact ⟨origin, ⟨.action path (.view change)⟩⟩
  | _, _, _, _, _, .select source selected, location =>
    cases List.mem_singleton.mp member
    exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location selected ends
  | _, _, _, _, _, .action source change, location =>
    cases List.mem_singleton.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location (List.mem_singleton_self _)
      (ends.normalAdapterBack (change.toGeneralAdapter henv hscoped formed))
    exact ⟨origin, ⟨.action path change⟩⟩
termination_by sizeOf query

theorem RichCert.familyConstantOrigin
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    (notDefinition : registry.definitions name = none) (notNative : registry.natives name = none)
    {root : EndpointRef sourceEnv U source rootExpression rootType}
    {node : EndpointState sourceEnv U source (.const name levels) assigned}
    {demand : Profile n}
    (query : RichCert sourceEnv env U registry target node locals σ relevant demand footprint)
    (location : Located root node) (member : atom ∈ demand.atoms) (ends : FamilyEndDemand atom) :
    ∃ seed : RetainedRichFamilySeed root env registry target name levels,
      Nonempty (GeneralOutputPath env U registry target seed.atom atom) := by
  match n, demand, footprint, assigned, node, query, location with
  | _, _, _, _, _, .legacy source, location =>
    exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location member ends
  | _, _, _, _, _, .observe source _, location => exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location member ends
  | _, _, _, _, _, .route path source, location => exact source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative (path.locate location) member ends
  | _, _, _, _, _, .union left right, location =>
    rcases List.mem_append.mp member with h | h
    · obtain ⟨origin, path⟩ := left.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
    · obtain ⟨origin, path⟩ := right.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends
      exact ⟨origin, path⟩
  | _, _, _, _, _, .pad source, location =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, ⟨path⟩⟩ := source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location ha ends
    exact ⟨origin, ⟨.pad path⟩⟩
  | _, _, _, _, _, .down source, location =>
    exact familyCodeOrigin .down source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, _, _, .map view source, location =>
    exact familyCodeOrigin (.map view) source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, _, _, .support action source, location =>
    exact familyCodeOrigin (.support action) source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
  | _, _, _, _, _, .select source selected, location =>
    exact familyCodeOrigin (.select selected) source.formed (fun _ h ends => source.familyConstantOrigin henv hscoped formed ordered below notDefinition notNative location h ends) member ends
termination_by sizeOf query


end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
