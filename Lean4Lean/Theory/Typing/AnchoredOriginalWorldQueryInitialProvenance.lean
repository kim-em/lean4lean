import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryProvenance

/-! Construct actual initial provenance for the legacy and Sortable grammars.
Opening sites come from retained installation proofs and the fixed equation
stratification; no semantic F/R answer is requested. These existence producers
do not assert that the chosen worlds are sponsored by an arbitrary caller.
Full-cutoff header controls are deliberately distinct from such a bound. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut InductiveSignature
open NativeRecursorData (SaturatedProgram saturatedProgram_spec)
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

noncomputable def WorldQuerySite.closedReference
    {registry : CanonicalHead.Registry} {target : List VExpr}
    (strata : EquationStratification env)
    (reference : EndpointRef sourceEnv U [] expression assigned)
    (controls : OriginalWorldControls strata sourceEnv) (σ : Subst) :
    WorldQuerySite (registry := registry) (target := target) strata (.ref reference) [] σ :=
  ⟨.nil, .ofLocation .here .nil, σ, (fun _ => []), .nil, ⟨controls, .nil⟩⟩

private def initialControls (strata : EquationStratification env)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env) (fuel : Nat → Nat) :
    OriginalWorldControls strata sourceEnv :=
  ⟨ordered, strata.rules.length, Nat.le_refl _, strata.fullCutoff.source_mono below, fuel⟩

private def selectedControls (strata : EquationStratification env)
    (selected : strata.Selected rule) (fuel : Nat → Nat) :
    OriginalWorldControls strata selected.origin.source :=
  ⟨selected.origin.ordered, selected.ordinal - 1, Nat.le_trans (Nat.sub_le _ _) selected.ordinal_le,
    selected.sourceCutoff, fuel⟩

mutual
noncomputable def Obs.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : Obs env U registry target locals σ expression profile footprint) : WorldLegacyObsProvenance strata query := by
  match query with
  | .delta (typeRealization := typeRealization) (bodyRealization := bodyRealization) lookup name_eq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    let selected := strata.select registered.2
    exact .delta lookup name_eq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body (CodeCert.initialWorldProvenance strata ordered fuel certificate) (Obs.initialWorldProvenance strata ordered fuel body) selected.origin
        (WorldQuerySite.closedReference strata (.left (EquationHeaderOrigin.instantiatedType selected.origin seedWF))
          (selectedControls strata selected fuel) typeRealization)
        (WorldQuerySite.closedReference strata (.left (EquationHeaderOrigin.instantiatedRhs selected.origin seedWF))
          (selectedControls strata selected fuel) bodyRealization)
  | .native (typeRealization := typeRealization) lookup notDefinition name_eq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    have headerLookup := registered.recursorType signature.typeOrigin
    rw [name_eq] at headerLookup
    let origin := Classical.choice (ordered.constantHeaderOrigin headerLookup)
    exact .native lookup notDefinition name_eq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree (CodeCert.initialWorldProvenance strata ordered fuel typeCertificate) (NativePlan.initialWorldProvenance strata ordered fuel registered seedWF tree) origin rfl (WorldQuerySite.closedReference strata (origin.familyHeader seedWF).reference
        (initialControls strata origin.ordered origin.sourceBelow fuel) typeRealization)
  | .family (typeRealization := typeRealization) lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    let origin := Classical.choice (ordered.constantHeaderOrigin lookup)
    exact .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree (CodeCert.initialWorldProvenance strata ordered fuel typeCertificate) (FamilyPlan.initialWorldProvenance strata ordered fuel tree) origin (WorldQuerySite.closedReference strata (origin.familyHeader seedWF).reference
        (initialControls strata origin.ordered origin.sourceBelow fuel) typeRealization)
  | .constructor (typeRealization := typeRealization) lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    let origin := Classical.choice (ordered.constantHeaderOrigin lookup)
    exact .constructor lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree (CodeCert.initialWorldProvenance strata ordered fuel typeCertificate) (ConstructorPlan.initialWorldProvenance strata ordered fuel tree) origin (WorldQuerySite.closedReference strata (origin.familyHeader seedWF).reference
        (initialControls strata origin.ordered origin.sourceBelow fuel) typeRealization)
  | .var locals σ i demand =>
    exact .var locals σ i demand
  | .empty =>
    exact .empty
  | .sort relevant =>
    exact .sort relevant
  | .app fn arg arguments admitted =>
    exact .app fn arg arguments admitted (Obs.initialWorldProvenance strata ordered fuel fn) (Obs.initialWorldProvenance strata ordered fuel arg)
  | .lam domain guard body normal covered =>
    exact .lam domain guard body normal covered (CodeCert.initialWorldProvenance strata ordered fuel domain) (Obs.initialWorldProvenance strata ordered fuel body)
  | .pi domain guard bodies =>
    exact .pi domain guard bodies (CodeCert.initialWorldProvenance strata ordered fuel domain) (PiRows.initialWorldProvenance strata ordered fuel bodies)
  | .union left right =>
    exact .union left right (Obs.initialWorldProvenance strata ordered fuel left) (Obs.initialWorldProvenance strata ordered fuel right)
  | .view source view =>
    exact .view source view (Obs.initialWorldProvenance strata ordered fuel source)
  | .pad source =>
    exact .pad source (Obs.initialWorldProvenance strata ordered fuel source)
  | .unpad source =>
    exact .unpad source (Obs.initialWorldProvenance strata ordered fuel source)
  | .rowShift source =>
    exact .rowShift source (Obs.initialWorldProvenance strata ordered fuel source)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def CodeCert.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : CodeCert env U registry target locals σ expression profile footprint) : WorldLegacyCertProvenance strata query := by
  match query with
  | .seed observation formed =>
    exact .seed observation formed (Obs.initialWorldProvenance strata ordered fuel observation)
  | .union left right =>
    exact .union left right (CodeCert.initialWorldProvenance strata ordered fuel left) (CodeCert.initialWorldProvenance strata ordered fuel right)
  | .pad source =>
    exact .pad source (CodeCert.initialWorldProvenance strata ordered fuel source)
  | .familyPad source =>
    exact .familyPad source (CodeCert.initialWorldProvenance strata ordered fuel source)
  | .unpad source =>
    exact .unpad source (CodeCert.initialWorldProvenance strata ordered fuel source)
  | .down source =>
    exact .down source (CodeCert.initialWorldProvenance strata ordered fuel source)
  | .map view source =>
    exact .map view source (CodeCert.initialWorldProvenance strata ordered fuel source)
  | .select source member =>
    exact .select source member (CodeCert.initialWorldProvenance strata ordered fuel source)
  | .focusMinimal source minimal bound =>
    exact .focusMinimal source minimal bound (CodeCert.initialWorldProvenance strata ordered fuel source)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def PiRows.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : PiRows env U registry target locals σ A B ambient rows footprint) : WorldLegacyRowsProvenance strata query := by
  match query with
  | .nil =>
    exact .nil
  | .cons guard body normal covered tail =>
    exact .cons guard body normal covered tail (CodeCert.initialWorldProvenance strata ordered fuel body) (PiRows.initialWorldProvenance strata ordered fuel tail)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def NativeCaptures.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : NativeCaptures env U registry target program witnesses count required footprint) : WorldNativeCapturesProvenance strata query := by
  match query with
  | .prefix required =>
    exact .prefix required
  | .index naturalCertificate naturalResources declaredCertificate declaredResources naturalTyped declaredTyped alignment declaredCode nativeValue copiedValue pack covered previous =>
    exact .index naturalCertificate naturalResources declaredCertificate declaredResources naturalTyped declaredTyped alignment declaredCode nativeValue copiedValue pack covered previous (CodeCert.initialWorldProvenance strata ordered fuel naturalCertificate) (CodeCert.initialWorldProvenance strata ordered fuel declaredCertificate) (NativeCaptures.initialWorldProvenance strata ordered fuel previous)
  | .proof instruction captured sourceProof domainProof inhabitant pack previous =>
    exact .proof instruction captured sourceProof domainProof inhabitant pack previous (NativeCaptures.initialWorldProvenance strata ordered fuel previous)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def NativePlan.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    {signature : NativeConstantSignature data levels}
    (registered : NativeRecursorRegistered env data) (levelsWF : ∀ level ∈ levels, level.WF U)
    (query : NativePlan env U registry target signature arguments profile footprint) : WorldNativePlanProvenance strata query := by
  match query with
  | .terminal program selected lhsClosed rhsClosed saturated noTrailing prefix_eq witnesses witnessLength witnessPrefix argumentAlignment arguments_eq body captures =>
    have spec := saturatedProgram_spec selected
    let chosen := strata.select (registered.singletonEquation spec.2.2.2.2.2.2.2.2.1)
    exact .terminal program selected lhsClosed rhsClosed saturated noTrailing prefix_eq witnesses witnessLength witnessPrefix argumentAlignment arguments_eq body captures (Obs.initialWorldProvenance strata ordered fuel body) (NativeCaptures.initialWorldProvenance strata ordered fuel captures) chosen.origin levelsWF
        (WorldQuerySite.closedReference strata (.left (EquationHeaderOrigin.instantiatedRhs chosen.origin levelsWF))
          (selectedControls strata chosen fuel) (nativeCaptureSubst []))
  | .binder domainOrigin domainCode guard body pack covered =>
    exact .binder domainOrigin domainCode guard body pack covered (CodeCert.initialWorldProvenance strata ordered fuel domainCode) (NativePlan.initialWorldProvenance strata ordered fuel registered levelsWF body)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def FamilyCaptures.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : FamilyCaptures env U registry target source locals σ expressions keys footprint) : WorldFamilyCapturesProvenance strata query := by
  match query with
  | .nil =>
    exact .nil
  | .cons lookup value adapter alignment anchor tail =>
    exact .cons lookup value adapter alignment anchor tail (Obs.initialWorldProvenance strata ordered fuel value) (FamilyCaptures.initialWorldProvenance strata ordered fuel tail)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def FamilyPlan.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : FamilyPlan env U registry target name levels signature arguments profile footprint) : WorldLegacyFamilyPlanProvenance strata query := by
  match query with
  | .terminal saturated resultSort relevance captures =>
    exact .terminal saturated resultSort relevance captures (FamilyCaptures.initialWorldProvenance strata ordered fuel captures)
  | .binder domainOrigin domainCode guard body pack covered =>
    exact .binder domainOrigin domainCode guard body pack covered (CodeCert.initialWorldProvenance strata ordered fuel domainCode) (FamilyPlan.initialWorldProvenance strata ordered fuel body)
  | .view source view =>
    exact .view source view (FamilyPlan.initialWorldProvenance strata ordered fuel source)
  | .pad source =>
    exact .pad source (FamilyPlan.initialWorldProvenance strata ordered fuel source)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def ConstructorPlan.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : ConstructorPlan env U registry target name levels signature arguments profile footprint) : WorldLegacyConstructorPlanProvenance strata query := by
  match query with
  | .terminal saturated resultShape relevant captures resultCode =>
    exact .terminal saturated resultShape relevant captures resultCode (FamilyCaptures.initialWorldProvenance strata ordered fuel captures) (CodeCert.initialWorldProvenance strata ordered fuel resultCode)
  | .binder domainOrigin domainCode guard body pack covered =>
    exact .binder domainOrigin domainCode guard body pack covered (CodeCert.initialWorldProvenance strata ordered fuel domainCode) (ConstructorPlan.initialWorldProvenance strata ordered fuel body)
  | .view source view =>
    exact .view source view (ConstructorPlan.initialWorldProvenance strata ordered fuel source)
  | .pad source =>
    exact .pad source (ConstructorPlan.initialWorldProvenance strata ordered fuel source)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def SortableObs.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : SortableObs env U registry target locals σ expression profile footprint) : WorldSortableObsProvenance strata query := by
  match query with
  | .family (typeRealization := typeRealization) lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    let origin := Classical.choice (ordered.constantHeaderOrigin lookup)
    exact .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent signature typeClosed typeCertificate typed tree (SortableCert.initialWorldProvenance strata ordered fuel typeCertificate) (SortableFamilyPlan.initialWorldProvenance strata ordered fuel tree) origin (WorldQuerySite.closedReference strata (origin.familyHeader seedWF).reference
        (initialControls strata origin.ordered origin.sourceBelow fuel) typeRealization)
  | .legacy observation =>
    exact .legacy observation (Obs.initialWorldProvenance strata ordered fuel observation)
  | .code relevant certificate =>
    exact .code relevant certificate (SortableCert.initialWorldProvenance strata ordered fuel certificate)
  | .app fn arg arguments admitted =>
    exact .app fn arg arguments admitted (SortableObs.initialWorldProvenance strata ordered fuel fn) (SortableObs.initialWorldProvenance strata ordered fuel arg)
  | .lam domain guard body normal covered =>
    exact .lam domain guard body normal covered (SortableCert.initialWorldProvenance strata ordered fuel domain) (SortableObs.initialWorldProvenance strata ordered fuel body)
  | .union left right =>
    exact .union left right (SortableObs.initialWorldProvenance strata ordered fuel left) (SortableObs.initialWorldProvenance strata ordered fuel right)
  | .view source view =>
    exact .view source view (SortableObs.initialWorldProvenance strata ordered fuel source)
  | .action source action =>
    exact .action source action (SortableObs.initialWorldProvenance strata ordered fuel source)
  | .pad source =>
    exact .pad source (SortableObs.initialWorldProvenance strata ordered fuel source)
  | .unpad source =>
    exact .unpad source (SortableObs.initialWorldProvenance strata ordered fuel source)
  | .rowShift source =>
    exact .rowShift source (SortableObs.initialWorldProvenance strata ordered fuel source)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def SortableCert.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : SortableCert env U registry target locals σ expression relevant profile footprint) : WorldSortableCertProvenance strata query := by
  match query with
  | .ofCode source formed =>
    exact .ofCode source formed (CodeCert.initialWorldProvenance strata ordered fuel source)
  | .pi domain guard bodies =>
    exact .pi domain guard bodies (SortableCert.initialWorldProvenance strata ordered fuel domain) (SortableRows.initialWorldProvenance strata ordered fuel bodies)
  | .observe observation formed =>
    exact .observe observation formed (SortableObs.initialWorldProvenance strata ordered fuel observation)
  | .seed observation formed =>
    exact .seed observation formed (Obs.initialWorldProvenance strata ordered fuel observation)
  | .union left right =>
    exact .union left right (SortableCert.initialWorldProvenance strata ordered fuel left) (SortableCert.initialWorldProvenance strata ordered fuel right)
  | .pad source =>
    exact .pad source (SortableCert.initialWorldProvenance strata ordered fuel source)
  | .sortPad source =>
    exact .sortPad source (SortableCert.initialWorldProvenance strata ordered fuel source)
  | .familyPad source =>
    exact .familyPad source (SortableCert.initialWorldProvenance strata ordered fuel source)
  | .unpad source =>
    exact .unpad source (SortableCert.initialWorldProvenance strata ordered fuel source)
  | .down source =>
    exact .down source (SortableCert.initialWorldProvenance strata ordered fuel source)
  | .map view source =>
    exact .map view source (SortableCert.initialWorldProvenance strata ordered fuel source)
  | .support action source =>
    exact .support action source (SortableCert.initialWorldProvenance strata ordered fuel source)
  | .select source member =>
    exact .select source member (SortableCert.initialWorldProvenance strata ordered fuel source)
  | .focusMinimal source minimal bound =>
    exact .focusMinimal source minimal bound (SortableCert.initialWorldProvenance strata ordered fuel source)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def SortableRows.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : SortableRows env U registry target locals σ A B relevant ambient rows footprint) : WorldSortableRowsProvenance strata query := by
  match query with
  | .nil =>
    exact .nil
  | .cons guard body normal covered tail =>
    exact .cons guard body normal covered tail (SortableCert.initialWorldProvenance strata ordered fuel body) (SortableRows.initialWorldProvenance strata ordered fuel tail)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

noncomputable def SortableFamilyPlan.initialWorldProvenance (strata : EquationStratification env)
    (ordered : env.Ordered) (fuel : Nat → Nat)
    (query : SortableFamilyPlan env U registry target name levels signature arguments profile footprint) : WorldSortableFamilyPlanProvenance strata query := by
  match query with
  | .terminal saturated resultSort relevance captures =>
    exact .terminal saturated resultSort relevance captures (FamilyCaptures.initialWorldProvenance strata ordered fuel captures)
  | .binder domainOrigin domainCode guard body pack covered =>
    exact .binder domainOrigin domainCode guard body pack covered (SortableCert.initialWorldProvenance strata ordered fuel domainCode) (SortableFamilyPlan.initialWorldProvenance strata ordered fuel body)
  | .view source view =>
    exact .view source view (SortableFamilyPlan.initialWorldProvenance strata ordered fuel source)
  | .pad source =>
    exact .pad source (SortableFamilyPlan.initialWorldProvenance strata ordered fuel source)
termination_by sizeOf query
decreasing_by all_goals simp_wf <;> omega

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
