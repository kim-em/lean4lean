import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSortableSyntax
import Lean4Lean.Theory.Typing.AnchoredSortableFuture
import Lean4Lean.Theory.Typing.AnchoredDomainChainTransport
import Lean4Lean.Theory.Typing.AnchoredLiteralRecord
import Lean4Lean.Theory.Typing.AnchoredGeneralOutputPathFuture

/-! Future transport of complete endpoint-indexed queries. Original endpoints,
conversion routes and projection metadata remain fixed; only the target
world, realization, profiles and finite resources are renamed. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private subst_cons_future key_rename_map from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
open private head_lift from Lean4Lean.Theory.Typing.AnchoredProjectionOriginTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable def RecipeResourceTransfer.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (transfer : RecipeResourceTransfer env U registry Γ locals σ required footprint) :
    RecipeResourceTransfer env U registry Δ locals (σ.lift_r ρ)
      (Footprint.rename ρ required) (Footprint.rename ρ footprint) := by
  induction transfer with
  | nil => exact .nil
  | cons query tail ih =>
    simpa only [Footprint.rename, List.map_cons, List.map_append, Need.rename] using
      RecipeResourceTransfer.cons (query.future henv W) ih

mutual
noncomputable def RichCert.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (certificate : RichCert sourceEnv env U registry Γ node locals σ relevant profile footprint) :
    RichCert sourceEnv env U registry Δ node locals (σ.lift_r ρ) relevant (profile.rename ρ)
      (Footprint.rename ρ footprint) := by
  match certificate with
  | .legacy source => exact .legacy (source.future henv W)
  | .recipe code => exact .recipe (code.future henv W)
  | .observe source formed =>
    exact .observe (source.future henv W) (by
      simpa only [Profile.rename_sort] using (Profile.rename_hasType_iff (ρ := ρ)).mpr formed)
  | .pi hu hv domain guard rows =>
    simpa only [Profile.pi, Profile.rename_singleton, Atom.rename_pi, Footprint.rename_append] using
      RichCert.pi hu hv (domain.future henv W) (guard.future henv W) (rows.future henv W)
  | .route path source => exact .route path (source.future henv W)
  | .union first second =>
    simpa only [Profile.rename_union, Footprint.rename_append] using
      RichCert.union (first.future henv W) (second.future henv W)
  | .pad source => simpa only [Profile.rename_pad] using RichCert.pad (source.future henv W)
  | .down source => simpa only [Profile.down_rename] using RichCert.down (source.future henv W)
  | .map view source =>
    simpa only [← AtomView.mapType_future] using RichCert.map (view.future henv W) (source.future henv W)
  | .support action source =>
    rw [action.apply_future henv W]
    exact .support (action.future henv W) (source.future henv W)
  | .select source member =>
    simpa only [Profile.rename_singleton] using
      RichCert.select (source.future henv W) (List.mem_map_of_mem (f := Atom.rename ρ) member)
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichRows.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (rows : RichRows sourceEnv env U registry Γ domain body locals σ relevant ambient values footprint) :
    RichRows sourceEnv env U registry Δ domain body locals (σ.lift_r ρ) relevant (ambient.rename ρ)
      (Rows.rename ρ values) (Footprint.rename ρ footprint) := by
  match rows with
  | .nil => exact .nil
  | .cons guard code pack covered tail =>
    have child := code.future henv W
    rw [subst_cons_future] at child
    simpa only [Rows.rename, List.map_cons, Footprint.rename_append] using
      RichRows.cons (guard.future henv W) child (pack.rename ρ)
        (by
          intro atom member
          obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
          exact List.mem_map_of_mem (covered old oldMember)) (tail.future henv W)
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichObs.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (observation : RichObs sourceEnv env U registry Γ node locals σ profile footprint) :
    RichObs sourceEnv env U registry Δ node locals (σ.lift_r ρ) (profile.rename ρ)
      (Footprint.rename ρ footprint) := by
  match observation with
  | .rigidFamily (name := name) (frozenLevels := frozenLevels) (node := node) origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq typeClosed plan certificate ready typed =>
    have typed' := (Profile.rename_hasType_iff (ρ := ρ)).mpr typed
    have atomEq := plan.atom_rename ρ name frozenLevels []
    simp only [List.map_nil] at atomEq
    simpa only [Footprint.rename, List.map_nil, Profile.rename_singleton, ← atomEq] using
      RichObs.rigidFamily (node := node) origin lookup inert seedWF seedLength frozenWF levelsWF
        seedFrozen frozenLevelsEq typeClosed (plan.rename ρ)
        (by simpa only [Footprint.rename, List.map_nil] using certificate.future henv W)
        (plan.ready_transport ready (Admitted.future henv W))
        (by simpa only [Profile.rename_singleton, ← atomEq] using typed')
  | .family (name := name) (levels := levels) (node := node) origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    simpa only [Footprint.rename, List.map_nil] using
      RichObs.family (node := node) origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
        signature typeClosed (typeCertificate.future henv W) (Profile.rename_hasType_iff.mpr typed)
        (tree.future henv W)
  | .constructor (name := name) (levels := levels) (node := node) origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    simpa only [Footprint.rename, List.map_nil] using
      RichObs.constructor (node := node) origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
        signature typeClosed (typeCertificate.future henv W) (Profile.rename_hasType_iff.mpr typed)
        (tree.future henv W)
  | .canonicalDelta (strata := strata) (node := node) lookup nameEq registered seedWF seedLength levelsWF
      equivalent bodyClosed typeClosed certificate typed body =>
    simpa only [Footprint.rename, List.map_nil] using
      RichObs.canonicalDelta (strata := strata) (node := node) lookup nameEq registered seedWF seedLength levelsWF
        equivalent bodyClosed typeClosed (certificate.future henv W)
        (Profile.rename_hasType_iff.mpr typed) (body.future henv W)
  | .canonicalConst (name := name) (levels := levels) (node := node) origin realization child resources =>
    simpa only [Footprint.rename, List.map_nil] using
      RichObs.canonicalConst origin (realization.lift_r ρ) (child.future henv W) (by
        intro i need member
        obtain ⟨⟨j, original⟩, present, _⟩ := List.mem_map.mp member
        have impossible : original ∈ ([] : List Need) := resources j original present
        cases impossible)
  | .legacy source => exact .legacy (source.future henv W)
  | .code source => exact .code (source.future henv W)
  | .projection (record := record) (request := request) head nameEq member major field typed alignment =>
    have major' := major.future henv W
    simp only [Profile.rename_singleton, Atom.rename_record, RecordData.rename] at major'
    have alignment' := alignment.future henv W
    rw [lift'_subst] at alignment'
    simpa only [Footprint.rename_append, DataRequest.rename, DataRequest.map, KeyData.map] using
      RichObs.projection (record := record.rename ρ) (request := request.rename ρ) head nameEq
        (List.mem_map.mpr ⟨(_, request), member, rfl⟩) major' (field.future henv W)
        (Profile.rename_hasType_iff.mpr typed) alignment'
  | .projectionSortable (record := record) (request := request) head nameEq member major
      selected path sortable field typed =>
    have major' := major.future henv W
    simp only [Profile.rename_singleton, Atom.rename_record, RecordData.rename] at major'
    simpa only [Profile.rename_singleton, Footprint.rename_append] using
      RichObs.projectionSortable (record := record.rename ρ) (request := request.rename ρ) head nameEq
        (List.mem_map.mpr ⟨(_, request), member, rfl⟩) major'
        (List.mem_map_of_mem (f := Atom.rename ρ) selected) (path.future henv W)
        (by simpa only [Profile.rename_singleton, Profile.rename_sort] using
          (Profile.rename_hasType_iff (ρ := ρ)).mpr sortable)
        (field.future henv W)
        (by simpa only [Profile.rename_singleton] using
          (Profile.rename_hasType_iff (ρ := ρ)).mpr typed)
  | .app (domain := domain) (body := body) (result := result) hu hv fn arg arguments admitted =>
    have child := fn.future henv W
    simp only [Profile.fn, Profile.rename_singleton, Atom.rename_fn] at child
    have admitted' := Admitted.future henv W admitted
    rw [lift'_subst] at admitted'
    simpa only [Profile.rename_singleton, Footprint.rename_append] using
      RichObs.app (domain := domain) (body := body) (result := result) hu hv child (arg.future henv W)
        (GeneralNormalProfileAdapter.future henv W arguments) admitted'
  | .lam (codomain := codomain) hu hv domain guard body pack covered =>
    have child := body.future henv W
    rw [subst_cons_future, Profile.rename_singleton] at child
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn, Footprint.rename_append] using
      RichObs.lam (codomain := codomain) hu hv (domain.future henv W) (guard.future henv W) child
        (pack.rename ρ) (by
          intro atom member
          obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
          exact List.mem_map_of_mem (covered old oldMember))
  | .route path source => exact .route path (source.future henv W)
  | .union first second =>
    simpa only [Profile.rename_union, Footprint.rename_append] using
      RichObs.union (first.future henv W) (second.future henv W)
  | .view source view =>
    simpa only [Profile.rename_singleton] using RichObs.view (source.future henv W) (view.future henv W)
  | .action source action =>
    simpa only [Profile.rename_singleton] using RichObs.action (source.future henv W) (action.future henv W)
  | .select source member =>
    simpa only [Profile.rename_singleton] using
      RichObs.select (source.future henv W) (List.mem_map_of_mem (f := Atom.rename ρ) member)
  | .pad source => simpa only [Profile.rename_pad] using RichObs.pad (source.future henv W)
  | .unpad source =>
    have child := source.future henv W
    rw [Profile.rename_pad] at child
    exact RichObs.unpad child
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega
noncomputable def RichFamilyPlan.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (plan : RichFamilyPlan env U registry Γ header name levels signature context σ arguments demand footprint) :
    RichFamilyPlan env U registry Δ header name levels signature context (σ.lift_r ρ)
      (arguments.map (·.lift' ρ)) (demand.rename ρ) (Footprint.rename ρ footprint) := by
  match plan with
  | .terminal saturated resultSort relevance captures =>
    simpa only [List.length_map, Profile.rename_singleton, Atom.rename_family, FamilyData.map,
      key_rename_map] using
      RichFamilyPlan.terminal (header := header) (context := context)
        (arguments := arguments.map (·.lift' ρ))
        (by simpa only [List.length_map] using saturated) resultSort relevance (by simpa only [List.length_map, key_rename_map] using captures.future henv W)
  | .binder origin original location lineage domain guard body pack covered =>
    have child := body.future henv W
    rw [subst_cons_future] at child
    simp only [List.map_append, List.map_cons, List.map_nil, Profile.rename_singleton] at child
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn, Footprint.rename_append] using
      RichFamilyPlan.binder (arguments := arguments.map (·.lift' ρ))
        (by simpa only [List.length_map] using origin) original location lineage
        (by simpa only [List.length_map] using domain.future henv W)
        (guard.future henv W) child (pack.rename ρ)
        (by intro atom member; obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
            exact List.mem_map_of_mem (covered old oldMember))
  | .view source view =>
    simpa only [Profile.rename_singleton] using RichFamilyPlan.view (source.future henv W) (view.future henv W)
  | .pad source => simpa only [Profile.rename_pad] using RichFamilyPlan.pad (source.future henv W)
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega
noncomputable def RichConstructorPlan.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (plan : RichConstructorPlan env U registry Γ header name levels signature context σ arguments demand footprint) :
    RichConstructorPlan env U registry Δ header name levels signature context (σ.lift_r ρ)
      (arguments.map (·.lift' ρ)) (demand.rename ρ) (Footprint.rename ρ footprint) := by
  match plan with
  | .terminal (family := family) (keys := keys) saturated resultShape relevant resultNode resultLocation resultLineage captures resultCode =>
    simpa only [List.length_map, Profile.rename_singleton, Atom.rename_ctor,
      ConstructorData.map, FamilyData.rename, FamilyData.map, key_rename_map, Footprint.rename_append] using
      RichConstructorPlan.terminal (header := header) (context := context)
        (arguments := arguments.map (·.lift' ρ))
        (family := family.rename ρ) (keys := keys.map (DataRequest.rename ρ))
        (by simpa only [List.length_map] using saturated) resultShape relevant
        resultNode resultLocation resultLineage
        (by simpa only [List.length_map, key_rename_map] using captures.future henv W)
        (by simpa only [List.length_map, Profile.rename_singleton, Atom.rename_family,
          FamilyData.rename] using resultCode.future henv W)
  | .terminalRecord (demand := demand) registered lookup constructorName bounded saturated
      resultShape resultNode resultLocation resultLineage captures resultCode origins =>
    simpa only [List.length_map, Profile.rename_singleton, Atom.rename_record,
      RecordData.rename, Footprint.rename_append] using
      RichConstructorPlan.terminalRecord (header := header) (context := context)
        (arguments := arguments.map (·.lift' ρ)) (demand := demand.rename ρ)
        registered lookup constructorName
        (by
          intro entry member
          change entry ∈ demand.fields.map (fun old => (old.1, old.2.rename ρ)) at member
          obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
          exact bounded old oldMember)
        (by simpa only [List.length_map] using saturated) resultShape
        resultNode resultLocation resultLineage
        (by simpa only [List.length_map, RecordData.rename, RecordData.map,
          List.map_map, Function.comp_def, key_rename_map] using captures.future henv W)
        (by simpa only [List.length_map, Profile.rename_singleton, Atom.rename_family,
          RecordData.rename, RecordData.map, FamilyData.rename] using resultCode.future henv W)
        (by
          intro entry member
          change entry ∈ demand.fields.map (fun old => (old.1, old.2.rename ρ)) at member
          obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
          obtain ⟨origin⟩ := origins old oldMember
          exact ⟨by simpa only [RecordData.rename, RecordData.map, FamilyData.rename,
            FamilyData.map, DataRequest.rename, DataRequest.map, KeyData.map, List.length_map,
            head_lift, List.map_map, Function.comp_def, lift'_subst] using origin.future henv W⟩)
  | .binder origin original location lineage domain guard body pack covered =>
    have child := body.future henv W
    rw [subst_cons_future] at child
    simp only [List.map_append, List.map_cons, List.map_nil, Profile.rename_singleton] at child
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn, Footprint.rename_append] using
      RichConstructorPlan.binder (arguments := arguments.map (·.lift' ρ))
        (by simpa only [List.length_map] using origin) original location lineage
        (by simpa only [List.length_map] using domain.future henv W)
        (guard.future henv W) child (pack.rename ρ)
        (by intro atom member; obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
            exact List.mem_map_of_mem (covered old oldMember))
  | .view source view =>
    simpa only [Profile.rename_singleton] using RichConstructorPlan.view (source.future henv W) (view.future henv W)
  | .pad source => simpa only [Profile.rename_pad] using RichConstructorPlan.pad (source.future henv W)
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

noncomputable def RichCodeRecipe.future
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    (recipe : RichCodeRecipe env U registry Γ source locals σ expression relevant profile footprint) :
    RichCodeRecipe env U registry Δ source locals (σ.lift_r ρ) expression relevant
      (profile.rename ρ) (Footprint.rename ρ footprint) := by
  match recipe with
  | .root source locals σ owner node closed expressionEq realization certificate resources =>
    exact .root source locals (σ.lift_r ρ) owner node closed expressionEq
      (realization.lift_r ρ) (certificate.future henv W) (by
        intro i need member
        obtain ⟨⟨j, original⟩, present, _⟩ := List.mem_map.mp member
        have impossible : original ∈ ([] : List Need) := resources j original present
        cases impossible)
  | .domain parent =>
    have changed := parent.future henv W
    simp only [Profile.pi, Profile.rename_singleton, Atom.rename_pi] at changed
    exact .domain changed
  | .body (σ := σ) parent selected anchor =>
    have changed := parent.future henv W
    simp only [Profile.pi, Profile.rename_singleton, Atom.rename_pi] at changed
    have output := RichCodeRecipe.body (σ := σ.lift_r ρ) changed
      (List.mem_map_of_mem (f := fun entry => (entry.1.rename ρ, entry.2.rename ρ)) selected)
      (by simpa only [Key.rename, Subst.lift_r] using congrArg (VExpr.lift' · ρ) anchor)
    simpa only [Footprint.rename, Footprint.sourceLift, List.map_cons, List.map_map,
      Function.comp_def, Need.rename, Key.rename] using output
  | .fixedBody parent selected admitted =>
    have changed := parent.future henv W
    simp only [Profile.pi, Profile.rename_singleton, Atom.rename_pi] at changed
    exact .fixedBody changed
      (List.mem_map_of_mem (f := fun entry => (entry.1.rename ρ, entry.2.rename ρ)) selected)
      (Admitted.future henv W admitted)
  | .resources parent transfer => exact .resources (parent.future henv W) (transfer.future henv W)
  | .action change parent => exact .action (change.future henv W) (parent.future henv W)
termination_by sizeOf recipe
decreasing_by all_goals simp_wf <;> omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
