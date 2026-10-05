import Lean4Lean.Theory.Typing.AnchoredSortableRealization
import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation

/-! Target extensions transport the complete hereditary query, including
native formation rows in arguments and domains. Original source syntax and
its finite derivation locations remain unchanged. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open private subst_cons_future key_rename_map from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
set_option backward.isDefEq.respectTransparency false

mutual
noncomputable def SortableObs.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {expression : VExpr} {demand : Profile n}
    {footprint : Footprint} (observation : SortableObs env U registry Γ locals σ expression demand footprint) :
    SortableObs env U registry Δ locals (σ.lift_r ρ) expression (demand.rename ρ)
      (Footprint.rename ρ footprint) := by
  match observation with
  | .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    exact .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed (typeCertificate.future henv W) (Profile.rename_hasType_iff.mpr typed)
      (tree.future henv W typeClosed.instL)
  | .legacy source => exact .legacy (source.future henv W)
  | .code relevant source => exact .code relevant (source.future henv W)
  | .action source action =>
    have child := source.future henv W
    rw [Profile.rename_singleton] at child
    simpa only [Profile.rename_singleton] using SortableObs.action child (action.future henv W)
  | .app fn arg arguments admitted =>
    have ihfn := fn.future henv W
    have iharg := arg.future henv W
    simp only [Profile.fn, Profile.rename_singleton, Atom.rename_fn] at ihfn
    have admitted' := Admitted.future henv W admitted
    rw [lift'_subst] at admitted'
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append, lift'_subst] using SortableObs.app ihfn iharg (GeneralNormalProfileAdapter.future henv W arguments) admitted'
  | .lam domain guard body normal covered =>
    have ihdomain := domain.future henv W
    have ihbody := body.future henv W
    rw [subst_cons_future, Profile.rename_singleton] at ihbody
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append] using
      SortableObs.lam ihdomain (guard.future henv W) ihbody (normal.rename ρ)
        (by
          intro atom hm
          obtain ⟨old, hsource, rfl⟩ := List.mem_map.mp hm
          exact List.mem_map_of_mem (covered old hsource))
  | .union left right =>
    simpa only [Profile.rename_union, Footprint.rename_append] using
      SortableObs.union (left.future henv W) (right.future henv W)
  | .view source view =>
    simpa only [Profile.rename_singleton] using
      SortableObs.view (source.future henv W) (view.future henv W)
  | .pad source =>
    simpa only [Profile.rename_pad] using SortableObs.pad (source.future henv W)
  | .unpad source =>
    have ih := source.future henv W
    rw [Profile.rename_pad] at ih
    exact SortableObs.unpad ih
  | .rowShift source =>
    have ih := source.future henv W
    simp only [Profile.fn, Profile.rename_singleton, Atom.rename_fn] at ih
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pad,
      Key.pad_rename] using SortableObs.rowShift ih
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)


noncomputable def SortableCert.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {expression : VExpr} {profile : Profile n}
    {footprint : Footprint} (cert : SortableCert env U registry Γ locals σ expression relevant profile footprint) :
    SortableCert env U registry Δ locals (σ.lift_r ρ) expression relevant (profile.rename ρ)
      (Footprint.rename ρ footprint) := by
  match cert with
  | .seed observation formed =>
    have hf := (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
    rw [Profile.rename_sort] at hf
    exact .seed (observation.future henv W) hf
  | .observe observation formed =>
    have hf := (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
    rw [Profile.rename_sort] at hf
    exact .observe (observation.future henv W) hf
  | .ofCode observation formed =>
    have hf := (Profile.rename_hasType_iff (ρ := ρ)).mpr formed
    rw [Profile.rename_sort] at hf
    exact .ofCode (observation.future henv W) hf
  | .pi domain guard bodies =>
    have hd := domain.future henv W
    have hb := bodies.future henv W
    simpa only [Profile.pi, Profile.rename_singleton, Atom.rename_pi,
      Footprint.rename_append] using SortableCert.pi hd (guard.future henv W) hb
  | .union left right =>
    simpa only [Profile.rename_union, Footprint.rename_append] using
      SortableCert.union (left.future henv W) (right.future henv W)
  | .pad source =>
    simpa only [Profile.rename_pad] using SortableCert.pad (source.future henv W)
  | .sortPad source =>
    have child := source.future henv W
    rw [Profile.rename_sort] at child
    simpa only [Profile.rename_sort] using SortableCert.sortPad child
  | .familyPad source =>
    have child := source.future henv W
    simp only [Profile.rename_singleton, Atom.rename_family] at child
    simpa only [Profile.rename_singleton, Atom.rename_family, FamilyData.rename,
      FamilyData.map_map, Profile.pad_rename, Function.comp_def, id_eq] using
      SortableCert.familyPad child
  | .unpad source =>
    have ih := source.future henv W
    rw [Profile.rename_pad] at ih
    exact SortableCert.unpad ih
  | .down source =>
    simpa only [Profile.down_rename] using SortableCert.down (source.future henv W)
  | .support action source =>
    rw [action.apply_future henv W]
    exact .support (action.future henv W) (source.future henv W)
  | .map view source =>
    have ih := source.future henv W
    simpa only [← AtomView.mapType_future] using
      SortableCert.map (view.future henv W) ih
  | .select source member =>
    simpa only [Profile.rename_singleton] using
      SortableCert.select (source.future henv W) (List.mem_map_of_mem (f := Atom.rename ρ) member)
  | .focusMinimal source minimal bound =>
    exact .focusMinimal (source.future henv W) (minimal.rename ρ)
      (Profile.rename_le_iff.mpr bound)
termination_by sizeOf cert
decreasing_by all_goals (simp_wf <;> omega)

noncomputable def SortableRows.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : SortableRows env U registry Γ locals σ A B relevant ambient rows footprint) :
    SortableRows env U registry Δ locals (σ.lift_r ρ) A B relevant (ambient.rename ρ)
      (Rows.rename ρ rows) (Footprint.rename ρ footprint) := by
  match bodies with
  | .nil => exact .nil
  | .cons guard body normal covered tail =>
    have hb := body.future henv W
    rw [subst_cons_future] at hb
    simpa only [Rows.rename, List.map_cons, Footprint.rename_append] using
      SortableRows.cons (guard.future henv W) hb (normal.rename ρ)
        (by
          intro atom hm
          obtain ⟨old, hsource, rfl⟩ := List.mem_map.mp hm
          exact List.mem_map_of_mem (covered old hsource)) (tail.future henv W)
termination_by sizeOf bodies
decreasing_by all_goals (simp_wf <;> omega)


noncomputable def SortableFamilyPlan.future
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ Δ : List VExpr} {ρ : Lift} (henv : env.Ordered)
    (W : FutureInsertion env U Γ Δ ρ)
    {name : Name} {levels : List VLevel} {declaredType : VExpr}
    {signature : ConstantTelescope declaredType} {arguments : List VExpr}
    (typeClosed : declaredType.Closed)
    {demand : Profile n} {footprint : Footprint}
    (plan : SortableFamilyPlan env U registry Γ name levels signature arguments demand footprint) :
    SortableFamilyPlan env U registry Δ name levels signature (arguments.map (·.lift' ρ))
      (demand.rename ρ) (Footprint.rename ρ footprint) := by
  match plan with
  | .terminal saturated resultSort relevance captures =>
    have captures' := (captures.future henv W).realizePrefix
      (signature.contextClosed typeClosed)
      (nativeCaptureSubst (arguments.map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ
        (by simpa only [List.length_reverse, ← saturated] using hi))
    simpa only [List.length_map, Profile.rename_singleton, Atom.rename_family,
      FamilyData.map] using SortableFamilyPlan.terminal
      (by simpa only [List.length_map] using saturated) resultSort relevance
      (by simpa only [List.length_map, key_rename_map] using captures')
  | .binder origin domainCode guard body pack covered =>
    have scope := signature.domain_scope typeClosed origin
    have domain' := (domainCode.future henv W).realizePrefix scope
      (nativeCaptureSubst (arguments.map (·.lift' ρ)))
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)
    have guard' := guard.future henv W
    have he := subst_congr_closedN scope
      (fun _ hi => nativeCaptureSubst_rename_prefix arguments ρ hi)
    have guard'' : LambdaGuard env U registry Δ
        (nativeCaptureSubst (arguments.map (·.lift' ρ))) _ _ _ :=
      ⟨guard'.inputTyped, guard'.formed, he ▸ guard'.path, he ▸ guard'.domains, guard'.anchor⟩
    have body' := body.future henv W typeClosed
    simp only [List.map_append, List.map_cons, List.map_nil, Profile.rename_singleton] at body'
    simpa only [Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append, List.map_append, List.map_cons, List.map_nil] using
      SortableFamilyPlan.binder (by simpa only [List.length_map] using origin)
        (by simpa only [List.length_map] using domain') guard'' body' (pack.rename ρ)
        (by intro atom hm; obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hm
            exact List.mem_map_of_mem (covered old ho))
  | .view source view =>
    simpa only [Profile.rename_singleton] using
      SortableFamilyPlan.view (source.future henv W typeClosed) (view.future henv W)
  | .pad source =>
    simpa only [Profile.rename_pad] using SortableFamilyPlan.pad (source.future henv W typeClosed)
termination_by sizeOf plan
decreasing_by all_goals (simp_wf <;> omega)


end
end Lean4Lean.AnchoredSource.Adapted
