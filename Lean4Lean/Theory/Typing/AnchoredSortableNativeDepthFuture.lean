import Lean4Lean.Theory.Typing.AnchoredNativeDepthFuture
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthRealization
import Lean4Lean.Theory.Typing.AnchoredSortableFuture

/-! The actual target-future operation preserves every native source node.
Scope-directed realization changes only rename target operands; they do not
create observations or spend declaration-stage depth. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open InductiveSignature NativeRecursorData
open private subst_cons_future from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
variable {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
  {Γ Δ : List VExpr} {ρ : Lift}

mutual
@[simp] theorem SortableObs.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {expression : VExpr} {demand : Profile n}
    {footprint : Footprint} (observation : SortableObs env U registry Γ locals σ expression demand footprint) :
    (observation.future henv W).nativeDepth current = observation.nativeDepth current := by
  match observation with
  | .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    simp only [SortableObs.future, SortableObs.nativeDepth,
      tree.nativeDepth_future current henv W typeClosed.instL,
      typeCertificate.nativeDepth_future current henv W]
  | .legacy child | .code _ child =>
    simpa only [SortableObs.future, SortableObs.nativeDepth] using child.nativeDepth_future current henv W
  | .app fn arg arguments admitted =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableObs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, SortableObs.nativeDepth, SortableObs.nativeDepth_mp, SortableObs.nativeDepth_mpr,
      fn.nativeDepth_future current henv W, arg.nativeDepth_future current henv W]
  | .lam domain guard body pack covered =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableObs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, SortableObs.nativeDepth, SortableObs.nativeDepth_mp, SortableObs.nativeDepth_mpr,
      domain.nativeDepth_future current henv W, body.nativeDepth_future current henv W]
  | .union left right =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableObs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, SortableObs.nativeDepth, SortableObs.nativeDepth_mp, SortableObs.nativeDepth_mpr,
      left.nativeDepth_future current henv W, right.nativeDepth_future current henv W]
  | .action source action | .view source view | .pad source | .unpad source | .rowShift source =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableObs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, SortableObs.nativeDepth, SortableObs.nativeDepth_mp, SortableObs.nativeDepth_mpr,
      source.nativeDepth_future current henv W]
termination_by sizeOf observation
decreasing_by all_goals (simp_wf <;> omega)

@[simp] theorem SortableCert.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {expression : VExpr} {demand : Profile n}
    {footprint : Footprint} (certificate : SortableCert env U registry Γ locals σ expression relevant demand footprint) :
    (certificate.future henv W).nativeDepth current = certificate.nativeDepth current := by
  match certificate with
  | .ofCode observation formed | .observe observation formed | .seed observation formed =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableCert.future, Profile.rename_sort, SupportAction.apply_future, Profile.rename_singleton, Profile.rename_union, Profile.rename_pad,
      Profile.down_rename, ← AtomView.mapType_future, Footprint.rename_append, SortableCert.nativeDepth, observation.nativeDepth_future current henv W]
  | .pi domain guard bodies =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableCert.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, SortableCert.nativeDepth, SortableCert.nativeDepth_mp, SortableCert.nativeDepth_mpr,
      domain.nativeDepth_future current henv W, bodies.nativeDepth_future current henv W]
  | .union left right =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableCert.future, Profile.rename_sort, SupportAction.apply_future, Profile.rename_singleton, Profile.rename_union, Profile.rename_pad,
      Profile.down_rename, ← AtomView.mapType_future, Footprint.rename_append, SortableCert.nativeDepth, SortableCert.nativeDepth_mp, SortableCert.nativeDepth_mpr,
      left.nativeDepth_future current henv W, right.nativeDepth_future current henv W]
  | .familyPad source =>
    simp only [SortableCert.future, Profile.rename_sort, SupportAction.apply_future, Profile.rename_singleton, Atom.rename_family,
      FamilyData.rename, FamilyData.map_map, Profile.pad_rename, Function.comp_def, id_eq,
      SortableCert.nativeDepth, SortableCert.nativeDepth_mp, SortableCert.nativeDepth_mpr,
      source.nativeDepth_future current henv W]
  | .support action source =>
    rw [SortableCert.future]
    rw [SortableCert.nativeDepth_mpr current rfl rfl (action.apply_future henv W _).symm rfl]
    simp only [SortableCert.nativeDepth]
    exact source.nativeDepth_future current henv W
  | .sortPad source | .pad source | .unpad source | .down source | .map _ source | .select source _ | .focusMinimal source _ _ =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableCert.future, Profile.rename_sort, SupportAction.apply_future, Profile.rename_singleton, Profile.rename_union, Profile.rename_pad,
      Profile.down_rename, ← AtomView.mapType_future, Footprint.rename_append, SortableCert.nativeDepth, SortableCert.nativeDepth_mp, SortableCert.nativeDepth_mpr,
      source.nativeDepth_future current henv W]
termination_by sizeOf certificate
decreasing_by all_goals (simp_wf <;> omega)

@[simp] theorem SortableRows.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : SortableRows env U registry Γ locals σ A B relevant ambient rows footprint) :
    (bodies.future henv W).nativeDepth current = bodies.nativeDepth current := by
  match bodies with
  | .nil => simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableRows.future, SortableRows.nativeDepth]
  | .cons guard body pack covered tail =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableRows.future, Rows.rename, List.map_cons, Footprint.rename_append, subst_cons_future, SortableRows.nativeDepth, SortableRows.nativeDepth_mp, SortableRows.nativeDepth_mpr,
      SortableCert.nativeDepth_mp, SortableCert.nativeDepth_mpr, body.nativeDepth_future current henv W,
      tail.nativeDepth_future current henv W]
termination_by sizeOf bodies
decreasing_by all_goals (simp_wf <;> omega)
@[simp] theorem SortableFamilyPlan.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {name : Name} {levels : List VLevel}
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    (typeClosed : declaredType.Closed)
    (plan : SortableFamilyPlan env U registry Γ name levels signature arguments demand footprint) :
    (plan.future henv W typeClosed).nativeDepth current = plan.nativeDepth current := by
  match plan with
  | .terminal saturated resultSort relevance captures =>
    simp only [SortableFamilyPlan.future, id_eq, List.length_map, Profile.rename_singleton, Atom.rename_family,
      FamilyData.map, DataRequest.rename, DataRequest.map, KeyData.map,
      SortableFamilyPlan.nativeDepth, SortableFamilyPlan.nativeDepth_mpr, SortableFamilyPlan.nativeDepth_mp,
      FamilyCaptures.nativeDepth_mpr, FamilyCaptures.nativeDepth_mp,
      FamilyCaptures.nativeDepth_realizePrefix, captures.nativeDepth_future current henv W]
    exact (FamilyCaptures.nativeDepth_mp current rfl rfl rfl rfl rfl _ _).trans
      ((FamilyCaptures.nativeDepth_realizePrefix current _ _ _ _).trans
        (captures.nativeDepth_future current henv W))
  | .binder origin domain guard body pack covered =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, SortableFamilyPlan.future, Profile.fn,
      Profile.rename_singleton, Atom.rename_fn, Footprint.rename_append, List.length_map,
      List.map_cons, List.map_nil, SortableFamilyPlan.nativeDepth,
      SortableFamilyPlan.nativeDepth_mpr, SortableFamilyPlan.nativeDepth_mp,
      SortableCert.nativeDepth_mpr, SortableCert.nativeDepth_mp, SortableCert.nativeDepth_realizePrefix,
      domain.nativeDepth_future current henv W, body.nativeDepth_future current henv W typeClosed]
  | .view source view | .pad source =>
    simp only [SortableFamilyPlan.future, id_eq, Profile.rename_singleton, Profile.rename_pad,
      SortableFamilyPlan.nativeDepth, SortableFamilyPlan.nativeDepth_mpr, SortableFamilyPlan.nativeDepth_mp,
      source.nativeDepth_future current henv W typeClosed]
termination_by sizeOf plan
decreasing_by all_goals (simp_wf <;> omega)

end

end Lean4Lean.AnchoredSource.Adapted
