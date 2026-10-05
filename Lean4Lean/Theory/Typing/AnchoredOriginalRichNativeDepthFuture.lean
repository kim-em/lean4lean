import Lean4Lean.Theory.Typing.AnchoredOriginalRichNativeDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFuture
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthFuture

/-! Target future insertion preserves every rich declaration control on the
actual transported query, including the two earlier-source delta children. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private subst_cons_future key_rename_map from Lean4Lean.Theory.Typing.AnchoredAdaptedSourceObservation
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

@[simp] theorem RichObs.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : RichObs sourceEnv env U registry target node ls σ p f = RichObs sourceEnv env U registry target node ms τ q g)
    (query : RichObs sourceEnv env U registry target node ls σ p f) :
    (equal.mp query).nativeDepth current = query.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem RichObs.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : RichObs sourceEnv env U registry target node ms τ q g = RichObs sourceEnv env U registry target node ls σ p f)
    (query : RichObs sourceEnv env U registry target node ls σ p f) :
    (equal.mpr query).nativeDepth current = query.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem RichCert.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : RichCert sourceEnv env U registry target node ls σ relevant p f = RichCert sourceEnv env U registry target node ms τ relevant q g)
    (query : RichCert sourceEnv env U registry target node ls σ relevant p f) :
    (equal.mp query).nativeDepth current = query.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem RichCert.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : RichCert sourceEnv env U registry target node ms τ relevant q g = RichCert sourceEnv env U registry target node ls σ relevant p f)
    (query : RichCert sourceEnv env U registry target node ls σ relevant p f) :
    (equal.mpr query).nativeDepth current = query.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem RichRows.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {rs ss : List (Key n × Profile n)} {f g : Footprint}
    (realization : σ = τ) (profile : p = q) (rows : rs = ss) (footprint : f = g)
    (equal : RichRows sourceEnv env U registry target domain body locals σ relevant p rs f = RichRows sourceEnv env U registry target domain body locals τ relevant q ss g)
    (query : RichRows sourceEnv env U registry target domain body locals σ relevant p rs f) :
    (equal.mp query).nativeDepth current = query.nativeDepth current := by
  cases realization; cases profile; cases rows; cases footprint; cases equal; rfl

@[simp] theorem RichRows.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {rs ss : List (Key n × Profile n)} {f g : Footprint}
    (realization : σ = τ) (profile : p = q) (rows : rs = ss) (footprint : f = g)
    (equal : RichRows sourceEnv env U registry target domain body locals τ relevant q ss g = RichRows sourceEnv env U registry target domain body locals σ relevant p rs f)
    (query : RichRows sourceEnv env U registry target domain body locals σ relevant p rs f) :
    (equal.mpr query).nativeDepth current = query.nativeDepth current := by
  cases realization; cases profile; cases rows; cases footprint; cases equal; rfl


@[simp] theorem RichFamilyPlan.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (realization : σ = τ) (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : RichFamilyPlan env U registry target header name levels signature context σ as p f =
      RichFamilyPlan env U registry target header name levels signature context τ bs q g)
    (plan : RichFamilyPlan env U registry target header name levels signature context σ as p f) :
    (equal.mp plan).nativeDepth current = plan.nativeDepth current := by
  cases realization; cases arguments; cases profile; cases footprint; cases equal; rfl

@[simp] theorem RichFamilyPlan.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (realization : σ = τ) (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : RichFamilyPlan env U registry target header name levels signature context τ bs q g =
      RichFamilyPlan env U registry target header name levels signature context σ as p f)
    (plan : RichFamilyPlan env U registry target header name levels signature context σ as p f) :
    (equal.mpr plan).nativeDepth current = plan.nativeDepth current := by
  cases realization; cases arguments; cases profile; cases footprint; cases equal; rfl


@[simp] theorem RichConstructorPlan.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (realization : σ = τ) (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : RichConstructorPlan env U registry target header name levels signature context σ as p f =
      RichConstructorPlan env U registry target header name levels signature context τ bs q g)
    (plan : RichConstructorPlan env U registry target header name levels signature context σ as p f) :
    (equal.mp plan).nativeDepth current = plan.nativeDepth current := by
  cases realization; cases arguments; cases profile; cases footprint; cases equal; rfl

@[simp] theorem RichConstructorPlan.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {as bs : List VExpr} {p q : Profile n} {f g : Footprint}
    (realization : σ = τ) (arguments : as = bs) (profile : p = q) (footprint : f = g)
    (equal : RichConstructorPlan env U registry target header name levels signature context τ bs q g =
      RichConstructorPlan env U registry target header name levels signature context σ as p f)
    (plan : RichConstructorPlan env U registry target header name levels signature context σ as p f) :
    (equal.mpr plan).nativeDepth current = plan.nativeDepth current := by
  cases realization; cases arguments; cases profile; cases footprint; cases equal; rfl


@[simp] theorem RichCodeRecipe.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : RichCodeRecipe env U registry target source ls σ expression relevant p f =
      RichCodeRecipe env U registry target source ms τ expression relevant q g)
    (recipe : RichCodeRecipe env U registry target source ls σ expression relevant p f) :
    (equal.mp recipe).nativeDepth current = recipe.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl

@[simp] theorem RichCodeRecipe.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {p q : Profile n} {f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (profile : p = q) (footprint : f = g)
    (equal : RichCodeRecipe env U registry target source ms τ expression relevant q g =
      RichCodeRecipe env U registry target source ls σ expression relevant p f)
    (recipe : RichCodeRecipe env U registry target source ls σ expression relevant p f) :
    (equal.mpr recipe).nativeDepth current = recipe.nativeDepth current := by
  cases locals; cases realization; cases profile; cases footprint; cases equal; rfl


@[simp] theorem RecipeResourceTransfer.nativeDepth_mp (current : Name → Bool)
    {σ τ : Subst} {r s f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (required : r = s) (footprint : f = g)
    (equal : RecipeResourceTransfer env U registry target ls σ r f =
      RecipeResourceTransfer env U registry target ms τ s g)
    (transfer : RecipeResourceTransfer env U registry target ls σ r f) :
    (equal.mp transfer).nativeDepth current = transfer.nativeDepth current := by
  cases locals; cases realization; cases required; cases footprint; cases equal; rfl

@[simp] theorem RecipeResourceTransfer.nativeDepth_mpr (current : Name → Bool)
    {σ τ : Subst} {r s f g : Footprint} {ls ms : List Nat}
    (locals : ls = ms) (realization : σ = τ) (required : r = s) (footprint : f = g)
    (equal : RecipeResourceTransfer env U registry target ms τ s g =
      RecipeResourceTransfer env U registry target ls σ r f)
    (transfer : RecipeResourceTransfer env U registry target ls σ r f) :
    (equal.mpr transfer).nativeDepth current = transfer.nativeDepth current := by
  cases locals; cases realization; cases required; cases footprint; cases equal; rfl

theorem RecipeResourceTransfer.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (transfer : RecipeResourceTransfer env U registry Γ locals σ required footprint) :
    (transfer.future henv W).nativeDepth current = transfer.nativeDepth current := by
  induction transfer with
  | nil => rfl
  | cons query tail ih =>
    simp only [RecipeResourceTransfer.future, RecipeResourceTransfer.nativeDepth,
      Footprint.rename, List.map_cons, List.map_append, Need.rename,
      RecipeResourceTransfer.nativeDepth_mp, RecipeResourceTransfer.nativeDepth_mpr,
      query.nativeDepth_future current henv W]
    exact congrArg (max (query.nativeDepth current)) ih


mutual
theorem RichCert.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (certificate : RichCert sourceEnv env U registry Γ node locals σ relevant profile footprint) :
    (certificate.future henv W).nativeDepth current = certificate.nativeDepth current := by
  match certificate with
  | .legacy source => simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichCert.future, RichCert.nativeDepth, source.nativeDepth_future]
  | .recipe recipe =>
    simp only [RichCert.future, RichCert.nativeDepth, recipe.nativeDepth_future current henv W]
  | .observe source formed =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichCert.future, RichCert.nativeDepth, source.nativeDepth_future current henv W]
  | .pi hu hv domain guard rows =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichCert.future, RichCert.nativeDepth, domain.nativeDepth_future current henv W,
      rows.nativeDepth_future current henv W]
  | .route path source =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichCert.future, RichCert.nativeDepth, source.nativeDepth_future current henv W]
  | .union first second =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichCert.future, RichCert.nativeDepth, first.nativeDepth_future current henv W,
      second.nativeDepth_future current henv W]
  | .support action source =>
    rw [RichCert.future]
    rw [RichCert.nativeDepth_mpr current rfl rfl (action.apply_future henv W _).symm rfl]
    simp only [RichCert.nativeDepth]
    exact source.nativeDepth_future current henv W
  | .pad source | .down source | .map view source | .select source member =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichCert.future, RichCert.nativeDepth, source.nativeDepth_future current henv W]
termination_by sizeOf certificate
decreasing_by all_goals simp_wf <;> omega

theorem RichRows.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (rows : RichRows sourceEnv env U registry Γ domain body locals σ relevant ambient values footprint) :
    (rows.future henv W).nativeDepth current = rows.nativeDepth current := by
  match rows with
  | .nil => simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichRows.future, RichRows.nativeDepth]
  | .cons guard code pack covered tail =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichRows.future, RichRows.nativeDepth, code.nativeDepth_future current henv W,
      tail.nativeDepth_future current henv W]
termination_by sizeOf rows
decreasing_by all_goals simp_wf <;> omega

theorem RichObs.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (observation : RichObs sourceEnv env U registry Γ node locals σ profile footprint) :
    (observation.future henv W).nativeDepth current = observation.nativeDepth current := by
  match observation with
  | .rigidFamily (name := name) (frozenLevels := frozenLevels) (node := node)
      origin lookup inert seedWF seedLength frozenWF levelsWF seedFrozen frozenLevelsEq
      typeClosed plan certificate ready typed =>
    have atomEq := plan.atom_rename ρ name frozenLevels []
    simp only [List.map_nil] at atomEq
    simp only [RichObs.future, Footprint.rename, List.map_nil, Profile.rename_singleton,
      ← atomEq, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichObs.nativeDepth,
      RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr,
      certificate.nativeDepth_future current henv W]
  | .family (name := name) (levels := levels) (node := node) origin lookup notDefinition notNative notQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    simp only [RichObs.future, Footprint.rename, List.map_nil, RichObs.nativeDepth,
      RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr,
      certificate.nativeDepth_future current henv W, tree.nativeDepth_future current henv W]
  | .constructor (name := name) (levels := levels) (node := node) origin lookup notDefinition notNative notQuotient
      seedWF seedLength levelsWF equivalent signature typeClosed certificate typed tree =>
    simp only [RichObs.future, Footprint.rename, List.map_nil, RichObs.nativeDepth,
      RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr,
      certificate.nativeDepth_future current henv W, tree.nativeDepth_future current henv W]
  | .canonicalDelta (name := name) (levels := levels) (node := node) lookup nameEq registered
      seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichObs.future, RichObs.nativeDepth, certificate.nativeDepth_future current henv W,
      body.nativeDepth_future current henv W]
  | .canonicalConst (name := name) (levels := levels) (node := node) origin realization child resources =>
    simp only [RichObs.future, RichObs.nativeDepth, RichObs.nativeDepth_mp,
      RichObs.nativeDepth_mpr, child.nativeDepth_future current henv W,
      Footprint.rename, List.map_nil]
  | .legacy source => simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichObs.future, RichObs.nativeDepth, source.nativeDepth_future]
  | .code source =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichObs.future, RichObs.nativeDepth, source.nativeDepth_future current henv W]
  | .projection head nameEq member major field typed alignment =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichObs.future, RichObs.nativeDepth, major.nativeDepth_future current henv W,
      field.nativeDepth_future current henv W]
  | .projectionSortable head nameEq member major selected path sortable field typed =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichObs.future, RichObs.nativeDepth, major.nativeDepth_future current henv W,
      field.nativeDepth_future current henv W]
  | .app hu hv fn arg arguments admitted =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichObs.future, RichObs.nativeDepth, fn.nativeDepth_future current henv W,
      arg.nativeDepth_future current henv W]
  | .lam hu hv domain guard body pack covered =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichObs.future, RichObs.nativeDepth, domain.nativeDepth_future current henv W,
      body.nativeDepth_future current henv W]
  | .route path source =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichObs.future, RichObs.nativeDepth, source.nativeDepth_future current henv W]
  | .union first second =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichObs.future, RichObs.nativeDepth, first.nativeDepth_future current henv W,
      second.nativeDepth_future current henv W]
  | .view source view | .action source action | .select source member | .pad source | .unpad source =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi, Atom.rename_record, RecordData.rename, Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad, Key.pad_rename, Footprint.rename_append, subst_cons_future, Rows.rename, List.map_cons, Profile.down_rename, ← AtomView.mapType_future, SupportAction.apply_future, RichObs.nativeDepth_mp, RichObs.nativeDepth_mpr, RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr, RichRows.nativeDepth_mp, RichRows.nativeDepth_mpr, RichObs.future, RichObs.nativeDepth, source.nativeDepth_future current henv W]
termination_by sizeOf observation
decreasing_by all_goals simp_wf <;> omega

theorem RichFamilyPlan.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (plan : RichFamilyPlan env U registry Γ header name levels signature context σ arguments profile footprint) :
    (plan.future henv W).nativeDepth current = plan.nativeDepth current := by
  match plan with
  | .terminal saturated resultSort relevance captures =>
    simp only [RichFamilyPlan.future, id_eq, List.length_map, Profile.rename_singleton,
      Atom.rename_family, FamilyData.map, key_rename_map,
      RichFamilyPlan.nativeDepth, RichFamilyPlan.nativeDepth_mp, RichFamilyPlan.nativeDepth_mpr,
      FamilyCaptures.nativeDepth_mp, FamilyCaptures.nativeDepth_mpr,
      captures.nativeDepth_future current henv W]
  | .binder origin original location lineage domain guard body pack covered =>
    simp only [RichFamilyPlan.future, id_eq, List.length_map, Profile.fn, Profile.rename_singleton,
      Atom.rename_fn, Footprint.rename_append, List.map_append, List.map_cons, List.map_nil,
      subst_cons_future, Key.rename, RichFamilyPlan.nativeDepth,
      RichFamilyPlan.nativeDepth_mp, RichFamilyPlan.nativeDepth_mpr,
      RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr,
      domain.nativeDepth_future current henv W, body.nativeDepth_future current henv W]
  | .view source view | .pad source =>
    simp only [RichFamilyPlan.future, id_eq, Profile.rename_singleton, Profile.rename_pad,
      RichFamilyPlan.nativeDepth, RichFamilyPlan.nativeDepth_mp, RichFamilyPlan.nativeDepth_mpr,
      source.nativeDepth_future current henv W]
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

theorem RichConstructorPlan.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (plan : RichConstructorPlan env U registry Γ header name levels signature context σ arguments profile footprint) :
    (plan.future henv W).nativeDepth current = plan.nativeDepth current := by
  match plan with
  | .terminal saturated resultShape relevant resultNode resultLocation resultLineage captures resultCode =>
    simp only [RichConstructorPlan.future, id_eq, List.length_map, Profile.rename_singleton,
      Atom.rename_ctor, Atom.rename_family, ConstructorData.map, FamilyData.rename, FamilyData.map, key_rename_map,
      Footprint.rename_append, List.map_append,
      RichConstructorPlan.nativeDepth, RichConstructorPlan.nativeDepth_mp, RichConstructorPlan.nativeDepth_mpr,
      FamilyCaptures.nativeDepth_mp, FamilyCaptures.nativeDepth_mpr,
      RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr,
      captures.nativeDepth_future current henv W, resultCode.nativeDepth_future current henv W]
  | .terminalRecord registered lookup cname bounded saturated resultShape resultNode resultLocation resultLineage captures resultCode origins =>
    simp only [RichConstructorPlan.future, id_eq, List.length_map, Profile.rename_singleton,
      Atom.rename_record, Atom.rename_family, RecordData.rename, RecordData.map,
      FamilyData.rename, FamilyData.map, key_rename_map, List.map_map, Function.comp_def,
      Footprint.rename_append, RichConstructorPlan.nativeDepth,
      RichConstructorPlan.nativeDepth_mp, RichConstructorPlan.nativeDepth_mpr,
      FamilyCaptures.nativeDepth_mp, FamilyCaptures.nativeDepth_mpr,
      RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr,
      captures.nativeDepth_future current henv W, resultCode.nativeDepth_future current henv W]
  | .binder origin original location lineage domain guard body pack covered =>
    simp only [RichConstructorPlan.future, id_eq, List.length_map, Profile.fn, Profile.rename_singleton,
      Atom.rename_fn, Footprint.rename_append, List.map_append, List.map_cons, List.map_nil,
      subst_cons_future, Key.rename, RichConstructorPlan.nativeDepth,
      RichConstructorPlan.nativeDepth_mp, RichConstructorPlan.nativeDepth_mpr,
      RichCert.nativeDepth_mp, RichCert.nativeDepth_mpr,
      domain.nativeDepth_future current henv W, body.nativeDepth_future current henv W]
  | .view source view | .pad source =>
    simp only [RichConstructorPlan.future, id_eq, Profile.rename_singleton, Profile.rename_pad,
      RichConstructorPlan.nativeDepth, RichConstructorPlan.nativeDepth_mp, RichConstructorPlan.nativeDepth_mpr,
      source.nativeDepth_future current henv W]
termination_by sizeOf plan
decreasing_by all_goals simp_wf <;> omega

theorem RichCodeRecipe.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (recipe : RichCodeRecipe env U registry Γ source locals σ expression relevant profile footprint) :
    (recipe.future henv W).nativeDepth current = recipe.nativeDepth current := by
  match recipe with
  | .root _ _ _ _ _ _ _ _ certificate _ =>
    simp only [RichCodeRecipe.future, RichCodeRecipe.nativeDepth,
      certificate.nativeDepth_future current henv W]
  | .domain parent | .fixedBody parent _ _ =>
    simp only [RichCodeRecipe.future, Profile.pi, Profile.rename_singleton, Atom.rename_pi,
      RichCodeRecipe.nativeDepth, RichCodeRecipe.nativeDepth_mp, RichCodeRecipe.nativeDepth_mpr,
      parent.nativeDepth_future current henv W]
  | .body parent _ _ =>
    simp only [RichCodeRecipe.future, Profile.pi, Profile.rename_singleton, Atom.rename_pi,
      Footprint.rename, Footprint.sourceLift, List.map_cons, List.map_map, Function.comp_def,
      Need.rename, Key.rename, RichCodeRecipe.nativeDepth,
      RichCodeRecipe.nativeDepth_mp, RichCodeRecipe.nativeDepth_mpr,
      parent.nativeDepth_future current henv W]
  | .resources parent transfer =>
    simp only [RichCodeRecipe.future, RichCodeRecipe.nativeDepth,
      parent.nativeDepth_future current henv W, transfer.nativeDepth_future current henv W]
  | .action _ parent =>
    simp only [RichCodeRecipe.future, RichCodeRecipe.nativeDepth,
      parent.nativeDepth_future current henv W]
termination_by sizeOf recipe
decreasing_by all_goals simp_wf <;> omega

end

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
