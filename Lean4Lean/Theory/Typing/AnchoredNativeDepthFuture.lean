import Lean4Lean.Theory.Typing.AnchoredNativeDepthTransport
import Lean4Lean.Theory.Typing.AnchoredNativeDepthCast

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
@[simp] theorem Obs.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {expression : VExpr} {demand : Profile n}
    {footprint : Footprint} (observation : Obs env U registry Γ locals σ expression demand footprint) :
    (observation.future henv W).nativeDepth current = observation.nativeDepth current := by
  match observation with
  | .delta lookup nameEq registered seedWF seedLength levelsWF equivalent bodyClosed typeClosed certificate typed body =>
    simp only [Obs.future, Profile.rename_singleton, Footprint.rename, List.map_nil,
      Obs.nativeDepth, Obs.nativeDepth_mp, Obs.nativeDepth_mpr,
      body.nativeDepth_future current henv W, certificate.nativeDepth_future current henv W]
  | .native lookup notDefinition name_eq registered seedWF levelsWF equivalent signature typeClosed typeCertificate typed tree =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Obs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, Obs.nativeDepth, tree.nativeDepth_future current henv W typeClosed,
      typeCertificate.nativeDepth_future current henv W]
  | .family lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    simp only [Obs.future, Obs.nativeDepth,
      tree.nativeDepth_future current henv W typeClosed.instL,
      typeCertificate.nativeDepth_future current henv W]
  | .constructor lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
      signature typeClosed typeCertificate typed tree =>
    simp only [Obs.future, Obs.nativeDepth,
      tree.nativeDepth_future current henv W typeClosed.instL,
      typeCertificate.nativeDepth_future current henv W]
  | .var .. | .empty | .sort .. => simp only [Key.pad, Key.rename, id_eq, List.map_append, Obs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, Obs.nativeDepth, Obs.nativeDepth_mp, Obs.nativeDepth_mpr]
  | .app fn arg arguments admitted =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Obs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, Obs.nativeDepth, Obs.nativeDepth_mp, Obs.nativeDepth_mpr,
      fn.nativeDepth_future current henv W, arg.nativeDepth_future current henv W]
  | .lam domain guard body pack covered =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Obs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, Obs.nativeDepth, Obs.nativeDepth_mp, Obs.nativeDepth_mpr,
      domain.nativeDepth_future current henv W, body.nativeDepth_future current henv W]
  | .pi domain guard bodies =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Obs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, Obs.nativeDepth, Obs.nativeDepth_mp, Obs.nativeDepth_mpr,
      domain.nativeDepth_future current henv W, bodies.nativeDepth_future current henv W]
  | .union left right =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Obs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, Obs.nativeDepth, Obs.nativeDepth_mp, Obs.nativeDepth_mpr,
      left.nativeDepth_future current henv W, right.nativeDepth_future current henv W]
  | .view source view | .pad source | .unpad source | .rowShift source =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, Obs.future, Profile.pi, Profile.fn, Profile.rename_singleton, Atom.rename_fn, Atom.rename_pi,
      Profile.rename_sort, Footprint.rename, List.map_nil, Profile.rename_union, Profile.rename_pad, Atom.rename_pad,
      Key.pad_rename, Footprint.rename_append, subst_cons_future, Obs.nativeDepth, Obs.nativeDepth_mp, Obs.nativeDepth_mpr,
      source.nativeDepth_future current henv W]
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

@[simp] theorem CodeCert.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {expression : VExpr} {demand : Profile n}
    {footprint : Footprint} (certificate : CodeCert env U registry Γ locals σ expression demand footprint) :
    (certificate.future henv W).nativeDepth current = certificate.nativeDepth current := by
  match certificate with
  | .seed observation formed =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, CodeCert.future, Profile.rename_singleton, Profile.rename_union, Profile.rename_pad,
      Profile.down_rename, ← AtomView.mapType_future, Footprint.rename_append, CodeCert.nativeDepth, observation.nativeDepth_future current henv W]
  | .union left right =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, CodeCert.future, Profile.rename_singleton, Profile.rename_union, Profile.rename_pad,
      Profile.down_rename, ← AtomView.mapType_future, Footprint.rename_append, CodeCert.nativeDepth, CodeCert.nativeDepth_mp, CodeCert.nativeDepth_mpr,
      left.nativeDepth_future current henv W, right.nativeDepth_future current henv W]
  | .familyPad source =>
    simp only [CodeCert.future, Profile.rename_singleton, Atom.rename_family,
      FamilyData.rename, FamilyData.map_map, Profile.pad_rename, Function.comp_def, id_eq,
      CodeCert.nativeDepth, CodeCert.nativeDepth_mp, CodeCert.nativeDepth_mpr,
      source.nativeDepth_future current henv W]
  | .pad source | .unpad source | .down source | .map _ source | .select source _ | .focusMinimal source _ _ =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, CodeCert.future, Profile.rename_singleton, Profile.rename_union, Profile.rename_pad,
      Profile.down_rename, ← AtomView.mapType_future, Footprint.rename_append, CodeCert.nativeDepth, CodeCert.nativeDepth_mp, CodeCert.nativeDepth_mpr,
      source.nativeDepth_future current henv W]
termination_by sizeOf certificate
decreasing_by all_goals simp_wf; omega

@[simp] theorem PiRows.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {locals : List Nat} {σ : Subst} {A B : VExpr} {ambient : Profile n}
    {rows : List (Key n × Profile n)} {footprint : Footprint}
    (bodies : PiRows env U registry Γ locals σ A B ambient rows footprint) :
    (bodies.future henv W).nativeDepth current = bodies.nativeDepth current := by
  match bodies with
  | .nil => simp only [Key.pad, Key.rename, id_eq, List.map_append, PiRows.future, PiRows.nativeDepth]
  | .cons guard body pack covered tail =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, PiRows.future, Rows.rename, List.map_cons, Footprint.rename_append, subst_cons_future, PiRows.nativeDepth, PiRows.nativeDepth_mp, PiRows.nativeDepth_mpr,
      CodeCert.nativeDepth_mp, CodeCert.nativeDepth_mpr, body.nativeDepth_future current henv W,
      tail.nativeDepth_future current henv W]
termination_by sizeOf bodies
decreasing_by all_goals simp_wf; omega

@[simp] theorem NativeCaptures.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {data : NativeRecursorData} {program : SaturatedProgram data}
    {levels : List VLevel} {arguments witnesses : List VExpr}
    (typeClosed : ∀ type, data.recursorType = some type → type.Closed)
    (selected : data.saturatedProgram levels arguments = some program)
    (rhsClosed : program.equation.rhs.Closed)
    (witnessLength : witnesses.length = program.equationBody.domains.length)
    {field : Nat} {required outside : Footprint}
    (captures : NativeCaptures env U registry Γ program witnesses field required outside) :
    (captures.future henv W typeClosed selected rhsClosed witnessLength).nativeDepth current =
      captures.nativeDepth current := by
  match captures with
  | .prefix required =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, NativeCaptures.future, NativeIndexTemplates.rename, SaturatedProgram.rename,
      List.length_map, List.map_take, List.map_map, List.map_append, List.map_cons, List.map_nil,
      Footprint.rename_append, Footprint.rename, Footprint.sourceLift, Function.comp_def, Need.rename,
      NativeCaptures.nativeDepth, NativeCaptures.nativeDepth_mp, NativeCaptures.nativeDepth_mpr]
  | .index natural naturalResources declared declaredResources naturalTyped declaredTyped alignment declaredCode
      nativeValue copiedValue pack covered previous =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, NativeCaptures.future, NativeIndexTemplates.rename, SaturatedProgram.rename,
      List.length_map, List.map_take, List.map_map, List.map_append, List.map_cons, List.map_nil,
      Footprint.rename_append, Footprint.rename, Footprint.sourceLift, Function.comp_def, Need.rename,
      NativeCaptures.nativeDepth, NativeCaptures.nativeDepth_mp, NativeCaptures.nativeDepth_mpr,
      CodeCert.nativeDepth_mp, CodeCert.nativeDepth_mpr, CodeCert.nativeDepth_realizePrefix,
      natural.nativeDepth_future current henv W, declared.nativeDepth_future current henv W,
      previous.nativeDepth_future current henv W typeClosed selected rhsClosed witnessLength]
  | .proof instruction captured sourceProof domainProof inhabitant pack previous =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, NativeCaptures.future, NativeIndexTemplates.rename, SaturatedProgram.rename,
      List.length_map, List.map_take, List.map_map, List.map_append, List.map_cons, List.map_nil,
      Footprint.rename_append, Footprint.rename, Footprint.sourceLift, Function.comp_def, Need.rename,
      NativeCaptures.nativeDepth,
      previous.nativeDepth_future current henv W typeClosed selected rhsClosed witnessLength]
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

@[simp] theorem NativePlan.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {data : NativeRecursorData} {levels : List VLevel}
    {signature : NativeConstantSignature data levels} {arguments : List VExpr}
    (typeClosed : signature.type.Closed) {demand : Profile n} {footprint : Footprint}
    (plan : NativePlan env U registry Γ signature arguments demand footprint) :
    (plan.future henv W typeClosed).nativeDepth current = plan.nativeDepth current := by
  match plan with
  | .terminal program selected lhsClosed rhsClosed saturated noTrailing prefixEq
      witnesses witnessLength witnessPrefix argumentAlignment argumentsEq body captures =>
    have ihCaptures := captures.nativeDepth_future current henv W
      (fun type ht => (Option.some.inj (ht.symm.trans signature.typeOrigin)) ▸ typeClosed)
      selected rhsClosed witnessLength
    simp only [Key.pad, Key.rename, id_eq, List.map_append, NativePlan.future, Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append, List.length_map, List.map_append, List.map_cons, List.map_nil,
      NativePlan.nativeDepth, Obs.nativeDepth_realizePrefix,
      body.nativeDepth_future current henv W, ihCaptures]
  | .binder origin domain guard body pack covered =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, NativePlan.future, Profile.fn, Profile.rename_singleton, Atom.rename_fn,
      Footprint.rename_append, List.length_map, List.map_append, List.map_cons, List.map_nil,
      NativePlan.nativeDepth, NativePlan.nativeDepth_mp, NativePlan.nativeDepth_mpr,
      CodeCert.nativeDepth_mp, CodeCert.nativeDepth_mpr, CodeCert.nativeDepth_realizePrefix,
      domain.nativeDepth_future current henv W, body.nativeDepth_future current henv W typeClosed]
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

@[simp] theorem FamilyCaptures.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    (captures : FamilyCaptures env U registry Γ source locals σ expressions keys footprint) :
    (captures.future henv W).nativeDepth current = captures.nativeDepth current := by
  match captures with
  | .nil => simp only [FamilyCaptures.future, FamilyCaptures.nativeDepth]
  | .cons lookup value adapter alignment anchor tail =>
    obtain ⟨rawAnchor, rawPair, typed, formed, code, first, second⟩ := anchor
    simp only [FamilyCaptures.future, List.map_cons, Footprint.rename_append,
      FamilyCaptures.nativeDepth, FamilyCaptures.nativeDepth_mpr, FamilyCaptures.nativeDepth_mp,
      value.nativeDepth_future current henv W, tail.nativeDepth_future current henv W]
termination_by sizeOf captures
decreasing_by all_goals simp_wf; omega

@[simp] theorem FamilyPlan.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {name : Name} {levels : List VLevel}
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    (typeClosed : declaredType.Closed)
    (plan : FamilyPlan env U registry Γ name levels signature arguments demand footprint) :
    (plan.future henv W typeClosed).nativeDepth current = plan.nativeDepth current := by
  match plan with
  | .terminal saturated resultSort relevance captures =>
    simp only [FamilyPlan.future, id_eq, List.length_map, Profile.rename_singleton, Atom.rename_family,
      FamilyData.map, DataRequest.rename, DataRequest.map, KeyData.map,
      FamilyPlan.nativeDepth, FamilyPlan.nativeDepth_mpr, FamilyPlan.nativeDepth_mp,
      FamilyCaptures.nativeDepth_mpr, FamilyCaptures.nativeDepth_mp,
      FamilyCaptures.nativeDepth_realizePrefix, captures.nativeDepth_future current henv W]
    exact (FamilyCaptures.nativeDepth_mp current rfl rfl rfl rfl rfl _ _).trans
      ((FamilyCaptures.nativeDepth_realizePrefix current _ _ _ _).trans
        (captures.nativeDepth_future current henv W))
  | .binder origin domain guard body pack covered =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, FamilyPlan.future, Profile.fn,
      Profile.rename_singleton, Atom.rename_fn, Footprint.rename_append, List.length_map,
      List.map_cons, List.map_nil, FamilyPlan.nativeDepth,
      FamilyPlan.nativeDepth_mpr, FamilyPlan.nativeDepth_mp,
      CodeCert.nativeDepth_mpr, CodeCert.nativeDepth_mp, CodeCert.nativeDepth_realizePrefix,
      domain.nativeDepth_future current henv W, body.nativeDepth_future current henv W typeClosed]
  | .view source view | .pad source =>
    simp only [FamilyPlan.future, id_eq, Profile.rename_singleton, Profile.rename_pad,
      FamilyPlan.nativeDepth, FamilyPlan.nativeDepth_mpr, FamilyPlan.nativeDepth_mp,
      source.nativeDepth_future current henv W typeClosed]
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega
@[simp] theorem ConstructorPlan.nativeDepth_future (current : Name → Bool)
    (henv : env.Ordered) (W : FutureInsertion env U Γ Δ ρ)
    {name : Name} {levels : List VLevel}
    {declaredType : VExpr} {signature : ConstantTelescope declaredType}
    (typeClosed : declaredType.Closed)
    (plan : ConstructorPlan env U registry Γ name levels signature arguments demand footprint) :
    (plan.future henv W typeClosed).nativeDepth current = plan.nativeDepth current := by
  match plan with
  | .terminal saturated resultShape relevant captures resultCode =>
    simp only [ConstructorPlan.future, id_eq, List.length_map, Profile.rename_singleton, Atom.rename_ctor,
      ConstructorData.map, FamilyData.rename, FamilyData.map, DataRequest.rename, DataRequest.map, KeyData.map,
      Footprint.rename_append,
      ConstructorPlan.nativeDepth, ConstructorPlan.nativeDepth_mpr, ConstructorPlan.nativeDepth_mp,
      FamilyCaptures.nativeDepth_mpr, FamilyCaptures.nativeDepth_mp,
      FamilyCaptures.nativeDepth_realizePrefix, captures.nativeDepth_future current henv W,
      CodeCert.nativeDepth_mpr, CodeCert.nativeDepth_mp, CodeCert.nativeDepth_realizePrefix,
      resultCode.nativeDepth_future current henv W]
    rw [ConstructorPlan.nativeDepth_mp current rfl rfl rfl]
    simp only [ConstructorPlan.nativeDepth, FamilyCaptures.nativeDepth_mpr,
      FamilyCaptures.nativeDepth_mp, FamilyCaptures.nativeDepth_realizePrefix,
      captures.nativeDepth_future current henv W, CodeCert.nativeDepth_mpr,
      CodeCert.nativeDepth_mp, CodeCert.nativeDepth_realizePrefix,
      resultCode.nativeDepth_future current henv W]
    congr 1
    · exact (FamilyCaptures.nativeDepth_mpr current (by simp only [List.length_map]) rfl
        (by simp only [List.length_map]) rfl rfl _ _).trans
        ((FamilyCaptures.nativeDepth_mp current rfl rfl rfl rfl rfl _ _).trans
          ((FamilyCaptures.nativeDepth_realizePrefix current _ _ _ _).trans
            (captures.nativeDepth_future current henv W)))
    · exact (CodeCert.nativeDepth_mpr current (by simp only [List.length_map]) rfl rfl rfl _ _).trans
        ((CodeCert.nativeDepth_realizePrefix current _ _ _ _).trans
          (resultCode.nativeDepth_future current henv W))
  | .binder origin domain guard body pack covered =>
    simp only [Key.pad, Key.rename, id_eq, List.map_append, ConstructorPlan.future, Profile.fn,
      Profile.rename_singleton, Atom.rename_fn, Footprint.rename_append, List.length_map,
      List.map_cons, List.map_nil, ConstructorPlan.nativeDepth,
      ConstructorPlan.nativeDepth_mpr, ConstructorPlan.nativeDepth_mp,
      CodeCert.nativeDepth_mpr, CodeCert.nativeDepth_mp, CodeCert.nativeDepth_realizePrefix,
      domain.nativeDepth_future current henv W, body.nativeDepth_future current henv W typeClosed]
  | .view source view | .pad source =>
    simp only [ConstructorPlan.future, id_eq, Profile.rename_singleton, Profile.rename_pad,
      ConstructorPlan.nativeDepth, ConstructorPlan.nativeDepth_mpr, ConstructorPlan.nativeDepth_mp,
      source.nativeDepth_future current henv W typeClosed]
termination_by sizeOf plan
decreasing_by all_goals simp_wf; omega

end

end Lean4Lean.AnchoredSource.Adapted
