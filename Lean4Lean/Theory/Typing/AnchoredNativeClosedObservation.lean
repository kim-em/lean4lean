import Lean4Lean.Theory.Typing.AnchoredNativeLambdaBackwards
import Lean4Lean.Theory.Typing.AnchoredNativeOriginalObservation

/-! Rebuild an original equation's shared lambda telescope. Each binder uses
its original natural-type conversion chain and keeps the observer's exact key.
Only the finite body and extracted type-row leaves extend the local valuation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature NativeRecursorData
set_option backward.isDefEq.respectTransparency false

private theorem pack_append {p q : Profile n}
    (first : BinderPack n p before outside)
    (second : BinderPack n q after other) :
    BinderPack n (p.union q) (before ++ after) (outside ++ other) := by
  induction first with
  | nil => exact second
  | «local» need bound tail ih =>
    simpa only [Profile.union, Profile.atoms, Profile.mk, List.append_assoc, List.cons_append] using
      BinderPack.local need bound ih
  | external index need tail ih => exact .external index need ih

private theorem typed_subset {p q d : Profile n}
    (subset : ∀ atom ∈ p.atoms, atom ∈ q.atoms) (typed : q.HasType d) : p.HasType d := by
  cases n with
  | zero => exact fun atom hm => typed atom (subset atom hm)
  | succ n => exact ⟨fun atom hm => typed.1 atom (subset atom hm), typed.2.1,
      fun atom hm => typed.2.2 atom (subset atom hm)⟩

/-- Internal induction motive. The final declaration theorem supplies its
leaf by the concrete native initial-observation construction. -/
private def Rebuild (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source : List VExpr) (left right : VExpr) : Prop :=
  ∀ {assigned structural} (original : sourceEnv.HasTypeStrong U source left assigned structural)
    {target locals σ available}, available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ σ source →
    PairedFits env U registry source target locals σ σ available →
    ∀ {n} {demand support : Profile n} {footprint typeFootprint},
    Obs env U registry target locals σ right demand footprint →
    footprint.Available available →
    CodeCert env U registry target locals σ assigned support typeFootprint →
    typeFootprint.Available available → demand.HasType support →
    ∃ required, Nonempty (Obs env U registry target locals σ left demand required) ∧
      required.Available available

private theorem rebuild_lambda
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    {source : List VExpr} {A left right : VExpr}
    (next : Rebuild sourceEnv env U registry (A :: source) left right)
    {assigned structural}
    (original : sourceEnv.HasTypeStrong U source (.lam A left) assigned structural)
    {target locals σ available} (closed : available.AtomClosed)
    (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (fits : PairedFits env U registry source target locals σ σ available)
    {n} {demand support : Profile n} {footprint typeFootprint}
    (observation : Obs env U registry target locals σ (.lam A right) demand footprint)
    (resources : footprint.Available available)
    (certificate : CodeCert env U registry target locals σ assigned support typeFootprint)
    (typeResources : typeFootprint.Available available) (typed : demand.HasType support) :
    ∃ required, Nonempty (Obs env U registry target locals σ (.lam A left) demand required) ∧
      required.Available available := by
  match observation with
  | .empty => exact ⟨[], ⟨.empty⟩, fun _ _ hm => nomatch hm⟩
  | .lam (key := key) (bodyFootprint := bodyFootprint) domain guard body pack covered =>
    obtain ⟨origin⟩ := HasTypeStrong.originalLambdaOrigin (fun H => (earlier H).joint) original rfl
    obtain ⟨natural⟩ := origin.assignedCertificate henv hscoped hle closed hTarget
      substitutions fits certificate typeResources
    obtain ⟨result, ⟨row⟩, outputTyped⟩ := natural.naturalCertificate.piRow
      henv hscoped hTarget closed (origin.domainStrong.defeq.mono hle)
      (origin.bodyTypeStrong.defeq.mono hle) substitutions fits
      origin.domainJoint origin.bodyTypeJoint natural.resources typed
    have domainAvailable := fun i need hm => resources i need (List.mem_append_left _ hm)
    have outsideAvailable := fun i need hm => resources i need (List.mem_append_right _ hm)
    have joinedPack := pack_append pack row.pack
    have joinedCovered := fun atom hm => (List.mem_append.mp hm).elim
      (covered atom) (row.covered atom)
    have joinedOutside : (_ ++ row.outside).Available available := fun i need hm =>
      (List.mem_append.mp hm).elim (outsideAvailable i need) (row.outsideAvailable i need)
    let head := (bodyFootprint ++ row.bodyFootprint).localNeeds ++
      (bodyFootprint ++ row.bodyFootprint).localNeeds.flatMap Need.singletons
    have localClosed := Valuation.push_atomized_closed closed (bodyFootprint ++ row.bodyFootprint).localNeeds
    obtain ⟨raw, _, _, _, _, _, _, anchor⟩ := guard.anchor
    have arguments := Related.convert henv guard.inputTyped guard.domains anchor
    have paired : Ctx.SubstEq env U target (σ.cons key.anchor) (σ.cons key.anchor) (A :: source) := by
      exact .cons substitutions (origin.domainStrong.defeq.mono hle) (guard.path.cast raw)
    have localFits := fits.pushDiagonal henv hTarget domain domainAvailable guard.inputTyped arguments
      head (fun need hm => (joinedPack.atomized_localNeeds need hm).1)
      (fun need hm atom ha => joinedCovered atom ((joinedPack.atomized_localNeeds need hm).2 atom ha))
    have bothResources := joinedPack.available_atomized_localNeeds joinedOutside
    obtain ⟨required, ⟨changed⟩, changedAvailable⟩ := next origin.bodyTyping
      localClosed hTarget paired localFits body
      (fun i need hm => bothResources i need (List.mem_append_left _ hm)) row.body
      (fun i need hm => bothResources i need (List.mem_append_right _ hm)) outputTyped
    obtain ⟨newPacked, outside, newPack, newCovered, available⟩ :=
      Footprint.pack_available changedAvailable
        (fun need hm => (joinedPack.atomized_localNeeds need hm).1)
        (fun need hm atom ha => joinedCovered atom ((joinedPack.atomized_localNeeds need hm).2 atom ha))
    exact ⟨_, ⟨.lam domain guard changed newPack newCovered⟩, fun i need hm =>
      (List.mem_append.mp hm).elim (domainAvailable i need) (available i need)⟩
  | .union first second =>
    obtain ⟨f, ⟨first'⟩, firstAvailable⟩ := rebuild_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits first
      (fun i need hm => resources i need (List.mem_append_left _ hm)) certificate typeResources
      (typed_subset (fun _ hm => List.mem_append_left _ hm) typed)
    obtain ⟨s, ⟨second'⟩, secondAvailable⟩ := rebuild_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits second
      (fun i need hm => resources i need (List.mem_append_right _ hm)) certificate typeResources
      (typed_subset (fun _ hm => List.mem_append_right _ hm) typed)
    exact ⟨_, ⟨.union first' second'⟩, fun i need hm =>
      (List.mem_append.mp hm).elim (firstAvailable i need) (secondAvailable i need)⟩
  | .view child change =>
    obtain ⟨required, ⟨changed⟩, available⟩ := rebuild_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits child resources (.map (change.inverse henv) certificate)
      typeResources ((change.inverse henv).mapType_typed typed)
    exact ⟨_, ⟨.view changed change⟩, available⟩
  | .pad child =>
    obtain ⟨required, ⟨changed⟩, available⟩ := rebuild_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits child resources (.down certificate) typeResources typed.pad_inv
    exact ⟨_, ⟨.pad changed⟩, available⟩
  | .unpad child =>
    obtain ⟨required, ⟨changed⟩, available⟩ := rebuild_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits child resources (.pad certificate) typeResources typed.pad
    exact ⟨_, ⟨.unpad changed⟩, available⟩
  | @Obs.rowShift _ _ _ _ _ _ _ _ key output _ child =>
    have inverse := AtomView.uncommutePadFn (env := env) (U := U) (registry := registry)
      (Γ := target) key output
    have paddedTyped := inverse.mapType_typed typed
    have oldTyped : (Profile.fn key output).HasType (inverse.mapType support).down := by
      apply Profile.HasType.pad_inv
      simpa only [Profile.fn, Profile.pad_singleton] using paddedTyped
    obtain ⟨required, ⟨changed⟩, available⟩ := rebuild_lambda henv hscoped hle earlier next original
      closed hTarget substitutions fits child resources (.down (.map inverse certificate))
      typeResources oldTyped
    exact ⟨_, ⟨.rowShift changed⟩, available⟩
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

private theorem rebuild_telescope
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    (earlier : ∀ {Γ left right type} (H : sourceEnv.IsDefEqStrong U Γ left right type),
      OriginalPayload sourceEnv env U registry H)
    (domains : List VExpr) {source : List VExpr} {left right : VExpr}
    (terminal : Rebuild sourceEnv env U registry (domains.reverse ++ source) left right) :
    Rebuild sourceEnv env U registry source (wrapLams domains left) (wrapLams domains right) := by
  induction domains generalizing source with
  | nil => exact terminal
  | cons A domains ih =>
    apply rebuild_lambda henv hscoped hle earlier
    apply ih
    rw [List.reverse_cons, List.append_assoc, List.singleton_append] at terminal
    exact terminal


/-- Reconstruct the full original left equation at an actual assigned-type
certificate. Selection, capture origins and open-body construction are all
obtained from the installed declaration; no body-transfer callback is assumed. -/
theorem _root_.Lean4Lean.VEnv.NativeDeclarationOrigin.closedObservation_atType
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (eliminator : env.eliminators data.block data.schema)
    (singleton : data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels)
    (earlier : ∀ {Γ left right type}
      (H : origin.stage.typing.recursors.IsDefEqStrong U Γ left right type),
      OriginalPayload origin.stage.typing.recursors env U registry H)
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {signature : NativeConstantSignature data levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ [])
    (fits : PairedFits env U registry [] target locals σ σ available)
    {assigned : VExpr} {structural : Bool}
    (original : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.lhs.instL levels) assigned structural)
    {demand : Profile n} {bodyFootprint : Footprint}
    (observed : Obs env U registry target locals σ (rule.rhs.instL levels) demand bodyFootprint)
    (resources : bodyFootprint.Available available)
    {support : Profile n} {typeFootprint : Footprint}
    (certificate : CodeCert env U registry target locals σ assigned support typeFootprint)
    (typeResources : typeFootprint.Available available) (typed : demand.HasType support) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ
      (rule.lhs.instL levels) demand footprint) ∧ footprint.Available available := by
  have terminal : Rebuild origin.stage.typing.recursors env U registry
      (body.domains.map (·.instL levels)).reverse (body.lhs.instL levels) (body.rhs.instL levels) := by
    intro assigned structural original target locals σ available closed hTarget substitutions fits
      n demand support footprint typeFootprint observation resources certificate typeResources typed
    have build : ∀ atoms : List (Atom n), (∀ atom ∈ atoms, atom ∈ demand.atoms) →
        ∃ required, Nonempty (Obs env U registry target locals σ (body.lhs.instL levels)
          (Profile.mk atoms) required) ∧ required.Available available := by
      intro atoms
      induction atoms with
      | nil => exact fun _ => ⟨[], ⟨.empty⟩, fun _ _ hm => nomatch hm⟩
      | cons atom tail ih =>
        intro included
        obtain ⟨selected⟩ := observation.atom (included atom List.mem_cons_self)
        obtain ⟨headFootprint, ⟨head⟩, headAvailable⟩ := origin.initialObservation henv hscoped
          eliminator singleton earlier owner equation extracted levelLength levelsWF
          (signature := signature) lookup notDefinition closed hTarget substitutions fits original
          selected.observation (selected.atomizes.available_closed resources closed)
          certificate typeResources (typed.singleton_of_mem (included atom List.mem_cons_self))
        obtain ⟨tailFootprint, ⟨tail⟩, tailAvailable⟩ := ih
          (fun atom hm => included atom (List.mem_cons_of_mem _ hm))
        exact ⟨_, ⟨.union head tail⟩, fun i need hm =>
          (List.mem_append.mp hm).elim (headAvailable i need) (tailAvailable i need)⟩
    exact build demand.atoms (fun _ h => h)
  have leaf : Rebuild origin.stage.typing.recursors env U registry
      ((body.domains.map (·.instL levels)).reverse ++ [])
      (body.lhs.instL levels) (body.rhs.instL levels) := by
    rw [List.append_nil]
    exact terminal
  have rebuilt : Rebuild origin.stage.typing.recursors env U registry []
      (wrapLams (body.domains.map (·.instL levels)) (body.lhs.instL levels))
      (wrapLams (body.domains.map (·.instL levels)) (body.rhs.instL levels)) :=
    rebuild_telescope henv hscoped
    (origin.stage.typing.recursors_le.trans origin.stage.installedBelow) earlier
    (body.domains.map (·.instL levels)) leaf
  have parts := CaseSchema.EquationBody.extract_sound extracted
  have lhs : wrapLams (body.domains.map (·.instL levels)) (body.lhs.instL levels) =
      rule.lhs.instL levels := by rw [← instL_wrapLams, parts.1]
  have rhs : wrapLams (body.domains.map (·.instL levels)) (body.rhs.instL levels) =
      rule.rhs.instL levels := by rw [← instL_wrapLams, parts.2.1]
  rw [lhs, rhs] at rebuilt
  exact rebuilt original closed hTarget substitutions fits observed resources certificate typeResources typed

/-- The original right-side typing child produces the common assigned
certificate. Both converted lambda spines are thus reconstructed from actual
predecessor derivations and the given right-side observer alone. -/
theorem _root_.Lean4Lean.VEnv.NativeDeclarationOrigin.closedObservation
    {env : VEnv} {declarations : List VDecl} {data : NativeRecursorData}
    {U : Nat} {registry : CanonicalHead.Registry}
    (origin : NativeDeclarationOrigin env declarations data)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (eliminator : env.eliminators data.block data.schema)
    (singleton : data.schema.signature.SingletonElimination
      origin.stage.typing.types data.uvars data.levels)
    (earlier : ∀ {Γ left right type}
      (H : origin.stage.typing.recursors.IsDefEqStrong U Γ left right type),
      OriginalPayload origin.stage.typing.recursors env U registry H)
    {index : Fin data.schema.signature.constructors.size} {rule : VDefEq}
    (owner : data.schema.signature.constructors[index].owner = data.owner)
    (equation : data.equation index = some rule)
    {body : CaseSchema.EquationBody}
    (extracted : CaseSchema.EquationBody.extract rule.lhs rule.rhs rule.type = some body)
    {levels : List VLevel} (levelLength : levels.length = data.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {signature : NativeConstantSignature data levels}
    (lookup : registry.natives data.name = some data)
    (notDefinition : registry.definitions data.name = none)
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ σ [])
    (fits : PairedFits env U registry [] target locals σ σ available)
    {assigned : VExpr} {leftStructural rightStructural : Bool}
    (left : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.lhs.instL levels) assigned leftStructural)
    (right : origin.stage.typing.recursors.HasTypeStrong U []
      (rule.rhs.instL levels) assigned rightStructural)
    {demand : Profile n} {bodyFootprint : Footprint}
    (observed : Obs env U registry target locals σ (rule.rhs.instL levels) demand bodyFootprint)
    (resources : bodyFootprint.Available available) :
    ∃ footprint, Nonempty (Obs env U registry target locals σ
      (rule.lhs.instL levels) demand footprint) ∧ footprint.Available available := by
  obtain ⟨result⟩ := ((earlier right.refl).joint target locals σ σ available closed hTarget
    substitutions fits).1 observed resources
  exact origin.closedObservation_atType henv hscoped eliminator singleton earlier owner equation
    extracted levelLength levelsWF (signature := signature) lookup notDefinition closed hTarget
    substitutions fits left observed resources result.requestedCertificate result.typeAvailable result.requestedTyped

end Lean4Lean.AnchoredSource.Adapted
