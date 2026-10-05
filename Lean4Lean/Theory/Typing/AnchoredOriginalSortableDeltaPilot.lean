import Lean4Lean.Theory.Typing.AnchoredOriginalDefinitionEndpoint
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableFundamental
import Lean4Lean.Theory.Typing.AnchoredTraceTerm

/-! The hereditary definition boundary. The proposed source leaf stores
actual rich finite children; it has no semantic supplier. Its target replay
uses one fixed instantiated header-body formation and the registered delta
equation. The header-body F premise is conditional: a separate declaration
stage induction must discharge it before this becomes an original rule.
This module does not add a constructor to the shared source grammar. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Minimal same-level definition leaf. Universe changes can be handled by
the ordinary finite declaration packet separately. -/
structure SortableDeltaLeaf (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (value : VDefVal) (levels : List VLevel) (profile : Profile n) where
  lookup : registry.definitions value.name = some value
  registered : DefinitionRegistered env value
  levelsWF : ∀ level ∈ levels, level.WF U
  length : levels.length = value.uvars
  bodyClosed : value.value.Closed
  typeClosed : value.type.Closed
  support : Profile n
  certificate : SortableCert env U registry target [] .id (value.type.instL levels) true support []
  typed : profile.HasType support
  body : SortableObs env U registry target [] .id (value.value.instL levels) profile []

/-- This is an actual incoming query of a literal Pi body. Its nonempty row
can observe a proof-family code; it requires no legacy body certificate. -/
noncomputable def SortableDeltaLeaf.proofFamilyQuery
    {family : FamilyData (Profile n)} {key : Key (n + 1)} {support : Profile (n + 1)}
    (domain : SortableCert env U registry target [] .id A true support [])
    (guard : LambdaGuard env U registry target .id A key support)
    (body : SortableObs env U registry target [0] (Subst.id.cons key.anchor)
      B (.singleton (n := n + 1) (.family family)) [])
    (formed : (Profile.singleton (n := n + 1) (.family family)).HasType (.sort false)) :
    SortableObs env U registry target [] .id (.forallE A B)
      (Profile.pi (A.subst .id) (B.subst Subst.id.lift) support
        [(key, Profile.singleton (.family family))]) [] := by
  let rows : SortableRows env U registry target [] .id A B false support
      [(key, Profile.singleton (.family family))] [] :=
    .cons guard (.observe (by simpa only [Locals.push, List.map_nil] using body) formed)
      .nil (fun _ member => nomatch member) .nil
  exact .code false (.piLiteral domain rows)

private theorem emptyAvailable {footprint : Footprint}
    (resources : footprint.Available (fun _ => [])) : footprint = [] := by
  cases footprint with
  | nil => rfl
  | cons entry tail => exact nomatch resources entry.1 entry.2 List.mem_cons_self

/-- Conditional header-phase replay of the actual delta equation. Both
source certificates come from this fixed child, with no retyping supplier.
The local original F/C induction does not by itself supply `headerBodyIH`. -/
theorem DefinitionDeclarationOrigin.hereditaryDeltaPilot
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {declarations : List VDecl} {value : VDefVal}
    (origin : DefinitionDeclarationOrigin env declarations value)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {levels : List VLevel} (lookup : registry.definitions value.name = some value)
    (levelsWF : ∀ level ∈ levels, level.WF U) (length : levels.length = value.uvars)
    (headerBodyIH : DerivationHereditaryFundamental env registry .nil
      (DefinitionDeclarationOrigin.instantiatedBody origin levelsWF))
    {demand : Profile n}
    (body : SortableObs env U registry target [] .id (value.value.instL levels) demand []) :
    ∃ answer : SortableComputationalTransferResult env U registry target [] .id .id (fun _ => [])
        (value.value.instL levels) (value.value.instL levels) (value.type.instL levels) demand,
      ∃ leaf : SortableDeltaLeaf env U registry target value levels answer.raw,
        leaf.support = answer.support ∧
        Related env U registry target (.const value.name levels) (value.value.instL levels)
          (value.type.instL levels) (raiseProfile answer.rank answer.bound demand) answer.support ∧
        Related env U registry target (.const value.name levels) (.const value.name levels)
          (value.type.instL levels) answer.raw answer.support := by
  have closed : Valuation.AtomClosed (fun _ => []) := fun _ _ member => nomatch member
  have fits : SortableTailPairedFits env registry target
      (ContextDerivation.nil (env := origin.stage.header) (U := U)) [] .id .id (fun _ => []) :=
    ⟨.nil, .nil, rfl, rfl⟩
  obtain ⟨answer⟩ := (headerBodyIH target [] .id .id (fun _ => []) closed hTarget .nil fits).1
    body (fun _ _ member => nomatch member)
  have bodyFootprint := emptyAvailable answer.resources
  have typeFootprint := emptyAvailable answer.typeAvailable
  let leaf : SortableDeltaLeaf env U registry target value levels answer.raw := {
    lookup := lookup, registered := origin.registered, levelsWF := levelsWF, length := length
    bodyClosed := origin.closed.1, typeClosed := origin.closed.2
    support := answer.support
    certificate := typeFootprint ▸ answer.typeCertificate
    typed := answer.rawTyped
    body := bodyFootprint ▸ answer.observation }
  have delta : CanonicalHead.Trace registry (.const value.name levels) [] (value.value.instL levels) := by
    refine CanonicalHead.Trace.next (out := ⟨[], value.value.instL levels⟩) ?_ .refl
    simp [CanonicalHead.step, CanonicalHead.spineStep, VExpr.getAppFnArgs,
      VExpr.getAppFnArgs.go, lookup, length, VExpr.mkApps]
  have raw : env.IsDefEq U target (.const value.name levels) (value.value.instL levels)
      (value.type.instL levels) := by
    simpa only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id length] using
      (IsDefEq.extra (Γ := target) origin.registered.2 levelsWF length)
  have requested := answer.related
  have returned := answer.rawRelated
  simp only [subst_id] at requested returned
  have expansion : Related env U registry target (.const value.name levels) (value.value.instL levels)
      (value.type.instL levels) (raiseProfile answer.rank answer.bound demand) answer.support := by
    simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl,
      Profile.rename_refl] using Related.prependEndpoints (type := value.type.instL levels)
      henv hscoped (.traced (CanonicalDataHead.Trace.ofLegacy delta))
      (.traced CanonicalDataHead.Trace.refl)
      (ProofInsertion.refl hTarget)
      (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl] using raw)
      (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl] using raw.symm.trans raw)
      (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl,
        Profile.rename_refl] using requested)
  have diagonal : Related env U registry target (.const value.name levels) (.const value.name levels)
      (value.type.instL levels) answer.raw answer.support := by
    simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl,
      Profile.rename_refl] using Related.prependEndpoints (type := value.type.instL levels)
      henv hscoped (.traced (CanonicalDataHead.Trace.ofLegacy delta))
      (.traced (CanonicalDataHead.Trace.ofLegacy delta)) (ProofInsertion.refl hTarget)
      (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl] using raw)
      (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl] using raw)
      (by simpa only [List.nil_append, List.length_nil, Lift.skipN, VExpr.lift'_refl,
        Profile.rename_refl] using returned)
  exact ⟨answer, leaf, rfl, expansion, diagonal⟩

end Lean4Lean.AnchoredSource.Adapted
