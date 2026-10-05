import Lean4Lean.Theory.Typing.AnchoredSortableHeaderPhase
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableDeltaPilot
import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthCast

/-! A rich definition packet spends one current-header fuel unit. Its actual
body call is at the strictly smaller fuel, with all quiet caller budgets
unchanged. This checks the finite head producer before adding its constructor
to the shared mutually hereditary source grammar. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-- The prospective rich delta constructor uses the same head charge as the
legacy constructor and includes both actual rich source children. -/
def SortableDeltaLeaf.nativeDepth (current : Name → Bool)
    (leaf : SortableDeltaLeaf env U registry target value levels profile) : Nat :=
  max (leaf.body.nativeDepth current) (leaf.certificate.nativeDepth current) +
    if current value.name then 1 else 0

/-- Only the active header fuel is decremented. All caller controls ignore
this head; their precise bounds on both children are retained. -/
theorem SortableDeltaLeaf.childrenBound
    {budgets : HereditaryBudgeted.Budgets}
    (leaf : SortableDeltaLeaf env U registry target value levels profile)
    (current : Name → Bool) (active : current value.name = true)
    (quiet : ∀ filter limit, (filter, limit) ∈ budgets → filter value.name = false)
    (bounded : HereditaryBudgeted.Within ((current, fuel + 1) :: budgets) leaf.nativeDepth) :
    HereditaryBudgeted.Within ((current, fuel) :: budgets) leaf.body.nativeDepth ∧
      HereditaryBudgeted.Within ((current, fuel) :: budgets) leaf.certificate.nativeDepth := by
  constructor <;> intro filter limit member
  all_goals rcases List.mem_cons.mp member with equal | member
  · cases equal
    have h := bounded current (fuel + 1) List.mem_cons_self
    change leaf.nativeDepth current ≤ fuel + 1 at h
    simp only [SortableDeltaLeaf.nativeDepth, active, ↓reduceIte] at h
    exact Nat.le_trans (Nat.le_max_left (leaf.body.nativeDepth current) (leaf.certificate.nativeDepth current)) (by omega)
  · have h := bounded filter limit (List.mem_cons_of_mem _ member)
    change leaf.nativeDepth filter ≤ limit at h
    simp only [SortableDeltaLeaf.nativeDepth, quiet filter limit member, ↓reduceIte, Nat.add_zero] at h
    exact Nat.le_trans (Nat.le_max_left _ _) h
  · cases equal
    have h := bounded current (fuel + 1) List.mem_cons_self
    change leaf.nativeDepth current ≤ fuel + 1 at h
    simp only [SortableDeltaLeaf.nativeDepth, active, ↓reduceIte] at h
    exact Nat.le_trans (Nat.le_max_right (leaf.body.nativeDepth current) (leaf.certificate.nativeDepth current)) (by omega)
  · have h := bounded filter limit (List.mem_cons_of_mem _ member)
    change leaf.nativeDepth filter ≤ limit at h
    simp only [SortableDeltaLeaf.nativeDepth, quiet filter limit member, ↓reduceIte, Nat.add_zero] at h
    exact Nat.le_trans (Nat.le_max_right _ _) h

theorem SortableDeltaLeaf.noZeroFuel
    (leaf : SortableDeltaLeaf env U registry target value levels profile)
    (active : current value.name = true) : ¬ leaf.nativeDepth current ≤ 0 := by
  simp only [SortableDeltaLeaf.nativeDepth, active, ↓reduceIte]
  omega

private theorem emptyAvailable {footprint : Footprint}
    (resources : footprint.Available (fun _ => [])) : footprint = [] := by
  cases footprint with
  | nil => rfl
  | cons entry tail => exact nomatch resources entry.1 entry.2 List.mem_cons_self

private theorem obsFootprintDepth (current : Name → Bool) (equal : before = after)
    (source : SortableObs env U registry target locals σ expression demand before) :
    (equal ▸ source : SortableObs env U registry target locals σ expression demand after).nativeDepth current =
      source.nativeDepth current := by cases equal; rfl

private theorem certFootprintDepth (current : Name → Bool) (equal : before = after)
    (source : SortableCert env U registry target locals σ expression relevant demand before) :
    (equal ▸ source : SortableCert env U registry target locals σ expression relevant demand after).nativeDepth current =
      source.nativeDepth current := by cases equal; rfl

/-- The next rich delta packet is computed from the fixed original stored
body at predecessor fuel. No all-fuel body supplier or unrestricted budgeted
fundamental theorem is used in this step. The original body was specialized
in its pre-equation header; it is charged to header fuel, not local proof size. -/
theorem DefinitionDeclarationOrigin.deltaFuelStep
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {declarations : List VDecl} {value : VDefVal}
    (origin : DefinitionDeclarationOrigin env declarations value)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} (hTarget : OnCtx target (env.IsType U))
    {levels : List VLevel} {demand : Profile n}
    (incoming : SortableDeltaLeaf env U registry target value levels demand)
    {budgets : HereditaryBudgeted.Budgets}
    (quiet : ∀ filter limit, (filter, limit) ∈ budgets → filter value.name = false)
    (bounded : HereditaryBudgeted.Within ((origin.current, fuel + 1) :: budgets) incoming.nativeDepth)
    (bodyIH : HereditaryBudgeted.FundamentalAt ((origin.current, fuel) :: budgets)
      env registry .nil (DefinitionDeclarationOrigin.instantiatedBody origin incoming.levelsWF)) :
    ∃ answer : HereditaryBudgeted.Result ((origin.current, fuel) :: budgets)
        env U registry target [] .id .id (fun _ => []) (value.value.instL levels)
        (value.value.instL levels) (value.type.instL levels) demand,
      ∃ leaf : SortableDeltaLeaf env U registry target value levels answer.raw,
        leaf.support = answer.support ∧
        HereditaryBudgeted.Within ((origin.current, fuel + 1) :: budgets) leaf.nativeDepth ∧
        Related env U registry target (.const value.name levels) (value.value.instL levels)
          (value.type.instL levels) (raiseProfile answer.rank answer.bound demand) answer.support ∧
        Related env U registry target (.const value.name levels) (.const value.name levels)
          (value.type.instL levels) answer.raw answer.support := by
  have inputBound := (incoming.childrenBound origin.current origin.current_self quiet bounded).1
  have closed : Valuation.AtomClosed (fun _ => []) := fun _ _ member => nomatch member
  let fits : SortableTailPairedFits env registry target
      (ContextDerivation.nil (env := origin.stage.header) (U := U)) [] .id .id (fun _ => []) :=
    ⟨.nil, .nil, rfl, rfl⟩
  have fitted : HereditaryBudgeted.Within ((origin.current, fuel) :: budgets) fits.nativeDepth := by
    intro current limit member
    simp only [fits, SortableTailPairedFits.nativeDepth, SortableTailFits.nativeDepth, Nat.max_self]
    exact Nat.zero_le _
  obtain ⟨answer⟩ := (bodyIH target [] .id .id (fun _ => []) closed hTarget .nil fits fitted).1
    incoming.body inputBound (fun _ _ member => nomatch member)
  have bodyFootprint := emptyAvailable answer.resources
  have typeFootprint := emptyAvailable answer.typeAvailable
  let leaf : SortableDeltaLeaf env U registry target value levels answer.raw := {
    lookup := incoming.lookup, registered := origin.registered
    levelsWF := incoming.levelsWF, length := incoming.length
    bodyClosed := origin.closed.1, typeClosed := origin.closed.2
    support := answer.support
    certificate := typeFootprint ▸ answer.typeCertificate
    typed := answer.rawTyped
    body := bodyFootprint ▸ answer.observation }
  have leafBound : HereditaryBudgeted.Within ((origin.current, fuel + 1) :: budgets) leaf.nativeDepth := by
    intro current limit member
    change leaf.nativeDepth current ≤ limit
    simp only [leaf, SortableDeltaLeaf.nativeDepth, obsFootprintDepth, certFootprintDepth]
    rcases List.mem_cons.mp member with equal | member
    · cases equal
      have obsBound := answer.observationBound origin.current fuel List.mem_cons_self
      have codeBound := answer.certificateBound origin.current fuel List.mem_cons_self
      simp only [origin.current_self, ↓reduceIte]
      exact Nat.add_le_add_right (Nat.max_le.mpr ⟨obsBound, codeBound⟩) 1
    · have obsBound := answer.observationBound current limit (List.mem_cons_of_mem _ member)
      have codeBound := answer.certificateBound current limit (List.mem_cons_of_mem _ member)
      simp only [quiet current limit member, ↓reduceIte, Nat.add_zero]
      exact Nat.max_le.mpr ⟨obsBound, codeBound⟩
  have delta : CanonicalHead.Trace registry (.const value.name levels) [] (value.value.instL levels) := by
    refine CanonicalHead.Trace.next (out := ⟨[], value.value.instL levels⟩) ?_ .refl
    simp [CanonicalHead.step, CanonicalHead.spineStep, VExpr.getAppFnArgs,
      VExpr.getAppFnArgs.go, incoming.lookup, incoming.length, VExpr.mkApps]
  have raw : env.IsDefEq U target (.const value.name levels) (value.value.instL levels)
      (value.type.instL levels) := by
    simpa only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id incoming.length] using
      (IsDefEq.extra (Γ := target) origin.registered.2 incoming.levelsWF incoming.length)
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
  exact ⟨answer, leaf, rfl, leafBound, expansion, diagonal⟩

end Lean4Lean.AnchoredSource.Adapted
