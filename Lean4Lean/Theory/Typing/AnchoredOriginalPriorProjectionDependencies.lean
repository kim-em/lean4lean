import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryOccurrences
import Lean4Lean.Theory.Typing.AnchoredOriginalRichQueryCapture

/-! Select only prior projections actually present in the retained query
graph. Each demand keeps its original typing occurrence, complete query,
source frame and binder scope. No typing is required for an unused slot.
The input graph includes the explicit field/formation children of queries;
new assigned certificates are traversed only when their actual value result
is available. This is selection, not a total inverse-substitution theorem. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

structure PriorProjectionDependency
    (root : EndpointRef sourceEnv U source rootExpression rootType)
    (initialContext : ContextDerivation sourceEnv U source)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (ordered : sourceEnv.Ordered) (initialEnvironment : List Closure)
    (rootLeft rootRight : Subst) (name : Name) (current : Nat) (major : VExpr) where
  entry : RichQueryOccurrence root initialContext env registry target ordered initialEnvironment rootLeft rootRight
  index : Fin current
  expression_eq : entry.expression =
    (VExpr.proj name index.val major).lift' (.skipN .refl entry.location.binderPrefix.length)

namespace PriorProjectionDependency
variable {root : EndpointRef sourceEnv U source rootExpression rootType}
  {initialContext : ContextDerivation sourceEnv U source}
  {env : VEnv} {registry : CanonicalHead.Registry} {target : List VExpr}
  {ordered : sourceEnv.Ordered} {initialEnvironment : List Closure}
  {rootLeft rootRight : Subst} {name : Name} {current : Nat} {major : VExpr}

local notation "Dependency" => PriorProjectionDependency root initialContext env registry target ordered
  initialEnvironment rootLeft rootRight name current major

def need (selected : Dependency) : Need :=
  ⟨selected.entry.rank, selected.entry.profile⟩

def slot (selected : Dependency) : Nat :=
  current - 1 - selected.index.val

noncomputable def head
    (selected : Dependency) :
    ProjectionHead (selected.entry.node.cast
      (selected.expression_eq.trans (show
        (VExpr.proj name selected.index.val major).lift' (.skipN .refl selected.entry.location.binderPrefix.length) =
          .proj name selected.index.val (major.lift' (.skipN .refl selected.entry.location.binderPrefix.length)) from rfl)) rfl) :=
  projectionHead _

theorem cost_le
    (selected : Dependency) :
    (Closure.close (selected.entry.node.dependencyOrigin ordered)
      (selected.entry.occurrence.frame.dependencyEnvironment ordered)).cost ≤
      (Closure.close (root.dependencyOrigin ordered) initialEnvironment).cost :=
  selected.entry.cost_le

/-- In a proof-valued registered family, every selected prior projection
has an actual proof-valued field formation. A positive-field occurrence
cannot be manufactured by selecting an unused declaration position. -/
theorem field_prop
    (selected : Dependency)
    (registered : sourceEnv.projections name info) (resultZero : info.resultLevel = .zero) :
    selected.head.fieldLevel ≈ .zero := by
  have same : selected.head.info = info :=
    ordered.projections_unique selected.head.registered registered
  rcases selected.head.relevance with positive | proof
  · have impossible := positive []
    simp only [same, resultZero, VLevel.inst, VLevel.eval] at impossible
    exact (impossible rfl).elim
  · exact proof

theorem no_positive_field
    (selected : Dependency)
    (registered : sourceEnv.projections name info) (resultZero : info.resultLevel = .zero)
    (positive : ¬ selected.head.fieldLevel ≈ .zero) : False :=
  positive (selected.field_prop registered resultZero)

/-- No match hides an original node behind equality of target expressions.
Matching is at source syntax, with the exact original binder lift. -/
noncomputable def select
    (occurrences : List (RichQueryOccurrence root initialContext env registry target ordered
      initialEnvironment rootLeft rootRight)) :
    List (Dependency) := by
  classical
  exact occurrences.flatMap fun entry => (List.finRange current).flatMap fun index =>
    if matched : entry.expression =
        (VExpr.proj name index.val major).lift' (.skipN .refl entry.location.binderPrefix.length)
    then [⟨entry, index, matched⟩] else []

theorem select_complete
    (occurrences : List (RichQueryOccurrence root initialContext env registry target ordered
      initialEnvironment rootLeft rootRight))
    (entry : RichQueryOccurrence root initialContext env registry target ordered
      initialEnvironment rootLeft rootRight) (present : entry ∈ occurrences)
    (index : Fin current)
    (matched : entry.expression =
      (VExpr.proj name index.val major).lift' (.skipN .refl entry.location.binderPrefix.length)) :
    ∃ selected ∈ select (name := name) (major := major) occurrences,
      selected.entry = entry ∧ selected.index = index := by
  classical
  refine ⟨⟨entry, index, matched⟩, ?_, rfl, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨entry, present, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨index, by simp, ?_⟩
  simp only [dif_pos matched, List.mem_singleton]

theorem select_sound
    (occurrences : List (RichQueryOccurrence root initialContext env registry target ordered
      initialEnvironment rootLeft rootRight))
    (selected : Dependency)
    (present : selected ∈ select occurrences) : selected.entry ∈ occurrences := by
  classical
  obtain ⟨entry, member, inner⟩ := List.mem_flatMap.mp present
  obtain ⟨index, _, inner⟩ := List.mem_flatMap.mp inner
  split at inner
  · cases List.mem_singleton.mp inner
    exact member
  · cases inner

def demands
    (selected : List (Dependency)) : Footprint :=
  selected.map fun cut => (cut.slot, cut.need)

/-- Each demanded reverse slot returns the same complete, legally typed
owner query. In particular there is no premise supplying typings for the
other declaration slots. -/
theorem demand_owner
    (selected : List (Dependency))
    {requestedSlot : Nat} {requestedNeed : Need}
    (member : (requestedSlot, requestedNeed) ∈ demands selected) :
    ∃ cut ∈ selected, cut.slot = requestedSlot ∧ cut.need = requestedNeed := by
  obtain ⟨cut, present, equal⟩ := List.mem_map.mp member
  exact ⟨cut, present, (Prod.mk.inj equal).1, (Prod.mk.inj equal).2⟩

/-- Expansion of one actual returned assigned certificate. No future F
answers, arbitrary metadata query or completed alignment is assumed. -/
noncomputable def ofAssigned
    (entry : RichQueryOccurrence root initialContext env registry target ordered
      initialEnvironment rootLeft rootRight)
    (value : RichBinderValue sourceEnv env U registry target entry.node entry.locals entry.left entry.right
      entry.available entry.profile)
    (henv : env.Ordered) (sourceBelow : sourceEnv ≤ env) :
    List (Dependency) :=
  select (value.certificate.framedOccurrences entry.occurrence.assignedFormation henv sourceBelow
    entry.closed value.resources true (entry.sourceTail.at rfl))

end PriorProjectionDependency
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
