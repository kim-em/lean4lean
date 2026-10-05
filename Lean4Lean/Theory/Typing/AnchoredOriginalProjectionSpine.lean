import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionAtomRows
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPrefix

/-! An isolated typed application spine retains its actual AppView children
and the literal raw-input adapter of each application. Projection argument
queries are never erased to legacy Obs. This spine layer is not yet a full
hereditary grammar for lambda/Pi bodies containing new projection queries.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- The old grammar has no primitive projection node. This exact invariant
is used only for old cuts; it does not erase a nonempty typed projection. -/
theorem legacyProjectionEmpty
    (observation : Obs env U registry target locals σ (.proj name index major) demand footprint) :
    demand = .empty := by
  match observation with
  | .empty => rfl
  | .union left right => rw [legacyProjectionEmpty left, legacyProjectionEmpty right]; rfl
  | .view child change => have impossible := legacyProjectionEmpty child; cases impossible
  | .pad child => rw [legacyProjectionEmpty child]; rfl
  | .unpad child =>
    have equal := congrArg Profile.down (legacyProjectionEmpty child)
    simpa only [Profile.down_pad, Profile.down_empty] using equal
  | .rowShift child => have impossible := legacyProjectionEmpty child; cases impossible
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

inductive TypedSpineObs (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    {sourceEnv : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    (root : EndpointRef sourceEnv U rootSource rootExpression rootType)
    (locals : List Nat) (σ : Subst) :
    {source : List VExpr} → {expression assigned : VExpr} →
    (node : EndpointState sourceEnv U source expression assigned) → Located root node →
    {n : Nat} → Profile n → Footprint → Type where
  | legacy {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
      (observation : Obs env U registry target locals σ expression demand footprint) :
      TypedSpineObs env registry target root locals σ node start demand footprint
  | projection
      (query : ProjectionObs env registry target node locals σ demand footprint) :
      TypedSpineObs env registry target root locals σ node start demand footprint
  | app {node : EndpointState sourceEnv U source (.app f a) assigned} {start : Located root node}
      (packet : ApplicationPrefix start) {key : Key n} {output : Atom n}
      (function : TypedSpineObs env registry target root locals σ packet.view.function
        (.appFunction packet.view.location) (Profile.fn key output) functionFootprint)
      (argument : TypedSpineObs env registry target root locals σ packet.view.argument
        (.appArgument packet.view.location) rawInput argumentFootprint)
      (arguments : NormalProfileAdapter env U registry target rawInput key.input)
      (admitted : Admitted env U registry target key (a.subst σ) (a.subst σ)) :
      TypedSpineObs env registry target root locals σ node start (.singleton output)
        (functionFootprint ++ argumentFootprint)
  | union
      (first : TypedSpineObs env registry target root locals σ node start left leftFootprint)
      (second : TypedSpineObs env registry target root locals σ node start right rightFootprint) :
      TypedSpineObs env registry target root locals σ node start (left.union right)
        (leftFootprint ++ rightFootprint)
  | view
      (child : TypedSpineObs env registry target root locals σ node start (.singleton first) footprint)
      (change : AtomView env U registry target first second) :
      TypedSpineObs env registry target root locals σ node start (.singleton second) footprint
  | pad (child : TypedSpineObs env registry target root locals σ node start demand footprint) :
      TypedSpineObs env registry target root locals σ node start demand.pad footprint
  | unpad (child : TypedSpineObs env registry target root locals σ node start demand.pad footprint) :
      TypedSpineObs env registry target root locals σ node start demand footprint
  | rowShift {key : Key n} {output : Atom n}
      (child : TypedSpineObs env registry target root locals σ node start (Profile.fn key output) footprint) :
      TypedSpineObs env registry target root locals σ node start (Profile.fn key.pad (.pad output)) footprint

/-- Extract a projected argument from the actual application syntax,
including all query wrappers. The assigned type is exactly the original
AppView.argument type, not a declared telescope domain. -/
theorem TypedSpineObs.projectionQuery
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    {start : Located root node}
    (query : TypedSpineObs env registry target root locals σ node start demand footprint)
    (resources : footprint.Available available) :
    ∃ nextFootprint, Nonempty (ProjectionObs env registry target node locals σ demand nextFootprint) ∧
      nextFootprint.Available available := by
  match query with
  | .legacy observation =>
    have empty := legacyProjectionEmpty observation
    subst demand
    exact ⟨[], ⟨.empty⟩, fun _ _ member => nomatch member⟩
  | .projection query => exact ⟨_, ⟨query⟩, resources⟩
  | .union first second =>
    obtain ⟨firstFootprint, ⟨firstQuery⟩, firstResources⟩ := first.projectionQuery
      (fun i need member => resources i need (List.mem_append_left _ member))
    obtain ⟨secondFootprint, ⟨secondQuery⟩, secondResources⟩ := second.projectionQuery
      (fun i need member => resources i need (List.mem_append_right _ member))
    exact ⟨firstFootprint ++ secondFootprint, ⟨.union firstQuery secondQuery⟩,
      fun i need member => (List.mem_append.mp member).elim (firstResources i need) (secondResources i need)⟩
  | .view child change =>
    obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := child.projectionQuery resources
    exact ⟨nextFootprint, ⟨.view next change⟩, nextResources⟩
  | .pad child =>
    obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := child.projectionQuery resources
    exact ⟨nextFootprint, ⟨next.pad⟩, nextResources⟩
  | .unpad child =>
    obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := child.projectionQuery resources
    exact ⟨nextFootprint, ⟨.unpad next⟩, nextResources⟩
  | .rowShift child =>
    obtain ⟨nextFootprint, ⟨next⟩, nextResources⟩ := child.projectionQuery resources
    exact ⟨nextFootprint, ⟨next.rowShift⟩, nextResources⟩
termination_by sizeOf query
decreasing_by all_goals simp_wf; omega

structure ProjectedApplicationSeed
    {sourceEnv env : VEnv} {U : Nat} {rootSource : List VExpr} {rootExpression rootType : VExpr}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (registry : CanonicalHead.Registry) (target : List VExpr) (locals : List Nat) (σ : Subst)
    (available : Valuation)
    {node : EndpointState sourceEnv U source (.app f (.proj name index major)) assigned}
    {start : Located root node} (view : AppView start) (key : Key n) where
  seed : ProjectionArgumentSeed env registry target view.argument locals σ available
  grade : seed.rank = n
  adapter : NormalProfileAdapter env U registry target seed.demand
    (grade.symm ▸ key.input)
  admitted : Admitted env U registry target key
    ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ)

/-- Actual projected application children produce a typed seed and retain
their unchanged raw-input adapter. There is no supplied output metadata. -/
theorem TypedSpineObs.applicationSeed
    {node : EndpointState sourceEnv U source (.app f (.proj name index major)) assigned}
    {start : Located root node} (view : AppView start) {key : Key n}
    (argument : TypedSpineObs env registry target root locals σ view.argument
      (.appArgument view.location) rawInput argumentFootprint)
    (arguments : NormalProfileAdapter env U registry target rawInput key.input)
    (admitted : Admitted env U registry target key
      ((VExpr.proj name index major).subst σ) ((VExpr.proj name index major).subst σ))
    (resources : argumentFootprint.Available available) :
    Nonempty (ProjectedApplicationSeed (env := env) registry target locals σ available view key) := by
  obtain ⟨footprint, ⟨query⟩, queryResources⟩ := argument.projectionQuery resources
  exact ⟨⟨⟨n, rawInput, footprint, query, queryResources⟩, rfl, arguments, admitted⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
