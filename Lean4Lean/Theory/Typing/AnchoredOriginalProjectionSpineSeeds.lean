import Lean4Lean.Theory.Typing.AnchoredOriginalProjectionSpineReplay

/-! Source seed extraction is structural. The accepted application fragment
allows primitive typed projections as whole arguments and arbitrary legacy
parameter observations. A new projection nested inside a nonprojected
parameter needs the full hereditary typed fundamental theorem and is not
silently erased by this extraction. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
open OriginalEndpointFactor
set_option backward.isDefEq.respectTransparency false

def TypedSpineObs.Erasable
    (query : TypedSpineObs env registry target root locals σ node start demand footprint) : Prop :=
  match query with
  | .legacy _ => True
  | .projection _ => False
  | .app _ function argument _ _ => function.Erasable ∧ argument.Erasable
  | .union first second => first.Erasable ∧ second.Erasable
  | .view child _ | .pad child | .unpad child | .rowShift child => child.Erasable

def TypedSpineObs.erase
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    (query : TypedSpineObs env registry target root locals σ node start demand footprint)
    (erasable : query.Erasable) :
    Obs env U registry target locals σ expression demand footprint := by
  match query with
  | .legacy observation => exact observation
  | .projection _ => exact erasable.elim
  | .app _ function argument adapter admitted =>
    exact .app (function.erase erasable.1) (argument.erase erasable.2) adapter admitted
  | .union first second => exact .union (first.erase erasable.1) (second.erase erasable.2)
  | .view child change => exact .view (child.erase erasable) change
  | .pad child => exact .pad (child.erase erasable)
  | .unpad child => exact .unpad (child.erase erasable)
  | .rowShift child => exact .rowShift (child.erase erasable)

/-- This is an explicit syntax restriction, not a supply of output field
packets or semantic retyping. It holds for legacy parameters plus the actual
projected fields of a structure eta expansion. -/
def TypedSpineObs.SpineSupported
    (query : TypedSpineObs env registry target root locals σ node start demand footprint) : Prop :=
  match query with
  | .legacy _ => True
  | .projection _ => False
  | .app (a := a) _ function argument _ _ =>
      function.SpineSupported ∧
        (argument.Erasable ∨ ∃ name index major, a = .proj name index major)
  | .union first second => first.SpineSupported ∧ second.SpineSupported
  | .view child _ | .pad child | .unpad child | .rowShift child => child.SpineSupported

private theorem argumentSeeds
    (observation : Obs env U registry target locals σ expression demand footprint)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (resources : footprint.Available available) (member : atom ∈ demand.atoms) :
    Nonempty (NativeSpineSeeds env U registry target locals σ available expression) := by
  match observation with
  | .delta .. | .native .. | .family .. | .constructor .. => exact ⟨.constant⟩
  | .var .. | .sort .. | .lam .. | .pi .. => simp only [getAppFnArgs] at head; contradiction
  | .empty => cases member
  | .app function argument adapter admitted =>
    obtain ⟨previous⟩ := argumentSeeds function (by simpa only [getAppFnArgs_app] using head)
      (fun i need present => resources i need (List.mem_append_left _ present))
      (List.mem_singleton_self _)
    exact ⟨.app previous ⟨_, _, _, argument,
      fun i need present => resources i need (List.mem_append_right _ present)⟩⟩
  | .union first second =>
    rcases List.mem_append.mp member with present | present
    · exact argumentSeeds first head
        (fun i need present => resources i need (List.mem_append_left _ present)) present
    · exact argumentSeeds second head
        (fun i need present => resources i need (List.mem_append_right _ present)) present
  | .view child _ => exact argumentSeeds child head resources (List.mem_singleton_self _)
  | .pad child =>
    obtain ⟨_, present, _⟩ := List.mem_map.mp member
    exact argumentSeeds child head resources present
  | .unpad child => exact argumentSeeds child head resources (List.mem_map_of_mem member)
  | .rowShift child => exact argumentSeeds child head resources (List.mem_singleton_self _)
termination_by sizeOf observation
decreasing_by all_goals simp_wf; omega

private noncomputable def NativeSpineSeeds.typedSeeds
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned}
    (seeds : NativeSpineSeeds env U registry target locals σ available expression)
    (start : Located root node) (head : expression.getAppFnArgs.1 = .const name levels) :
    ProjectionSpineSeeds env registry target locals σ available (OriginalEndpointFactor.NativeSpineSeeds.originalSpine seeds start head) := by
  induction seeds generalizing assigned with
  | constant =>
    simp only [getAppFnArgs_const] at head
    cases head
    exact .constant
  | app function argument ih =>
    exact .legacy (ih (.appFunction (applicationPrefix start).view.location)
      (by simpa only [getAppFnArgs_app] using head)) argument

/-- Actual query children construct every spine seed. Whole projection
arguments retain their typed node and exact incoming adapter; no returned
recipe or finite argument ledger is assumed. -/
theorem TypedSpineObs.spineSeeds
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source expression assigned} {start : Located root node}
    (query : TypedSpineObs env registry target root locals σ node start demand footprint)
    (supported : query.SpineSupported)
    (head : expression.getAppFnArgs.1 = .const name levels)
    (resources : footprint.Available available) (member : atom ∈ demand.atoms) :
    ∃ spine : OriginalConstantSpine root name levels start,
      Nonempty (ProjectionSpineSeeds env registry target locals σ available spine) := by
  match query with
  | .legacy observation =>
    obtain ⟨seeds⟩ := argumentSeeds observation head resources member
    exact ⟨OriginalEndpointFactor.NativeSpineSeeds.originalSpine seeds start head, ⟨NativeSpineSeeds.typedSeeds seeds start head⟩⟩
  | .projection _ => exact supported.elim
  | .app packet function argument adapter admitted =>
    obtain ⟨previous, ⟨previousSeeds⟩⟩ := function.spineSeeds supported.1
      (by simpa only [getAppFnArgs_app] using head)
      (fun i need present => resources i need (List.mem_append_left _ present))
      (List.mem_singleton_self _)
    have argumentResources : Footprint.Available _ available :=
      fun i need present => resources i need (List.mem_append_right _ present)
    rcases supported.2 with erasable | ⟨fieldName, index, major, equal⟩
    · exact ⟨.application packet previous, ⟨.legacy previousSeeds
        ⟨_, _, _, argument.erase erasable, argumentResources⟩⟩⟩
    · cases equal
      obtain ⟨seed⟩ := argument.applicationSeed packet.view adapter admitted argumentResources
      exact ⟨.application packet previous, ⟨.projected previousSeeds seed⟩⟩
  | .union first second =>
    rcases List.mem_append.mp member with present | present
    · exact first.spineSeeds supported.1 head
        (fun i need present => resources i need (List.mem_append_left _ present)) present
    · exact second.spineSeeds supported.2 head
        (fun i need present => resources i need (List.mem_append_right _ present)) present
  | .view child _ => exact child.spineSeeds supported head resources (List.mem_singleton_self _)
  | .pad child =>
    obtain ⟨_, present, _⟩ := List.mem_map.mp member
    exact child.spineSeeds supported head resources present
  | .unpad child => exact child.spineSeeds supported head resources (List.mem_map_of_mem member)
  | .rowShift child => exact child.spineSeeds supported head resources (List.mem_singleton_self _)
termination_by sizeOf query
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
