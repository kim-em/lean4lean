import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationOrigins
import Lean4Lean.Theory.Typing.AnchoredOriginalOutputPathCode

/-! Function prefixes of a family application have genuine original children.
An arbitrary application code may instead be a charged recipe, but a finite
output path cannot turn such a sortable leaf into a function observation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem WorldObsProvenance.applicationOriginNonsortable
    {strata : EquationStratification env}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {demand : Profile n}
    {query : RichObs sourceEnv env U registry target node locals σ demand footprint}
    (annotation : WorldObsProvenance strata query)
    (location : Located root node) (member : atom ∈ demand.atoms)
    (nonsortable : ∀ flag, ¬ (Profile.singleton atom).HasType (.sort flag)) :
    ∃ origin : RichAppOrigin root env registry target source locals σ f arg,
    ∃ children : RichAppWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint ∧
      List.Subset children.worlds annotation.worlds ∧
      ∀ policy, max (origin.function.headDepth policy) (origin.argument.headDepth policy) ≤
        query.headDepth policy := by
  obtain ⟨origin, children, ⟨path⟩, included, worlds, depth⟩ :=
    annotation.applicationOrigin location member
  cases origin with
  | original origin =>
    cases children with
    | original children => exact ⟨origin, children, ⟨path⟩, included, worlds, depth⟩
  | charged origin =>
    have sorted := origin.recipe.formed
    exact (nonsortable _ ((GeneralOutputPath.codeAtInput path sorted).preservesSort sorted)).elim

/-- A function-valued application prefix supplies controlled queries at its
actual two original descendants. No whole-prefix reconstruction is assumed. -/
theorem ControlledStoredQuery.functionApplicationOrigin
    {strata : EquationStratification env}
    {n : Nat} {key : Key n} {output : Atom n}
    {controls : OriginalWorldControls strata controlSource}
    {frontier : List (World strata.rules.length)}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.app f arg) assigned}
    {query : RichObs sourceEnv env U registry target node locals σ (Profile.fn key output) footprint}
    (ready : ControlledStoredQuery controls frontier (.observation query))
    (location : Located root node) :
    ∃ origin : RichAppOrigin root env registry target source locals σ f arg,
      Nonempty (ControlledStoredQuery controls frontier (.observation origin.function)) ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation origin.argument)) ∧
      Nonempty (GeneralOutputPath env U registry target origin.output
        (show Atom (n + 1) from .fn key output)) ∧
      List.Subset (origin.functionFootprint ++ origin.argumentFootprint) footprint := by
  have nonsortable : ∀ flag, ¬ (Profile.fn key output).HasType (.sort flag) := by
    intro flag sorted
    obtain ⟨cover, member, impossible⟩ := sorted.2.2 _ (List.mem_singleton_self _)
    cases List.mem_singleton.mp member
    contradiction
  obtain ⟨origin, children, path, included, worlds, depth⟩ :=
    ready.annotation.applicationOriginNonsortable location (List.mem_singleton_self _) nonsortable
  refine ⟨origin, ⟨⟨children.function, ?_, ?_⟩⟩, ⟨⟨children.argument, ?_, ?_⟩⟩, path, included⟩
  · intro control active
    exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (depth _)) (ready.within control active)
  · intro world present
    exact ready.sponsored world (worlds (List.mem_append_left _ present))
  · intro control active
    exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (depth _)) (ready.within control active)
  · intro world present
    exact ready.sponsored world (worlds (List.mem_append_right _ present))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
