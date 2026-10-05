import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationProgress

/-! Legacy application programs contain no charged leaves. Their literal
children are attached at the actual original application prefix and executed
by its proper-child bank; no rebuilt certificate is recursively interpreted. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem WorldLegacyRowBodyProvenance.executeApplicationWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : LegacyRowBody env U registry target locals σ (.app f a) relevant profile footprint}
    (annotation : WorldLegacyRowBodyProvenance strata query)
    (within : WithinAbove controls.cutoff controls.fuel
      (fun control => query.certificate.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (sponsored : Sponsored frontier annotation.certificate.worlds)
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available)
    (henv : env.Ordered) (hscoped : registry.Scoped) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (selected : atom ∈ profile.atoms) :
    ∃ origin : RichAppOrigin provenance.root env registry target source locals σ f a,
      Nonempty (PrefixRoute sourceEnv U source (.app f a) node origin.node) ∧
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      Nonempty (RetainedApplicationAnswers origin controls frontier τ available) := by
  obtain ⟨original, children, path, included, worlds, depth⟩ :=
    annotation.certificate.applicationOrigin selected
  let origin := RichAppOrigin.ofSortablePrefix (applicationPrefix provenance.location) original
  have functionReady : ControlledStoredQuery controls frontier (.observation origin.function) := {
    annotation := .legacy original.function children.function
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, origin, RichAppOrigin.ofSortablePrefix, RichObs.headDepth] using
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (depth _) (within control active))
    sponsored := fun world member => sponsored world
      (worlds (List.mem_append_left _ member)) }
  have argumentReady : ControlledStoredQuery controls frontier (.observation origin.argument) := {
    annotation := .legacy original.argument children.argument
    within := by
      intro control active
      simpa only [StoredOriginalQuery.headDepth, origin, RichAppOrigin.ofSortablePrefix, RichObs.headDepth] using
        Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (depth _) (within control active))
    sponsored := fun world member => sponsored world
      (worlds (List.mem_append_right _ member)) }
  have supplied : (origin.functionFootprint ++ origin.argumentFootprint).Available available :=
    fun index need member => resources index need (included member)
  obtain ⟨answer⟩ := origin.executeWorld (applicationPrefix provenance.location).route
    provenance controls frame captured frontier data closed formed substitutions supplied
    functionReady argumentReady henv hscoped sourceBelow paid bank
  exact ⟨origin, ⟨(applicationPrefix provenance.location).route⟩, path, ⟨answer⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
