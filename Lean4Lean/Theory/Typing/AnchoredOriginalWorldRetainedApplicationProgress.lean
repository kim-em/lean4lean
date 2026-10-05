import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationSelectionSize
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationBody

/-! The operative selected-application step carries a strict bound for any
remaining charged annotation. A recursive interpreter may recurse on this
literal input; the operand F answers never enter that measure. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem ControlledStoredQuery.executeRetainedApplicationSized
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.app f a) assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query))
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
    ∃ origin : RetainedApplicationOrigin provenance.root env registry target source locals σ f a,
    ∃ children : RetainedApplicationWorlds strata origin,
      Nonempty (GeneralOutputPath env U registry target origin.output atom) ∧
      origin.footprint.Available available ∧ children.worlds ⊆ ready.annotation.worlds ∧
      origin.RootedAt node ∧ children.retainedSize < sizeOf (show WorldCertProvenance strata query from ready.annotation) ∧ (∀ policy, origin.headDepth policy ≤ query.headDepth policy) ∧
      Nonempty (RetainedApplicationStep controls frontier τ available origin) := by
  obtain ⟨origin, children, path, included, worlds, rooted, smaller, depth⟩ :=
    ready.annotation.retainedApplicationOriginSized provenance.location selected (budget := sizeOf (show WorldCertProvenance strata query from ready.annotation)) (Nat.le_refl _)
  have supplied : origin.footprint.Available
      available :=
    fun index need member => resources index need (included member)
  refine ⟨origin, children, path, supplied, worlds, rooted, smaller, depth, ?_⟩
  cases origin with
  | charged actual => exact ⟨.pending actual⟩
  | original actual =>
    cases children with
    | original annotation =>
      obtain ⟨route⟩ := rooted
      have functionReady : ControlledStoredQuery controls frontier (.observation actual.function) := {
        annotation := annotation.function
        within := fun control active => Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (depth _) (ready.within control active))
        sponsored := fun world member => ready.sponsored world
          (worlds (List.mem_append_left _ member)) }
      have argumentReady : ControlledStoredQuery controls frontier (.observation actual.argument) := {
        annotation := annotation.argument
        within := fun control active => Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (depth _) (ready.within control active))
        sponsored := fun world member => ready.sponsored world
          (worlds (List.mem_append_right _ member)) }
      obtain ⟨answer⟩ := actual.executeWorld route provenance controls frame captured
        frontier data closed formed substitutions supplied
        functionReady argumentReady henv hscoped sourceBelow paid bank
      exact ⟨.executed answer⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
