import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedRecipeMachine
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionAtoms

/-! Concrete pending application demands. Universe changes and skipped private
binders are explicit syntax operations; a body instruction owns its computed
right-anchor admission. No instruction contains an interpreter callback. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive RetainedApplicationDemand (env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    (goalFunction goalArgument : VExpr) (goalOutput : Atom goalRank) : VExpr → {n : Nat} → Atom n → Type where
  | application : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput
      (.app goalFunction goalArgument) goalOutput
  | output (path : GeneralOutputPath env U registry target old next)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression next) :
      RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression old
  | domain {support : Profile n} {rows : List (Key n × Profile n)}
      (member : atom ∈ support.atoms)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput A atom) :
      RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput (.forallE A B)
        (n := n + 1) (.pi prototypeDomain prototypeBody support rows)
  | body {support result : Profile n} {rows : List (Key n × Profile n)}
      (selected : (key, result) ∈ rows) (member : atom ∈ result.atoms)
      (anchor : VExpr) (admitted : Admitted env U registry target key anchor anchor)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput B atom) :
      RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput (.forallE A B)
        (n := n + 1) (.pi prototypeDomain prototypeBody support rows)
  | levels (equal : EqUpToLevels U sourceExpression expression)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom) :
      RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput sourceExpression atom
  | rename (ρ : Lift)
      (continuation : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom) :
      RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput (expression.lift' ρ) atom

private def PreparedRecipeContext.parentGoal
    (recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint)
    (τ : Subst) : Prop :=
  match recipe with
  | .root .. => True
  | .domain parent | .fixedBody parent _ _ | .resources parent _ | .action _ parent =>
      Nonempty (PreparedRecipeContext parent τ)
  | .body parent _ _ => Nonempty (PreparedRecipeContext parent τ.tail)

private theorem PreparedRecipeContext.parentPrepared
    (prepared : PreparedRecipeContext recipe τ) : PreparedRecipeContext.parentGoal recipe τ := by
  cases prepared with
  | root => trivial
  | domain parent | fixedBody parent | resources parent | action parent => exact ⟨parent⟩
  | body parent selected anchor admitted => exact ⟨parent⟩

/-- Push the full demand backward through every original recipe operation.
The next program is the SAME literal root certificate, with strict annotation
descent. Body guards have already been computed from genuine lower calls. -/
theorem WorldCodeRecipeProvenance.focusPreparedDemand
    {strata : EquationStratification env}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (prepared : PreparedRecipeContext recipe τ)
    (sources : annotation.Sources P)
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (member : atom ∈ profile.atoms) :
    ∃ input : RichRecipeRootInput env U registry target,
      Nonempty (RichRecipeContext input recipe) ∧ input.strata = strata ∧
      P input.owner.selected.origin.source ∧
      ∃ child : WorldCertProvenance strata input.certificate,
      ∃ controls : OriginalWorldControls strata input.owner.selected.origin.source,
      ∃ provenance : EndpointProvenance (.nil : ContextDerivation input.owner.selected.origin.source U []) input.node,
      ∃ selected ∈ input.profile.atoms,
        Nonempty (RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput
          input.canonicalExpression selected) ∧
        List.Subset ((WorldQuerySite.empty (registry := registry) (target := target)
          controls provenance input.realization).worlds ++ child.worlds) annotation.worlds ∧
        sizeOf child < sizeOf annotation := by
  match annotation with
  | .root source locals σ owner node closed expressionEq realization certificate supplied child controls provenance =>
    refine ⟨⟨_, _, owner, _, _, _, node, closed, expressionEq, source, locals, σ,
      realization, _, _, _, _, certificate, supplied⟩, ⟨.root⟩, rfl, sources,
      child, controls, provenance, atom, member, ⟨.levels expressionEq demand⟩,
      List.Subset.refl _, ?_⟩
    simp_wf
    omega
  | .domain child =>
    obtain ⟨previous⟩ := prepared.parentPrepared
    obtain ⟨input, ⟨pending⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, included, smaller⟩ :=
      child.focusPreparedDemand previous sources (.domain member demand) List.mem_cons_self
    refine ⟨input, ⟨.domain pending⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, included, Nat.lt_trans smaller ?_⟩
    simp_wf
    omega
  | .body child selected anchor =>
    obtain ⟨previous⟩ := prepared.parentPrepared
    obtain ⟨input, ⟨pending⟩, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, included, smaller⟩ :=
      child.focusPreparedDemand previous sources
        (.body selected member (τ 0) prepared.bodyAdmission demand) List.mem_cons_self
    refine ⟨input, ⟨.body pending selected anchor⟩, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, included, Nat.lt_trans smaller ?_⟩
    simp_wf
    omega
  | .fixedBody child selected admitted =>
    obtain ⟨previous⟩ := prepared.parentPrepared
    have lifted := RetainedApplicationDemand.rename (.skip .refl) demand
    rw [← lift_eq_lift'] at lifted
    obtain ⟨input, ⟨pending⟩, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, included, smaller⟩ :=
      child.focusPreparedDemand previous sources
        (.body selected member _ admitted lifted) List.mem_cons_self
    refine ⟨input, ⟨.fixedBody pending selected admitted⟩, same, sourceReady, cert, controls, provenance,
      nextAtom, present, nextDemand, included, Nat.lt_trans smaller ?_⟩
    simp_wf
    omega
  | .resources child transfer =>
    obtain ⟨previous⟩ := prepared.parentPrepared
    obtain ⟨input, ⟨pending⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, included, smaller⟩ :=
      child.focusPreparedDemand previous sources demand member
    refine ⟨input, ⟨.resources pending _⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, (fun _ h => List.mem_append_left _ (included h)),
      Nat.lt_trans smaller ?_⟩
    simp_wf
    omega
  | .action (parent := parent) change child =>
    obtain ⟨previous⟩ := prepared.parentPrepared
    obtain ⟨old, oldMember, ⟨selectedAction⟩⟩ := change.atom member
    obtain ⟨input, ⟨pending⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, included, smaller⟩ :=
      child.focusPreparedDemand previous sources
        (.output (.code .refl selectedAction (parent.formed.singleton_of_mem oldMember)) demand) oldMember
    refine ⟨input, ⟨.action pending change⟩, same, sourceReady, cert, controls, provenance,
      selected, present, nextDemand, included, Nat.lt_trans smaller ?_⟩
    simp_wf
    omega
termination_by sizeOf annotation
decreasing_by all_goals simp_wf; omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
