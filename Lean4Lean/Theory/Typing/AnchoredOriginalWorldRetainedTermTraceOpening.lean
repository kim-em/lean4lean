import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermProgramState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedRecipeTermDemandTrace

/-! Charged transitions retain the actual displayed requested term along with
strict descent and the same controlled source query, frame and history. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem WorldCodeRecipeProvenance.enterPreparedTermDemandTraceFromBank
    {strata : EquationStratification env} {P : VEnv → Prop}
    {recipe : RichCodeRecipe env U registry target source locals σ expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (caller : EndpointState callerEnv U callerSource callerExpression callerAssigned)
    (controls : OriginalWorldControls strata callerEnv)
    (baseline : WorldEnvironmentProvenance strata U environment)
    (frontier : List (World strata.rules.length))
    (callerPaid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline])
    (sources : annotation.Sources P) (sponsored : Sponsored frontier annotation.worlds)
    (bounded : WithinAbove controls.cutoff controls.fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller baseline]))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : RecipeResourceRealization env U registry target source σ τ footprint)
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (member : atom ∈ profile.atoms) :
    ∃ input : RichRecipeRootInput env U registry target,
    ∃ pending : RichRecipeContext input recipe,
      input.strata = strata ∧
      ∃ child : WorldCertProvenance strata input.certificate,
      ∃ childControls : OriginalWorldControls strata input.owner.selected.origin.source,
      ∃ provenance : EndpointProvenance (.nil : ContextDerivation input.owner.selected.origin.source U []) input.node,
      let frame : OriginalRichFrame input.owner.selected.origin.source env U registry target .nil
        [] input.realization input.realization (fun _ => []) := .nil
      child.worlds ⊆ annotation.worlds ∧ sizeOf child < sizeOf annotation ∧
      childControls.cutoff = input.owner.selected.ordinal - 1 ∧
      childControls.fuel = (fun control => input.certificate.stratifiedDepth (strata.headOrdinal registry) control) ∧
      ∃ data : WorldUnaryFrameData P childControls frontier frame .nil,
      ∃ ready : ControlledStoredQuery childControls frontier (.certificate input.certificate),
        ready.annotation = child ∧
        Sponsored frontier [originalCallWorld childControls .fundamental input.node .nil] ∧
        WorldBoundedUnaryCallBank env U registry strata P
          (frontier ++ [originalCallWorld childControls .fundamental input.node .nil]) ∧
        ∃ selected ∈ input.profile.atoms,
          ∃ nextDemand : RetainedTermDemand env U registry target goal goalOutput
            input.canonicalExpression selected,
          nextDemand.readback input.realization = demand.readback τ ∧
          Nonempty (RetainedRecipeTermDemandPush input pending τ demand nextDemand) := by
  obtain ⟨prepared⟩ := annotation.prepareContextFromBank henv hscoped formed caller controls baseline
    frontier callerPaid sources sponsored bounded bank substitutions resources
  obtain ⟨input, pending, same, sourceReady, child, oldControls, provenance,
    selected, present, nextDemand, sameReadback, pushed, included, smaller⟩ :=
    annotation.focusPreparedTermDemandTrace prepared sources demand member
  cases same
  have children : child.worlds ⊆ annotation.worlds :=
    fun world member => included (List.mem_append_right _ member)
  have rootBound : WithinAbove controls.cutoff controls.fuel
      (headDepth input.owner.selected.ordinal
        (fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control)) := by
    intro control active
    have rootDepth := pending.rootDepth (stratifiedHeadPolicy (input.strata.headOrdinal registry) control)
    have bound := Nat.le_trans rootDepth (bounded control active)
    simpa only [RichRecipeRootInput.recipe, RichCodeRecipe.headDepth, stratifiedHeadPolicy,
      input.owner.headOrdinal_eq, RichCert.stratifiedDepth, headDepth] using bound
  let fuel := fun control => input.certificate.stratifiedDepth (input.strata.headOrdinal registry) control
  let childControls := canonicalQueryControls input.owner.selected fuel
  obtain ⟨data, childPaid, childBank⟩ := canonicalNilOpeningBank (registry := registry) (target := target)
    input.owner input.node input.realization fuel caller controls baseline frontier callerPaid
    sourceReady rootBound bank
  let childReady : ControlledStoredQuery childControls frontier (.certificate input.certificate) := {
    annotation := child
    within := fun _ _ => Nat.le_refl _
    sponsored := fun world member => sponsored world (children member) }
  exact ⟨input, pending, rfl, child, childControls, provenance, children, smaller, rfl, rfl,
    data, childReady, rfl, childPaid, childBank, selected, present, nextDemand, sameReadback, pushed⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
