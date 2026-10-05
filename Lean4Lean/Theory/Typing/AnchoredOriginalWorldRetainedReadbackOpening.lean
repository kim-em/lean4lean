import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedDemandReadback

/-! Charged transitions retain the actual displayed final operands along with
strict descent and the same controlled source query, frame and history. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem WorldCodeRecipeProvenance.enterPreparedDemandReadbackFromBank
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
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
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
          ∃ nextDemand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput
            input.canonicalExpression selected,
          nextDemand.readback input.realization = demand.readback τ := by
  obtain ⟨prepared⟩ := annotation.prepareContextFromBank henv hscoped formed caller controls baseline
    frontier callerPaid sources sponsored bounded bank substitutions resources
  obtain ⟨input, ⟨pending⟩, same, sourceReady, child, oldControls, provenance,
    selected, present, nextDemand, sameReadback, included, smaller⟩ :=
    annotation.focusPreparedDemandReadback prepared sources demand member
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
    data, childReady, rfl, childPaid, childBank, selected, present, nextDemand, sameReadback⟩


theorem RetainedProgramState.openChargedReadback
    {n : Nat} {relevant : Bool} {profile : Profile n} {footprint : Footprint} {atom : Atom n}
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    {recipe : RichCodeRecipe env U registry target state.source state.locals state.left
      state.expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (sources : annotation.Sources P)
    (resources : footprint.Available state.available)
    (worlds : annotation.worlds ⊆ state.annotation.certificate.worlds)
    (depth : ∀ policy, recipe.headDepth policy ≤ state.program.certificate.headDepth policy)
    (smaller : sizeOf annotation < state.programSize)
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput state.expression atom)
    (member : atom ∈ profile.atoms)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < state.programSize ∧
      next.demand.readback next.right = demand.readback state.right := by
  have bounded : WithinAbove state.controls.cutoff state.controls.fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control) := by
    intro control active
    exact Nat.le_trans (depth _) (state.within control active)
  obtain ⟨input, pending, same, child, childControls, provenance, included, childSmaller,
    cutoffEq, fuelEq, data, ready, readyEq, paid, bank, selected, present, nextDemand, sameReadback⟩ :=
    annotation.enterPreparedDemandReadbackFromBank henv hscoped formed state.node state.controls state.captured
      frontier state.paid sources (fun world member => state.sponsored world (worlds member))
      bounded state.bank state.substitutions
      (state.frame.recipeResources henv hscoped formed resources) demand member
  let next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput := {
    sourceEnv := input.owner.selected.origin.source
    source := [], context := .nil
    expression := input.canonicalExpression, assigned := .sort input.level
    node := input.node, provenance := provenance, controls := childControls
    locals := [], left := input.realization, right := input.realization
    available := fun _ => [], frame := .nil, captured := .nil, data := data
    closed := fun _ _ impossible => nomatch impossible
    substitutions := .nil, sourceBelow := input.owner.selected.origin.sourceBelow
    relevant := input.relevant, rank := input.rank, profile := input.profile, footprint := input.footprint
    program := .rich input.certificate, annotation := .rich child
    within := ready.within
    sponsored := by
      change Sponsored frontier child.worlds
      rw [← readyEq]
      exact ready.sponsored
    resources := input.resources
    selected := selected, member := present, demand := nextDemand
    paid := paid, bank := bank }
  exact ⟨next, Nat.lt_trans childSmaller smaller, sameReadback⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
