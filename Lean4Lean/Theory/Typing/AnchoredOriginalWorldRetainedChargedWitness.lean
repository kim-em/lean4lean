import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedReadbackOpening
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedRecipeTraceOpening

/-! A charged transition retains the original recipe and its complete pending
context, including resource transfers. The next canonical state is constructed
from that same opening, so a caller compiler can inspect the actual route. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure RetainedChargedOpening
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {atom : Atom n}
    (recipe : RichCodeRecipe env U registry target before.source before.locals before.left
      before.expression relevant profile footprint)
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (incomingDemand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput before.expression atom) where
  input : RichRecipeRootInput env U registry target
  pending : RichRecipeContext input recipe
  strata_eq : input.strata = strata
  child : WorldCertProvenance strata input.certificate
  controls : OriginalWorldControls strata input.owner.selected.origin.source
  provenance : EndpointProvenance (.nil : ContextDerivation input.owner.selected.origin.source U []) input.node
  worlds : child.worlds ⊆ annotation.worlds
  smaller : sizeOf child < sizeOf annotation
  cutoff_eq : controls.cutoff = input.owner.selected.ordinal - 1
  fuel_eq : controls.fuel = fun control => input.certificate.stratifiedDepth (strata.headOrdinal registry) control
  data : WorldUnaryFrameData P controls frontier
    (.nil : OriginalRichFrame input.owner.selected.origin.source env U registry target .nil
      [] input.realization input.realization (fun _ => [])) .nil
  ready : ControlledStoredQuery controls frontier (.certificate input.certificate)
  ready_eq : ready.annotation = child
  paid : Sponsored frontier [originalCallWorld controls .fundamental input.node .nil]
  bank : WorldBoundedUnaryCallBank env U registry strata P
    (frontier ++ [originalCallWorld controls .fundamental input.node .nil])
  selected : Atom input.rank
  member : selected ∈ input.profile.atoms
  demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput input.canonicalExpression selected
  readback : demand.readback input.realization = incomingDemand.readback before.right
  pushed : Nonempty (RetainedRecipeDemandPush input pending before.right incomingDemand demand)

noncomputable def RetainedChargedOpening.next
    {before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {atom : Atom n}
    {recipe : RichCodeRecipe env U registry target before.source before.locals before.left
      before.expression relevant profile footprint}
    {annotation : WorldCodeRecipeProvenance strata recipe}
    {incomingDemand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput before.expression atom}
    (opening : RetainedChargedOpening before recipe annotation incomingDemand) :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput := {
  sourceEnv := opening.input.owner.selected.origin.source
  source := [], context := .nil
  expression := opening.input.canonicalExpression, assigned := .sort opening.input.level
  node := opening.input.node, provenance := opening.provenance, controls := opening.controls
  locals := [], left := opening.input.realization, right := opening.input.realization
  available := fun _ => [], frame := .nil, captured := .nil, data := opening.data
  closed := fun _ _ impossible => nomatch impossible
  substitutions := .nil, sourceBelow := opening.input.owner.selected.origin.sourceBelow
  relevant := opening.input.relevant, rank := opening.input.rank
  profile := opening.input.profile, footprint := opening.input.footprint
  program := .rich opening.input.certificate, annotation := .rich opening.child
  within := opening.ready.within
  sponsored := by
    change Sponsored frontier opening.child.worlds
    rw [← opening.ready_eq]
    exact opening.ready.sponsored
  resources := opening.input.resources
  selected := opening.selected, member := opening.member, demand := opening.demand
  paid := opening.paid, bank := opening.bank }

inductive RetainedChargedTransitionWitness
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput) :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput → Type where
  | intro
      {n : Nat} {relevant : Bool} {profile : Profile n} {footprint : Footprint} {atom : Atom n}
      {recipe : RichCodeRecipe env U registry target before.source before.locals before.left
        before.expression relevant profile footprint}
      (annotation : WorldCodeRecipeProvenance strata recipe)
      (sources : annotation.Sources P)
      (resources : footprint.Available before.available)
      (worlds : annotation.worlds ⊆ before.annotation.certificate.worlds)
      (depth : ∀ policy, recipe.headDepth policy ≤ before.program.certificate.headDepth policy)
      (smaller : sizeOf annotation < before.programSize)
      (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput before.expression atom)
      (member : atom ∈ profile.atoms)
      (path : GeneralOutputPath env U registry target atom before.selected)
      (demand_eq : demand = .output path before.demand)
      (opening : RetainedChargedOpening before recipe annotation demand) :
      RetainedChargedTransitionWitness before opening.next

theorem RetainedProgramState.openChargedWithWitness
    {n : Nat} {relevant : Bool} {profile : Profile n} {footprint : Footprint} {atom : Atom n}
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput)
    {recipe : RichCodeRecipe env U registry target before.source before.locals before.left
      before.expression relevant profile footprint}
    (annotation : WorldCodeRecipeProvenance strata recipe)
    (sources : annotation.Sources P)
    (resources : footprint.Available before.available)
    (worlds : annotation.worlds ⊆ before.annotation.certificate.worlds)
    (depth : ∀ policy, recipe.headDepth policy ≤ before.program.certificate.headDepth policy)
    (smaller : sizeOf annotation < before.programSize)
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput before.expression atom)
    (member : atom ∈ profile.atoms)
    (path : GeneralOutputPath env U registry target atom before.selected)
    (demand_eq : demand = .output path before.demand)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
      next.programSize < before.programSize ∧
      next.demand.readback next.right = before.demand.readback before.right ∧
      Nonempty (RetainedChargedTransitionWitness before next) := by
  have bounded : WithinAbove before.controls.cutoff before.controls.fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control) := by
    intro control active
    exact Nat.le_trans (depth _) (before.within control active)
  obtain ⟨input, pending, same, child, childControls, provenance, included, childSmaller,
    cutoffEq, fuelEq, data, ready, readyEq, paid, bank, selected, present, nextDemand, sameReadback, pushed⟩ :=
    annotation.enterPreparedDemandTraceFromBank henv hscoped formed before.node before.controls before.captured
      frontier before.paid sources (fun world member => before.sponsored world (worlds member))
      bounded before.bank before.substitutions
      (before.frame.recipeResources henv hscoped formed resources) demand member
  let opening : RetainedChargedOpening before recipe annotation demand := {
    input := input, pending := pending, strata_eq := same, child := child
    controls := childControls, provenance := provenance, worlds := included, smaller := childSmaller
    cutoff_eq := cutoffEq, fuel_eq := fuelEq, data := data, ready := ready, ready_eq := readyEq
    paid := paid, bank := bank, selected := selected, member := present, demand := nextDemand
    readback := sameReadback, pushed := pushed }
  have readback : demand.readback before.right = before.demand.readback before.right := by
    rw [demand_eq]
    rfl
  exact ⟨opening.next, Nat.lt_trans childSmaller smaller, sameReadback.trans readback,
    ⟨.intro annotation sources resources worlds depth smaller demand member path demand_eq opening⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
