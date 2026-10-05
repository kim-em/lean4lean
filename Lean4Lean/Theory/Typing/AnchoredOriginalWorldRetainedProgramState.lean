import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedRecipeDemandOpening
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLegacyPiSizedCursor

/-! Machine states distinguish literal rich and literal legacy programs from
attachment wrappers. The budget measures their actual retained annotations.
The charged transition constructs its next state from the original root,
including its real frame, inherited frontier and strictly lower call bank. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

inductive RetainedTypedProgram (sourceEnv env : VEnv) (U : Nat)
    (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {expression assigned : VExpr}
    (node : EndpointState sourceEnv U source expression assigned)
    (locals : List Nat) (σ : Subst) (relevant : Bool) (profile : Profile n) (footprint : Footprint) : Type where
  | rich (query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint) :
      RetainedTypedProgram sourceEnv env U registry target node locals σ relevant profile footprint
  | legacy (query : LegacyRowBody env U registry target locals σ expression relevant profile footprint) :
      RetainedTypedProgram sourceEnv env U registry target node locals σ relevant profile footprint

noncomputable def RetainedTypedProgram.certificate
    (program : RetainedTypedProgram sourceEnv env U registry target node locals σ relevant profile footprint) :
    RichCert sourceEnv env U registry target node locals σ relevant profile footprint :=
  match program with
  | .rich query => query
  | .legacy query => .legacy query.certificate

inductive RetainedTypedProgramProvenance (strata : EquationStratification env) :
    RetainedTypedProgram sourceEnv env U registry target node locals σ relevant profile footprint → Type where
  | rich {query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
      (child : WorldCertProvenance strata query) : RetainedTypedProgramProvenance strata (.rich query)
  | legacy {query : LegacyRowBody env U registry target locals σ expression relevant profile footprint}
      {node : EndpointState sourceEnv U source expression assigned}
      (child : WorldLegacyRowBodyProvenance strata query) :
      RetainedTypedProgramProvenance strata (RetainedTypedProgram.legacy (node := node) query)

noncomputable def RetainedTypedProgramProvenance.certificate
    {program : RetainedTypedProgram sourceEnv env U registry target node locals σ relevant profile footprint}
    (annotation : RetainedTypedProgramProvenance strata program) :
    WorldCertProvenance strata program.certificate :=
  match annotation with
  | .rich child => child
  | .legacy child => .legacy _ child.certificate

noncomputable def RetainedTypedProgramProvenance.programSize
    {program : RetainedTypedProgram sourceEnv env U registry target node locals σ relevant profile footprint}
    (annotation : RetainedTypedProgramProvenance strata program) : Nat :=
  match annotation with
  | .rich child => sizeOf child
  | .legacy child => child.programSize

structure RetainedProgramStateData (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env) (P : VEnv → Prop)
    (frontier : List (World strata.rules.length))
    (Demand : VExpr → {n : Nat} → Atom n → Type) where
  sourceEnv : VEnv
  source : List VExpr
  context : ContextDerivation sourceEnv U source
  expression : VExpr
  assigned : VExpr
  node : EndpointState sourceEnv U source expression assigned
  provenance : EndpointProvenance context node
  controls : OriginalWorldControls strata sourceEnv
  locals : List Nat
  left : Subst
  right : Subst
  available : Valuation
  frame : OriginalRichFrame sourceEnv env U registry target context locals left right available
  captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)
  data : WorldUnaryFrameData P controls frontier frame captured
  closed : available.AtomClosed
  substitutions : Ctx.SubstEq env U target left right source
  sourceBelow : sourceEnv ≤ env
  relevant : Bool
  rank : Nat
  profile : Profile rank
  footprint : Footprint
  program : RetainedTypedProgram sourceEnv env U registry target node locals left relevant profile footprint
  annotation : RetainedTypedProgramProvenance strata program
  within : WithinAbove controls.cutoff controls.fuel
    (fun control => program.certificate.stratifiedDepth (strata.headOrdinal registry) control)
  sponsored : Sponsored frontier annotation.certificate.worlds
  resources : footprint.Available available
  selected : Atom rank
  member : selected ∈ profile.atoms
  demand : Demand expression selected
  paid : Sponsored frontier [originalCallWorld controls .fundamental node captured]
  bank : WorldBoundedUnaryCallBank env U registry strata P
    (frontier ++ [originalCallWorld controls .fundamental node captured])

/-- The application machine specializes the shared original program/frame state.
Only the finite demand grammar depends on the requested terminal shape. -/
abbrev RetainedProgramState (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env) (P : VEnv → Prop)
    (frontier : List (World strata.rules.length)) (goalFunction goalArgument : VExpr)
    (goalOutput : Atom goalRank) :=
  RetainedProgramStateData env U registry target strata P frontier
    (RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput)

noncomputable def RetainedProgramState.programSize
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput) : Nat :=
  state.annotation.programSize

/-- The actual original typing supplies the universe well-formedness needed
by demand normalization; this is not an additional machine-state premise. -/
theorem RetainedProgramState.selfLevels
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput) :
    EqUpToLevels U state.expression state.expression :=
  (EqUpToLevels.refl state.context.forget.levelWF state.node.sound).1

noncomputable def RetainedProgramState.ready
    (state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput) :
    ControlledStoredQuery state.controls frontier (.certificate state.program.certificate) := {
  annotation := state.annotation.certificate
  within := state.within
  sponsored := state.sponsored }

/-- A literal charged leaf gives an actual smaller machine state. The input
inclusions are supplied by the joint literal selector, not semantic replies. -/
theorem RetainedProgramState.openCharged
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
      next.programSize < state.programSize := by
  have bounded : WithinAbove state.controls.cutoff state.controls.fuel
      (fun control => recipe.stratifiedDepth (strata.headOrdinal registry) control) := by
    intro control active
    exact Nat.le_trans (depth _) (state.within control active)
  obtain ⟨input, pending, same, child, childControls, provenance, included, childSmaller,
    cutoffEq, fuelEq, data, ready, readyEq, paid, bank, selected, present, ⟨nextDemand⟩⟩ :=
    annotation.enterPreparedDemandFromBank henv hscoped formed state.node state.controls state.captured
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
  exact ⟨next, Nat.lt_trans childSmaller smaller⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
