import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDemand

/-! Literal-term specialization of the shared original program state. Both
application and projection compilers retain the same frame, original query,
annotation, hereditary data and funded lower calls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

abbrev RetainedTermProgramState (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env) (P : VEnv → Prop)
    (frontier : List (World strata.rules.length)) (goal : VExpr)
    (goalOutput : Atom goalRank) :=
  RetainedProgramStateData env U registry target strata P frontier
    (RetainedTermDemand env U registry target goal goalOutput)

noncomputable def RetainedTermProgramState.programSize
    (state : RetainedTermProgramState env U registry target strata P frontier goal goalOutput) : Nat :=
  state.annotation.programSize

/-- The actual original typing supplies the universe well-formedness needed
by demand normalization; this is not an additional machine-state premise. -/
theorem RetainedTermProgramState.selfLevels
    (state : RetainedTermProgramState env U registry target strata P frontier goal goalOutput) :
    EqUpToLevels U state.expression state.expression :=
  (EqUpToLevels.refl state.context.forget.levelWF state.node.sound).1

noncomputable def RetainedTermProgramState.ready
    (state : RetainedTermProgramState env U registry target strata P frontier goal goalOutput) :
    ControlledStoredQuery state.controls frontier (.certificate state.program.certificate) := {
  annotation := state.annotation.certificate
  within := state.within
  sponsored := state.sponsored }

noncomputable def RetainedTermProgramState.ofRich
    {sourceEnv : VEnv} {source : List VExpr} {expression assigned : VExpr}
    {locals : List Nat} {σ τ : Subst} {available : Valuation}
    {relevant : Bool} {n : Nat} {profile : Profile n} {footprint : Footprint} {atom : Atom n}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source expression assigned}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {query : RichCert sourceEnv env U registry target node locals σ relevant profile footprint}
    (ready : ControlledStoredQuery controls frontier (.certificate query))
    (provenance : EndpointProvenance context node)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (closed : available.AtomClosed) (substitutions : Ctx.SubstEq env U target σ τ source)
    (resources : footprint.Available available) (sourceBelow : sourceEnv ≤ env)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (demand : RetainedTermDemand env U registry target goal goalOutput expression atom)
    (member : atom ∈ profile.atoms) :
    RetainedTermProgramState env U registry target strata P frontier goal goalOutput := {
  sourceEnv := sourceEnv, source := source, context := context, expression := expression, assigned := assigned
  node := node, provenance := provenance, controls := controls
  locals := locals, left := σ, right := τ, available := available
  frame := frame, captured := captured, data := data
  closed := closed, substitutions := substitutions, sourceBelow := sourceBelow
  relevant := relevant, rank := _, profile := profile, footprint := footprint
  program := .rich query, annotation := .rich ready.annotation
  within := ready.within, sponsored := ready.sponsored, resources := resources
  selected := atom, member := member, demand := demand, paid := paid, bank := bank }


end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
