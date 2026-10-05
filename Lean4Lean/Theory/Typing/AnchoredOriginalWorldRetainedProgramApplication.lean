import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramState
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedApplicationProgress

/-! Application machine step. A physical input performs the actual two proper
child F calls. A charged input enters the original canonical program at a
strictly smaller annotation budget. Terminal data remain source-relative. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure RetainedProgramTerminal (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env) (P : VEnv → Prop)
    (frontier : List (World strata.rules.length)) (goalFunction goalArgument : VExpr)
    (goalOutput : Atom goalRank) where
  state : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput
  function : VExpr
  argument : VExpr
  expressionEq : state.expression = .app function argument
  origin : RichAppOrigin state.provenance.root env registry target state.source state.locals state.left function argument
  rooted : PrefixRoute state.sourceEnv U state.source (.app function argument)
    (state.node.cast expressionEq rfl) origin.node
  answer : RetainedApplicationAnswers origin state.controls frontier state.right state.available
  sourceRenaming : Lift
  functionLevels : EqUpToLevels U function (goalFunction.lift' sourceRenaming)
  argumentLevels : EqUpToLevels U argument (goalArgument.lift' sourceRenaming)
  output : GeneralOutputPath env U registry target origin.output goalOutput

private noncomputable def appendTerminalPath
    (first : GeneralOutputPath env U registry target a b)
    (second : GeneralOutputPath env U registry target b c) :
    GeneralOutputPath env U registry target a c := by
  induction second with
  | refl => exact first
  | action path change ih => exact .action ih change
  | code path change formed ih => exact .code ih change formed
  | pad path ih => exact .pad ih
  | unpad path ih => exact .unpad ih

noncomputable def RetainedProgramState.ofRich
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
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput expression atom)
    (member : atom ∈ profile.atoms) :
    RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput := {
  sourceEnv := sourceEnv, source := source, context := context, expression := expression, assigned := assigned
  node := node, provenance := provenance, controls := controls
  locals := locals, left := σ, right := τ, available := available
  frame := frame, captured := captured, data := data
  closed := closed, substitutions := substitutions, sourceBelow := sourceBelow
  relevant := relevant, rank := _, profile := profile, footprint := footprint
  program := .rich query, annotation := .rich ready.annotation
  within := ready.within, sponsored := ready.sponsored, resources := resources
  selected := atom, member := member, demand := demand, paid := paid, bank := bank }

theorem richApplicationProgramStep
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
    (sourceClosed : ∀ next ≤ env, P next)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental node captured]))
    (demand : RetainedApplicationDemand env U registry target goalFunction goalArgument goalOutput (.app f a) atom)
    (selected : atom ∈ profile.atoms)
    (ρ : Lift) (functionLevels : EqUpToLevels U f (goalFunction.lift' ρ))
    (argumentLevels : EqUpToLevels U a (goalArgument.lift' ρ))
    (finalPath : GeneralOutputPath env U registry target atom goalOutput) :
    Nonempty (RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput) ∨
      ∃ next : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput,
        next.programSize < sizeOf (show WorldCertProvenance strata query from ready.annotation) := by
  let state := RetainedProgramState.ofRich ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank demand selected
  obtain ⟨origin, children, ⟨path⟩, supplied, worlds, rooted, smaller, depth, ⟨step⟩⟩ :=
    ready.executeRetainedApplicationSized provenance frame captured data closed formed substitutions
      resources henv hscoped sourceBelow paid bank selected
  cases step with
  | @executed actual answer =>
    obtain ⟨route⟩ := rooted
    exact .inl ⟨{
      state := state, function := f, argument := a, expressionEq := rfl
      origin := actual, rooted := route, answer := answer
      sourceRenaming := ρ, functionLevels := functionLevels, argumentLevels := argumentLevels
      output := appendTerminalPath path finalPath }⟩
  | pending actual =>
    cases children with
    | charged annotation =>
      obtain ⟨next, nextSmaller⟩ := state.openCharged annotation
        (annotation.sourcesBelow sourceClosed) supplied worlds depth smaller
        (.output path demand) actual.selected henv hscoped formed
      exact .inr ⟨next, nextSmaller⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
