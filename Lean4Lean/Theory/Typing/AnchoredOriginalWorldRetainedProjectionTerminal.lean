import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProjectionExecution
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermChargedWitness
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDemandHead

/-! A physical projection terminal owns the original major observation and
field certificate, their actual worlds and resource bounds, and the exact
normalized incoming demand. A charged terminal instead enters its original
recipe using the shared term-state transition. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private appendPath from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedTermDemandHead
open private SortableCert.retainedProjectionNoAtom from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProjectionSelection
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure RetainedProjectionOpening
    (before : RetainedTermProgramState env U registry target strata P frontier goal goalOutput) where
  name : Name
  index : Nat
  major : VExpr
  expressionEq : before.expression = .proj name index major
  origin : RetainedNativeProjectionOrigin before.provenance.root env registry target
    before.source before.locals before.left name index major
  rooted : PrefixRoute before.sourceEnv U before.source (.proj name index major)
    (before.node.cast expressionEq rfl) (projectionNatural origin.head)
  children : RetainedProjectionChildren strata origin
  worlds : children.worlds ⊆ before.annotation.certificate.worlds
  depth : ∀ policy, max (origin.majorQuery.headDepth policy) (origin.fieldCode.headDepth policy) ≤
    before.program.certificate.headDepth policy
  resources : (origin.majorFootprint ++ origin.fieldFootprint).Available before.available
  answer : RetainedProjectionMajorAnswer origin before.controls frontier before.right before.available
  sourceRenaming : Lift
  sourceLevels : EqUpToLevels U (.proj name index major) (goal.lift' sourceRenaming)
  selectedPath : GeneralOutputPath env U registry target origin.output before.selected
  finalPath : GeneralOutputPath env U registry target before.selected goalOutput
  normalized : RetainedTermHeadNormalization env U registry target goal goalOutput
    (expressionEq ▸ before.demand) (.terminal sourceRenaming sourceLevels finalPath)
  readback : goal.subst (Subst.lift_l sourceRenaming before.right) = before.demand.readback before.right

noncomputable def RetainedProjectionOpening.output
    {before : RetainedTermProgramState env U registry target strata P frontier goal goalOutput}
    (opening : RetainedProjectionOpening before) :
    GeneralOutputPath env U registry target opening.origin.output goalOutput :=
  appendPath opening.selectedPath opening.finalPath

structure RetainedProjectionProgramTerminal (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (strata : EquationStratification env) (P : VEnv → Prop)
    (frontier : List (World strata.rules.length)) (goal : VExpr) (goalOutput : Atom goalRank) where
  state : RetainedTermProgramState env U registry target strata P frontier goal goalOutput
  opening : RetainedProjectionOpening state

noncomputable def RetainedProjectionProgramTerminal.readback
    (terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier goal goalOutput) : VExpr :=
  goal.subst (Subst.lift_l terminal.opening.sourceRenaming terminal.state.right)

inductive RetainedProjectionTerminalWitness
    (before : RetainedTermProgramState env U registry target strata P frontier goal goalOutput) :
    RetainedProjectionProgramTerminal env U registry target strata P frontier goal goalOutput → Type where
  | intro (opening : RetainedProjectionOpening before) :
      RetainedProjectionTerminalWitness before ⟨before, opening⟩

theorem RetainedProjectionTerminalWitness.readback
    (witness : RetainedProjectionTerminalWitness before terminal) :
    terminal.readback = before.demand.readback before.right := by
  cases witness with
  | intro opening => exact opening.readback

/-- Literal projection selection returns its actual physical opening or a
strictly smaller charged state. No source or caller interpretation is supplied
as a terminal hypothesis. -/
theorem richProjectionProgramStepWitness
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source (.proj name index value) assigned}
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
    (demand : RetainedTermDemand env U registry target goal goalOutput (.proj name index value) atom)
    (selected : atom ∈ profile.atoms)
    (ρ : Lift) (sourceLevels : EqUpToLevels U (.proj name index value) (goal.lift' ρ))
    (finalPath : GeneralOutputPath env U registry target atom goalOutput)
    (sameReadback : goal.subst (Subst.lift_l ρ τ) = demand.readback τ)
    (normalized : RetainedTermHeadNormalization env U registry target goal goalOutput
      demand (.terminal ρ sourceLevels finalPath)) :
    let state := RetainedTermProgramState.ofRich ready provenance frame captured data closed substitutions
      resources sourceBelow paid bank demand selected
    (∃ terminal : RetainedProjectionProgramTerminal env U registry target strata P frontier goal goalOutput,
      terminal.readback = demand.readback τ ∧
        Nonempty (RetainedProjectionTerminalWitness state terminal)) ∨
      ∃ next : RetainedTermProgramState env U registry target strata P frontier goal goalOutput,
        next.programSize < sizeOf (show WorldCertProvenance strata query from ready.annotation) ∧
        Nonempty (RetainedTermChargedTransitionWitness state next) := by
  let state := RetainedTermProgramState.ofRich ready provenance frame captured data closed substitutions
    resources sourceBelow paid bank demand selected
  obtain ⟨origin, children, ⟨path⟩, supplied, worlds, rooted, smaller, depth, ⟨step⟩⟩ :=
    ready.executeRetainedProjectionSized provenance frame captured data closed formed substitutions
      resources paid bank selected
  cases step with
  | @executed actual answer =>
    obtain ⟨route⟩ := rooted
    cases children with
    | original annotation =>
      let opening : RetainedProjectionOpening state := {
        name := name, index := index, major := value, expressionEq := rfl
        origin := actual, rooted := route, children := annotation
        worlds := worlds, depth := depth, resources := supplied, answer := answer
        sourceRenaming := ρ, sourceLevels := sourceLevels
        selectedPath := path, finalPath := finalPath, normalized := normalized, readback := sameReadback }
      exact .inl ⟨⟨state, opening⟩, sameReadback, ⟨.intro opening⟩⟩
  | pending actual =>
    cases children with
    | charged annotation =>
      obtain ⟨next, nextSmaller, readback, witness⟩ := state.openChargedWithWitness annotation
        (annotation.sourcesBelow sourceClosed) supplied worlds depth smaller
        (.output path demand) actual.selected path rfl henv hscoped formed
      exact .inr ⟨next, nextSmaller, witness⟩

/-- Legacy syntax has no literal projection constructor. It therefore cannot
be a selected projection terminal; it is never reattached to inflate the
annotation bound for another recursive step. -/
theorem legacyProjectionProgramNoMember
    (query : LegacyRowBody env U registry target locals σ (.proj name index value) relevant profile footprint)
    (selected : atom ∈ profile.atoms) : False :=
  SortableCert.retainedProjectionNoAtom query.certificate selected

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
