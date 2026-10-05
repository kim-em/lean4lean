import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplicationReadback
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedLegacyBodyDispatch
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedChargedWitness

/-! A physical application terminal retains the original operand queries,
their exact selected output path and the same normalized incoming demand.
The terminal's state is the actual input, including raw legacy programs. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder EquationStratifiedFuel
open private appendTerminalPath from Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedProgramApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

structure RetainedApplicationOpening
    {goalRank : Nat} {goalOutput : Atom goalRank}
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput) where
  function : VExpr
  argument : VExpr
  expressionEq : before.expression = .app function argument
  origin : RichAppOrigin before.provenance.root env registry target before.source before.locals before.left function argument
  rooted : PrefixRoute before.sourceEnv U before.source (.app function argument)
    (before.node.cast expressionEq rfl) origin.node
  children : RichAppWorlds strata origin
  worlds : children.worlds ⊆ before.annotation.certificate.worlds
  depth : ∀ policy, max (origin.function.headDepth policy) (origin.argument.headDepth policy) ≤
    before.program.certificate.headDepth policy
  resources : (origin.functionFootprint ++ origin.argumentFootprint).Available before.available
  answer : RetainedApplicationAnswers origin before.controls frontier before.right before.available
  sourceRenaming : Lift
  functionLevels : EqUpToLevels U function (goalFunction.lift' sourceRenaming)
  argumentLevels : EqUpToLevels U argument (goalArgument.lift' sourceRenaming)
  selectedPath : GeneralOutputPath env U registry target origin.output before.selected
  finalPath : GeneralOutputPath env U registry target before.selected goalOutput
  normalized : RetainedDemandHeadNormalization env U registry target goalFunction goalArgument goalOutput
    (expressionEq ▸ before.demand) (.application sourceRenaming functionLevels argumentLevels finalPath)
  readback : (goalFunction.subst (Subst.lift_l sourceRenaming before.right),
    goalArgument.subst (Subst.lift_l sourceRenaming before.right)) = before.demand.readback before.right

noncomputable def RetainedApplicationOpening.terminal
    {before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (opening : RetainedApplicationOpening before) :
    RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput := {
  state := before, function := opening.function, argument := opening.argument
  expressionEq := opening.expressionEq, origin := opening.origin, rooted := opening.rooted
  answer := opening.answer, sourceRenaming := opening.sourceRenaming
  functionLevels := opening.functionLevels, argumentLevels := opening.argumentLevels
  output := appendTerminalPath opening.selectedPath opening.finalPath }

inductive RetainedApplicationTerminalWitness
    (before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput) :
    RetainedProgramTerminal env U registry target strata P frontier goalFunction goalArgument goalOutput → Type where
  | intro (opening : RetainedApplicationOpening before) :
      RetainedApplicationTerminalWitness before opening.terminal

theorem RetainedApplicationTerminalWitness.readback
    (witness : RetainedApplicationTerminalWitness before terminal) :
    terminal.readback = before.demand.readback before.right := by
  cases witness with
  | intro opening => exact opening.readback

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
