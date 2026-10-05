import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFunctionApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldConstantValuePruning
import Lean4Lean.Theory.Typing.AnchoredOriginalCanonicalConstOrigin

/-! Extract the actual constant input of the inner application selected from
an exact retained terminal. The returned closed query is pruned from that
original input, with its annotation and all-policy depth retained jointly. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem twoVariableLevelsShape
    {function argument : VExpr} (ρ : Lift)
    (functionLevels : EqUpToLevels U function
      (.app (.const name levels) (.bvar (ρ.liftVar firstIndex))))
    (argumentLevels : EqUpToLevels U argument (.bvar (ρ.liftVar secondIndex))) :
    ∃ sourceLevels, function = .app (.const name sourceLevels) (.bvar (ρ.liftVar firstIndex)) ∧
      argument = .bvar (ρ.liftVar secondIndex) ∧
      EqUpToLevels U (.const name sourceLevels) (.const name levels) := by
  cases functionLevels with
  | app constant argument =>
    cases constant with
    | const leftWF rightWF same =>
      cases argument
      cases argumentLevels
      exact ⟨_, rfl, rfl, .const leftWF rightWF same⟩

/-- The exact operand-level witnesses determine both arbitrary source
indices and the source constant instance. No fixed source slots are assumed. -/
theorem RetainedApplicationOpening.twoVariableShape
    {before : RetainedProgramState env U registry target strata P frontier
      (.app (.const name levels) (.bvar firstIndex)) (.bvar secondIndex) goalOutput}
    (opening : RetainedApplicationOpening before) :
    ∃ sourceLevels,
      opening.function = .app (.const name sourceLevels)
        (.bvar (opening.sourceRenaming.liftVar firstIndex)) ∧
      opening.argument = .bvar (opening.sourceRenaming.liftVar secondIndex) ∧
      EqUpToLevels U (.const name sourceLevels) (.const name levels) :=
  twoVariableLevelsShape opening.sourceRenaming opening.functionLevels opening.argumentLevels

/-- Real inner operand Fs are executed from the saved outer input. The
constant query is then closed at an actual primitive source occurrence;
this exact witness is the base input for reverse charged return. -/
theorem RetainedApplicationOpening.constantFunctionWorld
    {argument : VExpr}
    {before : RetainedProgramState env U registry target strata P frontier goalFunction goalArgument goalOutput}
    (opening : RetainedApplicationOpening before)
    (functionEq : opening.function = .app (.const name levels) argument)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ inner : RichAppOrigin before.provenance.root env registry target
        before.source before.locals before.left (.const name levels) argument,
    ∃ answer : RetainedApplicationAnswers inner before.controls frontier before.right before.available,
    ∃ path : GeneralOutputPath env U registry target inner.output
        (show Atom (opening.origin.rank + 1) from .fn opening.origin.key opening.origin.output),
    ∃ assigned, ∃ site : EndpointRef before.sourceEnv U [] (.const name levels) assigned,
    ∃ query : RichObs before.sourceEnv env U registry target (.ref site) [] before.right
        (Profile.fn inner.key inner.output) [],
    ∃ ready : ControlledStoredQuery before.controls frontier (.observation query),
      ready.annotation.worlds ⊆ before.annotation.certificate.worlds ∧
      ∀ policy, query.headDepth policy ≤ before.program.certificate.headDepth policy := by
  obtain ⟨inner, children, answer, ⟨path⟩, resources, worlds, rooted, depth, functionReady, argumentReady⟩ :=
    opening.physicalFunctionApplicationWorld functionEq henv hscoped formed
  let ready : ControlledStoredQuery before.controls frontier (.observation inner.function) := {
    annotation := children.function
    within := fun control active => Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (depth _) (opening.functionReady.within control active))
    sponsored := fun world member => opening.functionReady.sponsored world
      (worlds (List.mem_append_left _ member)) }
  let head := constantPrefix inner.functionNode
  obtain ⟨closed⟩ := EndpointRef.closedPrimitiveConstant head.reference rfl head.primitive
  obtain ⟨query, queryReady, included, smaller⟩ := ready.pruneConstantFunction (.ref closed.site) [] before.right
  refine ⟨inner, answer, path, _, closed.site, query, queryReady, ?_, ?_⟩
  · intro world member
    exact opening.worlds (List.mem_append_left _
      (worlds (List.mem_append_left _ (included member))))
  · intro policy
    exact Nat.le_trans (smaller policy) (Nat.le_trans (Nat.le_max_left _ _)
      (Nat.le_trans (depth policy) (Nat.le_trans (Nat.le_max_left _ _) (opening.depth policy))))

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
