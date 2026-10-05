import Lean4Lean.Theory.Typing.AnchoredOriginalWorldEqualityRouteStep
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldUnaryDiagonal

/-! Execute an actual original equality at the selected left-diagonal frame,
then return to the externally retained generation without losing histories. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

theorem originalEqualityCallWorld
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (original : Derivation sourceEnv U source A B assigned) (forward : Bool)
    (captured : WorldEnvironmentProvenance strata U environment) :
    originalCallWorld controls .fundamental (.ref (originalTypeRouteSide original forward)) captured =
      originalCallWorld controls .fundamental (.ref (.left original)) captured := by
  cases forward <;> rfl

theorem AmbientBoundedParameterReply.equalityStepWorld
    {sourceEnv env : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {target common : List VExpr}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {commonLeft commonRight : Subst} {start : VExpr}
    {context : ContextDerivation sourceEnv U source}
    (graph : OriginalCaptureMap (common := common) context raw)
    (original : Derivation sourceEnv U source A B (.sort level)) (forward : Bool)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U))
    {strata : EquationStratification env} {P : VEnv → Prop}
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier parent : List (World strata.rules.length))
    (answer : AmbientBoundedParameterReply base commonCaps start
      (parameterEqualityDisplay graph original forward) commonLeft commonRight
      (profile : Profile n) (environmentCost baselineEnvironment))
    (answerData : WorldParameterReplyData (P := P) controls baseline frontier answer)
    (sorted : profile.HasType (.sort relevant))
    (sponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.ref (.left original)) baseline])
    (smaller : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental (.ref (.left original)) baseline]) parent)
    (bank : WorldBoundedUnaryCallBank env U registry strata P parent) :
    ∃ result : AmbientBoundedParameterReply base commonCaps start
        (parameterEqualityDisplay graph original (!forward)) commonLeft commonRight profile
        (environmentCost baselineEnvironment),
      Nonempty (WorldParameterReplyData (P := P) controls baseline frontier result) := by
  let prior := answer.reply.answer.reply
  obtain ⟨footprint, certificate, ready, resources, _⟩ :=
    prior.query.code_controlled henv controls answerData.query sorted
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated prior.realization.frame
    answerData.generation answerData.controlled
    answerData.replayable answerData.compatible answerData.hereditary
  let diagonal := prior.realization.frame.leftDiagonal
  let captured := prior.realization.frame.diagonalWorld controls answerData.generation.environment
  have capacity : environmentCost (diagonal.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment := by
    simpa only [diagonal, OriginalRichFrame.dependencyEnvironment_leftDiagonal]
      using answer.reply.bounded controls.ordered
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      captured.worlds baseline.worlds := by
    simpa only [captured, OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds]
      using answerData.covered
  obtain ⟨changed, ⟨changedReady⟩⟩ := (bank _ smaller).equality original forward
    (.ofLocation .here context) controls diagonal captured baseline frontier capacity covered
    (by rw [originalEqualityCallWorld])
    (by simpa only [originalEqualityCallWorld] using sponsored)
    frameData.leftDiagonal prior.closed formed prior.realization.substitutions.left
    (.code certificate) resources ready.code
  obtain ⟨result, output, _, _, _⟩ := answer.equalityResultWorld graph original forward
    henv hscoped formed controls baseline frontier answerData sorted changed changedReady
  exact ⟨result, ⟨output⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
