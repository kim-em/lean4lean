import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchor
import Lean4Lean.Theory.Typing.AnchoredOriginalSourcePredicatesDiagonal

/-! Unary equality uses the actual left-diagonal frame. Its existing queries
and closure annotations are unchanged; the caller's operative generation is
retained outside the identity sandbox. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private theorem transport_worlds
    {strata : EquationStratification env}
    {first second : List Closure} (same : first = second)
    (world : WorldEnvironmentProvenance strata U first) :
    (same ▸ world : WorldEnvironmentProvenance strata U second).worlds = world.worlds := by
  cases same
  rfl

noncomputable def OriginalRichFrame.diagonalWorld
    {strata : EquationStratification env}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)) :
    WorldEnvironmentProvenance strata U (frame.leftDiagonal.dependencyEnvironment controls.ordered) :=
  by
    change WorldEnvironmentProvenance strata U
      (frame.raw.dependencyEnvironment controls.ordered) at captured
    change WorldEnvironmentProvenance strata U
      (frame.raw.leftDiagonal.dependencyEnvironment controls.ordered)
    simpa only [RawOriginalRichFrame.dependencyEnvironment_leftDiagonal] using captured

theorem OriginalRichFrame.diagonalWorld_worlds
    {strata : EquationStratification env}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)) :
    (frame.diagonalWorld controls captured).worlds = captured.worlds :=
  by
    have same : frame.diagonalWorld controls captured =
        (frame.dependencyEnvironment_leftDiagonal controls.ordered).symm ▸ captured := by
      apply eq_of_heq
      simp only [OriginalRichFrame.diagonalWorld, Eq.mpr, eqRec_heq_iff, heq_eqRec_iff, id_eq]
      rfl
    rw [same]
    exact transport_worlds _ captured

noncomputable def WorldUnaryFrameData.leftDiagonal
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)}
    {frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)}
    (data : WorldUnaryFrameData P controls frontier frame captured) :
    WorldUnaryFrameData P controls frontier frame.leftDiagonal (frame.diagonalWorld controls captured) where
  ambient := OriginalRichFrame.Ambient.leftDiagonal frame data.ambient
  sources := OriginalRichFrame.AllSources.leftDiagonal frame data.sources
  queries := frame.diagonal_queryControls controls data.queries
  history := .leftDiagonal data.history
  historyReady := data.historyReady

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
