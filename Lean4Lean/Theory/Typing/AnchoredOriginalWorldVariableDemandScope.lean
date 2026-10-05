import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemandData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldUnweaken

/-! A variable demand crosses temporary common scopes without changing its
source frame, selected need, or dormant annotations. This permits descent
under an outer binder while retaining the actual incoming original. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private realizeVariableTail from Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemand
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem WorldVariableDemandReply.weaken
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps nextCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U environment}
    {frontier : List (World strata.rules.length)}
    (answer : WorldVariableDemandReply P base caps graph commonLeft commonRight controls baseline frontier index requested)
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (capsTail : (fun i => nextCaps (ρ.liftVar i)) = caps) :
    Nonempty (WorldVariableDemandReply P base nextCaps (.weaken graph insertion) nextLeft nextRight
      controls baseline frontier index requested) := by
  let generated := answer.generation.weaken insertion leftTail rightTail capsTail
  let hereditary : generated.Hereditary frontier :=
    ⟨answer.hereditary.tablesClosed, answer.hereditary.bases, answer.hereditary.ready⟩
  let ready : generated.Controlled frontier :=
    ⟨answer.controlled.annotation, answer.controlled.within, answer.controlled.sponsored⟩
  obtain ⟨realization, actual, replayable, ⟨ready⟩, compatible, ⟨actualHereditary⟩, worlds, environments⟩ :=
    realizeVariableTail answer.realization.frame generated answer.realization.substitutions
      answer.replayable ready answer.compatible hereditary
  refine ⟨{
    locals := answer.locals, available := answer.available, realization := realization, generation := actual
    replayable := replayable, controlled := ready, compatible := compatible, hereditary := actualHereditary
    capacity := ?_, covered := ?_, demand := answer.demand }⟩
  · intro ordered
    rw [environments ordered]
    exact answer.capacity ordered
  · rw [worlds]
    exact answer.covered

theorem WorldVariableDemandReply.unweaken
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps nextCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    {controls : OriginalWorldControls strata sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U environment}
    {frontier : List (World strata.rules.length)}
    {ρ : Lift} (insertion : Ctx.Lift' ρ common next)
    (leftTail : Subst.lift_l ρ nextLeft = commonLeft)
    (rightTail : Subst.lift_l ρ nextRight = commonRight)
    (capsTail : (fun i => nextCaps (ρ.liftVar i)) = caps)
    (answer : WorldVariableDemandReply P base nextCaps (.weaken graph insertion) nextLeft nextRight
      controls baseline frontier index requested) :
    Nonempty (WorldVariableDemandReply P base caps graph commonLeft commonRight
      controls baseline frontier index requested) := by
  cases leftTail
  cases rightTail
  cases capsTail
  obtain ⟨generated, environmentEq, queries, replayable, compatible, bases, tables, ready, readyWorlds⟩ :=
    answer.generation.unweakenControlled answer.controlled
  let hereditary : generated.Hereditary frontier :=
    ⟨tables.mpr answer.hereditary.tablesClosed,
      answer.hereditary.bases.cast bases.symm,
      answer.hereditary.bases.ready_cast bases.symm answer.hereditary.ready⟩
  obtain ⟨realization, actual, actualReplayable, ⟨actualReady⟩, actualCompatible,
      ⟨actualHereditary⟩, worlds, environments⟩ :=
    realizeVariableTail answer.realization.frame generated answer.realization.substitutions
      (replayable.mpr answer.replayable) ready ((compatible _ _).mpr answer.compatible) hereditary
  refine ⟨{
    locals := answer.locals, available := answer.available, realization := realization, generation := actual
    replayable := actualReplayable, controlled := actualReady, compatible := actualCompatible, hereditary := actualHereditary
    capacity := ?_, covered := ?_, demand := answer.demand }⟩
  · intro ordered
    rw [environments ordered]
    exact answer.capacity ordered
  · rw [worlds]
    change Covered _ generated.environment.worlds baseline.worlds
    rw [environmentEq]
    exact answer.covered

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
