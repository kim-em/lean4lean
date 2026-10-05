import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecordContinuation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalRichCodeHeadDepth

/-! The R-to-F seam retains both actual sponsors. Source-derived openings may
remain below the source, while newly reconstructed right projection sites
are paid by the actual next destination F. All evidence names one and the
same selected reply, generation, and extracted observer. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open private recordShape_raise recordShape_normal recordAdapter_rigid from
  Lean4Lean.Theory.Typing.AnchoredOriginalRichRecordExtraction
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

@[simp] theorem RichObs.headDepth_lowerRaised (current : Name → Nat → Nat)
    {n N : Nat} {profile : Profile n} {bound : n ≤ N}
    (source : RichObs sourceEnv env U registry target node locals σ
      (raiseProfile N bound profile) footprint) :
    source.lowerRaised.headDepth current = source.headDepth current := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simp only [RichObs.lowerRaised, dif_pos]
      exact RichObs.headDepth_mpr current rfl rfl (raiseProfile_self ..) rfl
        (congrArg (fun p => RichObs sourceEnv env U registry target node locals σ p footprint)
          (raiseProfile_self profile).symm) source
    · have previous : n ≤ N := by omega
      simp only [RichObs.lowerRaised, dif_neg equal]
      let changed := (congrArg (fun p => RichObs sourceEnv env U registry target node locals σ p footprint)
        (raiseProfile_step previous profile)).mp source
      change (RichObs.unpad changed).lowerRaised.headDepth current = _
      refine (ih (source := .unpad changed)).trans ?_
      simp only [RichObs.headDepth]
      exact RichObs.headDepth_mp current rfl rfl (raiseProfile_step previous profile) rfl _ source

theorem RichGradedResult.recordObservation_worlds_depth
    (henv : env.Ordered)
    (result : RichGradedResult sourceEnv env U registry target node locals σ available
      (Profile.singleton (n := n + 1) (.record (record : RecordData (Profile n)))))
    (annotation : WorldObsProvenance strata result.observation) :
    ∃ footprint, ∃ observation : RichObs sourceEnv env U registry target node locals σ
      (Profile.singleton (n := n + 1) (.record record)) footprint,
      ∃ output : WorldObsProvenance strata observation,
        footprint.Available available ∧ output.worlds = annotation.worlds ∧
        ∀ policy, observation.headDepth policy = result.observation.headDepth policy := by
  have adapter := result.adapter
  rw [raiseProfile_singleton] at adapter
  have shape := recordShape_raise record result.bound
  have normalized := recordShape_normal shape
  change GeneralProfileAdapter env U registry target _ (.singleton (AdapterNormal.atom _)) at adapter
  rw [normalized] at adapter
  obtain ⟨normal, member, ⟨entry⟩⟩ := adapter.origin (List.mem_singleton_self _)
  obtain ⟨original, originalMember, equal⟩ := List.mem_map.mp member
  subst normal
  have same := recordAdapter_rigid entry shape
  let selected := RichObs.view (.select result.observation originalMember) (AdapterNormal.view henv original)
  have outputEq : Profile.singleton (AdapterNormal.atom original) =
      raiseProfile result.rank result.bound (Profile.singleton (n := n + 1) (.record record)) := by
    simp only [raiseProfile_singleton, same]
  let observed : RichObs sourceEnv env U registry target node locals σ
      (raiseProfile result.rank result.bound (Profile.singleton (n := n + 1) (.record record))) result.footprint :=
    (congrArg (fun profile => RichObs sourceEnv env U registry target node locals σ profile result.footprint) outputEq).mp selected
  let output : WorldObsProvenance strata observed.lowerRaised :=
    .lowerRaised (.castProfile outputEq (.view (.select annotation originalMember) (AdapterNormal.view henv original)))
  refine ⟨result.footprint, observed.lowerRaised, output, result.resources, rfl, ?_⟩
  intro policy
  rw [RichObs.headDepth_lowerRaised]
  exact (RichObs.headDepth_mp policy rfl rfl outputEq rfl _ selected).trans
    (by simp only [selected, RichObs.headDepth])


/-- Actual mixed-sponsor continuation. The R producer must supply coverage
of its selected frame and readiness under the source plus next destination;
neither follows merely from numerical capacity. Extraction preserves both
its worlds and head depths on the SAME observer. -/
theorem BoundedGeneratedQueryReply.controlledRecordContinuation
    {base : OriginalCaptureBase env U registry target}
    {display : OriginalNestedDisplay U common expression assigned}
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata display.sourceEnv)
    (henv : env.Ordered)
    (prior : OriginalCaptureRealization display.graph env registry target
      locals commonLeft commonRight available)
    (priorGeneration : WorldGenerated strata P base caps commonLeft commonRight
      display.graph prior.frame.raw controls)
    (reply : BoundedGeneratedQueryReply base caps display commonLeft commonRight
      (Profile.singleton (n := n + 1) (.record (record : RecordData (Profile n))))
      (environmentCost (prior.frame.dependencyEnvironment controls.ordered)))
    (nextGeneration : WorldGenerated strata P base caps commonLeft commonRight
      display.graph reply.answer.reply.realization.frame.raw controls)
    (source : EquationWorldClosureOrder.World strata.rules.length)
    (covered : EquationWorldClosureOrder.Covered (@EquationControlMeasure.Less strata.rules.length)
      nextGeneration.worlds priorGeneration.worlds)
    (ready : ControlledStoredQuery controls
      [source, originalCallWorld controls .fundamental display.node nextGeneration.environment]
      (.observation reply.answer.reply.query.observation)) :
    let previous := originalCallWorld controls .expressionReindex display.node priorGeneration.environment
    let next := originalCallWorld controls .fundamental display.node nextGeneration.environment
    ∃ footprint, ∃ observation : RichObs display.sourceEnv env U registry target display.node
      reply.answer.reply.locals (display.raw.comp commonLeft)
      (Profile.singleton (n := n + 1) (.record record)) footprint,
      ∃ output : ControlledStoredQuery controls [source, next] (.observation observation),
        footprint.Available reply.answer.reply.available ∧
        output.annotation.worlds = ready.annotation.worlds ∧
        EquationWorldClosureOrder.CallBelow strata.rules.length [source, next] [source, previous] ∧
        EquationWorldClosureOrder.Sponsored [source, next]
          (output.annotation.worlds ++ nextGeneration.worlds) := by
  obtain ⟨footprint, observation, annotation, resources, worlds, depth⟩ :=
    reply.answer.reply.query.recordObservation_worlds_depth henv ready.annotation
  let output : ControlledStoredQuery controls
      [source, originalCallWorld controls .fundamental display.node nextGeneration.environment]
      (.observation observation) := {
    annotation := annotation
    within := by
      intro control active
      change observation.headDepth _ ≤ _
      rw [depth]
      exact ready.within control active
    sponsored := by
      change EquationWorldClosureOrder.Sponsored _ annotation.worlds
      rw [worlds]
      exact ready.sponsored }
  have decrease := (reply.sponsoredFundamentalDecrease controls.ordered prior
    strata.rules.length controls.cutoff controls.fuel source priorGeneration.worlds
    nextGeneration.worlds [] covered (by intro _ member; cases member)).1
  refine ⟨footprint, observation, output, resources, worlds, decrease, ?_⟩
  apply output.sponsored.merge
  intro child member
  exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, .child member⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
