import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
import Lean4Lean.Theory.Typing.EquationWorldClosureMonotonicity

/-! Retaining an earlier family prefix merges the SAME selected generation
with its baseline. Both lists of dormant queries and exact world ledgers
survive, while their existing sponsors can be retained across the merge. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem WorldGenerated.merge_worlds
    {base : OriginalCaptureBase env U registry target}
    {first : WorldGenerated strata P base caps left right graph firstFrame controls}
    {second : WorldGenerated strata P base caps left right graph secondFrame controls} :
    (first.merge second).worlds = first.worlds ++ second.worlds :=
  WorldEnvironmentProvenance.worlds_append _ _

noncomputable def WorldGenerated.Controlled.merge
    {base : OriginalCaptureBase env U registry target}
    {first : WorldGenerated strata P base caps left right graph firstFrame controls}
    {second : WorldGenerated strata P base caps left right graph secondFrame controls}
    (firstReady : first.Controlled frontier) (secondReady : second.Controlled frontier) :
    (first.merge second).Controlled frontier where
  annotation := firstReady.annotation.append secondReady.annotation
  within := by
    intro control active
    exact Nat.max_le.mpr ⟨firstReady.within control active, secondReady.within control active⟩
  sponsored := by
    rw [RetainedQueryProvenance.worlds_append]
    exact firstReady.sponsored.merge secondReady.sponsored

/-- The old baseline is retained literally; the selected generation must
already be covered by that baseline. No coverage is inferred from cost. -/
theorem WorldGenerated.retainBaseline_covered
    {base : OriginalCaptureBase env U registry target}
    {first : WorldGenerated strata P base caps left right graph firstFrame controls}
    {baseline : WorldGenerated strata P base caps left right graph baselineFrame controls}
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) first.worlds baseline.worlds) :
    Covered (@EquationControlMeasure.Less strata.rules.length) (first.merge baseline).worlds baseline.worlds := by
  rw [WorldGenerated.merge_worlds]
  exact covered.merge (Covered.refl baseline.worlds)

/-- Sponsor children survive a change of captured frame at nondecreasing
capacity. Equal maximum costs use structural capture coverage, not a false
strict decrease between the two parent worlds. -/
theorem originalCallWorld_retargetBelow
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (node : EndpointState sourceEnv U source expression assigned) (phase : RichPhase)
    (previous : WorldEnvironmentProvenance strata U previousEnvironment)
    (next : WorldEnvironmentProvenance strata U nextEnvironment)
    (capacity : environmentCost previousEnvironment ≤ environmentCost nextEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) previous.worlds next.worlds)
    {child : World strata.rules.length}
    (smaller : WorldBelow strata.rules.length child (originalCallWorld controls phase node previous)) :
    WorldBelow strata.rules.length child (originalCallWorld controls phase node next) := by
  apply Below.retarget (r := @EquationControlMeasure.Less strata.rules.length)
    EquationControlMeasure.less_trans ?_ covered smaller
  have cost :
      (OriginalClosureMeasure.Closure.close (node.dependencyOrigin controls.ordered) previousEnvironment).cost ≤
      (OriginalClosureMeasure.Closure.close (node.dependencyOrigin controls.ordered) nextEnvironment).cost :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1)
  by_cases equal :
      (OriginalClosureMeasure.Closure.close (node.dependencyOrigin controls.ordered) previousEnvironment).cost =
      (OriginalClosureMeasure.Closure.close (node.dependencyOrigin controls.ordered) nextEnvironment).cost
  · left
    rw [equal]
  · right
    apply EquationControlMeasure.scheduleDecrease
    exact richSchedule_strict (Nat.lt_of_le_of_ne cost equal) _ _

/-- An existing source sponsor is unchanged. Destination-owned children
are transferred by the checked frame relation, without inserting an extra
copy of either sponsor into the measured frontier. -/
theorem originalCallWorld_retargetSponsorship
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (node : EndpointState sourceEnv U source expression assigned) (phase : RichPhase)
    (previous : WorldEnvironmentProvenance strata U previousEnvironment)
    (next : WorldEnvironmentProvenance strata U nextEnvironment)
    (capacity : environmentCost previousEnvironment ≤ environmentCost nextEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) previous.worlds next.worlds)
    (sourceSponsor : World strata.rules.length)
    {uses : List (World strata.rules.length)}
    (sponsored : Sponsored [sourceSponsor, originalCallWorld controls phase node previous] uses) :
    Sponsored [sourceSponsor, originalCallWorld controls phase node next] uses := by
  intro child member
  obtain ⟨sponsor, present, smaller⟩ := sponsored child member
  rcases List.mem_cons.mp present with rfl | present
  · exact ⟨_, List.mem_cons_self, smaller⟩
  · cases List.mem_singleton.mp present
    exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
      originalCallWorld_retargetBelow controls node phase previous next capacity covered smaller⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
