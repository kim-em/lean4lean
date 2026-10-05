import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyHistoryPreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldReplayableGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistory

/-! Leaving a temporary common scope retains the exact selected frame and
its dormant history. This is the positive-generation step needed after
replaying a captured owner into a weakened destination. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private retained_worlds_cast from Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private noncomputable def unweakenWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph frame controls) : Prop :=
  match graph, generated with
  | .weaken (ρ := ρ) previous _, generated =>
    ∃ next : WorldGenerated strata P base (fun index => commonCaps (ρ.liftVar index))
        (Subst.lift_l ρ commonLeft) (Subst.lift_l ρ commonRight) previous frame controls,
      next.environment = generated.environment ∧
      next.retainedQueries = generated.retainedQueries ∧
      (next.Replayable ↔ generated.Replayable) ∧
      (∀ cutoff fuel, next.UsesControlPrefix cutoff fuel ↔ generated.UsesControlPrefix cutoff fuel) ∧
      next.baseUses = generated.baseUses ∧
      (next.TablesClosed ↔ generated.TablesClosed)
  | _, _ => True

private theorem unweakenWorld_merge
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {graph : OriginalCaptureMap (common := common) context raw}
    {left : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ leftAvailable}
    {right : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ rightAvailable}
    {first : WorldGenerated strata P base commonCaps commonLeft commonRight graph left controls}
    {second : WorldGenerated strata P base commonCaps commonLeft commonRight graph right controls}
    (firstIH : unweakenWorld first) (secondIH : unweakenWorld second) :
    unweakenWorld (.merge first second) := by
  cases graph <;> try trivial
  obtain ⟨nextFirst, firstEnvironment, firstQueries, firstReplay, firstPrefix, firstBases, firstTables⟩ := firstIH
  obtain ⟨nextSecond, secondEnvironment, secondQueries, secondReplay, secondPrefix, secondBases, secondTables⟩ := secondIH
  refine ⟨.merge nextFirst nextSecond, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change nextFirst.environment.append nextSecond.environment = first.environment.append second.environment
    rw [firstEnvironment, secondEnvironment]
  · change nextFirst.retainedQueries ++ nextSecond.retainedQueries = first.retainedQueries ++ second.retainedQueries
    rw [firstQueries, secondQueries]
  · exact and_congr firstReplay secondReplay
  · intro cutoff fuel
    exact and_congr (firstPrefix cutoff fuel) (secondPrefix cutoff fuel)
  · change nextFirst.baseUses ++ nextSecond.baseUses = first.baseUses ++ second.baseUses
    rw [firstBases, secondBases]
  · exact and_congr firstTables secondTables

private theorem WorldGenerated.unweakenInvariant
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph frame controls) :
    unweakenWorld generated := by
  induction generated with
  | merge _ _ first second => exact unweakenWorld_merge first second
  | identity | empty | bind | capture | historyGroup => trivial
  | weaken generated insertion leftTail rightTail capsTail _ =>
    cases leftTail
    cases rightTail
    cases capsTail
    exact ⟨generated, rfl, rfl, Iff.rfl, (fun _ _ => Iff.rfl), rfl, Iff.rfl⟩

/-- Unweakening changes only the common scope. The actual annotated
capture environment and the entire retained query list are unchanged. -/
theorem WorldGenerated.unweaken
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {nextCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {ρ : Lift} {insertion : Ctx.Lift' ρ common next}
    (generated : WorldGenerated strata P base nextCaps nextLeft nextRight (.weaken graph insertion) frame controls) :
    ∃ previous : WorldGenerated strata P base (fun index => nextCaps (ρ.liftVar index))
        (Subst.lift_l ρ nextLeft) (Subst.lift_l ρ nextRight) graph frame controls,
      previous.environment = generated.environment ∧
      previous.retainedQueries = generated.retainedQueries ∧
      (previous.Replayable ↔ generated.Replayable) ∧
      (∀ cutoff fuel, previous.UsesControlPrefix cutoff fuel ↔ generated.UsesControlPrefix cutoff fuel) ∧
      previous.baseUses = generated.baseUses ∧
      (previous.TablesClosed ↔ generated.TablesClosed) :=
  generated.unweakenInvariant

/-- The control annotation is transported along the exact retained-query
identity, keeping its original query-owned worlds as well as the frame. -/
theorem WorldGenerated.unweakenControlled
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {nextCaps : CaptureCaps}
    {context : ContextDerivation sourceEnv U source}
    {controls : OriginalWorldControls strata sourceEnv}
    {graph : OriginalCaptureMap (common := common) context raw}
    {frame : RawOriginalRichFrame sourceEnv env U registry target context locals σ τ available}
    {ρ : Lift} {insertion : Ctx.Lift' ρ common next}
    (generated : WorldGenerated strata P base nextCaps nextLeft nextRight (.weaken graph insertion) frame controls)
    {frontier : List (World strata.rules.length)}
    (ready : generated.Controlled frontier) :
    ∃ previous : WorldGenerated strata P base (fun index => nextCaps (ρ.liftVar index))
        (Subst.lift_l ρ nextLeft) (Subst.lift_l ρ nextRight) graph frame controls,
      previous.environment = generated.environment ∧
      previous.retainedQueries = generated.retainedQueries ∧
      (previous.Replayable ↔ generated.Replayable) ∧
      (∀ cutoff fuel, previous.UsesControlPrefix cutoff fuel ↔ generated.UsesControlPrefix cutoff fuel) ∧
      previous.baseUses = generated.baseUses ∧
      (previous.TablesClosed ↔ generated.TablesClosed) ∧
      ∃ previousReady : previous.Controlled frontier,
        previousReady.annotation.worlds = ready.annotation.worlds := by
  obtain ⟨previous, environment, queries, replayable, compatible, bases, tables⟩ := generated.unweaken
  let annotation : RetainedQueryProvenance strata previous.retainedQueries := queries.symm ▸ ready.annotation
  have worlds : annotation.worlds = ready.annotation.worlds := retained_worlds_cast queries.symm ready.annotation
  let previousReady : previous.Controlled frontier := {
    annotation := annotation
    within := by
      intro control active
      change previous.retainedDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control) ≤ controls.fuel control
      rw [← previous.retainedQueries_depth, queries, generated.retainedQueries_depth]
      exact ready.within control active
    sponsored := worlds.symm ▸ ready.sponsored }
  exact ⟨previous, environment, queries, replayable, compatible, bases, tables, previousReady, worlds⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
