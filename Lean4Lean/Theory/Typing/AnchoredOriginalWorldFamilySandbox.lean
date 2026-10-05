import Lean4Lean.Theory.Typing.AnchoredOriginalWorldControlPrefix
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedBaseFreeze

/-! The retained-family caller deliberately rebases its entire current
source frame for local resource freezing. The sandbox has exactly the
caller's actual world ledger. Its raw queries inherit annotations from the
original hereditary generation; that original generation remains the
outer caller's state and is not reconstructed from the sandbox. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

/-- Every visible query is literally among the hereditary retained queries.
The reverse inclusion is deliberately not asserted: dormant histories need
the original generation after returning from an identity sandbox. -/
theorem WorldGenerated.storedQueries_in_retained
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls) :
    frame.storedQueries ⊆ generated.retainedQueries := by
  induction generated with
  | weaken _ _ _ _ _ ih => exact ih
  | merge first second ih₁ ih₂ =>
    intro query member
    change query ∈ first.retainedQueries ++ second.retainedQueries
    simp only [RawOriginalRichFrame.storedQueries] at member
    exact (List.mem_append.mp member).elim
      (fun member => List.mem_append_left _ (ih₁ member))
      (fun member => List.mem_append_right _ (ih₂ member))
  | identity => exact fun _ member => member
  | empty =>
    intro query member
    simp only [RawOriginalRichFrame.storedQueries] at member
    cases member
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    intro query member
    change query ∈ .certificate certificate :: generated.retainedQueries
    simp only [RawOriginalRichFrame.storedQueries] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih member)
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih =>
    intro selected member
    change selected ∈ .observation query :: .certificate certificate :: generated.retainedQueries
    simp only [RawOriginalRichFrame.storedQueries] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_self ..
    apply List.mem_cons_of_mem
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih member)
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      ih _ _ _ _ =>
    intro query member
    simp only [RawOriginalRichFrame.storedQueries] at member
    change query ∈ (((((richGroupedEntriesRaw entries).storedQueries ++ generated.retainedQueries) ++
      (.observation seed.query :: seedGenerated.retainedQueries)) ++ priorGenerated.retainedQueries) ++
      ((List.finRange history.route.frames.length).flatMap (fun index => (historyGenerated index).retainedQueries))) ++
      (entries.attach.flatMap (fun entry => (owners entry.val entry.property).retainedQueries))
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact (List.mem_append.mp member).elim
      (fun member => List.mem_append_left _ member)
      (fun member => List.mem_append_right _ (ih member))

/-- Choose the sandbox from the actual current frame. Its world list is
identical to the caller's, including every original captured closure; no
new sponsor or larger numerical control table is introduced. -/
theorem WorldGenerated.identitySandbox
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (generated : WorldGenerated strata P base caps left right graph frame.raw controls)
    (ready : generated.Controlled frontier) :
    let sandbox := frame.captureBase substitutions
    ∃ identity : WorldGenerated strata P sandbox sandbox.initialCaps σ τ
        (.identity context) frame.raw controls,
      identity.worlds = generated.worlds ∧
      identity.UsesControlPrefix controls.cutoff controls.fuel ∧
      Nonempty (identity.Controlled frontier) := by
  let sandbox := frame.captureBase substitutions
  let identity : WorldGenerated strata P sandbox sandbox.initialCaps σ τ
      (.identity context) frame.raw controls :=
    WorldGenerated.identity (base := sandbox) generated.erase.ambientGenerated.ambient.2
      generated.erase.sources.2 controls generated.environment
  obtain ⟨annotation, sponsored⟩ :=
    ready.annotation.sponsored_subset ready.sponsored generated.storedQueries_in_retained
  refine ⟨identity, rfl, ⟨rfl, rfl⟩, ⟨⟨annotation, ?_, sponsored⟩⟩⟩
  intro control active
  have smaller := StoredOriginalQuery.maximumDepth_mono
    (stratifiedHeadPolicy (strata.headOrdinal registry) control) generated.storedQueries_in_retained
  rw [RawOriginalRichFrame.storedQueries_depth, generated.retainedQueries_depth] at smaller
  exact Nat.le_trans smaller (ready.within control active)

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
