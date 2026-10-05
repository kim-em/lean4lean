import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation

/-! Retained-family replay uses the caller's cutoff and fuel at every source
and declaration header. This property follows the actual generation tree,
including dormant owner histories. It is not inferred for arbitrary captured
worlds: independently controlled canonical openings need their own invariant. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def OriginalWorldControls.HasPrefix
    (controls : OriginalWorldControls strata sourceEnv) (cutoff : Nat) (fuel : Nat → Nat) : Prop :=
  controls.cutoff = cutoff ∧ controls.fuel = fuel

noncomputable def WorldGenerated.UsesControlPrefix
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls)
    (cutoff : Nat) (fuel : Nat → Nat) : Prop := by
  induction generated with
  | weaken _ _ _ _ _ ih => exact ih
  | merge first second ih₁ ih₂ => exact ih₁ ∧ ih₂
  | identity ambient sources controls environment => exact controls.HasPrefix cutoff fuel
  | empty common left right below source controls => exact controls.HasPrefix cutoff fuel
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact ih
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih => exact ih
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH =>
    exact tailIH ∧ seedIH ∧ priorIH ∧
      (∀ index, historyIH index) ∧ (∀ entry member, ownerIH entry member) ∧
      ownerControls.HasPrefix cutoff fuel

theorem WorldGenerated.UsesControlPrefix.controls_match
    {base : OriginalCaptureBase env U registry target}
    {generated : WorldGenerated strata P base caps left right graph frame controls}
    (same : generated.UsesControlPrefix cutoff fuel) : controls.HasPrefix cutoff fuel := by
  induction generated with
  | weaken _ _ _ _ _ ih => exact ih same
  | merge first second ih₁ ih₂ => exact ih₁ same.1
  | identity => exact same
  | empty => exact same
  | bind generated baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered ih =>
    exact ih same
  | capture generated baseline capacity domain initial argument location lineage query queryAvailable queryBound queryAdapter
      certificate resources typed arguments needs bounded covered ih => exact ih same
  | historyGroup generated domain ownerGraph nominalGraph nominal provenance displayed ownerOrdered headerOrdered ownerInitial
      seed seedScope seedControls seedGenerated domainProvenance prior history priorGenerated initialProvenance baselines routeInputs
      historyWellFormed historyControls historyGenerated tailBound entries scopes ownerControls owners
      ownerAmbient nominalAmbient priorAmbient routeAmbient ownerSources nominalSources priorSources routeSources
      tailIH seedIH priorIH historyIH ownerIH => exact tailIH same.1

theorem OriginalWorldControls.HasPrefix.same
    {cutoff : Nat} {fuel : Nat → Nat}
    {first : OriginalWorldControls strata firstSource}
    {second : OriginalWorldControls strata secondSource}
    (hf : first.HasPrefix cutoff fuel) (hs : second.HasPrefix cutoff fuel) :
    first.cutoff = second.cutoff ∧ first.fuel = second.fuel :=
  ⟨hf.1.trans hs.1.symm, hf.2.trans hs.2.symm⟩

/-- Keep exactly the selected annotation and existing sponsor frontier.
The target controls already carry their own source-cutoff proof. Only the
query's numerical table is transported through the checked prefix equality. -/
def ControlledStoredQuery.recontrol
    {strata : EquationStratification env}
    {first : OriginalWorldControls strata firstSource}
    (second : OriginalWorldControls strata secondSource)
    {frontier : List (World strata.rules.length)}
    {query : StoredOriginalQuery env U registry target}
    (ready : ControlledStoredQuery first frontier query)
    (sameCutoff : first.cutoff = second.cutoff) (sameFuel : first.fuel = second.fuel) :
    ControlledStoredQuery second frontier query where
  annotation := ready.annotation
  within := by
    rw [← sameCutoff, ← sameFuel]
    exact ready.within
  sponsored := ready.sponsored

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
