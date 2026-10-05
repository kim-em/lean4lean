import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDependencyReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalCappedResourceClosure
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBindReservation

/-! Realize a finite common-head dependency at the actual fresh binder.
Only its admitted finite needs change; the tail, domain query, semantic
binder arguments, and immutable reservation remain the same. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private realizeVariableTail from Lean4Lean.Theory.Typing.AnchoredOriginalWorldVariableDemand
open private closeNeeds_fits from Lean4Lean.Theory.Typing.AnchoredOriginalCappedResourceClosure
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- Every new head leaf comes from the concrete finite common-cap program.
No single need at the output grade is requested or assumed available. -/
theorem realizeWorldBinderHeadDependency
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (tail : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph tail.frame.raw controls)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (tail.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (annotation : VExpr) (displayed : A.subst raw = annotation)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals (raw.comp commonLeft)
      true (support : Profile k) domainFootprint)
    (resources : domainFootprint.Available available) (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst (raw.comp commonLeft)) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ k)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade k).atoms, atom ∈ input.atoms)
    (substitutions : Ctx.SubstEq env U target ((raw.comp commonLeft).cons x)
      ((raw.comp commonRight).cons y) (A :: source))
    (frontier : List (World strata.rules.length))
    (replayable : (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).Replayable)
    (ready : (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).Controlled frontier)
    (compatible : (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : (generated.bind baseline capacity domain annotation displayed certificate resources typed arguments needs bounded covered).Hereditary frontier)
    (program : VariableDependencyProgram env U registry target (caps.push (Need.Fits input)) 0 requested) :
    Nonempty (WorldVariableDependencyReply P base (caps.push (Need.Fits input))
      (.bind graph domain annotation displayed) (commonLeft.cons x) (commonRight.cons y)
      controls (reservedBindWorldEnvironment controls domain baseline generated.environment)
      frontier 0 requested) := by
  let combined := needs ++ program.footprint.map Prod.snd
  have fit : ∀ need ∈ combined, Need.Fits input need := by
    intro need member
    rcases List.mem_append.mp member with old | added
    · exact ⟨bounded need old, covered need old⟩
    · obtain ⟨⟨index, wanted⟩, selected, equal⟩ := List.mem_map.mp added
      cases equal
      have indexEq := program.trace.indices selected
      subst index
      exact program.resources 0 wanted selected
  let nextNeeds := combined ++ combined.flatMap Need.singletons
  have fits : ∀ need ∈ nextNeeds, Need.Fits input need :=
    closeNeeds_fits input combined (fun need member => (fit need member).1)
      (fun need member => (fit need member).2)
  let nextFrame := (tail.frame.bind domain certificate resources typed arguments nextNeeds
    (fun need member => (fits need member).1) (fun need member => (fits need member).2)).reserve
      [.close (domain.dependencyOrigin controls.ordered) baselineEnvironment]
  let nextWorld := generated.bind baseline capacity domain annotation displayed certificate resources typed arguments
    nextNeeds (fun need member => (fits need member).1) (fun need member => (fits need member).2)
  let nextReady : nextWorld.Controlled frontier :=
    ⟨ready.annotation, ready.within, ready.sponsored⟩
  let nextH : nextWorld.Hereditary frontier :=
    ⟨⟨hereditary.tablesClosed.1, atomizedNeeds_closed combined⟩, hereditary.bases, hereditary.ready⟩
  obtain ⟨realized, actual, actualReplayable, ⟨actualReady⟩, actualCompatible, ⟨actualH⟩,
      actualWorlds, actualEnvironment⟩ :=
    realizeVariableTail nextFrame nextWorld substitutions replayable nextReady compatible nextH
  let dependency : WorldVariableDependency env U registry target (available.push nextNeeds) 0 requested := {
    rank := program.rank, bound := program.bound, raw := program.raw
    footprint := program.footprint, trace := program.trace, adapter := program.adapter
    resources := by
      intro index need member
      have indexEq := program.trace.indices member
      subst index
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨(0, need), member, rfl⟩)) }
  refine ⟨{
    locals := Locals.push locals, available := available.push nextNeeds
    realization := realized, generation := actual, replayable := actualReplayable
    controlled := actualReady, compatible := actualCompatible, hereditary := actualH
    dependency := dependency, capacity := ?_, covered := ?_ }⟩
  · intro ordered
    rw [actualEnvironment ordered]
    exact Nat.le_refl _
  · rw [actualWorlds]
    exact Covered.refl _

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
