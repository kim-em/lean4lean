import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFundedFamilyHeaderData
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyTerminalEnrichment

/-! Enriched independent header plans return through their actual retained
constant carriers. New header openings are funded by the enclosing call;
old canonical sites and their fuel masks are preserved literally. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

noncomputable def WorldFundedFamilyHeaderAt.rebuildControlled
    {strata : EquationStratification env}
    {callerControls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)} {parent : World strata.rules.length}
    (selected : WorldFundedFamilyHeaderAt callerControls U registry target name levels frontier parent)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    {typeRealization planRealization : Subst} {demand support : Profile n}
    (certificate : RichCert selected.header.origin.source env U registry target
      (.ref (selected.header.origin.familyHeader selected.header.seedWF).reference)
      [] typeRealization true support [])
    (typed : demand.HasType support)
    (plan : RichFamilyPlan env U registry target
      (selected.header.origin.familyHeader selected.header.seedWF).reference
      name selected.header.seed selected.header.signature .nil planRealization [] demand [])
    (certificateReady : ControlledStoredQuery selected.controls frontier (.certificate certificate))
    (planAnnotation : WorldFamilyPlanProvenance strata plan)
    (planWithin : EquationStratifiedFuel.WithinAbove selected.controls.cutoff selected.controls.fuel
      (fun control => plan.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control)))
    (planSponsored : Sponsored frontier planAnnotation.worlds)
    (callerPaid : Sponsored frontier [parent]) :
    ControlledStoredQuery callerControls frontier
      (.observation (selected.carrier.rebuild certificate typed plan caller locals σ)) := by
  apply selected.carrier.rebuildControlled certificate typed plan caller locals σ
    certificateReady planAnnotation planWithin planSponsored
  · intro world member
    obtain ⟨sponsor, present, smaller⟩ := callerPaid parent (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans (selected.openingsBelow world member) smaller⟩
  · intro world member
    change world ∈ [originalCallWorld selected.controls .fundamental
      (.ref (selected.header.origin.familyHeader selected.header.seedWF).reference) .nil] at member
    cases List.mem_singleton.mp member
    obtain ⟨sponsor, present, smaller⟩ := callerPaid parent (List.mem_singleton_self _)
    exact ⟨sponsor, present, EquationWorldClosureOrder.trans
      (r := @EquationControlMeasure.Less strata.rules.length)
      EquationControlMeasure.less_trans selected.headerBelow smaller⟩

/-- This consumes the actual enriched plan at its restored original header,
not a descriptor or a completed observation supplied by a semantic oracle. -/
theorem WorldFundedFamilyHeaderAt.rebuildPlanControlled
    {strata : EquationStratification env}
    {callerControls : OriginalWorldControls strata sourceEnv}
    {frontier : List (World strata.rules.length)} {parent : World strata.rules.length}
    (selected : WorldFundedFamilyHeaderAt callerControls U registry target name levels frontier parent)
    (caller : EndpointState sourceEnv U source (.const name levels) assigned)
    (locals : List Nat) (σ : Subst)
    (updated : RichFamilyPlanResult env U registry target
      (selected.header.origin.familyHeader selected.header.seedWF).reference
      name selected.header.seed selected.header.signature .nil
      (.ref (selected.header.origin.familyHeader selected.header.seedWF).reference)
      realization [] (fun _ => []) atom)
    (ready : updated.WorldControlled selected.controls frontier)
    (callerPaid : Sponsored frontier [parent]) :
    ∃ query : RichObs sourceEnv env U registry target caller locals σ (.singleton atom) [],
      ∃ output : ControlledStoredQuery callerControls frontier (.observation query),
        output.annotation.worlds = selected.carrier.openings ++
          (WorldQuerySite.empty (registry := registry) (target := target) selected.controls
            (EndpointProvenance.ofLocation
              (.here (root := (selected.header.origin.familyHeader selected.header.seedWF).reference)) .nil)
            realization).worlds ++ ready.code.annotation.worlds ++ ready.plan.worlds ∧
        ∀ policy, query.headDepth policy = selected.carrier.maskDepth policy
          (max (updated.plan.headDepth policy) (updated.certificate.headDepth policy)) := by
  rcases updated with ⟨footprint, plan, resources, support, typeFootprint, certificate, typeResources, typed⟩
  have empty : footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    exact nomatch resources index need member
  have typeEmpty : typeFootprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    rintro ⟨index, need⟩ member
    exact nomatch typeResources index need member
  cases empty
  cases typeEmpty
  let query := selected.carrier.rebuild certificate typed plan caller locals σ
  let output := selected.rebuildControlled caller locals σ certificate typed plan
    ready.code ready.plan ready.planWithin ready.planSponsored callerPaid
  refine ⟨query, output, ?_, ?_⟩
  · exact selected.carrier.rebuildAnnotation_worlds certificate typed plan caller locals σ
      ready.code.annotation ready.plan
  · exact selected.carrier.rebuild_headDepth certificate typed plan caller locals σ

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
