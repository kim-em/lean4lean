import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHeaderFamilyPlan
import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyApplication
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldGradedApplication

/-! A newly chosen caller header reconstructs its own native family query.
The same enriched request and actual packed argument rebuild the actual
caller application; no old carrier or captured-history reply is reused. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private bareFamilyWorld from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldRetainedFamilyApplication
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

/-- Reconstruct both the actual caller observation and its sorted certificate
from the restored header plan and the very same argument query. Every frozen
request field, including the full assigned support, remains literal. -/
theorem RichFamilyPlanResult.callerApplicationWorld
    {strata : EquationStratification env}
    {seedLevels levels : List VLevel}
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (origin : ConstantHeaderOrigin sourceEnv name info)
    (lookup : env.constants name = some info)
    (notDefinition : registry.definitions name = none)
    (notNative : registry.natives name = none) (notQuotient : name ≠ ``Quot.lift)
    (seedWF : ∀ level ∈ seedLevels, level.WF U)
    (seedLength : seedLevels.length = info.uvars)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) seedLevels levels)
    (signature : ConstantTelescope (info.type.instL seedLevels))
    (typeClosed : info.type.Closed)
    {request : DataRequest (Profile n)}
    (plan : RichFamilyPlanResult env U registry target (origin.familyHeader seedWF).reference
      name seedLevels signature .nil (.ref (origin.familyHeader seedWF).reference)
      realization [] (fun _ => []) (n := n+2)
      (.fn (Key.pad request.toKeyData) (.family ⟨name, seedLevels, familyRelevant, [request]⟩)))
    (planReady : plan.WorldControlled (controls.atHeader origin) frontier)
    {sourceDomain : EndpointState sourceEnv U source A (.sort u)}
    {sourceBody : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source (.const name levels) (.forallE A B)}
    {argument : EndpointState sourceEnv U source a A}
    {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (hu : u.WF U) (hv : v.WF U)
    (argumentQuery : RichGradedResult sourceEnv env U registry target argument locals σ available request.input)
    (argumentReady : ControlledStoredQuery controls frontier (.observation argumentQuery.observation))
    (anchorEq : request.anchor = a.subst σ)
    (admission : RankedData.RequestAdmission env U (relations env U registry n) target
      request (a.subst σ) rightValue)
    (caller : EndpointState sourceEnv U source callerExpression callerAssigned)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental caller baseline]) :
    ∃ query : RichGradedResult sourceEnv env U registry target
      (.app hu hv sourceDomain sourceBody function argument result) locals σ available
      (.singleton (n := n+1) (.family ⟨name, seedLevels, familyRelevant, [request]⟩)),
    ∃ queryReady : ControlledStoredQuery controls frontier (.observation query.observation),
      query.footprint = argumentQuery.footprint ∧
      ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target
        (.app hu hv sourceDomain sourceBody function argument result) locals σ familyRelevant
        (.singleton (n := n+1) (.family ⟨name, seedLevels, familyRelevant, [request]⟩)) footprint,
        footprint.Available available ∧
        ∃ certificateReady : ControlledStoredQuery controls frontier (.certificate certificate),
          certificateReady.annotation.worlds ⊆ queryReady.annotation.worlds := by
  let atCaller : plan.WorldControlled controls frontier := {
    plan := planReady.plan
    planWithin := planReady.planWithin
    planSponsored := planReady.planSponsored
    code := ControlledStoredQuery.recontrol controls planReady.code rfl rfl }
  obtain ⟨functionObservation, ⟨functionReady⟩⟩ := bareFamilyWorld controls frontier
    origin lookup notDefinition notNative notQuotient seedWF seedLength levelsWF equivalent
    signature typeClosed plan atCaller caller baseline .fundamental paid
    (node := function) (locals := locals) (σ := σ)
  have admitted : Admitted env U registry target request.toKeyData (a.subst σ) (a.subst σ) :=
    Admitted.left_diagonal admission.toAdmission
  have padded := Admitted.pad henv admitted
  have anchorAdmitted : Admitted env U registry target (Key.pad request.toKeyData)
      (Key.pad request.toKeyData).anchor (Key.pad request.toKeyData).anchor := by
    simpa only [Key.pad, anchorEq] using padded
  let functionQuery : RichGradedResult sourceEnv env U registry target function locals σ available
      (Profile.fn (Key.pad request.toKeyData) (.family ⟨name, seedLevels, familyRelevant, [request]⟩)) := {
    rank := n+2
    bound := Nat.le_refl _
    raw := Profile.fn (Key.pad request.toKeyData) (.family ⟨name, seedLevels, familyRelevant, [request]⟩)
    footprint := []
    observation := functionObservation
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := fun _ _ impossible => nomatch impossible
    live := Profile.Live.singleton_iff.mpr ⟨anchorAdmitted, trivial⟩ }
  obtain ⟨argumentPadReady⟩ := argumentReady.raise (Nat.le_max_left argumentQuery.rank (n+1))
  obtain ⟨query, queryReady, worlds, footprintEq, _depth⟩ := RichGradedResult.appControlled
    henv hscoped formed closed sourceDomain sourceBody result hu hv functionQuery
    (argumentQuery.pad henv hscoped formed) (.refl _) padded controls functionReady argumentPadReady
  have sorted : (Profile.singleton (n := n+1)
      (.family ⟨name, seedLevels, familyRelevant, [request]⟩)).HasType (.sort familyRelevant) := by
    refine ⟨?_, Profile.WF.sort (n := n+1) familyRelevant, ?_⟩
    · intro atom member
      cases List.mem_singleton.mp member
      change ∀ item ∈ [request], item.input.WF ∧ item.support.WF
      intro item member
      cases List.mem_singleton.mp member
      exact ⟨admission.2.2.1.wf_value, admission.2.2.2.1.wf_value⟩
    · intro atom member
      cases List.mem_singleton.mp member
      exact ⟨_, List.mem_singleton_self _, rfl⟩
  obtain ⟨footprint, certificate, certificateReady, resources, included⟩ :=
    query.code_controlled henv controls queryReady sorted
  refine ⟨query, queryReady, ?_, footprint, certificate, resources, certificateReady, included⟩
  simpa only [functionQuery, List.nil_append, RichGradedResult.pad, RichGradedResult.raiseTo] using footprintEq

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
