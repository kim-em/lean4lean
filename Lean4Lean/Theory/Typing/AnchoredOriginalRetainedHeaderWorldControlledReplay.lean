import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldHistoryReserveCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalLowerCallBank

/-! The retained-header R/F/R bridge preserves control evidence on every
actual selected query and final certificate. Code extraction copies or
selects existing sites, so it cannot refresh the sponsor frontier. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace RetainedHeaderUniverse

/-- The three exact primitive frontiers in this retained universe route. -/
abbrev ReplayFunding
    {U : Nat} {leftLevels rightLevels : List VLevel}
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (parent : List (World strata.rules.length)) : Prop :=
    let equality := original rightOrigin leftWF rightWF equivalent
    CallBelow strata.rules.length
      [originalCallWorld (controls.atHeader leftOrigin) .expressionReindex
        (.ref (leftOrigin.familyHeader leftWF).reference) .nil,
       originalCallWorld (controls.atHeader rightOrigin) .expressionReindex (.ref (.left equality)) .nil] parent ∧
    CallBelow strata.rules.length
      [originalCallWorld (controls.atHeader rightOrigin) .fundamental (.ref (.left equality)) .nil] parent ∧
    CallBelow strata.rules.length
      [originalCallWorld (controls.atHeader rightOrigin) .expressionReindex (.ref (.right equality)) .nil,
       originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
        (.ref (rightOrigin.familyHeader rightWF).reference) .nil] parent

theorem replayWorldControlledCore
    {U : Nat} {leftLevels rightLevels : List VLevel} {profile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (below : sourceEnv ≤ env)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (parent : List (World strata.rules.length))
    (funding : ReplayFunding controls leftOrigin rightOrigin leftWF rightWF equivalent parent)
    (certificate : RichCert leftOrigin.source env U registry target
      (.ref (leftOrigin.familyHeader leftWF).reference) [] σ relevant profile [])
    {frontier : List (World strata.rules.length)}
    (incomingReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (firstR :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader leftOrigin) .expressionReindex
          (.ref (leftOrigin.familyHeader leftWF).reference) .nil,
         originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (.left (original rightOrigin leftWF rightWF equivalent))) .nil]
        parent →
      ∀ {footprint} (incoming : RichObs leftOrigin.source env U registry target
        (.ref (leftOrigin.familyHeader leftWF).reference) [] σ profile footprint),
      footprint.Available (fun _ => []) →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ answer : RichGradedResult rightOrigin.source env U registry target
        (.ref (.left (original rightOrigin leftWF rightWF equivalent))) [] σ (fun _ => []) profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation answer.observation)))
    (equalityF :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader rightOrigin) .fundamental
          (.ref (.left (original rightOrigin leftWF rightWF equivalent))) .nil]
        parent →
      ∀ {footprint} (incoming : RichObs rightOrigin.source env U registry target
        (.ref (.left (original rightOrigin leftWF rightWF equivalent))) [] σ profile footprint),
      footprint.Available (fun _ => []) →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ answer : OriginalDirectionalEqualityResult (original rightOrigin leftWF rightWF equivalent)
        true env registry target [] σ σ (fun _ => []) profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation)))
    (lastR :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (.right (original rightOrigin leftWF rightWF equivalent))) .nil,
         originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (rightOrigin.familyHeader rightWF).reference) .nil]
        parent →
      ∀ {footprint} (incoming : RichObs rightOrigin.source env U registry target
        (.ref (.right (original rightOrigin leftWF rightWF equivalent))) [] σ profile footprint),
      footprint.Available (fun _ => []) →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ answer : RichGradedResult rightOrigin.source env U registry target
        (.ref (rightOrigin.familyHeader rightWF).reference) [] σ (fun _ => []) profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation answer.observation))) :
    ∃ answer : TemplateCodeResult env U registry target
      (.ref (leftOrigin.familyHeader leftWF).reference)
      (.ref (rightOrigin.familyHeader rightWF).reference) [] σ σ (fun _ => []) relevant profile,
      answer.footprint = [] ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  obtain ⟨first, ⟨firstReady⟩⟩ := firstR funding.1 (.code certificate)
    (by intro _ _ member; cases member) incomingReady.code
  obtain ⟨firstFootprint, firstCertificate, firstCodeReady, firstResources, _⟩ :=
    first.code_controlled henv controls firstReady certificate.formed
  obtain ⟨changed, ⟨changedReady⟩⟩ := equalityF funding.2.1 (.code firstCertificate)
    firstResources firstCodeReady.code
  obtain ⟨changedFootprint, changedCertificate, changedCodeReady, changedResources, _⟩ :=
    changed.rightQuery.code_controlled henv controls changedReady certificate.formed
  obtain ⟨last, ⟨lastReady⟩⟩ := lastR funding.2.2 (.code changedCertificate)
    changedResources changedCodeReady.code
  obtain ⟨footprint, output, outputReady, resources, _⟩ :=
    last.code_controlled henv controls lastReady certificate.formed
  have empty : footprint = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry member
    exact List.not_mem_nil (resources entry.1 entry.2 member)
  let equality := original rightOrigin leftWF rightWF equivalent
  have raw := (equality.forget.defeq.mono (rightOrigin.sourceBelow.trans below)).substDF
    henv (by trivial) formed (show Ctx.SubstEq env U target σ σ [] from .nil)
  exact ⟨{
    footprint := footprint, certificate := output, resources := resources
    related := changed.related.code_of_sortable henv hscoped formed certificate.formed
    path := .single (by simpa only [subst_sort] using raw) }, empty, ⟨outputReady⟩⟩

theorem replayWorldControlled
    {U : Nat} {leftLevels rightLevels : List VLevel} {profile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (below : sourceEnv ≤ env)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (caller : EndpointState sourceEnv U source expression assigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (certificate : RichCert leftOrigin.source env U registry target
      (.ref (leftOrigin.familyHeader leftWF).reference) [] σ relevant profile [])
    {frontier : List (World strata.rules.length)}
    (incomingReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (firstR :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader leftOrigin) .expressionReindex
          (.ref (leftOrigin.familyHeader leftWF).reference) .nil,
         originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (.left (original rightOrigin leftWF rightWF equivalent))) .nil]
        [originalCallWorld controls phase caller captured] →
      ∀ {footprint} (incoming : RichObs leftOrigin.source env U registry target
        (.ref (leftOrigin.familyHeader leftWF).reference) [] σ profile footprint),
      footprint.Available (fun _ => []) →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ answer : RichGradedResult rightOrigin.source env U registry target
        (.ref (.left (original rightOrigin leftWF rightWF equivalent))) [] σ (fun _ => []) profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation answer.observation)))
    (equalityF :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader rightOrigin) .fundamental
          (.ref (.left (original rightOrigin leftWF rightWF equivalent))) .nil]
        [originalCallWorld controls phase caller captured] →
      ∀ {footprint} (incoming : RichObs rightOrigin.source env U registry target
        (.ref (.left (original rightOrigin leftWF rightWF equivalent))) [] σ profile footprint),
      footprint.Available (fun _ => []) →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ answer : OriginalDirectionalEqualityResult (original rightOrigin leftWF rightWF equivalent)
        true env registry target [] σ σ (fun _ => []) profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation)))
    (lastR :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (.right (original rightOrigin leftWF rightWF equivalent))) .nil,
         originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (rightOrigin.familyHeader rightWF).reference) .nil]
        [originalCallWorld controls phase caller captured] →
      ∀ {footprint} (incoming : RichObs rightOrigin.source env U registry target
        (.ref (.right (original rightOrigin leftWF rightWF equivalent))) [] σ profile footprint),
      footprint.Available (fun _ => []) →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ answer : RichGradedResult rightOrigin.source env U registry target
        (.ref (rightOrigin.familyHeader rightWF).reference) [] σ (fun _ => []) profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation answer.observation))) :
    ∃ answer : TemplateCodeResult env U registry target
      (.ref (leftOrigin.familyHeader leftWF).reference)
      (.ref (rightOrigin.familyHeader rightWF).reference) [] σ σ (fun _ => []) relevant profile,
      answer.footprint = [] ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  exact replayWorldControlledCore henv hscoped formed controls leftOrigin rightOrigin below
    leftWF rightWF equivalent [originalCallWorld controls phase caller captured]
    (worldFunding controls leftOrigin rightOrigin leftWF rightWF equivalent caller captured phase)
    certificate incomingReady firstR equalityF lastR

theorem replayCapturedWorldControlled
    {U : Nat} {leftLevels rightLevels : List VLevel} {profile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (leftOrigin rightOrigin : ConstantHeaderOrigin sourceEnv name info)
    (below : sourceEnv ≤ env)
    (leftWF : ∀ level ∈ leftLevels, level.WF U)
    (rightWF : ∀ level ∈ rightLevels, level.WF U)
    (equivalent : List.Forall₂ (· ≈ ·) leftLevels rightLevels)
    (common : List VExpr) (commonLeft commonRight : Subst)
    (parentControls : OriginalWorldControls strata parentEnv)
    (caller : EndpointState parentEnv U parentSource expression assigned)
    (captured : WorldEnvironmentProvenance strata U environment) (phase : RichPhase)
    (reserved : ((route leftOrigin rightOrigin leftWF rightWF equivalent below common registry target commonLeft commonRight).worldReserve
      (worldInputs controls leftOrigin rightOrigin leftWF rightWF equivalent below common registry target commonLeft commonRight)).worlds
        ⊆ captured.worlds)
    (certificate : RichCert leftOrigin.source env U registry target
      (.ref (leftOrigin.familyHeader leftWF).reference) [] σ relevant profile [])
    {frontier : List (World strata.rules.length)}
    (incomingReady : ControlledStoredQuery controls frontier (.certificate certificate))
    (firstR :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader leftOrigin) .expressionReindex
          (.ref (leftOrigin.familyHeader leftWF).reference) .nil,
         originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (.left (original rightOrigin leftWF rightWF equivalent))) .nil]
        [originalCallWorld parentControls phase caller captured] →
      ∀ {footprint} (incoming : RichObs leftOrigin.source env U registry target
        (.ref (leftOrigin.familyHeader leftWF).reference) [] σ profile footprint),
      footprint.Available (fun _ => []) →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ answer : RichGradedResult rightOrigin.source env U registry target
        (.ref (.left (original rightOrigin leftWF rightWF equivalent))) [] σ (fun _ => []) profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation answer.observation)))
    (equalityF :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader rightOrigin) .fundamental
          (.ref (.left (original rightOrigin leftWF rightWF equivalent))) .nil]
        [originalCallWorld parentControls phase caller captured] →
      ∀ {footprint} (incoming : RichObs rightOrigin.source env U registry target
        (.ref (.left (original rightOrigin leftWF rightWF equivalent))) [] σ profile footprint),
      footprint.Available (fun _ => []) →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ answer : OriginalDirectionalEqualityResult (original rightOrigin leftWF rightWF equivalent)
        true env registry target [] σ σ (fun _ => []) profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation answer.rightQuery.observation)))
    (lastR :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (.right (original rightOrigin leftWF rightWF equivalent))) .nil,
         originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (rightOrigin.familyHeader rightWF).reference) .nil]
        [originalCallWorld parentControls phase caller captured] →
      ∀ {footprint} (incoming : RichObs rightOrigin.source env U registry target
        (.ref (.right (original rightOrigin leftWF rightWF equivalent))) [] σ profile footprint),
      footprint.Available (fun _ => []) →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ answer : RichGradedResult rightOrigin.source env U registry target
        (.ref (rightOrigin.familyHeader rightWF).reference) [] σ (fun _ => []) profile,
        Nonempty (ControlledStoredQuery controls frontier (.observation answer.observation))) :
    ∃ answer : TemplateCodeResult env U registry target
      (.ref (leftOrigin.familyHeader leftWF).reference)
      (.ref (rightOrigin.familyHeader rightWF).reference) [] σ σ (fun _ => []) relevant profile,
      answer.footprint = [] ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  exact replayWorldControlledCore henv hscoped formed controls leftOrigin rightOrigin below
    leftWF rightWF equivalent [originalCallWorld parentControls phase caller captured]
    (replayFundingOfCaptured controls leftOrigin rightOrigin leftWF rightWF equivalent below
      common registry target commonLeft commonRight parentControls caller captured phase reserved)
    certificate incomingReady firstR equalityF lastR

end RetainedHeaderUniverse
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
