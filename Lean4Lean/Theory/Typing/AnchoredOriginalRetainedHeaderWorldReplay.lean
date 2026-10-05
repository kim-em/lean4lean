import Lean4Lean.Theory.Typing.AnchoredOriginalRetainedHeaderWorldCalls
import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalLowerCallBank

/-! Productive retained-header universe transfer using the actual caller's
world guards. These are three fixed lower original clauses, not a supplied
header comparison or an unrestricted code-reindexing oracle. The full bank
must additionally preserve the query-owned sponsors on these same outputs. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace RetainedHeaderUniverse

theorem replayWorld
    {U : Nat} {leftLevels rightLevels : List VLevel} {profile : Profile n}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
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
    (firstR :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader leftOrigin) .expressionReindex
          (.ref (leftOrigin.familyHeader leftWF).reference) .nil,
         originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (.left (original rightOrigin leftWF rightWF equivalent))) .nil]
        [originalCallWorld controls phase caller captured] →
      ∀ {footprint}, RichObs leftOrigin.source env U registry target
        (.ref (leftOrigin.familyHeader leftWF).reference) [] σ profile footprint →
      footprint.Available (fun _ => []) →
      Nonempty (RichGradedResult rightOrigin.source env U registry target
        (.ref (.left (original rightOrigin leftWF rightWF equivalent))) [] σ (fun _ => []) profile))
    (equalityF :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader rightOrigin) .fundamental
          (.ref (.left (original rightOrigin leftWF rightWF equivalent))) .nil]
        [originalCallWorld controls phase caller captured] →
      ∀ {footprint}, RichObs rightOrigin.source env U registry target
        (.ref (.left (original rightOrigin leftWF rightWF equivalent))) [] σ profile footprint →
      footprint.Available (fun _ => []) →
      Nonempty (OriginalDirectionalEqualityResult (original rightOrigin leftWF rightWF equivalent)
        true env registry target [] σ σ (fun _ => []) profile))
    (lastR :
      CallBelow strata.rules.length
        [originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (.right (original rightOrigin leftWF rightWF equivalent))) .nil,
         originalCallWorld (controls.atHeader rightOrigin) .expressionReindex
          (.ref (rightOrigin.familyHeader rightWF).reference) .nil]
        [originalCallWorld controls phase caller captured] →
      ∀ {footprint}, RichObs rightOrigin.source env U registry target
        (.ref (.right (original rightOrigin leftWF rightWF equivalent))) [] σ profile footprint →
      footprint.Available (fun _ => []) →
      Nonempty (RichGradedResult rightOrigin.source env U registry target
        (.ref (rightOrigin.familyHeader rightWF).reference) [] σ (fun _ => []) profile)) :
    ∃ answer : TemplateCodeResult env U registry target
      (.ref (leftOrigin.familyHeader leftWF).reference)
      (.ref (rightOrigin.familyHeader rightWF).reference) [] σ σ (fun _ => []) relevant profile,
      answer.footprint = [] := by
  have funding := worldFunding controls leftOrigin rightOrigin leftWF rightWF equivalent caller captured phase
  obtain ⟨first⟩ := firstR funding.1 (.code certificate) (by intro _ _ member; cases member)
  obtain ⟨firstFootprint, ⟨firstCertificate⟩, firstResources⟩ := first.code henv certificate.formed
  obtain ⟨changed⟩ := equalityF funding.2.1 (.code firstCertificate) firstResources
  obtain ⟨changedFootprint, ⟨changedCertificate⟩, changedResources⟩ :=
    changed.rightQuery.code henv certificate.formed
  obtain ⟨last⟩ := lastR funding.2.2 (.code changedCertificate) changedResources
  obtain ⟨footprint, ⟨output⟩, resources⟩ := last.code henv certificate.formed
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
    path := .single (by simpa only [subst_sort] using raw) }, empty⟩

end RetainedHeaderUniverse
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
