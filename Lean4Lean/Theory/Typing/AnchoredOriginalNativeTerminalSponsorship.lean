import Lean4Lean.Theory.Typing.AnchoredOriginalNativeTerminalOccurrence
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldLocatedCoverage

/-! The actual open native body call and its computed domain captures consume
the retained closed equation sponsor. No new frontier or sponsor is selected;
zero-binder equality is handled by coverage before applying that sponsorship. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

private theorem transported_worlds (equal : first = second)
    (environment : WorldEnvironmentProvenance strata U first) :
    (equal ▸ environment : WorldEnvironmentProvenance strata U second).worlds = environment.worlds := by
  cases equal
  rfl

theorem NativeSupportedReplay.locatedSite_worlds
    {strata : EquationStratification env}
    {root : EndpointRef frameEnv U [] rootExpression rootType}
    {node : EndpointState frameEnv U declared expression assigned}
    (location : Located root node) (controls : OriginalWorldControls strata frameEnv)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (argumentsRaw : Ctx.SubstEq env U target arguments arguments argumentSource)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available) :
    (NativeSupportedReplay.locatedSite location controls henv formed below argumentContext
      argumentsSpine argumentsRaw replay).worlds =
      [originalCallWorld controls .fundamental node (WorldEnvironmentProvenance.located controls location .nil)] := by
  simp only [NativeSupportedReplay.locatedSite, OriginalRichOccurrenceFrame.worldSite,
    WorldQuerySite.worlds, WorldClosureProvenance.worlds, transported_worlds,
    NativeSupportedReplay.locatedOccurrence, NativeSupportedReplay.originalFrame_environment,
    location.contextDerivation_dependencyClosures, ContextDerivation.dependencyClosures,
    originalCallWorld]

theorem NativeSupportedReplay.locatedSite_sponsored
    {strata : EquationStratification env}
    {root : EndpointRef frameEnv U [] rootExpression rootType}
    {node : EndpointState frameEnv U declared expression assigned}
    (location : Located root node) (controls : OriginalWorldControls strata frameEnv)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (argumentsRaw : Ctx.SubstEq env U target arguments arguments argumentSource)
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable declared plan captures locals available)
    {frontier : List (World strata.rules.length)}
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental (.ref root) .nil]) :
    let site := NativeSupportedReplay.locatedSite location controls henv formed below argumentContext
      argumentsSpine argumentsRaw replay
    Sponsored frontier (site.worlds ++ site.annotation.environment.worlds) := by
  dsimp only
  obtain ⟨sponsor, member, smaller⟩ := sponsored _ (List.mem_singleton_self _)
  apply Sponsored.merge
  · rw [NativeSupportedReplay.locatedSite_worlds]
    intro world belongs
    obtain ⟨old, oldMember, same | next⟩ :=
      WorldEnvironmentProvenance.located_call_covered controls location .nil world belongs
    · have oldEq := List.mem_singleton.mp oldMember
      subst old
      subst world
      exact ⟨sponsor, member, smaller⟩
    · have oldEq := List.mem_singleton.mp oldMember
      subst old
      exact ⟨sponsor, member, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans next smaller⟩
  · change Sponsored frontier (_ : WorldEnvironmentProvenance strata U _).worlds
    simp only [NativeSupportedReplay.locatedSite, OriginalRichOccurrenceFrame.worldSite,
      transported_worlds]
    intro world belongs
    exact ⟨sponsor, member, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (WorldEnvironmentProvenance.located_captures_below controls location .nil world belongs) smaller⟩

theorem nativeTerminalSite_sponsored
    {strata : EquationStratification env}
    {rule : VDefEq} {levels : List VLevel} {U : Nat}
    (origin : EquationHeaderOrigin env rule)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    {body : InductiveSignature.CaseSchema.EquationBody}
    (extracted : InductiveSignature.CaseSchema.EquationBody.extract
      rule.lhs rule.rhs rule.type = some body)
    (controls : OriginalWorldControls strata origin.source)
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U)) (below : sourceEnv ≤ env)
    (argumentContext : ContextDerivation argumentEnv U argumentSource)
    (argumentsSpine : NativeCertificateSpine env U registry target
      argumentSource arguments rightArguments argumentAvailable)
    (argumentsRaw : Ctx.SubstEq env U target arguments arguments argumentSource)
    {plan : CapturePlan (body.domains.map (·.instL levels)).reverse}
    (replay : NativeSupportedReplay sourceEnv env U registry target argumentSource
      (List.range argumentSource.length) arguments argumentAvailable
      (body.domains.map (·.instL levels)).reverse plan captures locals available)
    {frontier : List (World strata.rules.length)}
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.ref (.left (EquationHeaderOrigin.instantiatedRhs origin levelsWF))) .nil]) :
    let site := nativeTerminalSite origin levelsWF extracted controls henv formed below argumentContext
      argumentsSpine argumentsRaw replay
    Sponsored frontier (site.worlds ++ site.annotation.environment.worlds) :=
  NativeSupportedReplay.locatedSite_sponsored
    (nativeRhsOccurrence origin levelsWF extracted).2.2 controls henv formed below
    argumentContext argumentsSpine argumentsRaw replay sponsored

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
