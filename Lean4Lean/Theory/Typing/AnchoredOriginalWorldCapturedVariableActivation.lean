import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCapturePreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation

/-! A destination captured-variable pilot emits an ordinary variable query.
The original operand observer can itself be a shared recipe. Its interpretation
is performed by the genuine smaller original call, and its demand becomes an
explicit head need. No permanent raw-substitution factorization is required by
the returned observer. The exact-domain case below has a concrete original
family-formation producer; independent declared domains require history replay.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem prefixActivation {count : Nat} {xs ys : List (World count)}
    (step : CallBelow count xs ys) (frontier : List (World count)) :
    CallBelow count (frontier ++ xs) (frontier ++ ys) := by
  induction frontier with
  | nil => exact step
  | cons head tail ih => exact ih.cons head

private theorem activationSponsor {count : Nat} {child parent : World count}
    {frontier : List (World count)} (sponsored : Sponsored frontier [parent])
    (lower : WorldBelow count child parent) : Sponsored frontier [child] := by
  intro value member
  cases List.mem_singleton.mp member
  obtain ⟨sponsor, present, bound⟩ := sponsored _ (List.mem_singleton_self _)
  exact ⟨sponsor, present, EquationWorldClosureOrder.trans
    (r := @EquationControlMeasure.Less count) EquationControlMeasure.less_trans lower bound⟩

private noncomputable def castCertificateReady
    {first second : EndpointState sourceEnv U source expression (.sort level)}
    (equal : first = second)
    (certificate : RichCert sourceEnv env U registry target first locals σ relevant profile footprint)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ControlledStoredQuery controls frontier (.certificate (equal ▸ certificate)) := by
  cases equal
  exact ready

/-- Only an actual original-node equation identifies the declared certificate.
There is no supplied activated frame, computational answer or TypeRelated. -/
theorem activateWorldCapturedVariableExact
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (argument : EndpointState sourceEnv U source a A)
    (domain : EndpointRef sourceEnv U source A (.sort argument.typeFormation.level))
    (domainEq : argument.typeFormation.node = .ref domain)
    (location : Located root argument)
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph realized.frame.raw controls)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons (location.contextDerivation initial) domain) variableNode)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (frontier : List (World strata.rules.length))
    (queryReady : ControlledStoredQuery controls frontier (.observation query))
    (tailReady : generated.Controlled frontier)
    (frameReplayable : generated.Replayable)
    (frameCompatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (frameHereditary : generated.Hereditary frontier)
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental variableNode
      (ownCaptureWorldEnvironment controls domain argument generated.environment)])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental variableNode
        (ownCaptureWorldEnvironment controls domain argument generated.environment)])) :
    ∃ reply : CappedGeneratedQueryReply base commonCaps
      (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
        variableNode variableProvenance) commonLeft commonRight profile,
      ∃ nextGenerated : WorldGenerated strata P base commonCaps commonLeft commonRight
        (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
          variableNode variableProvenance).graph reply.reply.realization.frame.raw controls,
        Nonempty (nextGenerated.Controlled frontier) ∧
        nextGenerated.worlds = (ownCaptureWorldEnvironment controls domain argument generated.environment).worlds ∧
        Nonempty (ControlledStoredQuery controls frontier (.observation reply.reply.query.observation)) ∧
        reply.reply.query.rank = n ∧ HEq reply.reply.query.raw profile ∧
        reply.reply.query.footprint = [(0, Need.mk n profile)] := by
  obtain ⟨data⟩ := WorldUnaryFrameData.ofGenerated realized.frame generated tailReady
    frameReplayable frameCompatible frameHereditary
  have argumentLower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental argument generated.environment)
      (originalCallWorld controls .fundamental variableNode
        (ownCaptureWorldEnvironment controls domain argument generated.environment)) := by
    apply Below.under (child := originalCallWorld controls .expressionReindex argument generated.environment)
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · apply original_child
      simp only [richSchedule, RichPhase.code]
      omega
  have formationLower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental argument.typeFormation.node generated.environment)
      (originalCallWorld controls .fundamental variableNode
        (ownCaptureWorldEnvironment controls domain argument generated.environment)) := by
    apply Below.under (child := originalCallWorld controls .expressionReindex argument generated.environment)
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · apply original_child
      have bound := argument.typeFormation_dependency_cost_le controls.ordered
        (realized.frame.dependencyEnvironment controls.ordered)
      simp only [OriginalRichFrame.dependencyEnvironment] at bound
      simp only [richSchedule, RichPhase.code]
      omega
  apply generatedOwnCaptureWorldControlled initial henv hscoped below controls domain argument location
    realized generated variableNode variableProvenance closed formed query resources frontier queryReady tailReady
  · intro smaller incoming incomingResources incomingReady
    obtain ⟨answer, answerReady, _⟩ := (bank _ (prefixActivation smaller frontier)).computational argument
      (.ofLocation location initial) controls realized.frame generated.environment generated.environment frontier
      (Nat.le_refl _) (Covered.refl _) rfl (activationSponsor sponsored argumentLower)
      data closed formed realized.substitutions incoming incomingResources incomingReady
    exact ⟨answer, answerReady⟩
  · intro _ q fp certificate certificateResources certificateReady
    have funded := prefixActivation
      (EquationWorldPolynomial.lower_mass (mass := [originalCallWorld controls .fundamental argument.typeFormation.node generated.environment])
        (by intro value member; cases List.mem_singleton.mp member; exact formationLower)) frontier
    obtain ⟨answer, _, _⟩ := (bank _ funded).computational argument.typeFormation.node
      (.ofLocation (.assignedFormation location) initial) controls realized.frame generated.environment
      generated.environment frontier (Nat.le_refl _) (Covered.refl _) rfl
      (activationSponsor sponsored formationLower) data closed formed realized.substitutions
      (.code certificate) certificateResources {
        annotation := .code certificateReady.annotation
        within := by
          intro control active
          simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using certificateReady.within control active
        sponsored := certificateReady.sponsored }
    let converted : RichCert sourceEnv env U registry target (.ref domain) locals
        (raw.comp commonLeft) true q fp := domainEq ▸ certificate
    have convertedReady : ControlledStoredQuery controls frontier (.certificate converted) :=
      castCertificateReady domainEq certificate certificateReady
    refine ⟨⟨fp, converted, certificateResources, ?_⟩, ⟨convertedReady⟩⟩
    exact (answer.related.code_of_sortable henv hscoped formed certificate.formed).left_diagonal

/-- Concrete production of the exact domain: the family-typed original
supplies its own computed formation reference. The public pilot has no
caller-supplied domain equality or semantic answer. -/
theorem activateWorldCapturedFamilyVariable
    {base : OriginalCaptureBase env U registry target}
    (original : Derivation sourceEnv U source a b (mkApps (.const name levels) arguments))
    (initial : ContextDerivation sourceEnv U source)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    {graph : OriginalCaptureMap (common := common) initial raw}
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph realized.frame.raw controls)
    (variableNode : EndpointState sourceEnv U ((mkApps (.const name levels) arguments) :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons initial original.familyFormationRef.reference) variableNode)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (query : RichObs sourceEnv env U registry target (.ref (.left original)) locals (raw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (frontier : List (World strata.rules.length))
    (queryReady : ControlledStoredQuery controls frontier (.observation query))
    (tailReady : generated.Controlled frontier)
    (frameReplayable : generated.Replayable)
    (frameCompatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (frameHereditary : generated.Hereditary frontier)
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental variableNode
      (ownCaptureWorldEnvironment controls original.familyFormationRef.reference (.ref (.left original)) generated.environment)])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental variableNode
        (ownCaptureWorldEnvironment controls original.familyFormationRef.reference (.ref (.left original)) generated.environment)])) :
    ∃ reply : CappedGeneratedQueryReply base commonCaps
      (applicationCaptureVariableDisplay graph original.familyFormationRef.reference (.ref (.left original)) (.ofLocation (.here : Located (.left original) (.ref (.left original))) initial)
        variableNode variableProvenance) commonLeft commonRight profile,
      ∃ nextGenerated : WorldGenerated strata P base commonCaps commonLeft commonRight
        (applicationCaptureVariableDisplay graph original.familyFormationRef.reference (.ref (.left original)) (.ofLocation (.here : Located (.left original) (.ref (.left original))) initial)
          variableNode variableProvenance).graph reply.reply.realization.frame.raw controls,
        Nonempty (nextGenerated.Controlled frontier) ∧
        nextGenerated.worlds = (ownCaptureWorldEnvironment controls original.familyFormationRef.reference (.ref (.left original)) generated.environment).worlds ∧
        Nonempty (ControlledStoredQuery controls frontier (.observation reply.reply.query.observation)) ∧
        reply.reply.query.rank = n ∧ HEq reply.reply.query.raw profile ∧
        reply.reply.query.footprint = [(0, Need.mk n profile)] := by
  exact activateWorldCapturedVariableExact initial henv hscoped below controls
    (.ref (.left original)) original.familyFormationRef.reference original.familyFormationRef.exactNode
    (.here : Located (.left original) (.ref (.left original))) realized generated variableNode variableProvenance
    closed formed query resources frontier queryReady tailReady frameReplayable frameCompatible frameHereditary sponsored bank

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
