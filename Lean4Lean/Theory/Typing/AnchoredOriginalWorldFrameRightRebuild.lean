import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBaseHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalRightFrameTranscript
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedUnaryCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation

/-! One productive clause of coherent right-frame reconstruction. The right
 tail is a single already selected recursive result. Domain interpretation is
 performed on the original paired tail, and the very same returned certificate
 is installed in the right binder. No right-certificate supplier is assumed.
 This does not yet transform dormant histories or synchronize alternate proofs
 of generation over a shared base. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

private theorem singletonSponsoredBelow
    {strata : EquationStratification env}
    {frontier : List (World strata.rules.length)}
    {child parent : World strata.rules.length}
    (sponsored : Sponsored frontier [parent])
    (lower : WorldBelow strata.rules.length child parent) :
    Sponsored frontier [child] := by
  intro value member
  cases List.mem_singleton.mp member
  obtain ⟨sponsor, member, bound⟩ := sponsored parent (List.mem_singleton_self _)
  exact ⟨sponsor, member, EquationWorldClosureOrder.trans
    (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans lower bound⟩

private theorem worldCode
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier parent : List (World strata.rules.length))
    (bank : WorldBoundedUnaryCallBank env U registry strata P parent)
    (funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental node captured]) parent)
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental node captured])
    (provenance : EndpointProvenance context node)
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant profile footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ answer : RichCodeTransferResult env U registry target node node locals σ τ available relevant profile,
      Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)) := by
  obtain ⟨answer, _, ⟨answerReady⟩⟩ := (bank _ funded).computational node provenance controls frame captured captured
    frontier (Nat.le_refl _) (Covered.refl _) rfl sponsored data closed formed substitutions
    (.code certificate) resources {
      annotation := .code ready.annotation
      within := by
        intro control active
        simpa only [StoredOriginalQuery.headDepth, RichObs.headDepth] using ready.within control active
      sponsored := ready.sponsored }
  obtain ⟨outputFootprint, output, outputReady, outputResources, _⟩ :=
    answer.rightQuery.code_controlled henv controls answerReady certificate.formed
  exact ⟨⟨outputFootprint, output, outputResources,
    answer.related.code_of_sortable henv hscoped formed certificate.formed⟩, ⟨outputReady⟩⟩

private theorem prefixRightRebuildCall {count : Nat} {xs ys : List (World count)}
    (step : CallBelow count xs ys) (front : List (World count)) :
    CallBelow count (front ++ xs) (front ++ ys) := by
  induction front with
  | nil => exact step
  | cons head tail ih => exact ih.cons head

/-- The domain opening is paid by its actual retained binder closure, even if
its own source control is larger than the current caller's control. -/
theorem rightBinderDomainBelow
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (captured : WorldEnvironmentProvenance strata U environment)
    (caller : EndpointState sourceEnv U (A :: source) expression assigned) :
    WorldBelow strata.rules.length (originalCallWorld controls .fundamental (.ref domain) captured)
      (originalCallWorld controls .fundamental caller
        (.cons (.original (.ref domain) controls captured) captured)) := by
  apply Below.child
  exact List.mem_append_left _ (List.mem_singleton_self _)

/-- Rebuild one actual binder, preserving its resources and exact closure
ledger. The actual domain F call is strictly below the caller by capture
membership; its right query is converted to code and used without reselection. -/
theorem rebuildWorldRightBinder
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    (controls : OriginalWorldControls strata sourceEnv)
    (tail : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (rightTail : OriginalRichFrame sourceEnv env U registry target context locals τ τ available)
    (tailTranscript : RawFrameRightRebuilt env U registry target tail.raw rightTail.raw)
    (captured : WorldEnvironmentProvenance strata U (tail.dependencyEnvironment controls.ordered))
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (provenance : EndpointProvenance context (.ref domain))
    (caller : EndpointState sourceEnv U (A :: source) expression assigned)
    (frontier : List (World strata.rules.length))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller
        (.cons (.original (.ref domain) controls captured) captured)]))
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental caller
      (.cons (.original (.ref domain) controls captured) captured)])
    (data : WorldUnaryFrameData P controls frontier tail captured)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    ∃ nextFootprint,
      ∃ next : RichCert sourceEnv env U registry target (.ref domain) locals τ true support nextFootprint,
      ∃ nextResources : nextFootprint.Available available,
      Nonempty (ControlledStoredQuery controls frontier (.certificate next)) ∧
      ∃ nextArguments : Related env U registry target y y (A.subst τ) input support,
      Nonempty (RawFrameRightRebuilt env U registry target
        (OriginalRichFrame.bind tail domain certificate resources typed arguments needs bounded covered).raw
        (OriginalRichFrame.bind rightTail domain next nextResources typed nextArguments needs bounded covered).raw) ∧
      ∀ ordered,
        (OriginalRichFrame.bind rightTail domain next nextResources typed nextArguments needs bounded covered).dependencyEnvironment ordered =
        (OriginalRichFrame.bind tail domain certificate resources typed arguments needs bounded covered).dependencyEnvironment ordered := by
  have lower := rightBinderDomainBelow controls domain captured caller
  have funded := prefixRightRebuildCall
    (EquationWorldPolynomial.lower_mass (mass := [originalCallWorld controls .fundamental (.ref domain) captured])
      (by intro value member; cases List.mem_singleton.mp member; exact lower)) frontier
  obtain ⟨answer, ⟨answerReady⟩⟩ := worldCode controls tail captured frontier _ bank funded
    (singletonSponsoredBelow sponsored lower) provenance data henv hscoped closed formed substitutions
    certificate resources ready
  have rightArguments : Related env U registry target y y (A.subst τ) input support :=
    (arguments.symm henv).left_diagonal.convert henv typed answer.related
  refine ⟨answer.footprint, answer.certificate, answer.resources, ⟨answerReady⟩, rightArguments, ?_, ?_⟩
  · exact ⟨.bind tailTranscript domain certificate resources answer.certificate answer.resources
      typed arguments rightArguments needs bounded covered⟩
  intro ordered
  change Closure.close (domain.dependencyOrigin ordered) (rightTail.dependencyEnvironment ordered) ::
      rightTail.dependencyEnvironment ordered = _
  rw [show rightTail.dependencyEnvironment ordered = tail.dependencyEnvironment ordered from
    tailTranscript.environment ordered]
  rfl


/-- Rebuild the captured argument and declared-domain observations under the
same original paired tail. The owner call spends the stored R-phase reserve;
it is not an unfunded F call at an arbitrary captured source. -/
theorem rebuildWorldRightCapture
    {strata : EquationStratification env} {P : VEnv → Prop}
    {context : ContextDerivation sourceEnv U source}
    (controls : OriginalWorldControls strata sourceEnv)
    (tail : OriginalRichFrame sourceEnv env U registry target context locals σ τ available)
    (rightTail : OriginalRichFrame sourceEnv env U registry target context locals τ τ available)
    (tailTranscript : RawFrameRightRebuilt env U registry target tail.raw rightTail.raw)
    (captured : WorldEnvironmentProvenance strata U (tail.dependencyEnvironment controls.ordered))
    (domain : EndpointRef sourceEnv U source A (.sort level))
    (domainProvenance : EndpointProvenance context (.ref domain))
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (lineage : location.contextDerivation initial = context)
    (caller : EndpointState sourceEnv U (A :: source) expression assigned)
    (frontier : List (World strata.rules.length))
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental caller
        (.cons (.bundle (.scheduled .expressionReindex argument controls captured)
          (.original (.ref domain) controls captured)) captured)]))
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental caller
      (.cons (.bundle (.scheduled .expressionReindex argument controls captured)
        (.original (.ref domain) controls captured)) captured)])
    (data : WorldUnaryFrameData P controls frontier tail captured)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ source)
    (query : RichObs sourceEnv env U registry target argument locals σ (rawInput : Profile k) argumentFootprint)
    (queryResources : argumentFootprint.Available available)
    (queryReady : ControlledStoredQuery controls frontier (.observation query))
    (certificate : RichCert sourceEnv env U registry target (.ref domain) locals σ true
      (support : Profile n) footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (typed : input.HasType support)
    (arguments : Related env U registry target x y (A.subst σ) input support)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    ∃ nextQuery : RichGradedResult sourceEnv env U registry target argument locals τ available rawInput,
      Nonempty (ControlledStoredQuery controls frontier (.observation nextQuery.observation)) ∧
      ∃ nextFootprint,
      ∃ next : RichCert sourceEnv env U registry target (.ref domain) locals τ true support nextFootprint,
      ∃ nextResources : nextFootprint.Available available,
      Nonempty (ControlledStoredQuery controls frontier (.certificate next)) ∧
      ∃ nextArguments : Related env U registry target y y (A.subst τ) input support,
      Nonempty (RawFrameRightRebuilt env U registry target
        (OriginalRichFrame.capture tail domain initial argument location lineage
          query queryResources certificate resources typed arguments needs bounded covered).raw
        (OriginalRichFrame.capture rightTail domain initial argument location lineage
          nextQuery.observation nextQuery.resources next nextResources typed nextArguments needs bounded covered).raw) ∧
      ∀ ordered,
        (OriginalRichFrame.capture rightTail domain initial argument location lineage
          nextQuery.observation nextQuery.resources next nextResources typed nextArguments
          needs bounded covered).dependencyEnvironment ordered =
        (OriginalRichFrame.capture tail domain initial argument location lineage
          query queryResources certificate resources typed arguments needs bounded covered).dependencyEnvironment ordered := by
  have domainLower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental (.ref domain) captured)
      (originalCallWorld controls .fundamental caller
        (.cons (.bundle (.scheduled .expressionReindex argument controls captured)
          (.original (.ref domain) controls captured)) captured)) := by
    apply Below.child
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  have ownerLower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental argument captured)
      (originalCallWorld controls .fundamental caller
        (.cons (.bundle (.scheduled .expressionReindex argument controls captured)
          (.original (.ref domain) controls captured)) captured)) := by
    apply Below.under (child := originalCallWorld controls .expressionReindex argument captured)
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _))
    · apply original_child
      simp only [richSchedule, RichPhase.code]
      omega
  have domainFunded := prefixRightRebuildCall
    (EquationWorldPolynomial.lower_mass (mass := [originalCallWorld controls .fundamental (.ref domain) captured])
      (by intro value member; cases List.mem_singleton.mp member; exact domainLower)) frontier
  have ownerFunded := prefixRightRebuildCall
    (EquationWorldPolynomial.lower_mass (mass := [originalCallWorld controls .fundamental argument captured])
      (by intro value member; cases List.mem_singleton.mp member; exact ownerLower)) frontier
  obtain ⟨ownerAnswer, _, ⟨ownerReady⟩⟩ := (bank _ ownerFunded).computational argument
    (lineage ▸ EndpointProvenance.ofLocation location initial) controls tail captured captured frontier
    (Nat.le_refl _) (Covered.refl _) rfl (singletonSponsoredBelow sponsored ownerLower)
    data closed formed substitutions query queryResources queryReady
  obtain ⟨answer, ⟨answerReady⟩⟩ := worldCode controls tail captured frontier _ bank domainFunded
    (singletonSponsoredBelow sponsored domainLower) domainProvenance data henv hscoped closed formed substitutions
    certificate resources ready
  have rightArguments : Related env U registry target y y (A.subst τ) input support :=
    (arguments.symm henv).left_diagonal.convert henv typed answer.related
  refine ⟨ownerAnswer.rightQuery, ⟨ownerReady⟩, answer.footprint, answer.certificate,
    answer.resources, ⟨answerReady⟩, rightArguments, ?_, ?_⟩
  · exact ⟨.capture tailTranscript domain initial argument location lineage query queryResources
      ownerAnswer.rightQuery.observation ownerAnswer.rightQuery.resources certificate resources
      answer.certificate answer.resources typed arguments rightArguments needs bounded covered⟩
  intro ordered
  change Closure.bundle
      (Closure.close (argument.dependencyOrigin ordered) (rightTail.dependencyEnvironment ordered))
      (Closure.close (domain.dependencyOrigin ordered) (rightTail.dependencyEnvironment ordered)) ::
      rightTail.dependencyEnvironment ordered = _
  rw [show rightTail.dependencyEnvironment ordered = tail.dependencyEnvironment ordered from
    tailTranscript.environment ordered]
  rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
