import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureCalls

/-! Own-capture preservation constructs provenance, fuel bounds, and sponsorship
on the SAME returned frame and observer. The F/R clauses remain explicitly
qualified recursive calls; this is one producer of the global invariant,
not a proof of the entire lower-call bank. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The controls bound the actual query, and sponsorship concerns the
opening worlds computed from that query's actual positive annotation. -/
structure ControlledStoredQuery
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata controlSource)
    (frontier : List (EquationWorldClosureOrder.World strata.rules.length))
    (query : StoredOriginalQuery env U registry target) where
  annotation : query.Provenance strata
  within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
    (fun control => query.headDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
  sponsored : EquationWorldClosureOrder.Sponsored frontier annotation.worlds

/-- Captured frames retain all their actual queries and dormant histories.
This does not replace their separately computed original closure ledger. -/
structure WorldGenerated.Controlled
    {base : OriginalCaptureBase env U registry target}
    (generated : WorldGenerated strata P base caps left right graph frame controls)
    (frontier : List (EquationWorldClosureOrder.World strata.rules.length)) where
  annotation : generated.QueryProvenance
  within : EquationStratifiedFuel.WithinAbove controls.cutoff controls.fuel
    (fun control => generated.retainedDepth (stratifiedHeadPolicy (strata.headOrdinal registry) control))
  sponsored : EquationWorldClosureOrder.Sponsored frontier annotation.worlds

theorem RetainedQueryProvenance.sponsored_subset
    (annotations : RetainedQueryProvenance strata queries)
    (bounded : EquationWorldClosureOrder.Sponsored frontier annotations.worlds)
    (included : selected ⊆ queries) :
    ∃ selectedAnnotations : RetainedQueryProvenance strata selected,
      EquationWorldClosureOrder.Sponsored frontier selectedAnnotations.worlds := by
  induction selected with
  | nil => exact ⟨.nil, by intro _ member; cases member⟩
  | cons query rest ih =>
    obtain ⟨annotation, sponsored⟩ := annotations.sponsored_member bounded
      (included (List.mem_cons_self ..))
    obtain ⟨tail, tailSponsored⟩ := ih (fun _ member => included (List.mem_cons_of_mem _ member))
    exact ⟨.cons annotation tail, sponsored.merge tailSponsored⟩

theorem StoredOriginalQuery.maximumDepth_mono
    (policy : Name → Nat → Nat)
    {selected queries : List (StoredOriginalQuery env U registry target)}
    (included : selected ⊆ queries) : maximumDepth policy selected ≤ maximumDepth policy queries := by
  induction selected with
  | nil => exact Nat.zero_le _
  | cons query rest ih =>
    exact Nat.max_le.mpr ⟨headDepth_le_maximumDepth policy (included (List.mem_cons_self ..)),
      ih (fun _ member => included (List.mem_cons_of_mem _ member))⟩

/-- The observer and its provenance come from the same retained entry. -/
theorem WorldGenerated.Controlled.selectStored
    {base : OriginalCaptureBase env U registry target}
    {generated : WorldGenerated strata P base caps left right graph frame controls}
    (ready : generated.Controlled frontier)
    (member : query ∈ generated.retainedQueries) :
    Nonempty (ControlledStoredQuery controls frontier query) := by
  obtain ⟨annotation, sponsored⟩ := ready.annotation.sponsored_member ready.sponsored member
  exact ⟨⟨annotation, generated.retainedQuery_bound ready.within query member, sponsored⟩⟩

/-- A selected generation keeps every dormant query, not just its raw frame
queries. Numeric control compatibility is a real hypothesis here. -/
theorem WorldGenerated.Controlled.selectGeneration
    {base : OriginalCaptureBase env U registry target}
    {generated : WorldGenerated strata P base caps left right graph frame controls}
    (ready : generated.Controlled frontier)
    (child : WorldGenerated strata P base childCaps childLeft childRight childGraph childFrame childControls)
    (included : child.retainedQueries ⊆ generated.retainedQueries)
    (cutoff : childControls.cutoff = controls.cutoff)
    (fuel : childControls.fuel = controls.fuel) :
    Nonempty (child.Controlled frontier) := by
  obtain ⟨annotation, sponsored⟩ := ready.annotation.sponsored_subset ready.sponsored included
  refine ⟨⟨annotation, ?_, sponsored⟩⟩
  intro control active
  rw [cutoff] at active
  rw [fuel]
  have bound := StoredOriginalQuery.maximumDepth_mono
    (stratifiedHeadPolicy (strata.headOrdinal registry) control) included
  rw [child.retainedQueries_depth, generated.retainedQueries_depth] at bound
  exact Nat.le_trans bound (ready.within control active)

private theorem retained_worlds_cast
    {first second : List (StoredOriginalQuery env U registry target)}
    (equal : first = second) (annotation : RetainedQueryProvenance strata first) :
    (equal ▸ annotation : RetainedQueryProvenance strata second).worlds = annotation.worlds := by
  cases equal
  rfl

/-- Store the actual argument observer and exact aligned certificate returned
by the qualified children. Their provenance is composed with the existing
generation; no bound is inferred from frame capacity or an empty footprint. -/
theorem generatedOwnCaptureWorldControlled
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {strata : EquationStratification env}
    (controls : OriginalWorldControls strata sourceEnv)
    (domain : EndpointRef sourceEnv U source A (.sort u))
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (realized : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight graph realized.frame.raw controls)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons (location.contextDerivation initial) domain) variableNode)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (frontier : List (EquationWorldClosureOrder.World strata.rules.length))
    (queryReady : ControlledStoredQuery controls frontier (.observation query))
    (tailReady : WorldGenerated.Controlled generated frontier)
    (argumentF :
      EquationWorldClosureOrder.CallBelow strata.rules.length
        [originalCallWorld controls .fundamental argument generated.environment]
        [originalCallWorld controls .fundamental variableNode
          (ownCaptureWorldEnvironment controls domain argument generated.environment)] →
      ∀ incoming : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft) profile footprint,
      footprint.Available available →
      ControlledStoredQuery controls frontier (.observation incoming) →
      ∃ answer : RichComputationalValue sourceEnv env U registry target argument locals
          (raw.comp commonLeft) (raw.comp commonRight) available profile,
        Nonempty (ControlledStoredQuery controls frontier (.certificate answer.certificate)))
    (domainR :
      EquationWorldClosureOrder.CallBelow strata.rules.length
        [originalCallWorld controls .expressionReindex argument.typeFormation.node generated.environment,
         originalCallWorld controls .expressionReindex (.ref domain) generated.environment]
        [originalCallWorld controls .fundamental variableNode
          (ownCaptureWorldEnvironment controls domain argument generated.environment)] →
      ∀ {q : Profile n} {fp}
        (certificate : RichCert sourceEnv env U registry target argument.typeFormation.node locals
          (raw.comp commonLeft) true q fp),
      fp.Available available →
      ControlledStoredQuery controls frontier (.certificate certificate) →
      ∃ aligned : RichCodeTransferResult env U registry target argument.typeFormation.node (.ref domain) locals
          (raw.comp commonLeft) (raw.comp commonLeft) available true q,
        Nonempty (ControlledStoredQuery controls frontier (.certificate aligned.certificate))) :
    ∃ reply : CappedGeneratedQueryReply base commonCaps
      (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
        variableNode variableProvenance) commonLeft commonRight profile,
      ∃ generatedReply : WorldGenerated strata P base commonCaps commonLeft commonRight
        (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
          variableNode variableProvenance).graph reply.reply.realization.frame.raw controls,
      Nonempty (WorldGenerated.Controlled generatedReply frontier) ∧
      generatedReply.worlds =
        (ownCaptureWorldEnvironment controls domain argument generated.environment).worlds ∧
      Nonempty (ControlledStoredQuery controls frontier (.observation reply.reply.query.observation)) ∧
      reply.reply.query.rank = n ∧ HEq reply.reply.query.raw profile ∧
      reply.reply.query.footprint = [(0, Need.mk n profile)] := by
  obtain ⟨argumentCall, domainCall⟩ := ownCaptureWorldFunding
    controls domain argument variableNode generated.environment
  obtain ⟨answer, ⟨answerReady⟩⟩ := argumentF argumentCall query resources queryReady
  obtain ⟨aligned, ⟨alignedReady⟩⟩ := domainR domainCall
    answer.certificate answer.resources answerReady
  obtain ⟨reply, generatedReply, retained, capturedWorlds, observationAnnotation, observationWorlds, observationDepth, rankEq, rawEq, footprintEq, _⟩ :=
    generatedOwnCaptureWorldReplyAt initial henv hscoped below controls domain argument location
      realized generated generated.environment (Nat.le_refl _) variableNode variableProvenance closed formed query resources answer aligned
  let stored : RetainedQueryProvenance strata
      (.observation query :: .certificate aligned.certificate :: generated.retainedQueries) :=
    .cons queryReady.annotation (.cons alignedReady.annotation tailReady.annotation)
  let returned : RetainedQueryProvenance strata generatedReply.retainedQueries := retained.symm ▸ stored
  have worlds : returned.worlds =
      queryReady.annotation.worlds ++ alignedReady.annotation.worlds ++ tailReady.annotation.worlds := by
    simp only [returned, retained_worlds_cast]
    simp only [stored, RetainedQueryProvenance.worlds, List.append_assoc]
  refine ⟨reply, generatedReply, ⟨⟨returned, ?_, ?_⟩⟩, capturedWorlds, ⟨⟨observationAnnotation, ?_, ?_⟩⟩, rankEq, rawEq, footprintEq⟩
  · intro control active
    change generatedReply.retainedDepth
      (stratifiedHeadPolicy (strata.headOrdinal registry) control) ≤ controls.fuel control
    rw [← generatedReply.retainedQueries_depth, retained]
    simp only [StoredOriginalQuery.maximumDepth_cons, StoredOriginalQuery.headDepth,
      generated.retainedQueries_depth]
    exact Nat.max_le.mpr ⟨queryReady.within control active,
      Nat.max_le.mpr ⟨alignedReady.within control active, tailReady.within control active⟩⟩
  · rw [worlds, List.append_assoc]
    exact queryReady.sponsored.merge (alignedReady.sponsored.merge tailReady.sponsored)
  · intro control _
    change reply.reply.query.observation.headDepth _ ≤ _
    rw [observationDepth]
    exact Nat.zero_le _
  · change EquationWorldClosureOrder.Sponsored frontier observationAnnotation.worlds
    rw [observationWorlds]
    intro child member
    cases member

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
