import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationBody
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationAssignedPacking
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldScopedResourceReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyParameterReplay

/-! The actual backward application query selects its argument owners.
Every owner is replayed at the original argument and frozen to the caller's
identity sandbox. The ordinary Pi request retains those exact observers,
the selected body certificate, and all their control evidence. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private raiseCertificateControlled transportControlledCertificate from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationPack
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

private theorem applicationCallsPrefix {count : Nat} {calls parent : List (World count)}
    (smaller : CallBelow count calls parent) (frontier : List (World count)) :
    CallBelow count (frontier ++ calls) (frontier ++ parent) := by
  induction frontier with
  | nil => exact smaller
  | cons head tail ih => exact ih.cons head

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (frame : OriginalRichFrame sourceEnv env U registry target
    (location.contextDerivation initial) locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)

/-- The body packet and its exact selected generation are returned together.
Its owners can therefore be queried without selecting another existential
frame or recovering world labels from its numerical capacity. -/
structure WorldApplicationBackwardQueries
    {strata : EquationStratification env} (P : VEnv → Prop)
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length)) (relevant : Bool) (profile : Profile n)
    extends ApplicationBackwardQueries initial domain body function argument result hu hv location
      frame substitutions controls.ordered relevant profile where
  generation : WorldGenerated strata P (frame.captureBase substitutions)
    (frame.captureBase substitutions).initialCaps σ τ
    (applicationBodyDisplay initial domain body function argument result hu hv location (.identity _)).graph
    reply.answer.reply.realization.frame.raw controls
  replayable : generation.Replayable
  controlled : generation.Controlled frontier
  compatible : generation.UsesControlPrefix controls.cutoff controls.fuel
  covered : Covered (@EquationControlMeasure.Less strata.rules.length)
    generation.worlds (ownCaptureWorldEnvironment controls domain argument captured).worlds
  certificateReady : ControlledStoredQuery controls frontier (.certificate certificate)
  hereditary : generation.Hereditary frontier

/-- Actual result-to-body R followed by the finitely many original owner R
calls selected by that same body certificate. All returned argument queries
use the original caller resources after identity freezing. -/
theorem generatedWorldApplicationArguments
    {strata : EquationStratification env} {P : VEnv → Prop}
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (frameData : WorldUnaryFrameData P controls frontier frame captured)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (bank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (certificate : RichCert sourceEnv env U registry target result locals σ
      relevant (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (queryReady : ControlledStoredQuery controls frontier (.certificate certificate)) :
    ∃ packet : WorldApplicationBackwardQueries initial domain body function argument result hu hv location
        frame substitutions P controls captured frontier relevant profile,
      ∃ supply : RichArgumentSupply sourceEnv env U registry target argument locals σ available
          packet.footprint.localNeeds,
        supply.Controlled controls frontier := by
  let base := frame.captureBase substitutions
  let identity := frameData.generation substitutions
  obtain ⟨identityReady⟩ := frameData.controlled substitutions
  have identityCompatible : identity.UsesControlPrefix controls.cutoff controls.fuel := ⟨rfl, rfl⟩
  obtain ⟨reply, ⟨replyData⟩⟩ := generatedWorldApplicationBody initial domain body function argument result hu hv
    location (.identity _) controls henv hscoped formed base.identityRealization identity trivial frontier
    identityReady identityCompatible (frameData.generation_hereditary substitutions) closed baseline capacity covered sponsored bank certificate resources queryReady
  obtain ⟨bodyFootprint, bodyCode, bodyReady, bodyResources, _⟩ :=
    reply.answer.reply.query.code_controlled henv controls replyData.query certificate.formed
  let destination := OriginalNestedDisplay.identity base argument (.ofLocation (.appArgument location) initial)
  let destinationData : WorldCallFrameData (P := P) (base := base) (caps := base.initialCaps)
      (display := destination) controls captured frontier base.identityRealization :=
    ⟨identity, trivial, identityReady, identityCompatible, closed, Nat.le_refl _, Covered.refl _, frameData.generation_hereditary substitutions⟩
  have applicationBound := originalCallWorld_boundedNode controls .fundamental
    (.app hu hv (.ref domain) body function argument result) captured baseline capacity covered
  have bodyBound := originalCallWorld_boundedNode controls .expressionReindex body
    replyData.generation.environment (ownCaptureWorldEnvironment controls domain argument captured)
    (reply.bounded controls.ordered) replyData.covered
  have bodyLower := (applicationBodyWorldChildren domain body function argument result hu hv controls captured).2
  have reserve := application_cost_le_captured (domain.dependencyOrigin controls.ordered)
    (body.dependencyOrigin controls.ordered) (function.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (result.dependencyOrigin controls.ordered)
    (frame.dependencyEnvironment controls.ordered)
  have argumentCost : (Closure.close (argument.dependencyOrigin controls.ordered)
      (frame.dependencyEnvironment controls.ordered)).cost <
      (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin controls.ordered)
        baselineEnvironment).cost :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (binder_other_cost (by simp) _) reserve)
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left capacity 1))
  have argumentLower : WorldBelow strata.rules.length
      (originalCallWorld controls .expressionReindex argument captured)
      (originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline) :=
    smaller_root (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (EquationControlMeasure.scheduleDecrease (richSchedule_strict argumentCost _ _) _ _ _ _) covered
  have selectAndReplay (need : Need) (member : need ∈ bodyFootprint.localNeeds) :
      ∃ head : CapturedHeadQuery base base.initialCaps source σ τ a need
          (applicationCaptureCapacity initial domain body function argument result hu hv location frame controls.ordered),
        ∃ query : RichGradedResult sourceEnv env U registry target argument locals σ available need.profile,
          Nonempty (ControlledStoredQuery controls frontier (.observation query.observation)) := by
    have present := bodyResources 0 need (Footprint.mem_localNeeds.mp member)
    obtain ⟨selectedHead⟩ := replyData.generation.headQuery replyData.replayable replyData.compatible
      replyData.controlled replyData.hereditary reply.answer.reply.realization.frame.valid
      reply.answer.reply.realization.substitutions controls.ordered need present
    let head := selectedHead.relabel (show a.subst .id = a from subst_id)
    have headLowerBody : WorldBelow strata.rules.length
        (originalCallWorld head.controls .expressionReindex head.display.node head.baseline)
        (originalCallWorld controls .expressionReindex body
          (ownCaptureWorldEnvironment controls domain argument captured)) :=
      BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans bodyBound (.child head.baselineMember)
    have headLower : WorldBelow strata.rules.length
        (originalCallWorld head.controls .expressionReindex head.display.node head.baseline)
        (originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline) :=
      BoundedNode.child (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans applicationBound
        (EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
          EquationControlMeasure.less_trans headLowerBody bodyLower)
    let calls := [originalCallWorld head.controls .expressionReindex head.display.node head.baseline,
      originalCallWorld controls .expressionReindex argument captured]
    have lower : ∀ call ∈ calls, WorldBelow strata.rules.length call
        (originalCallWorld controls .fundamental (.app hu hv (.ref domain) body function argument result) baseline) := by
      intro call belongs
      rcases List.mem_cons.mp belongs with rfl | belongs
      · exact headLower
      · cases List.mem_singleton.mp belongs
        exact argumentLower
    have callsSponsored : Sponsored frontier calls := by
      intro call belongs
      obtain ⟨parent, present, bound⟩ := sponsored _ (List.mem_singleton_self _)
      exact ⟨parent, present, EquationWorldClosureOrder.trans (r := @EquationControlMeasure.Less strata.rules.length)
        EquationControlMeasure.less_trans (lower call belongs) bound⟩
    obtain ⟨answer, ⟨answerData⟩⟩ := head.replayWorldAt henv hscoped formed closed destination controls
      rfl rfl captured base.identityRealization destinationData _ callsSponsored
      (applicationCallsPrefix (split_call lower) frontier) bank
    obtain ⟨frozenReady⟩ := answer.answer.freezeBase_controlled answerData.query
    exact ⟨head.toCapturedHeadQuery.enlarge (by
      simpa only [base, OriginalRichFrame.captureBase, OriginalCaptureBase.identityRealization,
        OriginalRichFrame.dependencyEnvironment, applicationCaptureCapacity, List.cons_append, List.nil_append,
        environmentCost, ← Nat.max_assoc, Nat.max_self] using reply.bounded controls.ordered),
      answer.answer.freezeBase, ⟨frozenReady⟩⟩
  have supplyAll (needs : List Need) (members : ∀ need ∈ needs, need ∈ bodyFootprint.localNeeds) :
      ∃ queries : CapturedArgumentQueries base base.initialCaps source σ τ a
          (applicationCaptureCapacity initial domain body function argument result hu hv location frame controls.ordered) needs,
        ∃ supply : RichArgumentSupply sourceEnv env U registry target argument locals σ available needs,
          supply.Controlled controls frontier := by
    induction needs with
    | nil => exact ⟨.nil, .nil, trivial⟩
    | cons need needs ih =>
      obtain ⟨head, query, ready⟩ := selectAndReplay need (members need List.mem_cons_self)
      obtain ⟨tail, supply, supplied⟩ := ih (fun need member => members need (List.mem_cons_of_mem _ member))
      exact ⟨.cons head tail, .cons query supply, ready, supplied⟩
  obtain ⟨queries, supply, supplied⟩ := supplyAll bodyFootprint.localNeeds (fun _ member => member)
  let packet : WorldApplicationBackwardQueries initial domain body function argument result hu hv location
      frame substitutions P controls captured frontier relevant profile := {
    toApplicationBackwardQueries := ⟨{
      answer := reply.answer
      bounded := fun ordered => by
        simpa only [base, OriginalRichFrame.captureBase, OriginalCaptureBase.identityRealization,
        OriginalRichFrame.dependencyEnvironment, applicationCaptureCapacity, List.cons_append, List.nil_append,
          environmentCost, ← Nat.max_assoc, Nat.max_self] using reply.bounded ordered },
      bodyFootprint, bodyCode, bodyResources, queries⟩
    generation := replyData.generation, hereditary := replyData.hereditary, replayable := replyData.replayable, controlled := replyData.controlled
    compatible := replyData.compatible, covered := replyData.covered, certificateReady := bodyReady }
  exact ⟨packet, supply, supplied⟩

end

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  {initial : ContextDerivation sourceEnv U rootSource}
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {function : EndpointState sourceEnv U source f (.forallE A B)}
  {argument : EndpointState sourceEnv U source a A}
  {result : EndpointState sourceEnv U source (B.inst a) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {frame : OriginalRichFrame sourceEnv env U registry target (location.contextDerivation initial) locals σ τ available}
  {substitutions : Ctx.SubstEq env U target σ τ source}

/-- Ordinary packing consumes the actual finite argument supply. In
particular, it needs neither an extra argument query nor an assigned-code
seed merely to construct the application's own whole-Pi request. -/
theorem WorldApplicationBackwardQueries.piRequestWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {controls : OriginalWorldControls strata sourceEnv}
    {captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered)}
    {frontier : List (World strata.rules.length)}
    (packet : WorldApplicationBackwardQueries initial domain body function argument result hu hv location
      frame substitutions P controls captured frontier relevant (profile : Profile n))
    (frameData : WorldUnaryFrameData P controls frontier frame captured)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (supply : RichArgumentSupply sourceEnv env U registry target argument locals σ available packet.footprint.localNeeds)
    (supplyReady : supply.Controlled controls frontier) :
    ∃ packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target locals σ available relevant profile,
      Nonempty (packed.Controlled controls frontier) := by
  have headReady : ∀ query ∈ packet.reply.answer.reply.realization.frame.raw.storedQueries,
      Nonempty (ControlledStoredQuery controls frontier query) :=
    fun query member => packet.controlled.selectStored (packet.generation.storedQueries_in_retained member)
  obtain ⟨packed, ⟨domainReady⟩⟩ := packet.toApplicationBackwardQueries.typedPackWorld (n := n) controls captured
    baseline capacity covered frameData headReady henv hscoped formed closed sponsored bank
  obtain ⟨argumentQuery, ⟨argumentReady⟩⟩ :=
    binderPackArgumentQueryControlled henv hscoped formed packed.pack supply supplyReady
  let key : Key packed.rank := ⟨A.subst σ, a.subst σ, packed.input⟩
  have raw := (argument.sound.defeq.mono below).substDF henv substitutions.wf formed substitutions.left
  have related := packed.related.left_diagonal
  let guard : LambdaGuard env U registry target σ A key packed.support :=
    ⟨packed.typed, packed.certificate.formed, .refl, packed.code,
      ⟨raw, raw, packed.support, packed.typed, packed.certificate.formed, packed.code, related, related⟩⟩
  obtain ⟨raisedBody, ⟨raisedBodyReady⟩⟩ := raiseCertificateControlled packet.certificateReady packed.bound
  have positions : packet.reply.answer.reply.locals = Locals.push locals := packet.reply.answer.reply.locals_eq
  have realization : (Subst.id.cons (a.subst .id)).comp σ = σ.cons (a.subst σ) := by
    funext i; cases i <;> simp only [Subst.comp, Subst.cons, subst_id] <;> rfl
  obtain ⟨bodyCode, ⟨bodyCodeReady⟩⟩ := transportControlledCertificate raisedBodyReady positions realization
  let rows : RichRows sourceEnv env U registry target (.ref domain) body locals σ relevant packed.support
      [(key, raiseProfile packed.rank packed.bound profile)] (packed.outside ++ []) :=
    .cons guard bodyCode packed.pack (fun _ member => member) .nil
  let request : GeneratedApplicationPiRequest domain body hu hv env registry target locals σ available a relevant profile :=
    ⟨packed.rank, packed.bound, key, packed.support, packed.footprint ++ (packed.outside ++ []),
      .pi hu hv packed.certificate PiGuard.literal rows,
      (fun i need member => (List.mem_append.mp member).elim (packed.resources i need)
        (fun member => packed.external i need (by simpa only [List.append_nil] using member))), guard.anchor, rfl⟩
  have requestReady : ControlledStoredQuery controls frontier (.certificate request.certificate) := by
    refine ⟨.pi hu hv packed.certificate PiGuard.literal rows domainReady.annotation
      (.cons guard bodyCode packed.pack (fun _ member => member) .nil bodyCodeReady.annotation .nil), ?_, ?_⟩
    · intro control active
      simpa only [StoredOriginalQuery.headDepth, request, rows, RichCert.headDepth, RichRows.headDepth, Nat.max_zero] using
        (Nat.max_le.mpr ⟨domainReady.within control active, bodyCodeReady.within control active⟩)
    · change Sponsored frontier (domainReady.annotation.worlds ++ (bodyCodeReady.annotation.worlds ++ []))
      simpa only [List.append_nil] using domainReady.sponsored.merge bodyCodeReady.sponsored
  exact ⟨⟨request, argumentQuery, packed.footprint, packed.certificate, packed.resources, packed.typed, packed.code⟩,
    ⟨⟨requestReady, argumentReady, domainReady⟩⟩⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
