import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationFunctionFormation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationRow
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldRecipeBodyExecutionAt

/-! Select and enter the actual Pi body behind the caller function formation.
The requested profile and selected frame come from the same enriched replay.
The stored recipe remains charged while all executed originals are caller-side. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

private theorem recontextUnary
    {strata : EquationStratification env} {P : VEnv → Prop}
    {first second : ContextDerivation sourceEnv U source}
    (same : first = second)
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    (frame : OriginalRichFrame sourceEnv env U registry target first locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (data : WorldUnaryFrameData P controls frontier frame captured) :
    ∃ next : OriginalRichFrame sourceEnv env U registry target second locals σ σ available,
    ∃ world : WorldEnvironmentProvenance strata U (next.dependencyEnvironment controls.ordered),
      HEq next frame ∧ HEq world captured ∧
      next.dependencyEnvironment controls.ordered = frame.dependencyEnvironment controls.ordered ∧
      world.worlds = captured.worlds ∧ Nonempty (WorldUnaryFrameData P controls frontier next world) := by
  cases same
  exact ⟨frame, captured, HEq.rfl, HEq.rfl, rfl, rfl, ⟨data⟩⟩

/-- The body and its domain are the originals selected by the actual selected.
The parent frame is only transported along equality of original contexts. -/
structure WorldPiPrefixBodyExecution
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    {start : Located root node}
    (selected : PiPrefix start)
    (controls : OriginalWorldControls strata sourceEnv)
    (frontier : List (World strata.rules.length))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (relevant : Bool) (key : Key n) (result : Profile n) where
  domain : EndpointRef sourceEnv U source A (.sort selected.view.domainLevel)
  domain_eq : selected.view.domain = .ref domain
  row : RichPiRowCertificate env U registry target locals σ available relevant
    (.ref domain) selected.view.body key result
  rowReady : row.Controlled controls frontier
  parentContext : ContextDerivation sourceEnv U source
  parent : OriginalRichFrame sourceEnv env U registry target parentContext locals σ σ available
  parent_eq : HEq parent frame
  parentWorld : WorldEnvironmentProvenance strata U (parent.dependencyEnvironment controls.ordered)
  parentWorld_eq : HEq parentWorld captured
  execution : RichPiRowBodyExecution (P := P) (context := parentContext) controls frontier domain
    selected.view.body row σ key.anchor selected.view.domainWF selected.view.bodyWF parentWorld

private theorem enterPrefixCertificate
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource)
    (start : Located root node)
    (selected : PiPrefix start)
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalRichFrame sourceEnv env U registry target (start.contextDerivation initial) locals σ σ available)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (frontier : List (World strata.rules.length))
    (data : WorldUnaryFrameData P controls frontier frame captured)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (certificate : RichCert sourceEnv env U registry target node locals σ relevant
      (Profile.pi prototypeDomain prototypeBody (support : Profile n) [(key, result)]) footprint)
    (resources : footprint.Available available)
    (ready : ControlledStoredQuery controls frontier (.certificate certificate))
    (whole : TypeRelated env U registry target ((VExpr.forallE A B).subst σ)
      ((VExpr.forallE A B).subst σ) (Profile.pi prototypeDomain prototypeBody support [(key, result)]))
    (admitted : Admitted env U registry target key key.anchor key.anchor)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental
      (.pi selected.view.domainWF selected.view.bodyWF selected.view.domain selected.view.body) baseline])
    (bank : WorldBoundedUnaryCallBank env U registry strata P (frontier ++
      [originalCallWorld controls .fundamental
        (.pi selected.view.domainWF selected.view.bodyWF selected.view.domain selected.view.body) baseline])) :
    Nonempty (WorldPiPrefixBodyExecution (P := P) selected controls frontier frame captured relevant key result) := by
  rcases selected with ⟨view, route, locationEq⟩
  rcases view with ⟨u, v, hu, hv, domainNode, body, location, prefixEq, cost⟩
  dsimp only at route locationEq paid bank ⊢
  obtain ⟨domain, domainEq⟩ := location.originalDomains.1
  cases domainEq
  have contextEq : location.contextDerivation initial = start.contextDerivation initial := by
    rw [← locationEq, PrefixRoute.locate_contextDerivation]
  obtain ⟨parent, parentWorld, parentEq, parentWorldEq, environmentEq, worldsEq, ⟨parentData⟩⟩ :=
    recontextUnary contextEq.symm controls frontier frame captured data
  have parentCapacity : environmentCost (parent.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment := by
    rw [environmentEq]; exact capacity
  have parentCovered : Covered (@EquationControlMeasure.Less strata.rules.length) parentWorld.worlds baseline.worlds := by
    rw [worldsEq]; exact covered
  have bodyContext : (Located.piBody location).contextDerivation initial =
      .cons ((Located.piDomain location).contextDerivation initial) domain := by
    change ContextDerivation.cons (location.contextDerivation initial) (Classical.choose location.originalDomains.1) = _
    exact congrArg (ContextDerivation.cons (location.contextDerivation initial))
      (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
  obtain ⟨row, ⟨rowReady⟩⟩ := certificate.piRow_controlled henv hscoped formed closed
    (fun row rowReady admission => row.reanchorWorldAt initial henv hscoped below controls
      domain (.piDomain location) body (.piBody location) bodyContext hu hv parent parentWorld
      baseline parentCapacity parentCovered frontier parentData bank paid closed formed substitutions rowReady admission)
    hu hv route resources ready (List.mem_singleton_self _) (List.mem_singleton_self _)
    (by simpa only [subst] using whole) admitted
  obtain ⟨execution⟩ := row.enterBodyWorldAt initial henv hscoped below controls
    domain (.piDomain location) body (.piBody location) bodyContext hu hv parent parentWorld
    baseline parentCapacity parentCovered frontier parentData bank paid closed formed substitutions rowReady admitted
  exact ⟨⟨domain, rfl, row, rowReady, location.contextDerivation initial, parent, parentEq,
    parentWorld, parentWorldEq, execution⟩⟩

/-- This consumes the SAME returned whole query and frame. Physical and
charged Pi origins are both resolved by the checked finite row traversal. -/
theorem AmbientBoundedParameterReply.enterPiPrefixBodyWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {node : EndpointState sourceEnv U source (.forallE A B) assigned}
    (initial : ContextDerivation sourceEnv U rootSource)
    (start : Located root node)
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (start.contextDerivation initial) raw)
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (answer : AmbientBoundedParameterReply base commonCaps first
      (OriginalNestedDisplay.ofOccurrence initial start graph) commonLeft commonRight
      (Profile.pi protoDomain protoBody (support : Profile n) [(key, result)])
      (environmentCost baselineEnvironment))
    (data : WorldParameterReplyData (P := P) controls baseline frontier answer)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi protoDomain protoBody support [(key, result)]).HasType (.sort relevant))
    (admitted : Admitted env U registry target key key.anchor key.anchor)
    (paid : Sponsored frontier [originalCallWorld controls .fundamental
      (.pi (piPrefix start).view.domainWF (piPrefix start).view.bodyWF
        (piPrefix start).view.domain (piPrefix start).view.body) baseline])
    (bank : WorldBoundedUnaryCallBank env U registry strata P (frontier ++
      [originalCallWorld controls .fundamental
        (.pi (piPrefix start).view.domainWF (piPrefix start).view.bodyWF
          (piPrefix start).view.domain (piPrefix start).view.body) baseline])) :
    Nonempty (WorldPiPrefixBodyExecution (P := P) (piPrefix start) controls frontier
      answer.reply.answer.reply.realization.frame.leftDiagonal
      (answer.reply.answer.reply.realization.frame.diagonalWorld controls data.generation.environment)
      relevant key result) := by
  let prior := answer.reply.answer.reply
  obtain ⟨footprint, certificate, certificateReady, resources, _⟩ :=
    prior.query.code_controlled henv controls data.query sorted
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated prior.realization.frame
    data.generation data.controlled data.replayable data.compatible data.hereditary
  have capacity : environmentCost (prior.realization.frame.leftDiagonal.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment := by
    simpa only [OriginalRichFrame.dependencyEnvironment_leftDiagonal] using answer.reply.bounded controls.ordered
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      (prior.realization.frame.diagonalWorld controls data.generation.environment).worlds baseline.worlds := by
    simpa only [OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds] using data.covered
  exact enterPrefixCertificate initial start (piPrefix start) controls prior.realization.frame.leftDiagonal
    (prior.realization.frame.diagonalWorld controls data.generation.environment) baseline capacity covered
    frontier frameData.leftDiagonal henv hscoped below formed prior.closed prior.realization.substitutions.left
    certificate resources certificateReady
    (by simpa only [OriginalNestedDisplay.ofOccurrence, subst_subst] using
      (answer.related.symm henv sorted.wf_value).left_diagonal)
    admitted paid bank

/-- The enriched application request is interpreted and replayed to the
actual caller function formation, then its exact selected row is entered.
Every admission and lower bank is computed from the request and outer banks. -/
theorem OriginalApplicationTypeRouteSide.piRequestFunctionBodyWorld
    (side : OriginalApplicationTypeRouteSide U common)
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    (controls : OriginalWorldControls strata side.sourceEnv)
    (frame : OriginalCaptureRealization side.graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base commonCaps commonLeft commonRight side.graph frame.frame.raw controls)
    (replayable : generated.Replayable)
    (frontier : List (World strata.rules.length))
    (frameReady : generated.Controlled frontier)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : side.sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (request : GeneratedApplicationPiRequest side.domain side.body side.hu side.hv
      env registry target locals (side.raw.comp commonLeft) available side.a relevant (profile : Profile n))
    (requestReady : ControlledStoredQuery controls frontier (.certificate request.certificate))
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental side.node baseline])
    (unaryBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental side.node baseline]))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental side.node baseline])) :
    ∃ answer : AmbientBoundedParameterReply base commonCaps
      ((VExpr.forallE side.A side.B).subst (side.raw.comp commonLeft))
      side.functionFormationDisplay commonLeft commonRight
      (Profile.pi (side.A.subst (side.raw.comp commonLeft)) (side.B.subst (side.raw.comp commonLeft).lift)
        request.support [(request.key, raiseProfile request.rank request.bound profile)])
      (environmentCost baselineEnvironment),
    ∃ answerData : WorldParameterReplyData (P := P) controls baseline frontier answer,
      Nonempty (WorldPiPrefixBodyExecution (P := P)
        (piPrefix (.assignedFormation (.appFunction side.location))) controls frontier
        answer.reply.answer.reply.realization.frame.leftDiagonal
        (answer.reply.answer.reply.realization.frame.diagonalWorld controls answerData.generation.environment)
        relevant request.key (raiseProfile request.rank request.bound profile)) := by
  obtain ⟨answer, ⟨answerData⟩⟩ := side.piRequestFunctionFormationWorld controls frame generated replayable
    frontier frameReady compatible hereditary baseline capacity covered henv hscoped formed closed
    request requestReady sponsored unaryBank replayBank
  obtain ⟨piPaid, piBank⟩ := side.functionPiWorldBank controls baseline frontier sponsored unaryBank
  have admitted : Admitted env U registry target request.key request.key.anchor request.key.anchor := by
    rw [request.anchor_eq]
    exact request.admitted
  have executed := answer.enterPiPrefixBodyWorld side.initial (.assignedFormation (.appFunction side.location))
    side.graph controls baseline frontier answerData henv hscoped below formed request.certificate.formed
    admitted piPaid piBank
  exact ⟨answer, answerData, executed⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
