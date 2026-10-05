import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiRowPreservation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorBaseline
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterReply
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldUnaryDiagonal

/-! A selected whole-Pi reply yields its requested row and the exact controls
of that row. Reanchoring spends the fixed original Pi baseline, using the
selected frame's numerical and hereditary non-growth witnesses together. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

 theorem AmbientBoundedParameterReply.nativePiRowWorld
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (initial : ContextDerivation sourceEnv U rootSource)
    (location : Located root (.pi hu hv (.ref domain) body))
    {base : OriginalCaptureBase env U registry target}
    (graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw)
    {strata : EquationStratification env} {P : VEnv → Prop}
    (controls : OriginalWorldControls strata sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length))
    (answer : AmbientBoundedParameterReply base commonCaps start
      (OriginalNestedDisplay.ofOccurrence initial location graph) commonLeft commonRight
      (Profile.pi protoDomain protoBody (support : Profile n) [(key, result)])
      (environmentCost baselineEnvironment))
    (data : WorldParameterReplyData (P := P) controls baseline frontier answer)
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    (sorted : (Profile.pi protoDomain protoBody support [(key, result)]).HasType (.sort true))
    (sponsored : Sponsored frontier
      [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline])
    (bank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental (.pi hu hv (.ref domain) body) baseline]))
    (admitted : Admitted env U registry target key key.anchor key.anchor) :
    ∃ row : RichPiRowCertificate env U registry target answer.reply.answer.reply.locals
      (raw.comp commonLeft) answer.reply.answer.reply.available true (.ref domain) body key result,
      Nonempty (row.Controlled controls frontier) := by
  let prior := answer.reply.answer.reply
  obtain ⟨footprint, certificate, certificateReady, resources, _⟩ :=
    prior.query.code_controlled henv controls data.query sorted
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated prior.realization.frame
    data.generation data.controlled
    data.replayable data.compatible data.hereditary
  have bodyContext : (Located.piBody location).contextDerivation initial =
      .cons ((Located.piDomain location).contextDerivation initial) domain := by
    change ContextDerivation.cons (location.contextDerivation initial)
      (Classical.choose location.originalDomains.1) = _
    exact congrArg (ContextDerivation.cons (location.contextDerivation initial))
      (EndpointState.ref.inj (Classical.choose_spec location.originalDomains.1).symm)
  let diagonal := prior.realization.frame.leftDiagonal
  let captured := prior.realization.frame.diagonalWorld controls data.generation.environment
  have capacity : environmentCost (diagonal.dependencyEnvironment controls.ordered) ≤
      environmentCost baselineEnvironment := by
    simpa only [diagonal, OriginalRichFrame.dependencyEnvironment_leftDiagonal]
      using answer.reply.bounded controls.ordered
  have covered : Covered (@EquationControlMeasure.Less strata.rules.length)
      captured.worlds baseline.worlds := by
    simpa only [captured, OriginalRichFrame.diagonalWorld_worlds, WorldGenerated.worlds]
      using data.covered
  exact certificate.piRow_controlled henv hscoped formed prior.closed
    (fun row rowReady admitted => row.reanchorWorldAt initial henv hscoped below controls
      domain (.piDomain location) body (.piBody location) bodyContext hu hv diagonal captured
      baseline capacity covered frontier frameData.leftDiagonal bank sponsored prior.closed formed
      prior.realization.substitutions.left rowReady admitted)
    hu hv (.done _) resources certificateReady (List.mem_singleton_self _) (List.mem_singleton_self _)
    (by simpa only [OriginalNestedDisplay.ofOccurrence, subst_subst, subst, ← Subst.comp_lift]
      using (answer.related.symm henv sorted.wf_value).left_diagonal) admitted

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
