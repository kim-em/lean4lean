import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPackingData
import Lean4Lean.Theory.Typing.AnchoredOriginalAmbientApplyPiHistoryGeneration
import Lean4Lean.Theory.Typing.AnchoredOriginalApplyPiSeedHistory
import Lean4Lean.Theory.Typing.AnchoredOriginalGeneratedPiCaptureData

/-! Exact application replay outputs and their row semantics. Producers retain these same records. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

structure OriginalApplyPiReplayResult
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (field : EndpointRef left.sourceEnv U left.source fieldExpression fieldType)
    (major : EndpointRef left.sourceEnv U left.source majorExpression majorType)
    (ownerInitial : List Closure)
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (profile : Profile n) where
  selected : OriginalTypeRouteFrame env registry target left.graph commonLeft commonRight
  selectedGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight left.graph selected.realization.frame.raw
  selectedBound : ∀ ordered : left.sourceEnv.Ordered,
    environmentCost (selected.realization.frame.dependencyEnvironment ordered) ≤
      environmentCost (history.sourceFrame.realization.frame.dependencyEnvironment ordered)
  packed : GeneratedApplicationPackedRequest left.domain left.body left.argument left.hu left.hv env registry target
    selected.locals (left.raw.comp commonLeft) selected.available true profile
  whole : BoundedParameterReply base commonCaps
    ((VExpr.forallE left.A left.B).subst (left.raw.comp commonLeft)) right.display commonLeft commonRight
    (Profile.pi (left.A.subst (left.raw.comp commonLeft)) (left.B.subst (left.raw.comp commonLeft).lift)
      packed.request.support [(packed.request.key, raiseProfile packed.request.rank packed.request.bound profile)])
    (environmentCost history.final)
  seed : PendingRichCapture (field := field) (major := major) history.rightDomain env registry target
    history.headerFrame.locals (right.raw.comp commonLeft) history.headerFrame.available
    ownerInitial left.a packed.request.key.anchor (left.a.subst (left.raw.comp commonRight))
  sourceGenerated : CappedCaptureGenerated base commonCaps commonLeft commonRight left.graph history.sourceFrame.realization.frame.raw
  seedScope : CappedOwnerScope common left.raw commonLeft commonRight commonCaps seed.depth
    (seed.owner.context seed.initialContext)
  seedGenerated : CappedCaptureGenerated base seedScope.caps seedScope.left seedScope.right seedScope.graph seed.frame.raw
  headerProvenance : EndpointProvenance (right.location.contextDerivation right.initial) (.ref history.rightDomain)
  seedHistory : OriginalSeedTypeHistory seed seedScope.toOriginalOwnerScope right.graph headerProvenance
    history.headerFrame.realization history.leftOrdered history.rightOrdered
  seedHistoryGenerated : seedHistory.route.Generated base seedScope.caps
  seedHistoryReserve : seedHistory.route.reserve = history.argumentSeedReserve
  pending : PendingRichCapture (field := field) (major := major) history.rightDomain env registry target
    whole.reply.answer.reply.locals (right.raw.comp commonLeft) whole.reply.answer.reply.available
    ownerInitial left.a packed.request.key.anchor (left.a.subst (left.raw.comp commonRight))
  pendingOwner : pending.owner = seed.owner
  entries : RichGroupedCapture (field := field) (major := major) history.rightDomain env registry target
    whole.reply.answer.reply.locals (right.raw.comp commonLeft) whole.reply.answer.reply.available
    ownerInitial left.a packed.request.key.anchor (left.a.subst (left.raw.comp commonRight))
  captureTrace : GeneratedArgumentCaptureTrace selected.realization.frame pending packed.request.key.input entries
  reply : CappedGeneratedQueryReply base commonCaps history.destination commonLeft commonRight profile
  environment_eq : ∀ ordered : right.sourceEnv.Ordered, reply.reply.realization.frame.dependencyEnvironment ordered =
    ((whole.reply.answer.reply.realization.frame.group history.rightDomain history.leftOrdered ownerInitial entries).reserve
      (groupCaptureHistoryReserve field major history.rightDomain history.leftOrdered history.rightOrdered ownerInitial
        history.final history.argumentSeedReserve)).dependencyEnvironment ordered
  related : TypeRelated env U registry target ((left.B.inst left.a).subst (left.raw.comp commonLeft))
    (right.B.subst ((right.raw.comp commonLeft).cons (left.a.subst (left.raw.comp commonLeft)))) profile
  path : TypeConversion env U target ((left.B.inst left.a).subst (left.raw.comp commonLeft))
    (right.B.subst ((right.raw.comp commonLeft).cons (left.a.subst (left.raw.comp commonLeft))))


structure AmbientApplyPiReplayResult
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    (field : EndpointRef left.sourceEnv U left.source fieldExpression fieldType)
    (major : EndpointRef left.sourceEnv U left.source majorExpression majorType)
    (ownerInitial : List Closure)
    (base : OriginalCaptureBase env U registry target) (commonCaps : CaptureCaps)
    (profile : Profile n)
    extends OriginalApplyPiReplayResult history field major ownerInitial base commonCaps profile where
  selectedGeneration : AmbientCaptureGenerated base commonCaps commonLeft commonRight left.graph selected.realization.frame.raw
  sourceGeneration : AmbientCaptureGenerated base commonCaps commonLeft commonRight left.graph history.sourceFrame.realization.frame.raw
  wholeGeneration : AmbientCaptureGenerated base commonCaps commonLeft commonRight right.display.graph whole.reply.answer.reply.realization.frame.raw
  seedGeneration : AmbientCaptureGenerated base seedScope.caps seedScope.left seedScope.right seedScope.graph seed.frame.raw
  historyGeneration : seedHistory.route.AmbientGenerated base seedScope.caps
  generation : AmbientCaptureGenerated base commonCaps commonLeft commonRight history.destination.graph reply.reply.realization.frame.raw


/-- The queried row supplies the codomain conversion even when the original
result request is empty. Lowering removes only the query's computed grade
padding; the actual argument and original header codomain are unchanged. -/
theorem OriginalApplyPiHistory.resultSemantics
    {left : OriginalApplicationTypeRouteSide U common}
    {right : OriginalPiTypeRouteSide U common}
    (history : OriginalApplyPiHistory env registry target commonLeft commonRight left right)
    {base : OriginalCaptureBase env U registry target}
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (request : GeneratedApplicationPiRequest left.domain left.body left.hu left.hv
      env registry target locals (left.raw.comp commonLeft) available left.a true (profile : Profile n))
    (answer : BoundedParameterReply base commonCaps
      ((VExpr.forallE left.A left.B).subst (left.raw.comp commonLeft)) right.display commonLeft commonRight
      (Profile.pi (left.A.subst (left.raw.comp commonLeft)) (left.B.subst (left.raw.comp commonLeft).lift)
        request.support [(request.key, raiseProfile request.rank request.bound profile)]) capacity) :
    TypeConversion env U target ((left.B.inst left.a).subst (left.raw.comp commonLeft))
      (right.B.subst ((right.raw.comp commonLeft).cons (left.a.subst (left.raw.comp commonLeft)))) ∧
    TypeRelated env U registry target ((left.B.inst left.a).subst (left.raw.comp commonLeft))
      (right.B.subst ((right.raw.comp commonLeft).cons (left.a.subst (left.raw.comp commonLeft)))) profile := by
  have whole : TypeRelated env U registry target
      (.forallE (left.A.subst (left.raw.comp commonLeft)) (left.B.subst (left.raw.comp commonLeft).lift))
      (.forallE (right.A.subst (right.raw.comp commonLeft)) (right.B.subst (right.raw.comp commonLeft).lift))
      (Profile.pi (left.A.subst (left.raw.comp commonLeft)) (left.B.subst (left.raw.comp commonLeft).lift)
        request.support [(request.key, raiseProfile request.rank request.bound profile)]) := by
    simpa only [OriginalPiTypeRouteSide.display, OriginalNestedDisplay.ofOccurrence,
      subst_subst, subst, ← Subst.comp_lift] using answer.related
  have body := whole.literalPiBody_pair henv hscoped formed (List.mem_singleton_self _) request.admitted
  have lowered := body.2.lower henv request.bound
  rw [OriginalFactorCut.lower_raised] at lowered
  exact ⟨by simpa only [subst_inst, inst_lift_cons] using body.1,
    by simpa only [subst_inst, inst_lift_cons] using lowered⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
