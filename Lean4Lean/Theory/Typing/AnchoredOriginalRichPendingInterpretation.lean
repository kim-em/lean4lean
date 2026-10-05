import Lean4Lean.Theory.Typing.AnchoredOriginalRichPendingCapture
import Lean4Lean.Theory.Typing.AnchoredOriginalGenericComputational

/-! The first producer stage invokes original F at the retained whole-query
owner before choosing its declared-domain demands. It uses the actual rooted
induction contract, not a frame or alignment supplier. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail
set_option backward.isDefEq.respectTransparency false

def HeaderOwner.ComputationalInductionAt
    {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (owner : HeaderOwner field major) (env : VEnv) (registry : CanonicalHead.Registry)
    (ordered : sourceEnv.Ordered) (initial : ContextDerivation sourceEnv U source) (limit : Nat) : Prop :=
  match owner with
  | .inl occurrence => OriginalComputationalInductionAt env registry ordered initial occurrence.location limit
  | .inr occurrence => OriginalComputationalInductionAt env registry ordered initial occurrence.location limit

theorem HeaderOwner.ComputationalInductionAt.apply
    {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    {initial : ContextDerivation sourceEnv U source} {ordered : sourceEnv.Ordered}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {owner : HeaderOwner field major}
    (calls : owner.ComputationalInductionAt env registry ordered initial limit)
    (frame : OriginalRichFrame sourceEnv env U registry target (owner.context initial) locals σ τ available)
    (bound : (Closure.close (owner.node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit)
    (closed : available.AtomClosed) (formed : OnCtx target (env.IsType U))
    (substitutions : Ctx.SubstEq env U target σ τ owner.source)
    (query : RichObs sourceEnv env U registry target owner.node locals σ profile footprint)
    (resources : footprint.Available available) :
    Nonempty (RichComputationalValue sourceEnv env U registry target owner.node locals σ τ available profile) := by
  cases owner with
  | inl occurrence => exact calls _ _ _ _ _ frame bound closed formed substitutions query resources
  | inr occurrence => exact calls _ _ _ _ _ frame bound closed formed substitutions query resources

theorem PendingRichCapture.projectionValue
    (sourceOrdered : sourceEnv.Ordered)
    (registered : sourceEnv.projections name info)
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelCount : levels.length = info.uvars)
    (parameterCount : params.length = info.nparams)
    (indexCount : indices.length = info.nindices)
    (selected : info.fieldType name levels params index sourceMajor = some fieldType)
    (fieldWF : fieldLevel.WF U)
    (field : EndpointRef sourceEnv U source fieldType (.sort fieldLevel))
    (major : Derivation sourceEnv U source sourceMajor majorExpression
      (VExpr.mkApps (.const name levels) (params ++ indices)))
    (closed : info.ctorType.Closed)
    (allowed : (info.resultLevel.inst levels).IsNeverZero ∨ fieldLevel ≈ .zero)
    (pending : PendingRichCapture (field := field) (major := .left major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (formed : OnCtx target (env.IsType U))
    (ownerF : pending.owner.ComputationalInductionAt env registry sourceOrdered pending.initialContext
      (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
        selected fieldWF (.ref field) major closed allowed).dependencyOrigin sourceOrdered) ownerInitial).cost) :
    Nonempty (RichComputationalValue sourceEnv env U registry target pending.owner.node pending.ownerLocals
      pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input) := by
  have bound := pending.projection_owner_schedule sourceOrdered registered levelsWF levelCount parameterCount
    indexCount selected fieldWF field major closed allowed
  have costBound : (Closure.close (pending.owner.node.dependencyOrigin sourceOrdered)
      (pending.frame.dependencyEnvironment sourceOrdered)).cost <
    (Closure.close ((EndpointState.proj registered levelsWF levelCount parameterCount indexCount
      selected fieldWF (.ref field) major closed allowed).dependencyOrigin sourceOrdered) ownerInitial).cost := by
    simpa only [richSchedule, RichPhase.code, Nat.add_zero, Nat.mul_lt_mul_left (by decide : 0 < 3)] using bound
  exact HeaderOwner.ComputationalInductionAt.apply ownerF pending.frame costBound pending.ownerClosed formed pending.substitutions
    pending.query pending.queryAvailable

/-- Finish the current slot after syntax replay at its actual declared
occurrence. The original F answer already contains diagonal type semantics;
source-display equality transports them without a second semantic supplier. -/
noncomputable def PendingRichCapture.completeReconstructed
    {footprint : Footprint}
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (pending : PendingRichCapture (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue)
    (value : RichComputationalValue sourceEnv env U registry target pending.owner.node pending.ownerLocals
      pending.ownerLeft pending.ownerRight pending.ownerAvailable pending.input)
    (certificate : RichCert headerEnv env U registry target (.ref domain) headerLocals declaredLeft
      true value.support footprint)
    (resources : footprint.Available headerAvailable)
    (display : pending.owner.assigned.subst pending.ownerLeft = A.subst declaredLeft) :
    RichGroupedCaptureEntry (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue :=
  pending.complete {
    value := value.toRichBinderValue
    aligned := {
      footprint := footprint
      certificate := certificate
      resources := resources
      related := by rw [display]; simpa only [display] using value.typeCode }
    path := by rw [display]; exact .refl }

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
