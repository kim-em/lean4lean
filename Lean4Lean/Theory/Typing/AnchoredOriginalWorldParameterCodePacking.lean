import Lean4Lean.Theory.Typing.AnchoredOriginalWorldParameterDemandPacking
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryOperations

/-! Pack a requested parameter CODE demand literally, while retaining all
old value demands. The finite code extraction uses the SAME actual extra
query and controls, so the later hole consumer needs only true subset
selection and never requires the mixed complete input to be sortable. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem ProjectionHead.parameterCodeDemandPackedWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {outer : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead outer)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    {initial : ContextDerivation sourceEnv U rootSource}
    {domain : EndpointRef sourceEnv U source A (.sort u)}
    {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
    {function : EndpointState sourceEnv U source f (.forallE A B)}
    {argument : EndpointState sourceEnv U source head.fieldType A}
    {result : EndpointState sourceEnv U source (B.inst head.fieldType) (.sort v)}
    {hu : u.WF U} {hv : v.WF U}
    (location : Located root (.app hu hv (.ref domain) body function argument result))
    (majorLocation : Located (.right head.major) (.app hu hv (.ref domain) body function argument result))
    (fieldProvenance : EndpointProvenance (location.contextDerivation initial) head.field)
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (frameReady : generated.Controlled frontier)
    (frameReplayable : generated.Replayable)
    (frameCompatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (frameHereditary : generated.Hereditary frontier)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) generated.worlds baseline.worlds)
    (other : World strata.rules.length)
    (packet : ApplicationBackwardQueries initial domain body function argument result hu hv location
      frame.frame frame.substitutions controls.ordered relevant (profile : Profile n))
    (headReady : ∀ query ∈ packet.reply.answer.reply.realization.frame.raw.storedQueries,
      Nonempty (ControlledStoredQuery controls frontier query))
    (bodyReady : ControlledStoredQuery controls frontier (.certificate packet.certificate))
    (supply : RichArgumentSupply sourceEnv env U registry target argument locals (raw.comp commonLeft)
      available packet.footprint.localNeeds)
    (supplyReady : supply.Controlled controls frontier)
    (extraQuery : RichGradedResult sourceEnv env U registry target argument locals
      (raw.comp commonLeft) available (extra : Profile m))
    (extraReady : ControlledStoredQuery controls frontier (.observation extraQuery.observation))
    (extraSorted : extra.HasType (.sort extraRelevant))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (paid : Sponsored frontier [other, originalCallWorld controls .assignedComparison outer baseline])
    (unaryBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline]))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [other, originalCallWorld controls .assignedComparison outer baseline])) :
    ∃ output : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
        locals (raw.comp commonLeft) available relevant profile,
      Nonempty (output.Controlled controls frontier) ∧
      assignedSortFlag head.fieldLevel ∈ output.request.support.sortFlags ∧
      ∃ extraBound : m ≤ output.request.rank,
        ∀ atom ∈ (raiseProfile output.request.rank extraBound extra).atoms,
          atom ∈ output.request.key.input.atoms := by
  obtain ⟨footprint, certificate, certificateReady, resources, _worlds⟩ :=
    extraQuery.code_controlled henv controls extraReady extraSorted
  let normalized : RichGradedResult sourceEnv env U registry target argument locals
      (raw.comp commonLeft) available extra := {
    rank := m
    bound := Nat.le_refl _
    raw := extra
    footprint := footprint
    observation := .code certificate
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := resources
    live := Profile.HasType.sortable_live certificate.formed }
  obtain ⟨output, ready, flagPresent, extraBound, included⟩ :=
    ProjectionHead.parameterDemandPackedWorld head location majorLocation fieldProvenance controls
      frame generated frontier frameReady frameReplayable frameCompatible frameHereditary baseline capacity covered other packet headReady bodyReady
      supply supplyReady normalized certificateReady.code henv hscoped formed closed paid unaryBank replayBank
  exact ⟨output, ready, flagPresent, extraBound, included⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
