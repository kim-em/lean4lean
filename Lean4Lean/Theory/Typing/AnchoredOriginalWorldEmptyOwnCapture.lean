import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureHeadActivation

/-! Capture an actual major before opening its charged projection observer.
The empty initial request constructs its own answer and alignment; the SAME
positive capture retains the caller's controlled generation and histories.
The later nonempty replay still needs its actual recursive call bound. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private captureActivatedReply from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldCaptureHeadActivation
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

theorem emptyOwnCaptureWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    (argument : EndpointState sourceEnv U source a A)
    (location : Located root argument)
    (domain : EndpointRef sourceEnv U source A (.sort level))
    {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}
    (controls : OriginalWorldControls strata sourceEnv)
    (frame : OriginalCaptureRealization graph env registry target locals commonLeft commonRight available)
    (generated : WorldGenerated strata P base caps commonLeft commonRight graph frame.frame.raw controls)
    (frontier : List (World strata.rules.length))
    (ready : generated.Controlled frontier)
    (replayable : generated.Replayable)
    (compatible : generated.UsesControlPrefix controls.cutoff controls.fuel)
    (hereditary : generated.Hereditary frontier)
    (variableNode : EndpointState sourceEnv U (A :: source) (.bvar 0) assigned)
    (variableProvenance : EndpointProvenance (.cons (location.contextDerivation initial) domain) variableNode)
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U)) :
    ∃ reply : AmbientBoundedGeneratedQueryReply base caps
        (applicationCaptureVariableDisplay graph domain argument (.ofLocation location initial)
          variableNode variableProvenance) commonLeft commonRight (Profile.empty : Profile 0)
        (environmentCost ([Closure.bundle
          (.close (argument.dependencyOrigin controls.ordered) (frame.frame.dependencyEnvironment controls.ordered))
          (.close (domain.dependencyOrigin controls.ordered) (frame.frame.dependencyEnvironment controls.ordered))] ++
          (Closure.bundle (.close (argument.dependencyOrigin controls.ordered) (frame.frame.dependencyEnvironment controls.ordered))
            (.close (domain.dependencyOrigin controls.ordered) (frame.frame.dependencyEnvironment controls.ordered)) ::
            frame.frame.dependencyEnvironment controls.ordered))),
      Nonempty (WorldGeneratedQueryReplyData (P := P) controls
        (ownCaptureWorldEnvironment controls domain argument generated.environment) frontier reply) := by
  let query : RichObs sourceEnv env U registry target argument locals (raw.comp commonLeft)
      (Profile.empty : Profile 0) [] := .legacy (.legacy .empty)
  let queryReady : ControlledStoredQuery controls frontier (.observation query) := {
    annotation := .empty
    within := by
      intro control active
      simp only [query, StoredOriginalQuery.headDepth, RichObs.headDepth, SortableObs.headDepth]
      rw [Lean4Lean.AnchoredSource.Adapted.Obs.headDepth.eq_def]
      exact Nat.zero_le _
    sponsored := by intro world member; cases member }
  let answer : RichComputationalValue sourceEnv env U registry target argument locals
      (raw.comp commonLeft) (raw.comp commonRight) available (Profile.empty : Profile 0) := .empty
  let aligned : RichCodeTransferResult env U registry target argument.typeFormation.node (.ref domain)
      locals (raw.comp commonLeft) (raw.comp commonLeft) available true answer.support := {
    footprint := []
    certificate := .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true)))
    resources := fun _ _ member => nomatch member
    related := TypeRelated.of_singletons (fun _ member => nomatch member) }
  let alignedReady : ControlledStoredQuery controls frontier (.certificate aligned.certificate) := {
    annotation := .legacy _ (.seed _ _ .empty)
    within := by
      intro control active
      simp only [aligned, StoredOriginalQuery.headDepth, RichCert.headDepth, SortableCert.headDepth]
      rw [Lean4Lean.AnchoredSource.Adapted.Obs.headDepth.eq_def]
      exact Nat.zero_le _
    sponsored := by intro world member; cases member }
  obtain ⟨reply, data, _⟩ := captureActivatedReply initial argument location domain controls frame generated
    frontier ready replayable compatible hereditary generated.environment (Nat.le_refl _) (Covered.refl _)
    generated.environment (Nat.le_refl _) variableNode variableProvenance henv hscoped formed
    query (fun _ _ member => nomatch member) queryReady answer aligned alignedReady
  exact ⟨reply, data⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
