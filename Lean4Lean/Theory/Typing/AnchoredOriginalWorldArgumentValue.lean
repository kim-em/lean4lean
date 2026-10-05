import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilyParameterReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationInput
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFamilySandbox
import Lean4Lean.Theory.Typing.AnchoredOriginalApplicationPackingData

/-! The advertised application argument value is produced by actual lower
original F and formation R. The latter runs in the exact caller identity
sandbox and freezes its same selected observer before code extraction. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

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
  {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}

/-- The support is the computed packed support. The raw argument's unrelated
natural support is never substituted for it. Both calls are proper actual
application children and keep all inherited query sponsors. -/
theorem GeneratedApplicationPackedRequest.argumentValueWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target}
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
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
      locals (raw.comp commonLeft) available relevant (profile : Profile n))
    (ready : packed.Controlled controls frontier)
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (unaryBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline])) :
    ∃ value : RichSupportedValue sourceEnv env U registry target argument locals
        (raw.comp commonLeft) (raw.comp commonRight) available packed.request.key.input,
      value.support = packed.request.support ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate value.certificate)) := by
  let captured := generated.environment
  let parent := originalCallWorld controls .fundamental
    (.app hu hv (.ref domain) body function argument result) baseline
  have enlarged := application_cost_le_captured (domain.dependencyOrigin controls.ordered)
    (body.dependencyOrigin controls.ordered) (function.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (result.dependencyOrigin controls.ordered)
    (frame.frame.dependencyEnvironment controls.ordered)
  have domainLess := Nat.lt_of_lt_of_le (binder_domain_cost (domain.dependencyOrigin controls.ordered)
    [body.dependencyOrigin controls.ordered]
    [function.dependencyOrigin controls.ordered, argument.dependencyOrigin controls.ordered,
      result.dependencyOrigin controls.ordered] (frame.frame.dependencyEnvironment controls.ordered)) enlarged
  have argumentLess := Nat.lt_of_lt_of_le (binder_other_cost
    (child := argument.dependencyOrigin controls.ordered)
    (domain := domain.dependencyOrigin controls.ordered)
    (bodies := [body.dependencyOrigin controls.ordered])
    (children := [function.dependencyOrigin controls.ordered, argument.dependencyOrigin controls.ordered,
      result.dependencyOrigin controls.ordered]) (by simp) (frame.frame.dependencyEnvironment controls.ordered)) enlarged
  have lower {context expression assigned} (node : EndpointState sourceEnv U context expression assigned)
      (phase : RichPhase)
      (cost : (Closure.close (node.dependencyOrigin controls.ordered)
        (frame.frame.dependencyEnvironment controls.ordered)).cost <
        (Closure.close ((EndpointState.app hu hv (.ref domain) body function argument result).dependencyOrigin controls.ordered)
          (frame.frame.dependencyEnvironment controls.ordered)).cost) :
      WorldBelow strata.rules.length (originalCallWorld controls phase node captured) parent := by
    apply originalCallWorld_retargetBelow controls
      (.app hu hv (.ref domain) body function argument result) .fundamental captured baseline capacity covered
    exact smaller_root (r := @EquationControlMeasure.Less strata.rules.length) EquationControlMeasure.less_trans
      (EquationControlMeasure.scheduleDecrease (richSchedule_strict cost _ _) _ _ _ _) (Covered.refl _)
  have argBelow := lower argument .fundamental argumentLess
  have domainBelow := lower (.ref domain) .expressionReindex domainLess
  have formationBelow := lower argument.typeFormation.node .expressionReindex
    (Nat.lt_of_le_of_lt (argument.typeFormation_dependency_cost_le controls.ordered _) argumentLess)
  have fund {children : List (World strata.rules.length)}
      (below : ∀ child ∈ children, WorldBelow strata.rules.length child parent) :
      CallBelow strata.rules.length (frontier ++ children) (frontier ++ [parent]) := by
    have smaller := split_call below
    clear unaryBank replayBank ready frameReady sponsored frameHereditary
    induction frontier with
    | nil => exact smaller
    | cons sponsor rest ih => exact ih.cons sponsor
  have argFunded := fund (children := [originalCallWorld controls .fundamental argument captured])
    (fun child member => by cases List.mem_singleton.mp member; exact argBelow)
  have pairFunded := fund (children := [originalCallWorld controls .expressionReindex (.ref domain) captured,
      originalCallWorld controls .expressionReindex argument.typeFormation.node captured])
    (fun child member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact domainBelow
      · cases List.mem_singleton.mp member; exact formationBelow)
  have pairSponsored : Sponsored frontier
      [originalCallWorld controls .expressionReindex (.ref domain) captured,
       originalCallWorld controls .expressionReindex argument.typeFormation.node captured] := by
    intro world member
    rcases List.mem_cons.mp member with rfl | member
    · exact singletonSponsoredBelow sponsored domainBelow _ (List.mem_singleton_self _)
    · cases List.mem_singleton.mp member
      exact singletonSponsoredBelow sponsored formationBelow _ (List.mem_singleton_self _)
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated frame.frame generated frameReady
    frameReplayable frameCompatible frameHereditary
  obtain ⟨rawAnswer, _rawCertificateReady, _rawAnswerReady⟩ :=
    (unaryBank _ argFunded).computational argument (.ofLocation (.appArgument location) initial)
      controls frame.frame captured captured frontier (Nat.le_refl _) (Covered.refl _) rfl
      (singletonSponsoredBelow sponsored argBelow) frameData closed formed frame.substitutions
      packed.argumentQuery.observation packed.argumentQuery.resources ready.argument
  let sandbox := frame.frame.captureBase frame.substitutions
  let identity := frameData.generation frame.substitutions
  obtain ⟨identityReady⟩ := frameData.controlled frame.substitutions
  let leftDisplay := applicationDomainDisplay (frame := frame.frame) (substitutions := frame.substitutions)
  let rightDisplay := applicationArgumentFormationDisplay (frame := frame.frame) (substitutions := frame.substitutions)
  let leftData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := leftDisplay) controls captured frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, Nat.le_refl _, Covered.refl _,
      frameData.generation_hereditary frame.substitutions⟩
  let rightData : WorldCallFrameData (P := P) (base := sandbox) (caps := sandbox.initialCaps)
      (display := rightDisplay) controls captured frontier sandbox.identityRealization :=
    ⟨identity, trivial, identityReady, ⟨rfl, rfl⟩, closed, Nat.le_refl _, Covered.refl _,
      frameData.generation_hereditary frame.substitutions⟩
  obtain ⟨replayed, ⟨replayedData⟩⟩ :=
    (replayBank _ pairFunded).observation sandbox sandbox.initialCaps leftDisplay rightDisplay
      (raw.comp commonLeft) (raw.comp commonRight) controls controls rfl rfl captured captured frontier rfl
      pairSponsored sandbox.identityRealization leftData sandbox.identityRealization rightData
      (.code packed.domainCertificate) packed.domainResources ready.domain.code
  obtain ⟨frozenReady⟩ := replayed.answer.freezeBase_controlled replayedData.query
  obtain ⟨footprint, certificate, certificateReady, resources, _worlds⟩ :=
    replayed.answer.freezeBase.code_controlled henv controls frozenReady packed.domainCertificate.formed
  have atRaised := packed.argumentQuery.adapter.termMap henv hscoped formed
    (Profile.HasType.raise packed.argumentQuery.bound packed.inputTyped)
    (packed.domainRelated.raise henv packed.argumentQuery.bound) rawAnswer.related
  have related := lowerProfile.related packed.argumentQuery.bound henv formed atRaised
  rw [OriginalFactorCut.lower_raised] at related
  exact ⟨{
    support := packed.request.support, footprint := footprint, certificate := certificate, resources := resources
    typed := packed.inputTyped, related := related, typeCode := packed.domainRelated }, rfl, ⟨certificateReady⟩⟩
end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
