import Lean4Lean.Theory.Typing.AnchoredOriginalWorldFunctionDemandSupport
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldPriorArgumentField

/-! The caller's actual graded function observer supplies the certificate
needed at its prior-projection argument's exposed field. The function F and
both domain/field replay calls are proper children of the same application.
Every returned query uses the original caller frame and resource table. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut OriginalTail EquationWorldClosureOrder
open private singletonSponsoredBelow from
  Lean4Lean.Theory.Typing.AnchoredOriginalWorldPiReanchorReplay
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
  {argument : EndpointState sourceEnv U source (.proj name index value) A}
  {result : EndpointState sourceEnv U source (B.inst (.proj name index value)) (.sort v)}
  {hu : u.WF U} {hv : v.WF U}
  {location : Located root (.app hu hv (.ref domain) body function argument result)}
  {graph : OriginalCaptureMap (common := common) (location.contextDerivation initial) raw}

/-- Factor, interpret and attach the actual function demand. The output
keeps the selected literal key and both of its adapters, rather than treating
an arbitrary graded result as the requested singleton. -/
theorem applicationFunctionPriorFieldWorld
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
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (closed : available.AtomClosed)
    (head : ProjectionHead argument)
    {key : Key n} {output : Atom n}
    (query : RichGradedResult sourceEnv env U registry target function locals
      (raw.comp commonLeft) available (Profile.fn key output))
    (queryReady : ControlledStoredQuery controls frontier (.observation query.observation))
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (unary : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (replay : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline])) :
    ∃ factor : RichFunctionDemandFactor sourceEnv env U registry target function locals
        (raw.comp commonLeft) available key output,
    ∃ factorReady : ControlledStoredQuery controls frontier (.observation factor.observation),
    ∃ support : Profile factor.rank,
    ∃ footprint, ∃ certificate : RichCert sourceEnv env U registry target head.field locals
        (raw.comp commonLeft) true support footprint,
      footprint.Available available ∧ factor.key.input.HasType support ∧ support.HasType (.sort true) ∧
      TypeConversion env U target factor.key.domain (head.fieldType.subst (raw.comp commonLeft)) ∧
      TypeRelated env U registry target factor.key.domain (head.fieldType.subst (raw.comp commonLeft)) support ∧
      Nonempty (DomainChain env U registry target factor.key.input factor.key.domain
        (head.fieldType.subst (raw.comp commonLeft))) ∧
      Nonempty (ControlledStoredQuery controls frontier (.certificate certificate)) ∧
      factorReady.annotation.worlds = queryReady.annotation.worlds ∧
      factor.footprint = query.footprint ∧
      ∀ policy, factor.observation.headDepth policy = query.observation.headDepth policy := by
  obtain ⟨factor, factorReady, factorWorlds, factorFootprint, factorDepth⟩ :=
    query.functionDemandWorld queryReady henv hscoped formed
  obtain ⟨frameData⟩ := WorldUnaryFrameData.ofGenerated frame.frame generated frameReady
    frameReplayable frameCompatible frameHereditary
  have enlarged := application_cost_le_captured (domain.dependencyOrigin controls.ordered)
    (body.dependencyOrigin controls.ordered) (function.dependencyOrigin controls.ordered)
    (argument.dependencyOrigin controls.ordered) (result.dependencyOrigin controls.ordered) baselineEnvironment
  have functionLess := Nat.lt_of_lt_of_le (binder_other_cost
    (child := function.dependencyOrigin controls.ordered)
    (domain := domain.dependencyOrigin controls.ordered)
    (bodies := [body.dependencyOrigin controls.ordered])
    (children := [function.dependencyOrigin controls.ordered, argument.dependencyOrigin controls.ordered,
      result.dependencyOrigin controls.ordered]) (by simp) baselineEnvironment) enlarged
  have lower : WorldBelow strata.rules.length
      (originalCallWorld controls .fundamental function baseline)
      (originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline) :=
    original_child (richSchedule_strict functionLess _ _) _ _ _ _ baseline.worlds
  have funded : CallBelow strata.rules.length
      (frontier ++ [originalCallWorld controls .fundamental function baseline])
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]) := by
    have appendDecrease : ∀ inherited : List (World strata.rules.length),
        CallBelow strata.rules.length
          (inherited ++ [originalCallWorld controls .fundamental function baseline])
          (inherited ++ [originalCallWorld controls .fundamental
            (.app hu hv (.ref domain) body function argument result) baseline]) := by
      intro inherited
      induction inherited with
      | nil => exact split_call (by intro child member; cases List.mem_singleton.mp member; exact lower)
      | cons world tail ih => exact ih.cons world
    exact appendDecrease frontier
  obtain ⟨answer, ⟨answerReady⟩, _⟩ := (unary _ funded).computational function
    (.ofLocation (.appFunction location) initial) controls frame.frame generated.environment baseline frontier
    capacity covered rfl (singletonSponsoredBelow sponsored lower) frameData closed formed
    frame.substitutions factor.observation factor.resources factorReady
  obtain ⟨support, domainCode, domainReady, inputTyped, supportFormed, inputPath, inputCode, _, _⟩ :=
    answer.toRichSupportedValue.functionDomainWorld (.appFunction location) answerReady henv hscoped formed
  let selected := piPrefix (.assignedFormation (.appFunction location))
  obtain ⟨footprint, certificate, resources, fieldCode, fieldPath, fieldReady⟩ :=
    applicationPriorFieldWorld (location := location) controls frame generated frontier
      frameReady frameReplayable frameCompatible frameHereditary baseline capacity covered henv closed head
      selected.route domainCode.certificate domainCode.resources domainReady sponsored replay
  have combinedPath := inputPath.trans fieldPath
  have combinedCode := inputCode.trans henv fieldCode
  exact ⟨factor, factorReady, support, footprint, certificate, resources, inputTyped, supportFormed,
    combinedPath, combinedCode, ⟨.step combinedPath inputTyped supportFormed combinedCode (.refl _)⟩,
    fieldReady, factorWorlds, factorFootprint, factorDepth⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
