import Lean4Lean.Theory.Typing.AnchoredOriginalWorldArgumentValue

/-! A caller-relative family request retains all packed value and assigned
support demands. Its paired admission comes from actual argument F and
formation reindexing, independently of a stored header's source or controls. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

section Request
variable
  {domain : EndpointRef sourceEnv U source A (.sort u)}
  {body : EndpointState sourceEnv U (A :: source) B (.sort v)}
  {argument : EndpointState sourceEnv U source a A}
  {hu : u.WF U} {hv : v.WF U}

/-- Use the actual caller's declared domain. The packed key's domain may
have a finite alignment to this type; that alignment is not silently
substituted for an independent retained-header certificate. -/
def GeneratedApplicationPackedRequest.parameterRequest
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
      locals σ available relevant (profile : Profile n)) : DataRequest (Profile packed.request.rank) :=
  ⟨⟨A.subst σ, a.subst σ, packed.request.key.input⟩, packed.request.support⟩

@[simp] theorem GeneratedApplicationPackedRequest.parameterRequest_input
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
      locals σ available relevant (profile : Profile n)) :
    packed.parameterRequest.input = packed.request.key.input := rfl

@[simp] theorem GeneratedApplicationPackedRequest.parameterRequest_support
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
      locals σ available relevant (profile : Profile n)) :
    packed.parameterRequest.support = packed.request.support := rfl

theorem GeneratedApplicationPackedRequest.parameterRequest_anchor
    (packed : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
      locals σ available relevant (profile : Profile n)) :
    packed.parameterRequest.anchor = packed.request.key.anchor := packed.request.anchor_eq.symm

end Request

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

/-- The same proper argument calls used by packing produce the complete
paired admission. Both input and support remain exactly the packed ones,
including independently added assigned-code demands when input is empty. -/
theorem GeneratedApplicationPackedRequest.parameterRequestWorld
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
      Nonempty (ControlledStoredQuery controls frontier (.certificate value.certificate)) ∧
      RankedData.RequestAdmission env U (relations env U registry packed.request.rank) target
        packed.parameterRequest (a.subst (raw.comp commonLeft)) (a.subst (raw.comp commonRight)) := by
  obtain ⟨value, supportEq, valueReady⟩ := packed.argumentValueWorld controls frame generated frontier
    frameReady frameReplayable frameCompatible frameHereditary baseline capacity covered
    henv hscoped formed closed ready sponsored unaryBank replayBank
  have below : sourceEnv ≤ env := generated.erase.ambientGenerated.ambient.1.below
  have rawPair := (argument.sound.defeq.mono below).substDF henv frame.substitutions.wf formed frame.substitutions
  have related := value.related
  rw [supportEq] at related
  refine ⟨value, supportEq, valueReady, ?_⟩
  exact ⟨rawPair.hasType.1, rawPair, packed.inputTyped, packed.domainCertificate.formed,
    packed.domainRelated, related.left_diagonal, related⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
