import Lean4Lean.Theory.Typing.AnchoredOriginalRawTypeRouteReplay

/-! The actual seven-edge parameter alignment, retained below capture
generation as original derivations and frame environments. Its generation
proof mentions only the four actual frame leaves; no query or replay
function is stored in the history. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

def ParameterReplyFrame.typeRouteFrame
    {base : OriginalCaptureBase env U registry target}
    {context : ContextDerivation sourceEnv U source}
    {graph : OriginalCaptureMap (common := common) context raw}
    (frame : ParameterReplyFrame base commonCaps graph commonLeft commonRight) :
    OriginalTypeRouteFrame env registry target graph commonLeft commonRight :=
  ⟨frame.locals, frame.available, frame.realization, frame.closed⟩

section
variable
    {env familyEnv baseEnv typesEnv ctorEnv : VEnv} {U : Nat}
    {registry : CanonicalHead.Registry} {target common : List VExpr}
    {base : OriginalCaptureBase env U registry target} {commonCaps : CaptureCaps}
    {familyContext : ContextDerivation familyEnv U familySource}
    {seedContext universeContext : ContextDerivation baseEnv U seedSource}
    {requestedContext : ContextDerivation typesEnv U requestedSource}
    {ctorContext : ContextDerivation ctorEnv U ctorSource}
    (familyGraph : OriginalCaptureMap (common := common) familyContext raw)
    (seedGraph : OriginalCaptureMap (common := common) seedContext raw)
    (universeGraph : OriginalCaptureMap (common := common) universeContext raw)
    (requestedGraph : OriginalCaptureMap (common := common) requestedContext raw)
    (ctorGraph : OriginalCaptureMap (common := common) ctorContext raw)
    (family : EndpointRef familyEnv U familySource familyDomain (.sort familyLevel))
    (familyProvenance : EndpointProvenance familyContext (.ref family))
    (familyCell : Derivation baseEnv U seedSource seedDomain familyDomain (.sort familySort))
    (universeCell : Derivation baseEnv U seedSource seedDomain requestedDomain (.sort universeSort))
    (ctorCell : Derivation typesEnv U requestedSource requestedDomain ctorDomain (.sort ctorSort))
    (constructor : EndpointRef ctorEnv U ctorSource ctorDomain (.sort ctorLevel))
    (ctorProvenance : EndpointProvenance ctorContext (.ref constructor))
    (familyOrdered : familyEnv.Ordered) (baseOrdered : baseEnv.Ordered)
    (typesOrdered : typesEnv.Ordered) (ctorOrdered : ctorEnv.Ordered)
    (baseBelow : baseEnv ≤ env) (typesBelow : typesEnv ≤ env)
    (initial : List Closure)
    (seedFrame : ParameterReplyFrame base commonCaps seedGraph commonLeft commonRight)
    (universeFrame : ParameterReplyFrame base commonCaps universeGraph commonLeft commonRight)
    (requestedFrame : ParameterReplyFrame base commonCaps requestedGraph commonLeft commonRight)
    (ctorFrame : ParameterReplyFrame base commonCaps ctorGraph commonLeft commonRight)

/-- Each R edge names its actual initial frame, and each equality keeps
the environment chosen for its predecessor. Both parameter ledgers and
the universe conversion therefore survive an empty captured query. -/
noncomputable def rawParameterCellsTypeRoute :
    RawGeneratedTypeRoute env registry target commonLeft commonRight
      (familyGraph.parameterCellDisplay family familyProvenance)
      (ctorGraph.parameterCellDisplay constructor ctorProvenance)
      initial (ctorFrame.realization.frame.dependencyEnvironment ctorOrdered) :=
  .trans (.same (familyGraph.parameterCellDisplay family familyProvenance)
      (seedGraph.typeEqualityDisplay familyCell false) familyOrdered baseOrdered initial seedFrame.typeRouteFrame)
    (.trans (.equality seedGraph familyCell false baseOrdered baseBelow
        (seedFrame.realization.frame.dependencyEnvironment baseOrdered))
      (.trans (.same (seedGraph.typeEqualityDisplay familyCell true)
          (universeGraph.typeEqualityDisplay universeCell true) baseOrdered baseOrdered
          (seedFrame.realization.frame.dependencyEnvironment baseOrdered) universeFrame.typeRouteFrame)
        (.trans (.equality universeGraph universeCell true baseOrdered baseBelow
            (universeFrame.realization.frame.dependencyEnvironment baseOrdered))
          (.trans (.same (universeGraph.typeEqualityDisplay universeCell false)
              (requestedGraph.typeEqualityDisplay ctorCell true) baseOrdered typesOrdered
              (universeFrame.realization.frame.dependencyEnvironment baseOrdered) requestedFrame.typeRouteFrame)
            (.trans (.equality requestedGraph ctorCell true typesOrdered typesBelow
                (requestedFrame.realization.frame.dependencyEnvironment typesOrdered))
              (.same (requestedGraph.typeEqualityDisplay ctorCell false)
                (ctorGraph.parameterCellDisplay constructor ctorProvenance) typesOrdered ctorOrdered
                (requestedFrame.realization.frame.dependencyEnvironment typesOrdered) ctorFrame.typeRouteFrame))))))

/-- The low-level retained history really is generated by the supplied
actual prefixes. There is no universal alignment hypothesis. -/
theorem rawParameterCellsTypeRoute_generated :
    (rawParameterCellsTypeRoute familyGraph seedGraph universeGraph requestedGraph ctorGraph
      family familyProvenance familyCell universeCell ctorCell constructor ctorProvenance
      familyOrdered baseOrdered typesOrdered ctorOrdered baseBelow typesBelow initial
      seedFrame universeFrame requestedFrame ctorFrame).Generated base commonCaps := by
  refine ⟨?_, ?_⟩
  · simp [rawParameterCellsTypeRoute, RawGeneratedTypeRoute.WellFormed.eq_def]
  · intro boxed member
    simp only [rawParameterCellsTypeRoute, RawGeneratedTypeRoute.frames.eq_def,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact seedFrame.capped
    · exact universeFrame.capped
    · exact requestedFrame.capped
    · exact ctorFrame.capped

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
