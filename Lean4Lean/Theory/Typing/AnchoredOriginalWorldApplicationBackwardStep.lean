import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationFunctionFormation
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldApplicationArguments
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCallerFamilyRequest

/-! One actual backward step for initializing a rigid application observer.
Starting at the application result certificate, construct the enriched argument
request and transfer the whole Pi request to the actual function formation.
No literal declaration telescope or projection-specific input is required. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

section
variable
  {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
  (initial : ContextDerivation sourceEnv U rootSource)
  (domain : EndpointRef sourceEnv U source A (.sort u))
  (body : EndpointState sourceEnv U (A :: source) B (.sort v))
  (function : EndpointState sourceEnv U source f (.forallE A B))
  (argument : EndpointState sourceEnv U source a A)
  (result : EndpointState sourceEnv U source (B.inst a) (.sort v))
  (hu : u.WF U) (hv : v.WF U)
  (location : Located root (.app hu hv (.ref domain) body function argument result))
  (frame : OriginalRichFrame sourceEnv env U registry target
    (location.contextDerivation initial) locals σ τ available)
  (substitutions : Ctx.SubstEq env U target σ τ source)

/-- All intermediate result/body transfers, owner queries, argument F, and
function-formation R calls are executed here. The output retains the SAME
packed key, full input and assigned support, paired argument admission, and
selected function reply with its hereditary history. -/
theorem applicationBackwardStepWorld
    {strata : EquationStratification env} {P : VEnv → Prop}
    (controls : OriginalWorldControls strata sourceEnv)
    (captured : WorldEnvironmentProvenance strata U (frame.dependencyEnvironment controls.ordered))
    (frontier : List (World strata.rules.length))
    (frameData : WorldUnaryFrameData P controls frontier frame captured)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (capacity : environmentCost (frame.dependencyEnvironment controls.ordered) ≤ environmentCost baselineEnvironment)
    (covered : Covered (@EquationControlMeasure.Less strata.rules.length) captured.worlds baseline.worlds)
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (sponsored : Sponsored frontier [originalCallWorld controls .fundamental
      (.app hu hv (.ref domain) body function argument result) baseline])
    (unaryBank : WorldBoundedUnaryCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (replayBank : WorldBoundedCallBank env U registry strata P
      (frontier ++ [originalCallWorld controls .fundamental
        (.app hu hv (.ref domain) body function argument result) baseline]))
    (certificate : RichCert sourceEnv env U registry target result locals σ
      relevant (profile : Profile n) footprint)
    (resources : footprint.Available available)
    (certificateReady : ControlledStoredQuery controls frontier (.certificate certificate)) :
    let base := frame.captureBase substitutions
    let side := originalApplicationTypeRouteSide initial domain body function argument result hu hv
      location (.identity _)
    ∃ output : GeneratedApplicationPackedRequest domain body argument hu hv env registry target
        locals σ available relevant profile,
      Nonempty (output.Controlled controls frontier) ∧
      (∃ value : RichSupportedValue sourceEnv env U registry target argument locals
          σ τ available output.request.key.input,
        value.support = output.request.support ∧
        Nonempty (ControlledStoredQuery controls frontier (.certificate value.certificate))) ∧
      RankedData.RequestAdmission env U (relations env U registry output.request.rank) target
        output.parameterRequest (a.subst σ) (a.subst τ) ∧
      ∃ answer : AmbientBoundedParameterReply base base.initialCaps
          ((VExpr.forallE A B).subst σ) side.functionFormationDisplay σ τ
          (Profile.pi (A.subst σ) (B.subst σ.lift) output.request.support
            [(output.request.key, raiseProfile output.request.rank output.request.bound profile)])
          (environmentCost baselineEnvironment),
        Nonempty (WorldParameterReplyData (P := P) controls baseline frontier answer) := by
  dsimp only
  let base := frame.captureBase substitutions
  let generated := frameData.generation substitutions
  obtain ⟨frameReady⟩ := frameData.controlled substitutions
  have compatible : generated.UsesControlPrefix controls.cutoff controls.fuel := ⟨rfl, rfl⟩
  have hereditary := frameData.generation_hereditary substitutions
  have below : sourceEnv ≤ env := generated.erase.ambientGenerated.ambient.1.below
  obtain ⟨packet, supply, supplyReady⟩ :=
    generatedWorldApplicationArguments initial domain body function argument result hu hv location frame
      substitutions controls captured frontier frameData baseline capacity covered henv hscoped formed closed
      sponsored replayBank certificate resources certificateReady
  obtain ⟨output, ⟨outputReady⟩⟩ := packet.piRequestWorld frameData baseline capacity covered
    henv hscoped below formed closed sponsored unaryBank supply supplyReady
  obtain ⟨value, supportEq, valueReady, admitted⟩ :=
    output.parameterRequestWorld controls base.identityRealization generated frontier frameReady trivial
      compatible hereditary baseline capacity covered henv hscoped formed closed outputReady
      sponsored unaryBank replayBank
  let side := originalApplicationTypeRouteSide initial domain body function argument result hu hv
    location (.identity _)
  obtain ⟨answer, answerData⟩ := side.piRequestFunctionFormationWorld controls base.identityRealization
    generated trivial frontier frameReady compatible hereditary baseline capacity covered henv hscoped
    formed closed output.request outputReady.request sponsored unaryBank replayBank
  exact ⟨output, ⟨outputReady⟩, ⟨value, supportEq, valueReady⟩, admitted, answer, answerData⟩

end
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
