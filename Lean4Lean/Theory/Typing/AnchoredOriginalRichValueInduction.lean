import Lean4Lean.Theory.Typing.AnchoredOriginalRichPiStep
import Lean4Lean.Theory.Typing.AnchoredOriginalRichVariableValue
import Lean4Lean.Theory.Typing.AnchoredSortableAppOrigin

/-! Shared value answers and their finite output actions live below the
application interpreter. These declarations retain their original statements;
canonical and captured query interpreters use the same answer type. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Unary value F at one fixed retained original child. -/
def HeaderValueInductionAt
    (header : EndpointRef headerEnv U [] headerExpression headerType)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (env : VEnv) (registry : CanonicalHead.Registry)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure)
    {headerSource : List VExpr} (context : ContextDerivation headerEnv U headerSource)
    (node : EndpointState headerEnv U headerSource expression assigned) (limit : Nat) : Prop :=
  ∀ target locals σ τ available,
    ∀ frame : HeaderBinderFrame header field major env registry target context locals σ τ available,
    (Closure.close (node.dependencyOrigin hf) (frame.dependencyEnvironment hf sf initial)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) →
    Ctx.SubstEq env U target σ τ headerSource →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs headerEnv env U registry target node locals σ profile footprint →
    footprint.Available available →
    Nonempty (RichSupportedValue headerEnv env U registry target node locals σ τ available profile)

/-- Output wrappers retain the actual assigned-type formation certificate. -/
theorem RichSupportedValue.outputPath
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichSupportedValue sourceEnv env U registry target node locals σ τ available (.singleton original))
    (path : GeneralOutputPath env U registry target original output) :
    Nonempty (RichSupportedValue sourceEnv env U registry target node locals σ τ available (.singleton output)) := by
  induction path with
  | refl => exact ⟨result⟩
  | action path action ih =>
    obtain ⟨prior⟩ := ih
    exact ⟨prior.action henv hscoped formed action⟩
  | code path action sorted ih =>
    obtain ⟨prior⟩ := ih
    exact prior.code henv hscoped formed action sorted
  | pad path ih =>
    obtain ⟨prior⟩ := ih
    exact ⟨prior.pad henv⟩
  | unpad path ih =>
    obtain ⟨prior⟩ := ih
    exact ⟨prior.unpad henv formed⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
