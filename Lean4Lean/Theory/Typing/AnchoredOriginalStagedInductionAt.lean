import Lean4Lean.Theory.Typing.AnchoredOriginalStagedLowerCallBank

/-! Fixed original child induction with the actual frame's source-stage
bound. These interfaces never quantify over unqualified hidden frames. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 4096

/-- Unary F is restricted to actual hereditary ambient frames. -/
def OriginalStagedComputationalInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (stage : Nat) (ordered : sourceEnv.Ordered)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    {node : EndpointState sourceEnv U source expression assigned}
    (location : Located root node) (limit : Nat) : Prop :=
  ∀ target locals σ τ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initial) locals σ τ available,
    frame.Ambient →
    frame.AllSources (SourceAtStage stage) →
    (Closure.close (node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ τ source →
    ∀ {n : Nat} {profile : Profile n} {footprint : Footprint},
    RichObs sourceEnv env U registry target node locals σ profile footprint →
    footprint.Available available →
    Nonempty (RichComputationalValue sourceEnv env U registry target node locals σ τ available profile)

def OriginalStagedCodeInductionAt
    (env : VEnv) (registry : CanonicalHead.Registry) (stage : Nat) (ordered : sourceEnv.Ordered)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    {node : EndpointState sourceEnv U source expression (.sort level)}
    (location : Located root node) (limit : Nat) : Prop :=
  ∀ target locals σ τ available,
    ∀ frame : OriginalRichFrame sourceEnv env U registry target
      (location.contextDerivation initial) locals σ τ available,
    frame.Ambient →
    frame.AllSources (SourceAtStage stage) →
    (Closure.close (node.dependencyOrigin ordered) (frame.dependencyEnvironment ordered)).cost < limit →
    available.AtomClosed → OnCtx target (env.IsType U) → Ctx.SubstEq env U target σ τ source →
    RichCodeTransfer env U registry target node node locals locals σ τ available available

namespace StagedOriginalLowerCallBank

/-- Same-stage smaller original closures are legal calls in the lexicographic bank. -/
theorem computationalAt
    (bank : StagedOriginalLowerCallBank env U registry stage (richSchedule .fundamental parentCost))
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource) {assignedType : VExpr}
    {node : EndpointState sourceEnv U source expression assignedType} (location : Located root node) :
    OriginalStagedComputationalInductionAt env registry stage ordered initial location parentCost := by
  intro target locals σ τ available frame ambient sources bound closed formed substitutions n profile footprint query resources
  exact bank.computational stage ordered below initial location target locals σ τ available frame ambient sources
    (Prod.Lex.right _ (richSchedule_strict bound _ _)) closed formed substitutions query resources

theorem codeAt
    (bank : StagedOriginalLowerCallBank env U registry stage (richSchedule .fundamental parentCost))
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (ordered : sourceEnv.Ordered) (below : sourceEnv ≤ env)
    {root : EndpointRef sourceEnv U rootSource rootExpression rootType}
    (initial : ContextDerivation sourceEnv U rootSource)
    {node : EndpointState sourceEnv U source expression (.sort level)} (location : Located root node) :
    OriginalStagedCodeInductionAt env registry stage ordered initial location parentCost := by
  intro target locals σ τ available frame ambient sources bound closed formed substitutions relevant n profile footprint query resources
  obtain ⟨answer⟩ := bank.computationalAt ordered below initial location target locals σ τ available frame
    ambient sources bound closed formed substitutions (.code query) resources
  exact answer.code henv hscoped formed query.formed

end StagedOriginalLowerCallBank
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
