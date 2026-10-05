import Lean4Lean.Theory.Typing.AnchoredOriginalTemplateComparison
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldBoundedCallBank
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldCodePreservation

/-! Exact selected output of local template assigned comparison. The source
and destination terms may have different displayed expressions. This is an
output contract, not an assertion that arbitrary such pairs are comparable.
The local compiler must establish its finite template/demand eligibility.

Both world coverage and capacity belong to the SAME selected reply. Code
extraction retains its actual original certificate and controls; it never
replaces the selected frame by the initial destination frame. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail EquationWorldClosureOrder
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

structure WorldTemplateAssignedReply
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    (base : OriginalCaptureBase env U registry target) (caps : CaptureCaps)
    (left : OriginalNestedDisplay U common leftExpression leftAssigned)
    (right : OriginalNestedDisplay U common rightExpression rightAssigned)
    (commonLeft commonRight : Subst)
    (controls : OriginalWorldControls strata right.sourceEnv)
    (baseline : WorldEnvironmentProvenance strata U baselineEnvironment)
    (frontier : List (World strata.rules.length)) (profile : Profile n) where
  reply : AmbientBoundedParameterReply base caps (leftAssigned.subst commonLeft)
    right.formationDisplay commonLeft commonRight profile (environmentCost baselineEnvironment)
  data : WorldParameterReplyData (P := P) (display := right.formationDisplay) controls baseline frontier reply

/-- Interpret the exact retained right observer as the requested code. This
is the same selected output expected by application and projection clauses;
all its bounds come from that observer, not a separately chosen certificate. -/
theorem WorldTemplateAssignedReply.code
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {controls : OriginalWorldControls strata right.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    (answer : WorldTemplateAssignedReply (P := P) base caps left right commonLeft commonRight
      controls baseline frontier (profile : Profile n))
    (henv : env.Ordered) (sorted : profile.HasType (.sort relevant)) :
    ∃ code : TemplateAssignedResult env U registry target left.node right.node
        answer.reply.reply.answer.reply.locals (left.raw.comp commonLeft) (right.raw.comp commonLeft)
        answer.reply.reply.answer.reply.available relevant profile,
      ∃ ready : ControlledStoredQuery controls frontier (.certificate code.certificate),
        ready.annotation.worlds ⊆ answer.data.query.annotation.worlds ∧
        ∀ policy, code.certificate.headDepth policy ≤
          answer.reply.reply.answer.reply.query.observation.headDepth policy := by
  obtain ⟨footprint, certificate, annotation, resources, worlds, depth⟩ :=
    answer.reply.reply.answer.reply.query.code_worlds_depth henv answer.data.query.annotation sorted
  let ready : ControlledStoredQuery controls frontier (.certificate certificate) := {
    annotation := annotation
    within := fun control active => Nat.le_trans (depth _) (answer.data.query.within control active)
    sponsored := fun world member => answer.data.query.sponsored world (worlds member) }
  refine ⟨{
    footprint := footprint
    certificate := certificate
    resources := resources
    related := ?_
    path := ?_ }, ready, worlds, depth⟩
  · simpa only [← left.realizedType commonLeft, ← right.realizedType commonLeft] using answer.reply.related
  · simpa only [← left.realizedType commonLeft, ← right.realizedType commonLeft] using answer.reply.path

/-- No extra frame is selected by code extraction. The exact original right
term, including later recursive children, is admitted under its fixed
baseline by BOTH the stored capacity and hereditary world coverage. -/
theorem WorldTemplateAssignedReply.callBound
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry} {target : List VExpr}
    {strata : EquationStratification env} {P : VEnv → Prop}
    {base : OriginalCaptureBase env U registry target} {caps : CaptureCaps}
    {left : OriginalNestedDisplay U common leftExpression leftAssigned}
    {right : OriginalNestedDisplay U common rightExpression rightAssigned}
    {controls : OriginalWorldControls strata right.sourceEnv}
    {baseline : WorldEnvironmentProvenance strata U baselineEnvironment}
    {frontier : List (World strata.rules.length)}
    (answer : WorldTemplateAssignedReply (P := P) base caps left right commonLeft commonRight
      controls baseline frontier (profile : Profile n)) (phase : RichPhase) :
    BoundedNode (@EquationControlMeasure.Less strata.rules.length)
      (originalCallWorld controls phase right.node answer.data.generation.environment)
      (originalCallWorld controls phase right.node baseline) :=
  originalCallWorld_boundedNode controls phase right.node answer.data.generation.environment baseline
    (answer.reply.reply.bounded controls.ordered) answer.data.covered

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
