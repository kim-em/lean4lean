import Lean4Lean.Theory.Typing.AnchoredOriginalRichRecordExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalRichPrefixMeasure
import Lean4Lean.Theory.Typing.AnchoredOriginalRichTail

/-! Actual two-original projection reconstruction. Major R uses a strictly
smaller original pair. Assigned-type C is called on the exposed original
projection pair at the lower phase, without reflecting field metadata. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalFactorCut
set_option backward.isDefEq.respectTransparency false

noncomputable def projectionNatural
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) :
    EndpointState sourceEnv U source (.proj name index major) head.fieldType :=
  .proj head.registered head.levelsWF head.levelCount head.parameterCount head.indexCount
    head.selected head.fieldWF head.field head.major head.closed head.relevance

private theorem projectionMajor_cost_lt
    {node : EndpointState sourceEnv U source (.proj name index major) assigned}
    (head : ProjectionHead node) (ordered : sourceEnv.Ordered) (captured : List Closure) :
    (Closure.close ((EndpointState.ref (.right head.major)).dependencyOrigin ordered) captured).cost <
      (Closure.close (node.dependencyOrigin ordered) captured).cost := by
  have child : (head.major.dependencyOrigin ordered).weight <
      ((projectionNatural head).dependencyOrigin ordered).weight := by
    apply Origin.rule_child
    simp
  have smaller := Nat.mul_lt_mul_of_pos_right child (show 0 < 1 + environmentCost captured by omega)
  exact Nat.lt_of_lt_of_le smaller (head.route.dependency_cost_le ordered captured)

private theorem projection_assignment_schedule
    {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (hl : leftEnv.Ordered) (hr : rightEnv.Ordered) (lc rc : List Closure) :
    richSchedule .assignedComparison
      ((Closure.close ((projectionNatural leftHead).dependencyOrigin hl) lc).cost +
       (Closure.close ((projectionNatural rightHead).dependencyOrigin hr) rc).cost) <
    richSchedule .expressionReindex
      ((Closure.close (left.dependencyOrigin hl) lc).cost +
       (Closure.close (right.dependencyOrigin hr) rc).cost) := by
  have le := Nat.add_le_add (leftHead.route.dependency_cost_le hl lc)
    (rightHead.route.dependency_cost_le hr rc)
  simp only [richSchedule, RichPhase.code, projectionNatural]
  omega

/-- The field reply is an actual assigned-C answer for these two exposed
projection nodes. Both the raw path and the destination rich field query are
needed: the former extends the retained request-domain chain. -/
structure RichProjectionAssignedReply
    (leftHead : ProjectionHead (left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType))
    (rightHead : ProjectionHead (right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType))
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (rightLocals : List Nat) (σ τ : Subst) (available : Valuation) (support : Profile n) where
  path : TypeConversion env U target (leftHead.fieldType.subst σ) (rightHead.fieldType.subst τ)
  code : RichCodeTransferResult env U registry target leftHead.field rightHead.field rightLocals σ τ available true support

/-- Finite source reconstruction from exactly scheduled induction replies.
Captured environments are preserved separately on the two original trees.
There is no equality assertion between their field formation occurrences. -/
theorem RichObs.projectionReindexSourceStep
    {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (hl : leftEnv.Ordered) (hr : rightEnv.Ordered) (henv : env.Ordered)
    (lc rc : List Closure)
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (major : RichObs leftEnv env U registry target (.ref (.right leftHead.major))
      leftLocals σ (Profile.singleton (n := n + 1) (.record record)) majorFootprint)
    (field : RichCert leftEnv env U registry target leftHead.field leftLocals σ true support fieldFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (leftHead.fieldType.subst σ))
    (resources : (majorFootprint ++ fieldFootprint).Available leftAvailable)
    (sameMajor : leftMajor.subst σ = rightMajor.subst τ)
    (majorR :
      leftMajor.subst σ = rightMajor.subst τ →
      RichObs leftEnv env U registry target (.ref (.right leftHead.major)) leftLocals σ
        (Profile.singleton (n := n + 1) (.record record)) majorFootprint →
      majorFootprint.Available leftAvailable →
      richSchedule .expressionReindex
        ((Closure.close ((EndpointState.ref (.right leftHead.major)).dependencyOrigin hl) lc).cost +
         (Closure.close ((EndpointState.ref (.right rightHead.major)).dependencyOrigin hr) rc).cost) <
      richSchedule .expressionReindex
        ((Closure.close (left.dependencyOrigin hl) lc).cost + (Closure.close (right.dependencyOrigin hr) rc).cost) →
      Nonempty (RichGradedResult rightEnv env U registry target (.ref (.right rightHead.major))
        rightLocals τ rightAvailable (Profile.singleton (n := n + 1) (.record record))))
    (assignedC :
      (VExpr.proj name index leftMajor).subst σ = (VExpr.proj name index rightMajor).subst τ →
      RichCert leftEnv env U registry target leftHead.field leftLocals σ true support fieldFootprint →
      fieldFootprint.Available leftAvailable →
      richSchedule .assignedComparison
        ((Closure.close ((projectionNatural leftHead).dependencyOrigin hl) lc).cost +
         (Closure.close ((projectionNatural rightHead).dependencyOrigin hr) rc).cost) <
      richSchedule .expressionReindex
        ((Closure.close (left.dependencyOrigin hl) lc).cost + (Closure.close (right.dependencyOrigin hr) rc).cost) →
      Nonempty (RichProjectionAssignedReply leftHead rightHead env registry target rightLocals σ τ rightAvailable support)) :
    ∃ footprint, Nonempty (RichObs rightEnv env U registry target right rightLocals τ request.input footprint) ∧
      footprint.Available rightAvailable := by
  obtain ⟨majorReply⟩ := majorR sameMajor major
    (fun i need hm => resources i need (List.mem_append_left _ hm)) (richSchedule_strict
    (Nat.add_lt_add (projectionMajor_cost_lt leftHead hl lc) (projectionMajor_cost_lt rightHead hr rc)) _ _)
  obtain ⟨majorFootprint, ⟨majorQuery⟩, majorAvailable⟩ := majorReply.recordObservation henv
  obtain ⟨fieldReply⟩ := assignedC (by simpa only [subst_proj] using congrArg (VExpr.proj name index) sameMajor) field
    (fun i need hm => resources i need (List.mem_append_right _ hm))
    (projection_assignment_schedule leftHead rightHead hl hr lc rc)
  let chain : DomainChain env U registry target request.input request.domain (rightHead.fieldType.subst τ) :=
    alignment.trans (.step fieldReply.path typed field.formed fieldReply.code.related (.refl _))
  exact ⟨majorFootprint ++ fieldReply.code.footprint,
    ⟨.projection rightHead nameEq member majorQuery fieldReply.code.certificate typed chain⟩,
    fun i need hm => (List.mem_append.mp hm).elim (majorAvailable i need) (fieldReply.code.resources i need)⟩

theorem RichObs.projectionReindexStep
    {left : EndpointState leftEnv U leftSource (.proj name index leftMajor) leftType}
    {right : EndpointState rightEnv U rightSource (.proj name index rightMajor) rightType}
    (leftHead : ProjectionHead left) (rightHead : ProjectionHead right)
    (hl : leftEnv.Ordered) (hr : rightEnv.Ordered) (henv : env.Ordered)
    (lc rc : List Closure) (hscoped : registry.Scoped) (hTarget : OnCtx target (env.IsType U))
    {record : RecordData (Profile n)} {request : DataRequest (Profile n)}
    (nameEq : record.family.name = name) (member : (index, request) ∈ record.fields)
    (major : RichObs leftEnv env U registry target (.ref (.right leftHead.major))
      leftLocals σ (Profile.singleton (n := n + 1) (.record record)) majorFootprint)
    (field : RichCert leftEnv env U registry target leftHead.field leftLocals σ true support fieldFootprint)
    (typed : request.input.HasType support)
    (alignment : DomainChain env U registry target request.input request.domain (leftHead.fieldType.subst σ))
    (resources : (majorFootprint ++ fieldFootprint).Available leftAvailable)
    (sameMajor : leftMajor.subst σ = rightMajor.subst τ)
    (majorR :
      leftMajor.subst σ = rightMajor.subst τ →
      RichObs leftEnv env U registry target (.ref (.right leftHead.major)) leftLocals σ
        (Profile.singleton (n := n + 1) (.record record)) majorFootprint →
      majorFootprint.Available leftAvailable →
      richSchedule .expressionReindex
        ((Closure.close ((EndpointState.ref (.right leftHead.major)).dependencyOrigin hl) lc).cost +
         (Closure.close ((EndpointState.ref (.right rightHead.major)).dependencyOrigin hr) rc).cost) <
      richSchedule .expressionReindex
        ((Closure.close (left.dependencyOrigin hl) lc).cost + (Closure.close (right.dependencyOrigin hr) rc).cost) →
      Nonempty (RichGradedResult rightEnv env U registry target (.ref (.right rightHead.major))
        rightLocals τ rightAvailable (Profile.singleton (n := n + 1) (.record record))))
    (assignedC :
      (VExpr.proj name index leftMajor).subst σ = (VExpr.proj name index rightMajor).subst τ →
      RichCert leftEnv env U registry target leftHead.field leftLocals σ true support fieldFootprint →
      fieldFootprint.Available leftAvailable →
      richSchedule .assignedComparison
        ((Closure.close ((projectionNatural leftHead).dependencyOrigin hl) lc).cost +
         (Closure.close ((projectionNatural rightHead).dependencyOrigin hr) rc).cost) <
      richSchedule .expressionReindex
        ((Closure.close (left.dependencyOrigin hl) lc).cost + (Closure.close (right.dependencyOrigin hr) rc).cost) →
      Nonempty (RichProjectionAssignedReply leftHead rightHead env registry target rightLocals σ τ rightAvailable support))
    (sourceF :
      RichObs leftEnv env U registry target left leftLocals σ request.input (majorFootprint ++ fieldFootprint) →
      (majorFootprint ++ fieldFootprint).Available leftAvailable →
      richSchedule .fundamental (Closure.close (left.dependencyOrigin hl) lc).cost <
      richSchedule .expressionReindex
        ((Closure.close (left.dependencyOrigin hl) lc).cost + (Closure.close (right.dependencyOrigin hr) rc).cost) →
      Nonempty (RichBinderValue leftEnv env U registry target left leftLocals σ σ leftAvailable request.input)) :
    Nonempty (RichGradedResult rightEnv env U registry target right rightLocals τ rightAvailable request.input) := by
  obtain ⟨footprint, ⟨observation⟩, available⟩ := RichObs.projectionReindexSourceStep
    leftHead rightHead hl hr henv lc rc nameEq member major field typed alignment resources sameMajor majorR assignedC
  have positive := (Closure.close (right.dependencyOrigin hr) rc).cost_pos
  obtain ⟨value⟩ := sourceF (.projection leftHead nameEq member major field typed alignment) resources
    (richSchedule_strict (by omega) _ _)
  exact ⟨{
    rank := n
    bound := Nat.le_refl _
    raw := request.input
    footprint := footprint
    observation := observation
    adapter := by rw [raiseProfile_self]; exact .refl _
    resources := available
    live := value.related.live henv hscoped hTarget }⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
