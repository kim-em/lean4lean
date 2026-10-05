import Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanLegacy
import Lean4Lean.Theory.Typing.AnchoredOriginalWorldQueryProvenance
import Lean4Lean.Theory.Typing.AnchoredOriginalRichHeadDepth

/-! Attach a legacy plan and its SAME annotation jointly to its retained
original header. Selection never annotates a separately chosen plan. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics InductiveSignature
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
open private castSpine from Lean4Lean.Theory.Typing.AnchoredOriginalRichFamilyPlanLegacy
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

theorem WorldLegacyFamilyPlanProvenance.toSortable
    {plan : FamilyPlan env U registry target name levels signature arguments profile footprint}
    (annotation : WorldLegacyFamilyPlanProvenance strata plan) :
    ∃ next : WorldSortableFamilyPlanProvenance strata plan.toSortable,
      next.worlds = annotation.worlds ∧
      ∀ policy, plan.toSortable.headDepth policy = plan.headDepth policy := by
  match annotation with
  | .terminal saturated shape relevant captures captureAnn =>
    rw [FamilyPlan.toSortable]
    refine ⟨.terminal saturated shape relevant captures captureAnn, rfl, ?_⟩
    intro policy
    rw [SortableFamilyPlan.headDepth, FamilyPlan.headDepth]
  | .binder origin domain guard body pack covered domainAnn bodyAnn =>
    obtain ⟨next, worlds, depth⟩ := bodyAnn.toSortable
    rw [FamilyPlan.toSortable]
    refine ⟨.binder origin (.ofCode domain domain.formed) guard body.toSortable pack covered
      (.ofCode domain domain.formed domainAnn) next, ?_, ?_⟩
    · change domainAnn.worlds ++ next.worlds = domainAnn.worlds ++ bodyAnn.worlds
      exact congrArg (domainAnn.worlds ++ ·) worlds
    · intro policy
      rw [SortableFamilyPlan.headDepth, FamilyPlan.headDepth,
        SortableCert.headDepth, depth]
  | .view source change child =>
    obtain ⟨next, worlds, depth⟩ := child.toSortable
    rw [FamilyPlan.toSortable]
    refine ⟨.view source.toSortable change next, worlds, ?_⟩
    intro policy
    rw [SortableFamilyPlan.headDepth, FamilyPlan.headDepth, depth]
  | .pad source child =>
    obtain ⟨next, worlds, depth⟩ := child.toSortable
    rw [FamilyPlan.toSortable]
    refine ⟨.pad source.toSortable next, worlds, ?_⟩
    intro policy
    rw [SortableFamilyPlan.headDepth, FamilyPlan.headDepth, depth]
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldSortableFamilyPlanProvenance.atOriginalSpine
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {context : ContextDerivation headerEnv U source}
    {signature : ConstantTelescope declaredType}
    {node : EndpointState headerEnv U source
      (wrapForalls (signature.domains.drop arguments.length) signature.result) (.sort level)}
    (spine : OriginalConstructorSpine (header := header) signature.result context
      (signature.domains.drop arguments.length) node)
    (sourceEq : source = (signature.domains.take arguments.length).reverse)
    {plan : SortableFamilyPlan env U registry target name levels signature arguments profile footprint}
    (annotation : WorldSortableFamilyPlanProvenance strata plan) :
    ∃ next : RichFamilyPlan env U registry target header name levels signature context
        (nativeCaptureSubst arguments) arguments profile footprint,
    ∃ nextAnnotation : WorldFamilyPlanProvenance strata next,
      nextAnnotation.worlds = annotation.worlds ∧
      ∀ policy, next.headDepth policy = plan.headDepth policy := by
  match annotation with
  | .terminal saturated resultSort relevance captures captureAnn =>
    have contextEq : source = signature.domains.reverse := by
      rw [sourceEq, saturated, List.take_length]
    cases contextEq
    refine ⟨.terminal saturated resultSort relevance captures,
      .terminal saturated resultSort relevance captures captureAnn, rfl, ?_⟩
    intro policy
    rw [RichFamilyPlan.headDepth, SortableFamilyPlan.headDepth]
  | .binder (domain := domain) (key := key) domainAt domainCode guard body pack covered domainAnn bodyAnn =>
    have small := (List.getElem?_eq_some_iff.mp domainAt).1
    have selected := (List.getElem?_eq_some_iff.mp domainAt).2
    have rest : signature.domains.drop arguments.length =
        domain :: signature.domains.drop (arguments.length+1) := by
      rw [List.drop_eq_getElem_cons small, selected]
    have selectedSpine := castSpine rest spine
    cases selectedSpine with
    | binder hu hv route location lineage child =>
      have nextSource : domain :: source = (signature.domains.take (arguments ++ [key.anchor]).length).reverse := by
        simpa only [List.length_append, List.length_singleton, sourceEq] using
          (signature.prefixContext_cons domainAt).symm
      let childSpine := castSpine (show signature.domains.drop (arguments.length+1) =
        signature.domains.drop (arguments ++ [key.anchor]).length by simp) child
      have nextResult := bodyAnn.atOriginalSpine childSpine nextSource
      rw [nativeCaptureSubst_append] at nextResult
      obtain ⟨nextBody, nextAnn, worlds, depth⟩ := nextResult
      refine ⟨.binder domainAt _ location lineage (.legacy domainCode) guard nextBody pack covered,
        .binder domainAt _ location lineage (.legacy domainCode) guard nextBody pack covered
          (.legacy domainCode domainAnn) nextAnn, ?_, ?_⟩
      · change domainAnn.worlds ++ nextAnn.worlds = domainAnn.worlds ++ bodyAnn.worlds
        exact congrArg (domainAnn.worlds ++ ·) worlds
      · intro policy
        rw [RichFamilyPlan.headDepth, SortableFamilyPlan.headDepth, RichCert.headDepth, depth]
  | .view source change child =>
    obtain ⟨next, nextAnn, worlds, depth⟩ := child.atOriginalSpine spine sourceEq
    refine ⟨.view next change, .view next change nextAnn, worlds, ?_⟩
    intro policy
    rw [RichFamilyPlan.headDepth, SortableFamilyPlan.headDepth, depth]
  | .pad source child =>
    obtain ⟨next, nextAnn, worlds, depth⟩ := child.atOriginalSpine spine sourceEq
    refine ⟨.pad next, .pad next nextAnn, worlds, ?_⟩
    intro policy
    rw [RichFamilyPlan.headDepth, SortableFamilyPlan.headDepth, depth]
termination_by sizeOf annotation
decreasing_by all_goals simp_wf <;> omega

theorem WorldSortableFamilyPlanProvenance.atOriginalHeader
    {header : EndpointRef headerEnv U [] declaredType (.sort headerLevel)}
    {signature : ConstantTelescope declaredType}
    {plan : SortableFamilyPlan env U registry target name levels signature [] profile []}
    (annotation : WorldSortableFamilyPlanProvenance strata plan) :
    ∃ next : RichFamilyPlan env U registry target header name levels signature .nil
        (nativeCaptureSubst []) [] profile [],
    ∃ nextAnnotation : WorldFamilyPlanProvenance strata next,
      nextAnnotation.worlds = annotation.worlds ∧
      ∀ policy, next.headDepth policy = plan.headDepth policy := by
  let node := (EndpointState.ref header).cast signature.type_eq rfl
  let location : Located header node := Located.here.castExpression signature.type_eq
  obtain ⟨spine⟩ := originalConstructorSpine (context := .nil) location (by
    rw [Located.castExpression_contextDerivation]; rfl)
  exact annotation.atOriginalSpine
    (castSpine (show signature.domains = signature.domains.drop ([] : List VExpr).length by simp) spine) rfl

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
