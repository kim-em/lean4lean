import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFrame
import Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTailBudget

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

noncomputable def HeaderBinderFrame.dependencyEnvironment
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (headerOrdered : headerEnv.Ordered) (sourceOrdered : sourceEnv.Ordered)
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (initial : List Closure) : List Closure :=
  match frame with
  | .captured tail => tail.dependencyEnvironment headerOrdered sourceOrdered initial
  | .bind tail domain .. =>
      let previous := tail.dependencyEnvironment headerOrdered sourceOrdered initial
      .close (domain.dependencyOrigin headerOrdered) previous :: previous

private theorem capture_environment_prefix
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {hf : headerEnv.Ordered} {sf : sourceEnv.Ordered}
    (before rest : List (Dependency.HeaderCaptureStep hf sf header field major))
    (initial : List Closure) :
    environmentCost (Dependency.headerCaptureEnvironment rest initial) ≤
      environmentCost (Dependency.headerCaptureEnvironment (before ++ rest) initial) := by
  induction before with
  | nil => exact Nat.le_refl _
  | cons step before ih =>
    simp only [List.cons_append, Dependency.headerCaptureEnvironment]
    split <;> exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem HeaderRichEntry.dependency_domain_bound
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {tail : HeaderRichTail header field major env registry target context locals left right available}
    (entry : HeaderRichEntry tail index need sourceType)
    (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure) :
    (Closure.close (entry.originalDomain.dependencyOrigin hf)
      (entry.tailFits.dependencyEnvironment hf sf initial)).cost ≤
    environmentCost (tail.dependencyEnvironment hf sf initial) := by
  obtain ⟨before, equal⟩ := entry.captureTail
  unfold HeaderRichTail.dependencyEnvironment HeaderRichTail.dependencySteps
  rw [equal, List.map_append, List.map_cons]
  apply Nat.le_trans _ (capture_environment_prefix _ _ initial)
  simp only [Dependency.headerCaptureEnvironment, Dependency.measureStep,
    Dependency.HeaderCaptureStep.argumentClosure, Option.map_some,
    Dependency.measureLocated, EndpointState.dependencyOrigin]
  split
  all_goals apply Nat.le_trans _ (Nat.le_max_left _ _)
  all_goals simp only [Closure.cost]; omega

structure MeasuredHeaderBinderEntry
    {header : EndpointRef headerEnv U [] he ht}
    {field : EndpointRef sourceEnv U source fe ft}
    {major : EndpointRef sourceEnv U source me majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (index : Nat) (need : Need) (sourceType : VExpr)
    extends HeaderBinderEntry frame index need sourceType where
  environment_le : ∀ (hf : headerEnv.Ordered) (sf : sourceEnv.Ordered) (initial : List Closure),
    (Closure.close (originalDomain.dependencyOrigin hf)
      (tailFrame.dependencyEnvironment hf sf initial)).cost ≤
    environmentCost (frame.dependencyEnvironment hf sf initial)

open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderFrame

theorem HeaderBinderFrame.lookupMeasured
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation headerEnv U headerSource}
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (member : need ∈ available index) (lookup : Lookup headerSource index sourceType) :
    Nonempty (MeasuredHeaderBinderEntry frame index need sourceType) := by
  induction frame generalizing index sourceType with
  | captured tail =>
    obtain ⟨entry⟩ := tail.lookup henv formed member lookup
    exact ⟨{
      front := entry.front, tailSource := entry.tailSource, domain := entry.domain
      source_eq := entry.source_eq, index_eq := entry.index_eq, sourceType_eq := entry.sourceType_eq
      tailContext := entry.tailContext, tailLocals := entry.tailLocals
      tailLeft := entry.tailLeft, tailRight := entry.tailRight, tailAvailable := entry.tailAvailable
      tailFrame := .captured entry.tailFits, level := entry.level, originalDomain := entry.originalDomain
      headerLocation := entry.headerLocation, headerLineage := entry.headerLineage
      originalLocation := entry.originalLocation, originalFront_eq := entry.originalFront_eq
      left_eq := entry.left_eq, right_eq := entry.right_eq, available_eq := entry.available_eq
      support := entry.support, footprint := entry.footprint, certificate := entry.certificate
      resources := entry.resources, typed := entry.typed, related := entry.related
      environment_le := fun hf sf initial => entry.dependency_domain_bound hf sf initial }⟩
  | @bind headerSource locals left right available A level n support footprint x y input
      context tail domain location lineage certificate resources typed arguments needs bounded covered ih =>
    cases lookup with
    | zero =>
      have hn := bounded need member
      have hc := covered need member
      simp only [Need.atGrade, dif_pos hn] at hc
      have ht := lowerProfile.hasType hn (typed_subset hc typed)
      have hr : Related env U registry target x y (A.subst left)
          (raiseProfile n hn need.profile) support :=
        Related.of_singletons (fun atom hm => arguments.singleton_of_mem (hc atom hm))
      have hl := lowerProfile.related hn henv formed hr
      refine ⟨{
        front := [], tailSource := headerSource, domain := A
        source_eq := rfl, index_eq := rfl, sourceType_eq := rfl
        tailContext := context, tailLocals := locals, tailLeft := left, tailRight := right
        tailAvailable := available, tailFrame := tail, level := level, originalDomain := domain
        headerLocation := location, headerLineage := lineage
        originalLocation := .here, originalFront_eq := rfl
        left_eq := rfl, right_eq := rfl, available_eq := fun _ => rfl
        support := _, footprint := footprint, certificate := certificate.lower need.rank hn
        resources := resources, typed := ht, related := ?_
        environment_le := by
          intro hf sf initial
          exact Nat.le_max_left _ _ }⟩
      simpa only [Subst.cons, lift_subst_cons] using hl
    | succ lookup =>
      obtain ⟨entry⟩ := ih member lookup
      refine ⟨{
        front := A :: entry.front, tailSource := entry.tailSource, domain := entry.domain
        source_eq := by simpa only [List.cons_append] using congrArg (List.cons A) entry.source_eq
        index_eq := by simpa only [List.length_cons] using congrArg (· + 1) entry.index_eq
        sourceType_eq := by simpa only [← liftN_succ] using congrArg VExpr.lift entry.sourceType_eq
        tailContext := entry.tailContext, tailLocals := entry.tailLocals
        tailLeft := entry.tailLeft, tailRight := entry.tailRight, tailAvailable := entry.tailAvailable
        tailFrame := entry.tailFrame, level := entry.level, originalDomain := entry.originalDomain
        headerLocation := entry.headerLocation, headerLineage := entry.headerLineage
        originalLocation := .there entry.originalLocation
        originalFront_eq := by
          change A :: entry.originalLocation.prefix = A :: entry.front
          exact congrArg (List.cons A) entry.originalFront_eq
        left_eq := ?_, right_eq := ?_, available_eq := ?_
        support := entry.support, footprint := entry.footprint, certificate := entry.certificate
        resources := entry.resources, typed := entry.typed, related := ?_
        environment_le := by
          intro hf sf initial
          exact Nat.le_trans (entry.environment_le hf sf initial) (Nat.le_max_right _ _) }⟩
      · rw [← entry.left_eq]
        funext i
        simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_assoc]
      · rw [← entry.right_eq]
        funext i
        simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_assoc]
      · intro i
        change entry.tailAvailable i = available (i + (_ + 1))
        exact entry.available_eq i
      · simpa only [Subst.cons, lift_subst_cons] using entry.related

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
