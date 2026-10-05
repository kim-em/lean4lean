import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameDepth
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderBinderMeasure

/-! Bounded rich lookup preserves the actual selected declaration entry.
All caller controls hold on one certificate and its exact retained tail. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
set_option backward.isDefEq.respectTransparency false

theorem HeaderRichTail.lookup_allDepth
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation headerEnv U headerSource}
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (member : need ∈ available index) (lookup : Lookup headerSource index sourceType) :
    ∃ entry : HeaderRichEntry tail index need sourceType,
      ∀ current, max (entry.certificate.nativeDepth current) (entry.tailFits.nativeDepth current) ≤
        tail.nativeDepth current := by
  induction tail generalizing index sourceType with
  | nil => cases lookup
  | @skip headerSource locals left right available A level leftValue rightValue
      context tail domain location lineage arguments ih =>
    cases lookup with
    | zero => cases member
    | succ lookup =>
      obtain ⟨entry, entryDepth⟩ := ih member lookup
      refine ⟨{
        front := A :: entry.front, tailSource := entry.tailSource, domain := entry.domain
        source_eq := by simpa only [List.cons_append] using congrArg (List.cons A) entry.source_eq
        index_eq := by simpa only [List.length_cons] using congrArg (· + 1) entry.index_eq
        sourceType_eq := by simpa only [← liftN_succ] using congrArg VExpr.lift entry.sourceType_eq
        tailContext := entry.tailContext, tailLocals := entry.tailLocals
        tailLeft := entry.tailLeft, tailRight := entry.tailRight, tailAvailable := entry.tailAvailable
        tailFits := entry.tailFits, level := entry.level, originalDomain := entry.originalDomain
        headerLocation := entry.headerLocation, headerLineage := entry.headerLineage
        originalLocation := .there entry.originalLocation
        originalFront_eq := by
          change A :: entry.originalLocation.prefix = A :: entry.front
          exact congrArg (List.cons A) entry.originalFront_eq
        owner := entry.owner, ownerMember := List.mem_cons_of_mem _ entry.ownerMember
        captureTail := by
          obtain ⟨before, equal⟩ := entry.captureTail
          exact ⟨_ :: before, congrArg (List.cons _) equal⟩
        captureMember := fun initial => List.mem_cons_of_mem _ (entry.captureMember initial)
        left_eq := ?_, right_eq := ?_, available_eq := ?_
        support := entry.support, footprint := entry.footprint, certificate := entry.certificate
        resources := entry.resources, typed := entry.typed, related := ?_ }, ?_⟩
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
      · exact entryDepth
  | @push headerSource locals left right available A level
      ownerLocals ownerLeft ownerRight ownerAvailable n input context
      tail domain location lineage owner answer arguments needs bounded covered ih =>
    cases lookup with
    | zero =>
      have hn := bounded need member
      have hc := covered need member
      simp only [Need.atGrade, dif_pos hn] at hc
      have ht := lowerProfile.hasType hn (typed_subset hc answer.value.typed)
      have hr : Related env U registry target (owner.expression.subst ownerLeft)
          (owner.expression.subst ownerRight) (A.subst left)
          (raiseProfile n hn need.profile) answer.value.support :=
        Related.of_singletons (fun atom hm => arguments.singleton_of_mem (hc atom hm))
      have hl := lowerProfile.related hn henv formed hr
      refine ⟨{
        front := [], tailSource := headerSource, domain := A
        source_eq := rfl, index_eq := rfl, sourceType_eq := rfl
        tailContext := context, tailLocals := locals, tailLeft := left, tailRight := right
        tailAvailable := available, tailFits := tail
        level := level, originalDomain := domain, headerLocation := location, headerLineage := lineage
        originalLocation := .here, originalFront_eq := rfl
        owner := owner, ownerMember := List.mem_cons_self
        captureTail := ⟨[], rfl⟩
        captureMember := by
          intro initial
          cases owner <;> exact List.mem_cons_self
        left_eq := rfl, right_eq := rfl, available_eq := fun _ => rfl
        support := _, footprint := answer.aligned.footprint
        certificate := answer.aligned.certificate.lower need.rank hn
        resources := answer.aligned.resources, typed := ht, related := ?_ }, ?_⟩
      · simpa only [Subst.cons, lift_subst_cons] using hl
      · intro current
        simp only [RichCert.nativeDepth_lower, HeaderRichTail.nativeDepth, HeaderValueAlignment.nativeDepth]
        exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    | succ lookup =>
      obtain ⟨entry, entryDepth⟩ := ih member lookup
      refine ⟨{
        front := A :: entry.front, tailSource := entry.tailSource, domain := entry.domain
        source_eq := by simpa only [List.cons_append] using congrArg (List.cons A) entry.source_eq
        index_eq := by simpa only [List.length_cons] using congrArg (· + 1) entry.index_eq
        sourceType_eq := by simpa only [← liftN_succ] using congrArg VExpr.lift entry.sourceType_eq
        tailContext := entry.tailContext, tailLocals := entry.tailLocals
        tailLeft := entry.tailLeft, tailRight := entry.tailRight, tailAvailable := entry.tailAvailable
        tailFits := entry.tailFits, level := entry.level, originalDomain := entry.originalDomain
        headerLocation := entry.headerLocation, headerLineage := entry.headerLineage
        originalLocation := .there entry.originalLocation
        originalFront_eq := by
          change A :: entry.originalLocation.prefix = A :: entry.front
          exact congrArg (List.cons A) entry.originalFront_eq
        owner := entry.owner, ownerMember := List.mem_cons_of_mem _ entry.ownerMember
        captureTail := by
          obtain ⟨before, equal⟩ := entry.captureTail
          exact ⟨_ :: before, congrArg (List.cons _) equal⟩
        captureMember := by
          intro initial
          cases owner <;> exact List.mem_cons_of_mem _ (entry.captureMember initial)
        left_eq := ?_, right_eq := ?_, available_eq := ?_
        support := entry.support, footprint := entry.footprint, certificate := entry.certificate
        resources := entry.resources, typed := entry.typed, related := ?_ }, ?_⟩
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
      · intro current
        exact Nat.le_trans (entryDepth current) (Nat.le_max_right _ _)

theorem HeaderBinderFrame.lookup_measured_allDepth
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation headerEnv U headerSource}
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (member : need ∈ available index) (lookup : Lookup headerSource index sourceType) :
    ∃ entry : MeasuredHeaderBinderEntry frame index need sourceType,
      ∀ current, max (entry.certificate.nativeDepth current) (entry.tailFrame.nativeDepth current) ≤
        frame.nativeDepth current := by
  induction frame generalizing index sourceType with
  | captured tail =>
    obtain ⟨entry, entryDepth⟩ := tail.lookup_allDepth henv formed member lookup
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
      environment_le := fun hf sf initial => entry.dependency_domain_bound hf sf initial }, entryDepth⟩
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
        environment_le := fun _ _ _ => Nat.le_max_left _ _ }, ?_⟩
      · simpa only [Subst.cons, lift_subst_cons] using hl
      · intro current
        simp only [RichCert.nativeDepth_lower, HeaderBinderFrame.nativeDepth]
        exact Nat.le_refl _
    | succ lookup =>
      obtain ⟨entry, entryDepth⟩ := ih member lookup
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
        environment_le := fun hf sf initial => Nat.le_trans (entry.environment_le hf sf initial) (Nat.le_max_right _ _) }, ?_⟩
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
      · intro current
        exact Nat.le_trans (entryDepth current) (Nat.le_max_right _ _)

theorem HeaderBinderFrame.lookup_allDepth
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation headerEnv U headerSource}
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (member : need ∈ available index) (lookup : Lookup headerSource index sourceType) :
    ∃ entry : HeaderBinderEntry frame index need sourceType,
      ∀ current, max (entry.certificate.nativeDepth current) (entry.tailFrame.nativeDepth current) ≤
        frame.nativeDepth current := by
  obtain ⟨entry, depth⟩ := frame.lookup_measured_allDepth henv formed member lookup
  exact ⟨entry.toHeaderBinderEntry, depth⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
