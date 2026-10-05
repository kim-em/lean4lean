import Lean4Lean.Theory.Typing.AnchoredSortableNativeDepthGrades

/-! Declaration budgets refer to the actual finite original-context stack.
Lookup lowers its stored certificate without increasing any control, and
retains the same bounded suffix. No fresh semantic entry supplier is used. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalTail
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalSortableTail

def SortableTailFits.nativeDepth (current : Name → Bool)
    (frame : SortableTailFits sourceEnv env U registry target source locals σ τ available) : Nat :=
  match frame with
  | .nil => 0
  | .push tail _ certificate .. => max (certificate.nativeDepth current) (tail.nativeDepth current)

@[simp] theorem SortableTailFits.nativeDepth_left (current : Name → Bool)
    (frame : SortableTailFits sourceEnv env U registry target source locals σ τ available) :
    frame.left.nativeDepth current = frame.nativeDepth current := by
  induction frame with
  | nil => rfl
  | push tail original certificate resources typed related needs bounded covered ih =>
    simpa only [SortableTailFits.left, SortableTailFits.rec, SortableTailFits.nativeDepth] using
      congrArg (max (certificate.nativeDepth current)) ih

@[simp] theorem SortableTailFits.nativeDepth_reorigin (current : Name → Bool)
    (frame : SortableTailFits sourceEnv env U registry target source locals σ τ available)
    (context : ContextDerivation sourceEnv U source) :
    (frame.reorigin context).nativeDepth current = frame.nativeDepth current := by
  induction frame with
  | nil => cases context; rfl
  | push tail original certificate resources typed related needs bounded covered ih =>
    cases context with
    | cons rest originalDomain =>
      simpa only [SortableTailFits.reorigin, SortableTailFits.nativeDepth] using
        congrArg (max (certificate.nativeDepth current)) (ih rest)

theorem SortableTailFits.lookup_allDepth {left right : Subst}
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (tailFits : SortableTailFits sourceEnv env U registry target source locals left right available)
    (member : need ∈ available index) (lookup : Lookup source index sourceType) :
    ∃ entry : SortableEntry sourceEnv env U registry source target locals left right available index need sourceType
      tailFits.contextDerivation,
      ∀ current, max (entry.certificate.nativeDepth current) (entry.tailFits.nativeDepth current) ≤
        tailFits.nativeDepth current := by
  induction tailFits generalizing index sourceType with
  | nil => cases lookup
  | @push source locals left right available A level N support input footprint x y
      tail originalDomain domain domainAvailable typed arguments localNeeds bounded covered ih =>
    cases lookup with
    | zero =>
      have hn := bounded need member
      have hc := covered need member
      simp only [Need.atGrade, dif_pos hn] at hc
      have ht := lowerProfile.hasType hn (typed_subset hc typed)
      have hr : Related env U registry target x y (A.subst left)
          (raiseProfile N hn need.profile) support :=
        Related.of_singletons (fun atom hatom => arguments.singleton_of_mem (hc atom hatom))
      have hl := lowerProfile.related hn henv hTarget hr
      refine ⟨{
        front := []
        tailSource := source
        domain := A
        source_eq := rfl
        index_eq := rfl
        sourceType_eq := rfl
        tailLocals := locals
        tailLeft := left
        tailRight := right
        tailAvailable := available
        tailFits := tail
        level := level
        originalDomain := originalDomain
        originalLocation := .here
        originalFront_eq := rfl
        left_eq := rfl
        right_eq := rfl
        available_eq := fun _ => rfl
        support := _
        footprint := footprint
        certificate := domain.lower need.rank hn
        resources := domainAvailable
        typed := ht
        related := ?_ }, ?_⟩
      · simpa only [Subst.cons, lift_subst_cons] using hl
      · intro current
        simp only [SortableTailFits.nativeDepth, SortableCert.nativeDepth_lower]
        exact Nat.le_refl _
    | succ lookup =>
      obtain ⟨entry, entryBound⟩ := ih member lookup
      refine ⟨{
        front := A :: entry.front
        tailSource := entry.tailSource
        domain := entry.domain
        source_eq := by simpa only [List.cons_append] using congrArg (List.cons A) entry.source_eq
        index_eq := by simpa only [List.length_cons] using congrArg (· + 1) entry.index_eq
        sourceType_eq := by
          simpa only [← liftN_succ] using congrArg VExpr.lift entry.sourceType_eq
        tailLocals := entry.tailLocals
        tailLeft := entry.tailLeft
        tailRight := entry.tailRight
        tailAvailable := entry.tailAvailable
        tailFits := entry.tailFits
        level := entry.level
        originalDomain := entry.originalDomain
        originalLocation := .there entry.originalLocation
        originalFront_eq := by
          change A :: entry.originalLocation.prefix = A :: entry.front
          exact congrArg (List.cons A) entry.originalFront_eq
        left_eq := ?_
        right_eq := ?_
        available_eq := ?_
        support := entry.support
        footprint := entry.footprint
        certificate := entry.certificate
        resources := entry.resources
        typed := entry.typed
        related := ?_ }, ?_⟩
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
        exact Nat.le_trans (entryBound current) (by
          simp only [SortableTailFits.nativeDepth]
          exact Nat.le_max_right _ _)

end Lean4Lean.AnchoredSource.Adapted.OriginalTail
