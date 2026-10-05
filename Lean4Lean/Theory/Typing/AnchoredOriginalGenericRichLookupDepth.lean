import Lean4Lean.Theory.Typing.AnchoredOriginalRichFrameLookupDepth

/-! Generic original lookup retains its genuine source-tail occurrence and
one bounded declared-domain certificate. A captured declaration frame is a
base case; ordinary open source binders need no closed-header fabrication. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail
set_option backward.isDefEq.respectTransparency false

structure OriginalRichEntry
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals left right available)
    (index : Nat) (need : Need) (sourceType : VExpr) where
  front : List VExpr
  tailSource : List VExpr
  domain : VExpr
  source_eq : source = front ++ domain :: tailSource
  index_eq : index = front.length
  sourceType_eq : sourceType = domain.liftN (index + 1)
  tailContext : ContextDerivation sourceEnv U tailSource
  tailLocals : List Nat
  tailLeft : Subst
  tailRight : Subst
  tailAvailable : Valuation
  tailFrame : OriginalRichFrame sourceEnv env U registry target tailContext
    tailLocals tailLeft tailRight tailAvailable
  level : VLevel
  originalDomain : EndpointRef sourceEnv U tailSource domain (.sort level)
  originalLocation : ContextDerivation.Location context tailContext originalDomain
  originalFront_eq : originalLocation.prefix = front
  left_eq : Subst.lift_l (.skipN .refl (index + 1)) left = tailLeft
  right_eq : Subst.lift_l (.skipN .refl (index + 1)) right = tailRight
  available_le : ∀ i need, need ∈ tailAvailable i → need ∈ available (i + (index + 1))
  support : Profile need.rank
  footprint : Footprint
  certificate : RichCert sourceEnv env U registry target (.ref originalDomain)
    tailLocals tailLeft true support footprint
  resources : footprint.Available tailAvailable
  typed : need.profile.HasType support
  related : Related env U registry target (left index) (right index)
    (sourceType.subst left) need.profile support
  environment_le : ∀ ordered : sourceEnv.Ordered,
    (Closure.close (originalDomain.dependencyOrigin ordered)
      (tailFrame.dependencyEnvironment ordered)).cost ≤
    environmentCost (frame.dependencyEnvironment ordered)

private theorem environmentCost_suffix (before rest : List Closure) :
    environmentCost rest ≤ environmentCost (before ++ rest) := by
  induction before with
  | nil => exact Nat.le_refl _
  | cons head before ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

/-- Selection traverses the actual finite capture spine and lowers its stored
aligned certificate. The same returned certificate satisfies every filter. -/
theorem RawRichGroupEntries.lookup_allDepth
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (entries : RawRichGroupEntries (field := field) (major := major) domain env registry target
      headerLocals declaredLeft headerAvailable ownerInitial rawCapture leftValue rightValue needs)
    (member : need ∈ needs) :
    ∃ support footprint,
      ∃ certificate : RichCert headerEnv env U registry target (.ref domain) headerLocals declaredLeft
        true (support : Profile need.rank) footprint,
      footprint.Available headerAvailable ∧ need.profile.HasType support ∧
      Related env U registry target leftValue rightValue (A.subst declaredLeft) need.profile support ∧
      ∀ current, certificate.nativeDepth current ≤ entries.nativeDepth current := by
  match entries with
  | .nil => cases member
  | .cons (input := input) entry tail =>
    rcases List.mem_append.mp member with member | member
    · have bounded := (captureNeeds_covered input need member).1
      have covered := (captureNeeds_covered input need member).2
      simp only [Need.atGrade, dif_pos bounded] at covered
      have typed := lowerProfile.hasType bounded (typed_subset covered entry.answer.value.typed)
      have related : Related env U registry target (entry.owner.expression.subst entry.ownerLeft)
          (entry.owner.expression.subst entry.ownerRight) (A.subst declaredLeft)
          (raiseProfile _ bounded need.profile) entry.answer.value.support :=
        Related.of_singletons (fun atom hm => (entry.answer.related henv).singleton_of_mem (covered atom hm))
      have lowered := lowerProfile.related bounded henv formed related
      rw [entry.left_eq, entry.right_eq] at lowered
      refine ⟨_, entry.answer.aligned.footprint, entry.answer.aligned.certificate.lower need.rank bounded,
        entry.answer.aligned.resources, typed, lowered, ?_⟩
      intro current
      rw [RichCert.nativeDepth_lower, RawRichGroupEntries.nativeDepth, RawRichGroupEntry.nativeDepth_eq]
      exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))
    · obtain ⟨support, footprint, certificate, resources, typed, related, bounded⟩ :=
        tail.lookup_allDepth henv formed member
      exact ⟨support, footprint, certificate, resources, typed, related,
        fun current => Nat.le_trans (bounded current) (by
          rw [RawRichGroupEntries.nativeDepth]; exact Nat.le_max_right _ _)⟩
termination_by sizeOf entries
decreasing_by all_goals simp_wf <;> omega

theorem OriginalRichFrame.lookup_allDepth
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation sourceEnv U source}
    (frame : OriginalRichFrame sourceEnv env U registry target context locals left right available)
    (member : need ∈ available index) (lookup : Lookup source index sourceType) :
    ∃ entry : OriginalRichEntry frame index need sourceType,
      ∀ current, max (entry.certificate.nativeDepth current) (entry.tailFrame.nativeDepth current) ≤
        frame.nativeDepth current := by
  rcases frame with ⟨raw, valid⟩
  match raw, valid with
  | .reserve frame closures, valid =>
    let inner : OriginalRichFrame _ _ _ _ _ _ _ _ _ _ :=
      ⟨frame, by simpa only [RawOriginalRichFrame.Valid] using valid⟩
    obtain ⟨entry, depth⟩ := inner.lookup_allDepth henv formed member lookup
    refine ⟨{ entry with
      environment_le := fun ordered => Nat.le_trans (entry.environment_le ordered) ?_ }, ?_⟩
    · change environmentCost (frame.dependencyEnvironment ordered) ≤
        environmentCost (closures ++ frame.dependencyEnvironment ordered)
      exact environmentCost_suffix _ _
    · intro current
      simpa only [OriginalRichFrame.nativeDepth, RawOriginalRichFrame.nativeDepth, inner] using depth current
  | .nil, valid => cases lookup
  | .header capturedOrdered initial headerFrame, valid =>
    obtain ⟨entry, entryDepth⟩ := headerFrame.lookup_measured_allDepth henv formed member lookup
    exact ⟨{
      front := entry.front, tailSource := entry.tailSource, domain := entry.domain
      source_eq := entry.source_eq, index_eq := entry.index_eq, sourceType_eq := entry.sourceType_eq
      tailContext := entry.tailContext, tailLocals := entry.tailLocals
      tailLeft := entry.tailLeft, tailRight := entry.tailRight, tailAvailable := entry.tailAvailable
      tailFrame := .header capturedOrdered initial entry.tailFrame, level := entry.level, originalDomain := entry.originalDomain
      originalLocation := entry.originalLocation, originalFront_eq := entry.originalFront_eq
      left_eq := entry.left_eq, right_eq := entry.right_eq, available_le := fun i need member => by simpa only [← entry.available_eq i] using member
      support := entry.support, footprint := entry.footprint, certificate := entry.certificate
      resources := entry.resources, typed := entry.typed, related := entry.related
      environment_le := fun ordered => entry.environment_le ordered capturedOrdered initial }, fun current => by
        simpa only [OriginalRichFrame.nativeDepth, OriginalRichFrame.header, RawOriginalRichFrame.nativeDepth]
          using entryDepth current⟩
  | @RawOriginalRichFrame.bind sourceEnv U source env registry target locals left right available A level n support footprint x y input
      context tail domain certificate resources typed arguments needs bounded covered, valid =>
    have tailValid : tail.Valid := by simpa only [RawOriginalRichFrame.Valid] using valid
    let tailFrame : OriginalRichFrame _ _ _ _ _ _ _ _ _ _ := ⟨tail, tailValid⟩
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
        front := [], tailSource := source, domain := A
        source_eq := rfl, index_eq := rfl, sourceType_eq := rfl
        tailContext := _, tailLocals := locals, tailLeft := left, tailRight := right
        tailAvailable := available, tailFrame := tailFrame, level := _, originalDomain := domain
        originalLocation := .here, originalFront_eq := rfl
        left_eq := rfl, right_eq := rfl, available_le := fun _ _ member => member
        support := _, footprint := footprint, certificate := certificate.lower need.rank hn
        resources := resources, typed := ht, related := ?_
        environment_le := fun _ => Nat.le_max_left _ _ }, ?_⟩
      · simpa only [Subst.cons, lift_subst_cons] using hl
      · intro current
        simp only [RichCert.nativeDepth_lower, OriginalRichFrame.nativeDepth,
          RawOriginalRichFrame.nativeDepth, tailFrame]
        exact Nat.le_refl _
    | succ lookup =>
      obtain ⟨entry, entryDepth⟩ := tailFrame.lookup_allDepth henv formed member lookup
      refine ⟨{
        front := A :: entry.front, tailSource := entry.tailSource, domain := entry.domain
        source_eq := by simpa only [List.cons_append] using congrArg (List.cons A) entry.source_eq
        index_eq := by simpa only [List.length_cons] using congrArg (· + 1) entry.index_eq
        sourceType_eq := by simpa only [← liftN_succ] using congrArg VExpr.lift entry.sourceType_eq
        tailContext := entry.tailContext, tailLocals := entry.tailLocals
        tailLeft := entry.tailLeft, tailRight := entry.tailRight, tailAvailable := entry.tailAvailable
        tailFrame := entry.tailFrame, level := entry.level, originalDomain := entry.originalDomain
        originalLocation := .there entry.originalLocation
        originalFront_eq := by
          change A :: entry.originalLocation.prefix = A :: entry.front
          exact congrArg (List.cons A) entry.originalFront_eq
        left_eq := ?_, right_eq := ?_, available_le := ?_
        support := entry.support, footprint := entry.footprint, certificate := entry.certificate
        resources := entry.resources, typed := entry.typed, related := ?_
        environment_le := fun ordered => Nat.le_trans (entry.environment_le ordered) (Nat.le_max_right _ _) }, ?_⟩
      · rw [← entry.left_eq]
        funext i
        simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_assoc]
      · rw [← entry.right_eq]
        funext i
        simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_assoc]
      · intro i need member
        exact entry.available_le i need member
      · simpa only [Subst.cons, lift_subst_cons] using entry.related
      · intro current
        exact Nat.le_trans (entryDepth current) (by
          change tail.nativeDepth current ≤ RawOriginalRichFrame.nativeDepth current _
          rw [RawOriginalRichFrame.nativeDepth]
          exact Nat.le_max_right _ _)

  | @RawOriginalRichFrame.capture sourceEnv U source env registry target locals left right available A level rootSource
      rootExpression rootType a k rawInput argumentFootprint n support footprint x y input
      context tail domain root initialContext argument argumentLocation argumentLineage
      argumentQuery argumentAvailable certificate resources typed arguments needs bounded covered, valid =>
    have tailValid : tail.Valid := by simpa only [RawOriginalRichFrame.Valid] using valid
    let tailFrame : OriginalRichFrame _ _ _ _ _ _ _ _ _ _ := ⟨tail, tailValid⟩
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
        front := [], tailSource := source, domain := A
        source_eq := rfl, index_eq := rfl, sourceType_eq := rfl
        tailContext := _, tailLocals := locals, tailLeft := left, tailRight := right
        tailAvailable := available, tailFrame := tailFrame, level := _, originalDomain := domain
        originalLocation := .here, originalFront_eq := rfl
        left_eq := rfl, right_eq := rfl, available_le := fun _ _ member => member
        support := _, footprint := footprint, certificate := certificate.lower need.rank hn
        resources := resources, typed := ht, related := ?_
        environment_le := fun _ => Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_left _ _) }, ?_⟩
      · simpa only [Subst.cons, lift_subst_cons] using hl
      · intro current
        simp only [RichCert.nativeDepth_lower, OriginalRichFrame.nativeDepth,
          RawOriginalRichFrame.nativeDepth, tailFrame]
        exact Nat.le_max_right _ _
    | succ lookup =>
      obtain ⟨entry, entryDepth⟩ := tailFrame.lookup_allDepth henv formed member lookup
      refine ⟨{
        front := A :: entry.front, tailSource := entry.tailSource, domain := entry.domain
        source_eq := by simpa only [List.cons_append] using congrArg (List.cons A) entry.source_eq
        index_eq := by simpa only [List.length_cons] using congrArg (· + 1) entry.index_eq
        sourceType_eq := by simpa only [← liftN_succ] using congrArg VExpr.lift entry.sourceType_eq
        tailContext := entry.tailContext, tailLocals := entry.tailLocals
        tailLeft := entry.tailLeft, tailRight := entry.tailRight, tailAvailable := entry.tailAvailable
        tailFrame := entry.tailFrame, level := entry.level, originalDomain := entry.originalDomain
        originalLocation := .there entry.originalLocation
        originalFront_eq := by
          change A :: entry.originalLocation.prefix = A :: entry.front
          exact congrArg (List.cons A) entry.originalFront_eq
        left_eq := ?_, right_eq := ?_, available_le := ?_
        support := entry.support, footprint := entry.footprint, certificate := entry.certificate
        resources := entry.resources, typed := entry.typed, related := ?_
        environment_le := fun ordered => Nat.le_trans (entry.environment_le ordered) (Nat.le_max_right _ _) }, ?_⟩
      · rw [← entry.left_eq]
        funext i
        simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_assoc]
      · rw [← entry.right_eq]
        funext i
        simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_assoc]
      · intro i need member
        exact entry.available_le i need member
      · simpa only [Subst.cons, lift_subst_cons] using entry.related
      · intro current
        exact Nat.le_trans (entryDepth current) (by
          change tail.nativeDepth current ≤ RawOriginalRichFrame.nativeDepth current _
          rw [RawOriginalRichFrame.nativeDepth]
          exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

  | @RawOriginalRichFrame.group headerEnv U headerSource capturedEnv capturedSource fe ft me mt env registry target locals left right available
      A level rawCapture leftValue rightValue needs context field major tail domain capturedOrdered ownerInitial entries, valid =>
    have tailValid : tail.Valid := (by simpa only [RawOriginalRichFrame.Valid] using valid : tail.Valid ∧ entries.Valid).1
    let tailFrame : OriginalRichFrame _ _ _ _ _ _ _ _ _ _ := ⟨tail, tailValid⟩
    cases lookup with
    | zero =>
      obtain ⟨support, footprint, certificate, resources, typed, related, bounded⟩ :=
        entries.lookup_allDepth henv formed member
      refine ⟨{
        front := [], tailSource := _, domain := _
        source_eq := rfl, index_eq := rfl, sourceType_eq := rfl
        tailContext := _, tailLocals := _, tailLeft := _, tailRight := _
        tailAvailable := _, tailFrame := tailFrame, level := _, originalDomain := domain
        originalLocation := .here, originalFront_eq := rfl
        left_eq := rfl, right_eq := rfl, available_le := fun _ _ member => member
        support := support, footprint := footprint, certificate := certificate
        resources := resources, typed := typed, related := ?_
        environment_le := fun _ => Nat.le_max_left _ _ }, ?_⟩
      · simpa only [Subst.cons, lift_subst_cons] using related
      · intro current
        simp only [OriginalRichFrame.nativeDepth, RawOriginalRichFrame.nativeDepth, tailFrame]
        exact Nat.max_le.mpr ⟨Nat.le_trans (bounded current) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    | succ lookup =>
      obtain ⟨entry, entryDepth⟩ := tailFrame.lookup_allDepth henv formed member lookup
      refine ⟨{
        front := A :: entry.front, tailSource := entry.tailSource, domain := entry.domain
        source_eq := by simpa only [List.cons_append] using congrArg (List.cons A) entry.source_eq
        index_eq := by simpa only [List.length_cons] using congrArg (· + 1) entry.index_eq
        sourceType_eq := by simpa only [← liftN_succ] using congrArg VExpr.lift entry.sourceType_eq
        tailContext := entry.tailContext, tailLocals := entry.tailLocals
        tailLeft := entry.tailLeft, tailRight := entry.tailRight, tailAvailable := entry.tailAvailable
        tailFrame := entry.tailFrame, level := entry.level, originalDomain := entry.originalDomain
        originalLocation := .there entry.originalLocation
        originalFront_eq := by
          change A :: entry.originalLocation.prefix = A :: entry.front
          exact congrArg (List.cons A) entry.originalFront_eq
        left_eq := ?_, right_eq := ?_, available_le := ?_
        support := entry.support, footprint := entry.footprint, certificate := entry.certificate
        resources := entry.resources, typed := entry.typed, related := ?_
        environment_le := fun ordered => Nat.le_trans (entry.environment_le ordered)
          (Nat.le_trans (environmentCost_suffix _ _) (Nat.le_max_right _ _)) }, ?_⟩
      · rw [← entry.left_eq]
        funext i
        simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_assoc]
      · rw [← entry.right_eq]
        funext i
        simp [Subst.lift_l, Lift.liftVar_skipN, Lift.liftVar, Subst.cons, Nat.add_assoc]
      · intro i need member
        exact entry.available_le i need member
      · simpa only [Subst.cons, lift_subst_cons] using entry.related
      · intro current
        exact Nat.le_trans (entryDepth current) (by
          change tail.nativeDepth current ≤ RawOriginalRichFrame.nativeDepth current _
          rw [RawOriginalRichFrame.nativeDepth]
          exact Nat.le_max_right _ _)
  | .merge first second, valid =>
    have both : first.Valid ∧ second.Valid := by simpa only [RawOriginalRichFrame.Valid] using valid
    let firstFrame : OriginalRichFrame _ _ _ _ _ _ _ _ _ _ := ⟨first, both.1⟩
    let secondFrame : OriginalRichFrame _ _ _ _ _ _ _ _ _ _ := ⟨second, both.2⟩
    rcases List.mem_append.mp member with member | member
    · obtain ⟨entry, depth⟩ := firstFrame.lookup_allDepth henv formed member lookup
      refine ⟨{ entry with
        available_le := fun i need present => List.mem_append_left _ (entry.available_le i need present)
        environment_le := fun ordered => Nat.le_trans (entry.environment_le ordered) ?_ }, ?_⟩
      · change environmentCost (first.dependencyEnvironment ordered) ≤
          environmentCost (first.dependencyEnvironment ordered ++ second.dependencyEnvironment ordered)
        rw [merge_environmentCost_append]
        exact Nat.le_max_left _ _
      · intro current
        exact Nat.le_trans (depth current) (by
          simp only [OriginalRichFrame.nativeDepth, firstFrame, RawOriginalRichFrame.nativeDepth]
          exact Nat.le_max_left _ _)
    · obtain ⟨entry, depth⟩ := secondFrame.lookup_allDepth henv formed member lookup
      refine ⟨{ entry with
        available_le := fun i need present => List.mem_append_right _ (entry.available_le i need present)
        environment_le := fun ordered => Nat.le_trans (entry.environment_le ordered) ?_ }, ?_⟩
      · change environmentCost (second.dependencyEnvironment ordered) ≤
          environmentCost (first.dependencyEnvironment ordered ++ second.dependencyEnvironment ordered)
        exact environmentCost_suffix _ _
      · intro current
        exact Nat.le_trans (depth current) (by
          simp only [OriginalRichFrame.nativeDepth, secondFrame, RawOriginalRichFrame.nativeDepth]
          exact Nat.le_max_right _ _)
termination_by (index, sizeOf frame.raw)
decreasing_by all_goals simp_wf <;> omega

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
