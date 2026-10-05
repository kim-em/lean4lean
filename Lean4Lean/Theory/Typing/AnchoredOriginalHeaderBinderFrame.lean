import Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail

/-! A captured declaration tail under genuine source binders. A newly bound
argument is justified by the actual Pi admission and the original declared
domain certificate. It is not assigned a fabricated captured-value origin.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

inductive HeaderBinderFrame
    {headerEnv sourceEnv : VEnv} {U : Nat}
    (header : EndpointRef headerEnv U [] headerExpression headerType)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr) :
    {headerSource : List VExpr} → ContextDerivation headerEnv U headerSource →
      List Nat → Subst → Subst → Valuation → Type where
  | captured (tail : HeaderRichTail header field major env registry target
      context locals left right available) :
      HeaderBinderFrame header field major env registry target context locals left right available
  | bind {context : ContextDerivation headerEnv U headerSource}
      (tail : HeaderBinderFrame header field major env registry target context locals left right available)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      (location : Located header (.ref domain))
      (lineage : location.contextDerivation .nil = context)
      (certificate : RichCert headerEnv env U registry target (.ref domain) locals left true
        (support : Profile n) footprint)
      (resources : footprint.Available available)
      (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst left) input support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      HeaderBinderFrame header field major env registry target (.cons context domain)
        (Locals.push locals) (left.cons x) (right.cons y) (available.push needs)

/-- Lookup preserves the original declared domain and its exact preceding
frame, whether the value was captured or freshly admitted at a Pi binder. -/
structure HeaderBinderEntry
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (index : Nat) (need : Need) (sourceType : VExpr) where
  front : List VExpr
  tailSource : List VExpr
  domain : VExpr
  source_eq : headerSource = front ++ domain :: tailSource
  index_eq : index = front.length
  sourceType_eq : sourceType = domain.liftN (index + 1)
  tailContext : ContextDerivation headerEnv U tailSource
  tailLocals : List Nat
  tailLeft : Subst
  tailRight : Subst
  tailAvailable : Valuation
  tailFrame : HeaderBinderFrame header field major env registry target tailContext
    tailLocals tailLeft tailRight tailAvailable
  level : VLevel
  originalDomain : EndpointRef headerEnv U tailSource domain (.sort level)
  headerLocation : Located header (.ref originalDomain)
  headerLineage : headerLocation.contextDerivation .nil = tailContext
  originalLocation : ContextDerivation.Location context tailContext originalDomain
  originalFront_eq : originalLocation.prefix = front
  left_eq : Subst.lift_l (.skipN .refl (index + 1)) left = tailLeft
  right_eq : Subst.lift_l (.skipN .refl (index + 1)) right = tailRight
  available_eq : ∀ i, tailAvailable i = available (i + (index + 1))
  support : Profile need.rank
  footprint : Footprint
  certificate : RichCert headerEnv env U registry target (.ref originalDomain)
    tailLocals tailLeft true support footprint
  resources : footprint.Available tailAvailable
  typed : need.profile.HasType support
  related : Related env U registry target (left index) (right index)
    (sourceType.subst left) need.profile support

private theorem typed_subset {small large support : Profile n}
    (subset : ∀ atom ∈ small.atoms, atom ∈ large.atoms)
    (typed : large.HasType support) : small.HasType support := by
  cases n with
  | zero => exact fun atom member => typed atom (subset atom member)
  | succ n => exact ⟨fun atom member => typed.1 atom (subset atom member), typed.2.1,
      fun atom member => typed.2.2 atom (subset atom member)⟩

theorem HeaderBinderFrame.lookup
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation headerEnv U headerSource}
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (member : need ∈ available index) (lookup : Lookup headerSource index sourceType) :
    Nonempty (HeaderBinderEntry frame index need sourceType) := by
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
      resources := entry.resources, typed := entry.typed, related := entry.related }⟩
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
        resources := resources, typed := ht, related := ?_ }⟩
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
        resources := entry.resources, typed := entry.typed, related := ?_ }⟩
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

/-- A real admitted pair extends the captured frame at an original header
binder. Both raw substitutions and all finite semantic needs are derived
from that same admission. -/
theorem HeaderBinderFrame.pushAdmitted
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (henv : env.Ordered) (headerBelow : headerEnv ≤ env)
    (frame : HeaderBinderFrame header field major env registry target context locals left right available)
    (substitutions : Ctx.SubstEq env U target left right headerSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (location : Located header (.ref domain)) (lineage : location.contextDerivation .nil = context)
    (certificate : RichCert headerEnv env U registry target (.ref domain) locals left true
      (support : Profile n) footprint)
    (resources : footprint.Available available)
    (guard : LambdaGuard env U registry target left A key support)
    (admitted : Admitted env U registry target key x y)
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms) :
    Nonempty (HeaderBinderFrame header field major env registry target (.cons context domain)
      (Locals.push locals) (left.cons x) (right.cons y) (available.push needs)) ∧
    Ctx.SubstEq env U target (left.cons x) (right.cons y) (A :: headerSource) := by
  obtain ⟨_, raw, _, _, _, _, _, arguments⟩ := admitted
  exact ⟨⟨.bind frame domain location lineage certificate resources guard.inputTyped
    (Related.convert henv guard.inputTyped guard.domains arguments) needs bounded covered⟩,
    .cons substitutions (domain.sound.defeq.mono headerBelow) (guard.path.cast raw)⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
