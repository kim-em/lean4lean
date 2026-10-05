import Lean4Lean.Theory.Typing.AnchoredOriginalRichTail
import Lean4Lean.Theory.Typing.AnchoredOriginalHeaderCaptureMeasure

/-! Earlier declaration contexts with current-source captured values. The
stored declared-domain certificate is an actual rich reindex output; the
value's original type certificate, context and location are kept separately.
-/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
open OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

abbrev HeaderOwner
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType) :=
  Sum (LocatedOrigin field) (LocatedOrigin major)

namespace HeaderOwner

def source (owner : HeaderOwner field major) : List VExpr :=
  match owner with | .inl node | .inr node => node.context

def expression (owner : HeaderOwner field major) : VExpr :=
  match owner with | .inl node | .inr node => node.expression

def assigned (owner : HeaderOwner field major) : VExpr :=
  match owner with | .inl node | .inr node => node.assigned

def node (owner : HeaderOwner (sourceEnv := sourceEnv) (U := U) field major) :
    EndpointState sourceEnv U owner.source owner.expression owner.assigned :=
  match owner with | .inl node | .inr node => node.node

noncomputable def context {source : List VExpr}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (owner : HeaderOwner (sourceEnv := sourceEnv) (U := U) (source := source) field major)
    (initial : ContextDerivation sourceEnv U source) : ContextDerivation sourceEnv U owner.source :=
  match owner with
  | .inl node => node.location.contextDerivation initial
  | .inr node => node.location.contextDerivation initial

def closure (owner : HeaderOwner field major) (initial : List Closure) : Closure :=
  match owner with | .inl node | .inr node => node.closure initial

def environment (owner : HeaderOwner field major) (initial : List Closure) : List Closure :=
  match owner with | .inl node | .inr node => node.location.environment initial

theorem closure_eq (owner : HeaderOwner field major) (initial : List Closure) :
    owner.closure initial = .close owner.node.origin (owner.environment initial) := by
  cases owner <;> rfl

end HeaderOwner

/-- One finite answer to the actual owner/declared-domain comparison. The
source contexts and environments may differ; both certificate occurrences
remain exact. This is data returned by a recursive call, not a callback. -/
structure HeaderValueAlignment
    {sourceEnv headerEnv : VEnv} {U : Nat}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (owner : HeaderOwner field major)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (ownerLocals headerLocals : List Nat) (ownerLeft ownerRight declaredLeft : Subst)
    (ownerAvailable headerAvailable : Valuation) (input : Profile n) where
  value : RichBinderValue sourceEnv env U registry target owner.node ownerLocals ownerLeft ownerRight ownerAvailable input
  aligned : RichCodeTransferResult env U registry target owner.node.typeFormation.node (.ref domain)
    headerLocals ownerLeft declaredLeft headerAvailable true value.support
  path : TypeConversion env U target (owner.assigned.subst ownerLeft) (A.subst declaredLeft)

theorem HeaderValueAlignment.related
    {domain : EndpointRef headerEnv U headerSource A (.sort level)}
    (henv : env.Ordered)
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals headerLocals
      ownerLeft ownerRight declaredLeft ownerAvailable headerAvailable input) :
    Related env U registry target (owner.expression.subst ownerLeft) (owner.expression.subst ownerRight)
      (A.subst declaredLeft) input answer.value.support :=
  answer.value.related.convert henv answer.value.typed answer.aligned.related

/-- Every stack cell keeps an actual header-domain location, an actual
current-source owner location, and the finite aligned source-code answer. -/
inductive HeaderRichTail
    {headerEnv sourceEnv : VEnv} {U : Nat}
    (header : EndpointRef headerEnv U [] headerExpression headerType)
    (field : EndpointRef sourceEnv U source fieldExpression fieldType)
    (major : EndpointRef sourceEnv U source majorExpression majorType)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr) :
    {headerSource : List VExpr} → ContextDerivation headerEnv U headerSource →
      List Nat → Subst → Subst → Valuation → Type where
  | nil : HeaderRichTail header field major env registry target .nil locals left right available
  | skip {context : ContextDerivation headerEnv U headerSource}
      (tail : HeaderRichTail header field major env registry target context locals left right available)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      (location : Located header (.ref domain))
      (lineage : location.contextDerivation .nil = context)
      (arguments : env.IsDefEq U target leftValue rightValue (A.subst left)) :
      HeaderRichTail header field major env registry target (.cons context domain) (Locals.push locals)
        (left.cons leftValue) (right.cons rightValue) (available.push [])
  | push {context : ContextDerivation headerEnv U headerSource}
      (tail : HeaderRichTail header field major env registry target context locals left right available)
      (domain : EndpointRef headerEnv U headerSource A (.sort level))
      (location : Located header (.ref domain))
      (lineage : location.contextDerivation .nil = context)
      (owner : HeaderOwner field major)
      (answer : HeaderValueAlignment owner domain env registry target ownerLocals locals
        ownerLeft ownerRight left ownerAvailable available (input : Profile n))
      (arguments : Related env U registry target (owner.expression.subst ownerLeft)
        (owner.expression.subst ownerRight) (A.subst left) input answer.value.support)
      (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
      HeaderRichTail header field major env registry target (.cons context domain) (Locals.push locals)
        (left.cons (owner.expression.subst ownerLeft)) (right.cons (owner.expression.subst ownerRight))
        (available.push needs)

/-- The finite syntactic ledger is exactly the one bounded by
`headerCaptureEnvironment_bound`; no fabricated numeric bound is stored. -/
def HeaderRichTail.steps
    (tail : HeaderRichTail header field major env registry target context locals left right available) :
    List (HeaderCaptureStep header field major) :=
  match tail with
  | .nil => []
  | .skip tail domain location .. =>
      ⟨⟨_, _, _, .ref domain, location⟩, none⟩ :: tail.steps
  | .push tail domain location _ owner .. =>
      ⟨⟨_, _, _, .ref domain, location⟩, some owner⟩ :: tail.steps

def HeaderRichTail.environment
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (initial : List Closure) : List Closure := headerCaptureEnvironment tail.steps initial

/-- The actual left target tuple, including unused raw slots, in source
argument order. It is computed by the same pushes as the typed tail. -/
def HeaderRichTail.arguments
    (tail : HeaderRichTail header field major env registry target context locals left right available) :
    List VExpr :=
  match tail with
  | .nil => []
  | .skip (leftValue := value) tail .. => tail.arguments ++ [value]
  | .push (ownerLeft := ownerLeft) tail _ _ _ owner .. =>
      tail.arguments ++ [owner.expression.subst ownerLeft]

/-- Construct the actual next header tail and raw substitution. Raw typing
of the owner is derived from its retained original node in its OWN source
environment; no source typing at the declared domain is requested. -/
theorem HeaderRichTail.pushAligned
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    (henv : env.Ordered) (headerBelow : headerEnv ≤ env) (sourceBelow : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation headerEnv U headerSource}
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (substitutions : Ctx.SubstEq env U target left right headerSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (location : Located header (.ref domain))
    (lineage : location.contextDerivation .nil = context)
    (owner : HeaderOwner field major)
    (ownerSubstitutions : Ctx.SubstEq env U target ownerLeft ownerRight owner.source)
    (answer : HeaderValueAlignment owner domain env registry target ownerLocals locals
      ownerLeft ownerRight left ownerAvailable available (input : Profile n))
    (needs : List Need) (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    Nonempty (HeaderRichTail header field major env registry target (.cons context domain) (Locals.push locals)
      (left.cons (owner.expression.subst ownerLeft)) (right.cons (owner.expression.subst ownerRight))
      (available.push needs)) ∧
    Ctx.SubstEq env U target (left.cons (owner.expression.subst ownerLeft))
      (right.cons (owner.expression.subst ownerRight)) (A :: headerSource) := by
  have raw := (owner.node.sound.defeq.mono sourceBelow).substDF henv ownerSubstitutions.wf
    formed ownerSubstitutions
  exact ⟨⟨.push tail domain location lineage owner answer (answer.related henv) needs bounded covered⟩,
    .cons substitutions (domain.sound.defeq.mono headerBelow) (answer.path.cast raw)⟩

/-- Unqueried captures need only actual TARGET typing. No original
projection occurrence or source certificate is invented for an empty slot. -/
theorem HeaderRichTail.skipRaw
    {context : ContextDerivation headerEnv U headerSource}
    (headerBelow : headerEnv ≤ env)
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (substitutions : Ctx.SubstEq env U target left right headerSource)
    (domain : EndpointRef headerEnv U headerSource A (.sort level))
    (location : Located header (.ref domain))
    (lineage : location.contextDerivation .nil = context)
    (arguments : env.IsDefEq U target leftValue rightValue (A.subst left)) :
    Nonempty (HeaderRichTail header field major env registry target (.cons context domain) (Locals.push locals)
      (left.cons leftValue) (right.cons rightValue) (available.push [])) ∧
    Ctx.SubstEq env U target (left.cons leftValue) (right.cons rightValue) (A :: headerSource) :=
  ⟨⟨.skip tail domain location lineage arguments⟩,
    .cons substitutions (domain.sound.defeq.mono headerBelow) arguments⟩

noncomputable def RichCert.lower {N : Nat} {profile : Profile N}
    (certificate : RichCert sourceEnv env U registry target node locals realization expressionFlag profile footprint)
    (n : Nat) (bound : n ≤ N) :
    RichCert sourceEnv env U registry target node locals realization expressionFlag
      (lowerProfile n bound profile) footprint := by
  induction N with
  | zero =>
    have equal : n = 0 := by omega
    subst n
    exact certificate
  | succ N ih =>
    by_cases equal : n = N + 1
    · subst n
      simpa only [lowerProfile_self] using certificate
    · have lower : n ≤ N := by omega
      rw [lowerProfile_step lower]
      exact ih certificate.down lower

structure HeaderRichEntry
    {header : EndpointRef headerEnv U [] headerExpression headerType}
    {field : EndpointRef sourceEnv U source fieldExpression fieldType}
    {major : EndpointRef sourceEnv U source majorExpression majorType}
    {context : ContextDerivation headerEnv U headerSource}
    (tail : HeaderRichTail header field major env registry target context locals left right available)
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
  tailFits : HeaderRichTail header field major env registry target tailContext
    tailLocals tailLeft tailRight tailAvailable
  level : VLevel
  originalDomain : EndpointRef headerEnv U tailSource domain (.sort level)
  headerLocation : Located header (.ref originalDomain)
  headerLineage : headerLocation.contextDerivation .nil = tailContext
  originalLocation : ContextDerivation.Location context tailContext originalDomain
  originalFront_eq : originalLocation.prefix = front
  owner : HeaderOwner field major
  ownerMember : (⟨⟨_, _, _, .ref originalDomain, headerLocation⟩, some owner⟩ :
    HeaderCaptureStep header field major) ∈ tail.steps
  captureTail : ∃ before, tail.steps = before ++
    (⟨⟨_, _, _, .ref originalDomain, headerLocation⟩, some owner⟩ : HeaderCaptureStep header field major) :: tailFits.steps
  captureMember : ∀ initial, Closure.bundle (owner.closure initial)
    (.close originalDomain.origin (tailFits.environment initial)) ∈ tail.environment initial
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

/-- Lookup never changes the rich code's source environment or proof
occurrence. It returns the original declaration-tail certificate and its
actual suffix, together with the exact paired owner/domain ledger member. -/
theorem HeaderRichTail.lookup
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    {context : ContextDerivation headerEnv U headerSource}
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (member : need ∈ available index) (lookup : Lookup headerSource index sourceType) :
    Nonempty (HeaderRichEntry tail index need sourceType) := by
  induction tail generalizing index sourceType with
  | nil => cases lookup
  | @skip headerSource locals left right available A level leftValue rightValue
      context tail domain location lineage arguments ih =>
    cases lookup with
    | zero => cases member
    | succ lookup =>
      obtain ⟨entry⟩ := ih member lookup
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
        resources := answer.aligned.resources, typed := ht, related := ?_ }⟩
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

theorem HeaderRichTail.steps_length
    {context : ContextDerivation headerEnv U headerSource}
    (tail : HeaderRichTail header field major env registry target context locals left right available) :
    tail.steps.length = headerSource.length := by
  induction tail with
  | nil => rfl
  | push tail domain location lineage owner answer arguments needs bounded covered ih =>
    simpa only [steps, List.length_cons] using congrArg (· + 1) ih
  | skip tail domain location lineage arguments ih =>
    simpa only [steps, List.length_cons] using congrArg (· + 1) ih

theorem HeaderRichTail.arguments_length
    {context : ContextDerivation headerEnv U headerSource}
    (tail : HeaderRichTail header field major env registry target context locals left right available) :
    tail.arguments.length = tail.steps.length := by
  induction tail with
  | nil => rfl
  | push tail domain location lineage owner answer arguments needs bounded covered ih =>
    simpa only [HeaderRichTail.arguments, steps, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add] using congrArg (· + 1) ih
  | skip tail domain location lineage arguments ih =>
    simpa only [HeaderRichTail.arguments, steps, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add] using congrArg (· + 1) ih

theorem HeaderRichTail.environment_bound
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (initial : List Closure) :
    1 + environmentCost (tail.environment initial) ≤
      headerCaptureReserve header.origin.weight field.origin.weight major.origin.weight tail.steps.length *
        (1 + environmentCost initial) :=
  headerCaptureEnvironment_bound tail.steps initial

/-- Reindexing an actual stored value to its declared domain fits below
lookup in the WHOLE captured header environment, at every slot. -/
theorem HeaderRichEntry.reindex_schedule
    {tail : HeaderRichTail header field major env registry target context locals left right available}
    (entry : HeaderRichEntry tail index need sourceType)
    (initial : List Closure) (lookupOrigin : Origin) :
    schedule .coherence
      ((Closure.close entry.owner.node.typeFormation.node.origin
          (entry.owner.environment initial)).cost +
        (Closure.close entry.originalDomain.origin (entry.tailFits.environment initial)).cost) <
    schedule .fundamental (Closure.close lookupOrigin (tail.environment initial)).cost := by
  apply schedule_strict
  have bound := Nat.add_le_add_right
    (entry.owner.node.typeFormation_cost_le (entry.owner.environment initial))
    (Closure.close entry.originalDomain.origin (entry.tailFits.environment initial)).cost
  rw [← entry.owner.closure_eq initial] at bound
  exact Nat.lt_of_le_of_lt bound (variable_lookup lookupOrigin (entry.captureMember initial))

/-- The actual typed stack supplies the finite capture ledger and count;
no independent numeric bound or capture list is requested. -/
theorem HeaderRichTail.reindex_schedule
    {context : ContextDerivation headerEnv U headerSource}
    (tail : HeaderRichTail header field major env registry target context locals left right available)
    (selectedHeader : LocatedOrigin header) (selectedField : LocatedOrigin field)
    (initial : List Closure) :
    schedule .coherence
      ((selectedField.closure initial).cost +
        (Closure.close selectedHeader.node.origin (tail.environment initial)).cost) <
    schedule .fundamental
      ((1 + field.origin.weight + major.origin.weight + header.origin.weight *
        headerCaptureReserve header.origin.weight field.origin.weight major.origin.weight
          headerSource.length) * (1 + environmentCost initial)) := by
  simpa only [← tail.steps_length, environment] using
    header_reindex_strict_reserve tail.steps selectedHeader selectedField initial

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
