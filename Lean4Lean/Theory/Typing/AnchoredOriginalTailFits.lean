import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceBinder
import Lean4Lean.Theory.Typing.AnchoredOriginalDerivation

/-! An isolated tail-indexed strengthening of the actual Fits producer.
Each binder retains its domain certificate BEFORE the new source variable
exists, together with the original formation endpoint in that tail.  A
lookup recovers that stored certificate and finite tail environment directly;
it never reflects arbitrary typing metadata out of a full-context entry.

This is an invariant for the CURRENT type-unindexed CodeCert.  A future typed
certificate must also be indexed by this retained original tail formation
(or tail original context).  The footprint bound alone does not restrict
original derivations embedded in a hypothetical enlarged certificate AST. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalTail
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

/-- A finite record of actual binder extensions.  The semantic data are the
same data consumed by Fits.push; the extra original formation is finite
source proof data, not a semantic producer. -/
inductive TailFits (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) :
    List VExpr → List Nat → Subst → Subst → Valuation → Type where
  | nil : TailFits sourceEnv env U registry target [] locals left right available
  | push
      {source : List VExpr} {locals : List Nat} {left right : Subst} {available : Valuation}
      {A : VExpr} {level : VLevel} {N : Nat} {support input : Profile N}
      {footprint : Footprint} {x y : VExpr}
      (tail : TailFits sourceEnv env U registry target source locals left right available)
      (originalDomain : EndpointRef sourceEnv U source A (.sort level))
      (domain : CodeCert env U registry target locals left A support footprint)
      (domainAvailable : footprint.Available available)
      (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst left) input support)
      (localNeeds : List Need)
      (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
      (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms,
        atom ∈ (input : Profile N).atoms) :
      TailFits sourceEnv env U registry target (A :: source) (Locals.push locals)
        (left.cons x) (right.cons y) (Valuation.push localNeeds available)

theorem TailFits.toFits (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (tailFits : TailFits sourceEnv env U registry target source locals left right available) :
    Fits env U registry source target locals left right available := by
  induction tailFits with
  | nil => constructor; intro i need member A lookup; cases lookup
  | push _ _ domain resources typed arguments needs bounded covered ih =>
    exact ih.push henv hTarget domain resources typed arguments needs bounded covered

def TailFits.contextDerivation
    (tailFits : TailFits sourceEnv env U registry target source locals left right available) :
    ContextDerivation sourceEnv U source :=
  match tailFits with
  | .nil => .nil
  | .push tail originalDomain .. => .cons tail.contextDerivation originalDomain

/-- Lookup returns the exact earlier source context and certificate.  Its
footprint is interpreted in `tailAvailable`, and `tailFits` is the actual
stored finite suffix, not an assumed universal tail supplier. -/
structure Entry (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (source target : List VExpr) (locals : List Nat) (left right : Subst)
    (available : Valuation) (index : Nat) (need : Need) (sourceType : VExpr)
    (context : ContextDerivation sourceEnv U source) where
  front : List VExpr
  tailSource : List VExpr
  domain : VExpr
  source_eq : source = front ++ domain :: tailSource
  index_eq : index = front.length
  sourceType_eq : sourceType = domain.liftN (index + 1)
  tailLocals : List Nat
  tailLeft : Subst
  tailRight : Subst
  tailAvailable : Valuation
  tailFits : TailFits sourceEnv env U registry target tailSource tailLocals tailLeft tailRight tailAvailable
  level : VLevel
  originalDomain : EndpointRef sourceEnv U tailSource domain (.sort level)
  originalLocation : ContextDerivation.Location context tailFits.contextDerivation originalDomain
  originalFront_eq : originalLocation.prefix = front
  left_eq : Subst.lift_l (.skipN .refl (index + 1)) left = tailLeft
  right_eq : Subst.lift_l (.skipN .refl (index + 1)) right = tailRight
  available_eq : ∀ i, tailAvailable i = available (i + (index + 1))
  support : Profile need.rank
  footprint : Footprint
  certificate : CodeCert env U registry target tailLocals tailLeft domain support footprint
  resources : footprint.Available tailAvailable
  typed : need.profile.HasType support
  related : Related env U registry target (left index) (right index)
    (sourceType.subst left) need.profile support

private theorem typed_subset {small large support : Profile n}
    (subset : ∀ atom ∈ small.atoms, atom ∈ large.atoms)
    (typed : large.HasType support) : small.HasType support := by
  cases n with
  | zero => exact fun atom hm => typed atom (subset atom hm)
  | succ n => exact ⟨fun atom hm => typed.1 atom (subset atom hm), typed.2.1,
      fun atom hm => typed.2.2 atom (subset atom hm)⟩

/-- Produce a tail certificate by following the finite binder stack.  The
head case lowers the ACTUAL supplied binder certificate; the successor case
keeps the stored certificate, formation and tail stack literally unchanged. -/
theorem TailFits.lookup
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (tailFits : TailFits sourceEnv env U registry target source locals left right available)
    (member : need ∈ available index) (lookup : Lookup source index sourceType) :
    Nonempty (Entry sourceEnv env U registry source target locals left right available index need sourceType
      tailFits.contextDerivation) := by
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
        related := ?_ }⟩
      simpa only [Subst.cons, lift_subst_cons] using hl
    | succ lookup =>
      obtain ⟨entry⟩ := ih member lookup
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
        related := ?_ }⟩
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

/-- Reconstruct the ordinary full-context entry only by SOURCE SHIFT of the
stored tail certificate.  No inverse operation on arbitrary metadata occurs. -/
noncomputable def Entry.toValuationEntry
    (entry : Entry sourceEnv env U registry source target locals left right available index need sourceType context) :
    ValuationEntry env U registry target locals left right available index need sourceType := by
  have shifted := entry.certificate.renameSource (.skipN .refl (index + 1)) left entry.left_eq locals
  refine ⟨entry.support, entry.footprint.sourceLift (.skipN .refl (index + 1)),
    ?_, ?_, entry.typed, entry.related⟩
  · have equal : entry.domain.lift' (.skipN .refl (index + 1)) = sourceType := by
      simpa only [← lift'_consN_skipN, Lift.consN] using entry.sourceType_eq.symm
    exact Eq.mp (congrArg (fun expression => CodeCert env U registry target locals left expression
      entry.support (entry.footprint.sourceLift (.skipN .refl (index + 1)))) equal) shifted
  · intro i needed member
    obtain ⟨⟨j, original⟩, present, equal⟩ := List.mem_map.mp member
    cases equal
    have live := entry.resources _ _ present
    rw [entry.available_eq] at live
    simpa only [Lift.liftVar_skipN, Lift.liftVar, Nat.add_comm] using live

/-- Every resource of a reconstructed lookup certificate lies strictly
after its own source slot.  The retained tail query itself is available in
the stored suffix environment. -/
theorem Entry.footprint_after
    (entry : Entry sourceEnv env U registry source target locals left right available index need sourceType context)
    (member : (slot, requested) ∈ entry.footprint.sourceLift (.skipN .refl (index + 1))) :
    index < slot := by
  obtain ⟨⟨j, original⟩, present, equal⟩ := List.mem_map.mp member
  have h := congrArg Prod.fst equal
  simp only [Lift.liftVar_skipN, Lift.liftVar] at h
  omega

/-- The recovered certificate's formation is the exact selected original
context node, so its COMPLETE tail-captured cost belongs to the root budget. -/
def Entry.lookupOrigin
    (entry : Entry sourceEnv env U registry source target locals left right available index need sourceType context) :
    ContextDerivation.LookupOrigin context index sourceType where
  tailSource := entry.tailSource
  tail := entry.tailFits.contextDerivation
  domain := entry.domain
  level := entry.level
  formation := entry.originalDomain
  location := entry.originalLocation
  index_eq := entry.index_eq.trans (congrArg List.length entry.originalFront_eq.symm)
  type_eq := entry.sourceType_eq

theorem Entry.reindex_schedule
    (entry : Entry sourceEnv env U registry source target locals left right available index need sourceType context)
    (lookup : Lookup source index sourceType)
    (levelWF : occurrenceLevel.WF U)
    (occurrence : Derivation sourceEnv U source sourceType sourceType (.sort occurrenceLevel)) :
    schedule .coherence
      ((Closure.close occurrence.origin context.closures).cost +
        (Closure.close entry.originalDomain.origin entry.tailFits.contextDerivation.closures).cost) <
      schedule .fundamental
        ((Closure.close (Derivation.bvar lookup levelWF occurrence).origin context.closures).cost) :=
  entry.lookupOrigin.reindex_schedule lookup levelWF occurrence

/-- Restriction to the older context simply projects the stored finite
stack.  No source reflection of any stored certificate is involved. -/
def TailFits.tail
    (fits : TailFits sourceEnv env U registry target (A :: source) locals left right available) :
    Σ tailLocals, TailFits sourceEnv env U registry target source tailLocals
      left.tail right.tail (fun index => available (index + 1)) := by
  cases fits with
  | push tail => exact ⟨_, tail⟩

theorem TailFits.suffix
    (fits : TailFits sourceEnv env U registry target (front ++ source) locals left right available) :
    ∃ tailLocals, Nonempty (TailFits sourceEnv env U registry target source tailLocals
      (Subst.lift_l (.skipN .refl front.length) left)
      (Subst.lift_l (.skipN .refl front.length) right)
      (fun index => available (index + front.length))) := by
  induction front generalizing locals left right available with
  | nil => exact ⟨_, ⟨fits⟩⟩
  | cons A front ih =>
    obtain ⟨tailLocals, tailFits⟩ := fits.tail
    obtain ⟨finalLocals, ⟨suffix⟩⟩ := ih tailFits
    have shift (σ : Subst) : Subst.lift_l (.skipN .refl front.length) σ.tail =
        Subst.lift_l (.skipN .refl (front.length + 1)) σ := by
      funext i
      simp [Subst.lift_l, Subst.tail, Lift.liftVar_skipN, Lift.liftVar, Nat.add_assoc]
    exact ⟨finalLocals, ⟨by
      simpa only [List.length_cons, shift, Nat.add_assoc] using suffix⟩⟩

end Lean4Lean.AnchoredSource.Adapted.OriginalTail
