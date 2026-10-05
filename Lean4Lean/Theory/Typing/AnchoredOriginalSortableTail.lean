import Lean4Lean.Theory.Typing.AnchoredSortableAdapter
import Lean4Lean.Theory.Typing.AnchoredOriginalTailFundamental

/-! Exact original source tails with hereditary sortable domain certificates.
There is no coercion from these frames to legacy Fits. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalTail
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

noncomputable def _root_.Lean4Lean.AnchoredSource.Adapted.SortableCert.lower {N : Nat}
    {profile : Profile N}
    (cert : SortableCert env U registry target locals realization expression relevant profile footprint)
    (n : Nat) (bound : n ≤ N) :
    SortableCert env U registry target locals realization expression relevant (lowerProfile n bound profile) footprint := by
  induction N with
  | zero =>
    have he : n = 0 := by omega
    subst n
    exact cert
  | succ N ih =>
    by_cases he : n = N + 1
    · subst n; simpa only [lowerProfile_self] using cert
    · have hn : n ≤ N := by omega
      rw [lowerProfile_step hn]
      exact ih cert.down hn


/-- A finite record of actual binder extensions.  The semantic data are the
same data consumed by Fits.push; the extra original formation is finite
source proof data, not a semantic producer. -/
inductive SortableTailFits (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) :
    List VExpr → List Nat → Subst → Subst → Valuation → Type where
  | nil : SortableTailFits sourceEnv env U registry target [] locals left right available
  | push
      {source : List VExpr} {locals : List Nat} {left right : Subst} {available : Valuation}
      {A : VExpr} {level : VLevel} {N : Nat} {support input : Profile N}
      {footprint : Footprint} {x y : VExpr}
      (tail : SortableTailFits sourceEnv env U registry target source locals left right available)
      (originalDomain : EndpointRef sourceEnv U source A (.sort level))
      (domain : SortableCert env U registry target locals left A true support footprint)
      (domainAvailable : footprint.Available available)
      (typed : input.HasType support)
      (arguments : Related env U registry target x y (A.subst left) input support)
      (localNeeds : List Need)
      (bounded : ∀ need ∈ localNeeds, need.rank ≤ N)
      (covered : ∀ need ∈ localNeeds, ∀ atom ∈ (need.atGrade N).atoms,
        atom ∈ (input : Profile N).atoms) :
      SortableTailFits sourceEnv env U registry target (A :: source) (Locals.push locals)
        (left.cons x) (right.cons y) (Valuation.push localNeeds available)

def SortableTailFits.contextDerivation
    (tailFits : SortableTailFits sourceEnv env U registry target source locals left right available) :
    ContextDerivation sourceEnv U source :=
  match tailFits with
  | .nil => .nil
  | .push tail originalDomain .. => .cons tail.contextDerivation originalDomain

/-- Lookup returns the exact earlier source context and certificate.  Its
footprint is interpreted in `tailAvailable`, and `tailFits` is the actual
stored finite suffix, not an assumed universal tail supplier. -/
structure SortableEntry (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
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
  tailFits : SortableTailFits sourceEnv env U registry target tailSource tailLocals tailLeft tailRight tailAvailable
  level : VLevel
  originalDomain : EndpointRef sourceEnv U tailSource domain (.sort level)
  originalLocation : ContextDerivation.Location context tailFits.contextDerivation originalDomain
  originalFront_eq : originalLocation.prefix = front
  left_eq : Subst.lift_l (.skipN .refl (index + 1)) left = tailLeft
  right_eq : Subst.lift_l (.skipN .refl (index + 1)) right = tailRight
  available_eq : ∀ i, tailAvailable i = available (i + (index + 1))
  support : Profile need.rank
  footprint : Footprint
  certificate : SortableCert env U registry target tailLocals tailLeft domain true support footprint
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
theorem SortableTailFits.lookup
    (henv : env.Ordered) (hTarget : OnCtx target (env.IsType U))
    (tailFits : SortableTailFits sourceEnv env U registry target source locals left right available)
    (member : need ∈ available index) (lookup : Lookup source index sourceType) :
    Nonempty (SortableEntry sourceEnv env U registry source target locals left right available index need sourceType
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


def SortableTailFits.reorigin
    (fits : SortableTailFits sourceEnv env U registry target source locals left right available)
    (desired : ContextDerivation sourceEnv U source) :
    SortableTailFits sourceEnv env U registry target source locals left right available :=
  match fits, desired with
  | .nil, .nil => .nil
  | .push tail _ domain resources typed arguments needs bounded covered, .cons rest originalDomain =>
      .push (tail.reorigin rest) originalDomain domain resources typed arguments needs bounded covered

theorem SortableTailFits.reorigin_contextDerivation
    (fits : SortableTailFits sourceEnv env U registry target source locals left right available)
    (desired : ContextDerivation sourceEnv U source) :
    (fits.reorigin desired).contextDerivation = desired := by
  induction fits with
  | nil => cases desired; rfl
  | push tail originalDomain domain resources typed arguments needs bounded covered ih =>
    cases desired with
    | cons rest formation =>
      change ContextDerivation.cons ((tail.reorigin rest).contextDerivation) formation = _
      rw [ih rest]

structure SortableTailPairedFits (env : VEnv) (registry : CanonicalHead.Registry)
    (target : List VExpr) {sourceEnv : VEnv} {U : Nat} {source : List VExpr}
    (context : ContextDerivation sourceEnv U source)
    (locals : List Nat) (left right : Subst) (available : Valuation) where
  forward : SortableTailFits sourceEnv env U registry target source locals left right available
  backward : SortableTailFits sourceEnv env U registry target source locals right left available
  forwardContext : forward.contextDerivation = context
  backwardContext : backward.contextDerivation = context

variable {sourceEnv env : VEnv} {U : Nat} {source target : List VExpr}

noncomputable def SortableTailFits.left
    (tail : SortableTailFits sourceEnv env U registry target source locals σ τ available) :
    SortableTailFits sourceEnv env U registry target source locals σ σ available := by
  induction tail with
  | nil => exact .nil
  | push rest original domain resources typed arguments needs bounded covered ih =>
    exact .push ih original domain resources typed arguments.left_diagonal needs bounded covered

@[simp] theorem SortableTailFits.contextDerivation_left
    (tail : SortableTailFits sourceEnv env U registry target source locals σ τ available) :
    tail.left.contextDerivation = tail.contextDerivation := by
  induction tail with
  | nil => rfl
  | push rest original domain resources typed arguments needs bounded covered ih =>
    exact congrArg (fun context => ContextDerivation.cons context original) ih

variable {context : ContextDerivation sourceEnv U source}

def SortableTailPairedFits.diagonal
    (context : ContextDerivation sourceEnv U source)
    (tail : SortableTailFits sourceEnv env U registry target source locals σ σ available) :
    SortableTailPairedFits env registry target context locals σ σ available :=
  ⟨tail.reorigin context, tail.reorigin context,
    tail.reorigin_contextDerivation context, tail.reorigin_contextDerivation context⟩

def SortableTailPairedFits.symm
    (frame : SortableTailPairedFits env registry target context locals σ τ available) :
    SortableTailPairedFits env registry target context locals τ σ available :=
  ⟨frame.backward, frame.forward, frame.backwardContext, frame.forwardContext⟩

noncomputable def SortableTailPairedFits.left
    (frame : SortableTailPairedFits env registry target context locals σ τ available) :
    SortableTailPairedFits env registry target context locals σ σ available :=
  ⟨frame.forward.left, frame.forward.left,
    frame.forward.contextDerivation_left.trans frame.forwardContext,
    frame.forward.contextDerivation_left.trans frame.forwardContext⟩

noncomputable def SortableTailPairedFits.right
    (frame : SortableTailPairedFits env registry target context locals σ τ available) :
    SortableTailPairedFits env registry target context locals τ τ available := frame.symm.left

/-- The new head is charged to the actual original domain formation on both
sides; source certificates remain in the earlier tail where they were built. -/
def SortableTailPairedFits.pushCertificates
    {n : Nat} {input leftSupport rightSupport : Profile n}
    (frame : SortableTailPairedFits env registry target context locals σ τ available)
    (originalDomain : EndpointRef sourceEnv U source A (.sort level))
    (leftDomain : SortableCert env U registry target locals σ A true leftSupport leftFootprint)
    (rightDomain : SortableCert env U registry target locals τ A true rightSupport rightFootprint)
    (leftResources : leftFootprint.Available available)
    (rightResources : rightFootprint.Available available)
    (leftTyped : (input : Profile n).HasType leftSupport)
    (rightTyped : input.HasType rightSupport)
    (forward : Related env U registry target x y (A.subst σ) input leftSupport)
    (backward : Related env U registry target y x (A.subst τ) input rightSupport)
    (needs : List Need)
    (bounded : ∀ need ∈ needs, need.rank ≤ n)
    (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ input.atoms) :
    SortableTailPairedFits env registry target (.cons context originalDomain) (Locals.push locals)
      (σ.cons x) (τ.cons y) (Valuation.push needs available) :=
  { forward := frame.forward.push originalDomain leftDomain leftResources leftTyped
      forward needs bounded covered
    backward := frame.backward.push originalDomain rightDomain rightResources rightTyped
      backward needs bounded covered
    forwardContext := congrArg (fun tail => ContextDerivation.cons tail originalDomain) frame.forwardContext
    backwardContext := congrArg (fun tail => ContextDerivation.cons tail originalDomain) frame.backwardContext }

end Lean4Lean.AnchoredSource.Adapted.OriginalTail
