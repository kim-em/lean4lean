import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSyntax
import Lean4Lean.Theory.Typing.AnchoredFamilyArguments
import Lean4Lean.Theory.Typing.AnchoredSourceBinder
import Lean4Lean.Theory.Typing.AnchoredSourceAvailability

/-! Finite declaration rows for primitive projection plans. No semantic
induction hypothesis is stored: the original declaration formation tree is
supplied only when these rows are interpreted. Earlier selectors retain the
same frozen requests and use the selected row's own domain certificate. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The declaration domain is the only source child needed by prefix replay.
The fixed admission support is deliberately separate from this natural domain
support; their concrete domain chain supplies the alignment. -/
structure ProjectionDomainRow (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (seed : Subst) (available : Valuation)
    (domain : VExpr) (key : Key n) where
  support : Profile n
  footprint : Footprint
  certificate : CodeCert env U registry target locals seed domain support footprint
  resources : footprint.Available available
  typed : key.input.HasType support
  alignment : DomainChain env U registry target key.input key.domain (domain.subst seed)

/-- All fields are finite source syntax or finite target guards. In
particular, no original semantic induction hypothesis or Pi-body observer is
stored. The singleton closure records exactly what valuation replay needs. -/
inductive ProjectionRows (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (required : Footprint) :
    List Nat → Subst → Valuation → VExpr → List VExpr → List FamilyKey → Type where
  | nil (resources : required.Available available) :
      ProjectionRows env U registry target required locals seed available expression [] []
  | cons
      (row : ProjectionDomainRow env U registry target locals seed available A (key : Key n))
      {support : Profile n}
      (admission : RankedData.RequestAdmission env U (relations env U registry n) target
        (⟨key, support⟩ : DataRequest (Profile n)) key.anchor key.anchor)
      (needs : List Need)
      (bounded : ∀ need ∈ needs, need.rank ≤ n)
      (covered : ∀ need ∈ needs, ∀ atom ∈ (need.atGrade n).atoms, atom ∈ key.input.atoms)
      (inputPresent : (⟨n, key.input⟩ : Need) ∈ needs)
      (singletons : ∀ need ∈ needs, ∀ selected ∈ need.singletons, selected ∈ needs)
      (tail : ProjectionRows env U registry target required (Locals.push locals)
        (seed.cons key.anchor) (Valuation.push needs available) B domains keys) :
      ProjectionRows env U registry target required locals seed available
        (.forallE A B) (A :: domains) (⟨n, key, support⟩ :: keys)

namespace ProjectionRows

def terminalLocals
    (rows : ProjectionRows env U registry target required locals seed available expression domains keys) :
    List Nat :=
  match rows with
  | .nil _ => locals
  | .cons _ _ _ _ _ _ _ tail => tail.terminalLocals

def terminalValuation
    (rows : ProjectionRows env U registry target required locals seed available expression domains keys) :
    Valuation :=
  match rows with
  | .nil _ => available
  | .cons _ _ _ _ _ _ _ tail => tail.terminalValuation

theorem length
    (rows : ProjectionRows env U registry target required locals seed available expression domains keys) :
    keys.length = domains.length := by
  induction rows with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ ih => exact congrArg Nat.succ ih

def forgetTerminal
    (rows : ProjectionRows env U registry target required locals seed available expression domains keys) :
    ProjectionRows env U registry target [] locals seed available expression domains keys :=
  match rows with
  | .nil _ => .nil (by intro _ _ member; cases member)
  | .cons row admission needs bounded covered inputPresent singletons tail =>
    .cons row admission needs bounded covered inputPresent singletons tail.forgetTerminal

end ProjectionRows

/-- Restricting a plan selects the original key and the original domain
template. The prefix is closed with that domain's own available footprint,
so no requirement from the later selected field is assumed at the earlier one. -/
structure ProjectionRowSlice (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (target : List VExpr) (locals : List Nat) (seed : Subst) (available : Valuation)
    (expression : VExpr) (domains : List VExpr) (keys : List FamilyKey) (position : Nat) where
  rank : Nat
  key : Key rank
  admissionSupport : Profile rank
  selected : keys[position]? = some ⟨rank, key, admissionSupport⟩
  domain : VExpr
  domainAt : domains[position]? = some domain
  support : Profile rank
  footprint : Footprint
  rows : ProjectionRows env U registry target footprint locals seed available expression
    (domains.take position) (keys.take position)
  certificate : CodeCert env U registry target rows.terminalLocals
    (((keys.take position).map (·.key.anchor)).foldl Subst.cons seed) domain support footprint
  typed : key.input.HasType support
  alignment : DomainChain env U registry target key.input key.domain
    (domain.subst (((keys.take position).map (·.key.anchor)).foldl Subst.cons seed))

/-- The earlier-domain plan is obtained by structural restriction. Its key
prefix is literal, allowing one fixed uniform grade and the same rich major
record observation to be reused throughout a field-index induction. -/
theorem ProjectionRows.restrictDomain
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {seed : Subst} {available : Valuation}
    {expression : VExpr} {domains : List VExpr} {keys : List FamilyKey} {required : Footprint}
    (rows : ProjectionRows env U registry target required locals seed available expression domains keys)
    (position : Nat) (bound : position < domains.length) :
    Nonempty (ProjectionRowSlice env U registry target locals seed available expression domains keys position) := by
  induction rows generalizing position with
  | nil => simp at bound
  | cons row admission needs bounded covered inputPresent singletons tail ih =>
    cases position with
    | zero =>
      exact ⟨{
        rank := _, key := _, admissionSupport := _, selected := rfl
        domain := _, domainAt := rfl, support := row.support
        footprint := row.footprint, rows := .nil row.resources
        certificate := row.certificate, typed := row.typed, alignment := row.alignment }⟩
    | succ position =>
      obtain ⟨slice⟩ := ih position (Nat.lt_of_succ_lt_succ bound)
      refine ⟨{
        rank := slice.rank, key := slice.key, admissionSupport := slice.admissionSupport
        selected := slice.selected, domain := slice.domain, domainAt := slice.domainAt
        support := slice.support, footprint := slice.footprint
        rows := .cons row admission needs bounded covered inputPresent singletons slice.rows
        certificate := ?_, typed := slice.typed, alignment := ?_ }⟩
      · simpa only [ProjectionRows.terminalLocals, List.take_succ_cons, List.map_cons,
          List.foldl_cons] using slice.certificate
      · simpa only [List.take_succ_cons, List.map_cons, List.foldl_cons] using slice.alignment

end Lean4Lean.AnchoredSource.Adapted
