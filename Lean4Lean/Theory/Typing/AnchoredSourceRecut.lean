import Lean4Lean.Theory.Typing.AnchoredAdaptedSourceSubstitution
import Lean4Lean.Theory.Typing.AnchoredLiveInterpretation

/-! Finite re-cutting after descendant head interpretation.

A cut slot denotes one raw head instance, without quotienting its level syntax.
The payload is the original returned observer (or its native-tree counterpart),
not an operation which can answer new observer requests.  Reconstruction uses
fresh raw demands at the same slots.  The existing graded substitution theorem
then retains an explicit finite ledger of whole or literal-singleton demands.
No returned observer is recursively interpreted as a new native descendant. -/

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

namespace Recut

/-- The finite evidence returned by interpreting one original descendant. -/
structure Entry (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (realization : Subst) (Payload : Nat → Need → Type)
    (index : Nat) where
  need : Need
  payload : Payload index need
  type : VExpr
  support : Profile need.rank
  typed : need.profile.HasType support
  code : TypeRelated env U registry Γ type type support
  related : Related env U registry Γ (realization index) (realization index)
    type need.profile support

/-- One descendant result answers its original finite demand, possibly at a
larger grade. The entry retains its actual raw demand and evidence. -/
structure Answer (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (realization : Subst) (Payload : Nat → Need → Type)
    (index : Nat) (requested : Need) where
  entry : Entry env U registry Γ realization Payload index
  bound : requested.rank ≤ entry.need.rank
  adapter : NormalProfileAdapter env U registry Γ entry.need.profile
    (raiseProfile entry.need.rank bound requested.profile)

inductive Answers (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (realization : Subst) (Payload : Nat → Need → Type) :
    Footprint → Type where
  | nil : Answers env U registry Γ realization Payload []
  | cons (answer : Answer env U registry Γ realization Payload index need)
      (tail : Answers env U registry Γ realization Payload rest) :
      Answers env U registry Γ realization Payload ((index, need) :: rest)

abbrev Ledger (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (realization : Subst) (Payload : Nat → Need → Type) :=
  List ((index : Nat) × Entry env U registry Γ realization Payload index)

def Answers.ledger : Answers env U registry Γ realization Payload required →
    Ledger env U registry Γ realization Payload
  | .nil => []
  | .cons answer tail => ⟨_, answer.entry⟩ :: tail.ledger

def Ledger.footprint (ledger : Ledger env U registry Γ realization Payload) : Footprint :=
  ledger.map fun entry => (entry.1, entry.2.need)

def valuation (footprint : Footprint) : Valuation :=
  fun index => footprint.filterMap fun entry =>
    if entry.1 = index then some entry.2 else none

theorem mem_valuation {footprint : Footprint} :
    need ∈ valuation footprint index ↔ (index, need) ∈ footprint := by
  simp only [valuation, List.mem_filterMap]
  constructor
  · rintro ⟨⟨i, n⟩, member, result⟩
    split at result
    · cases Option.some.inj result
      rename_i hindex
      change i = index at hindex
      subst i
      exact member
    · cases result
  · intro member
    exact ⟨(index, need), member, by simp⟩

def Ledger.available (ledger : Ledger env U registry Γ realization Payload) : Valuation :=
  Valuation.atomize (valuation ledger.footprint)

theorem Ledger.closed (ledger : Ledger env U registry Γ realization Payload) :
    ledger.available.AtomClosed := Valuation.atomize_closed _

/-- Every new demand is either the actual raw demand of a stored descendant
result or one literal atom thereof. No profile-refinement premise occurs. -/
inductive Selects {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {realization : Subst} {Payload : Nat → Need → Type}
    {index : Nat} (entry : Entry env U registry Γ realization Payload index) : Need → Type where
  | whole : Selects entry entry.need
  | atom (atom : Atom entry.need.rank) (member : atom ∈ entry.need.profile.atoms) :
      Selects entry ⟨entry.need.rank, .singleton atom⟩

def Selects.support
    {entry : Entry env U registry Γ realization Payload index}
    (selection : Selects entry need) : Profile need.rank := by
  cases selection
  · exact entry.support
  · exact entry.support

theorem Selects.typed
    {entry : Entry env U registry Γ realization Payload index}
    (selection : Selects entry need) : need.profile.HasType selection.support := by
  cases selection with
  | whole => exact entry.typed
  | atom atom member => exact entry.typed.singleton_of_mem member

theorem Selects.code
    {entry : Entry env U registry Γ realization Payload index}
    (selection : Selects entry need) :
    TypeRelated env U registry Γ entry.type entry.type selection.support := by
  cases selection <;> exact entry.code

theorem Selects.related
    {entry : Entry env U registry Γ realization Payload index}
    (selection : Selects entry need) :
    Related env U registry Γ (realization index) (realization index)
      entry.type need.profile selection.support := by
  cases selection with
  | whole => exact entry.related
  | atom atom member => exact entry.related.singleton_of_mem member

/-- A returned leaf names a concrete original ledger entry and a concrete
literal selection. Its semantic evidence is derived above, not requested. -/
structure Origin (ledger : Ledger env U registry Γ realization Payload)
    (index : Nat) (need : Need) where
  entry : Entry env U registry Γ realization Payload index
  member : Sigma.mk index entry ∈ ledger
  selection : Selects entry need

theorem Ledger.origin (ledger : Ledger env U registry Γ realization Payload)
    (member : need ∈ ledger.available index) : Nonempty (Origin ledger index need) := by
  rcases List.mem_append.mp member with whole | atom
  · obtain ⟨⟨i, entry⟩, original, he⟩ := List.mem_map.mp (mem_valuation.mp whole)
    cases Prod.mk.inj he with
    | intro hi hn =>
      change i = index at hi
      subst i
      cases hn
      exact ⟨⟨entry, original, .whole⟩⟩
  · obtain ⟨old, hold, hselected⟩ := List.mem_flatMap.mp atom
    obtain ⟨⟨i, entry⟩, original, he⟩ := List.mem_map.mp (mem_valuation.mp hold)
    cases Prod.mk.inj he with
    | intro hi hn =>
      change i = index at hi
      subst i
      cases hn
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hselected
      cases he
      exact ⟨⟨entry, original, .atom a ha⟩⟩

/-- Explicit finite return ledger, with one origin for each resulting source
leaf occurrence. Duplicates remain separate occurrences. -/
inductive ReturnLedger (ledger : Ledger env U registry Γ realization Payload) : Footprint → Type where
  | nil : ReturnLedger ledger []
  | cons (origin : Origin ledger index need) (tail : ReturnLedger ledger rest) :
      ReturnLedger ledger ((index, need) :: rest)

theorem ReturnLedger.of_available
    {ledger : Ledger env U registry Γ realization Payload}
    (resources : footprint.Available ledger.available) : Nonempty (ReturnLedger ledger footprint) := by
  induction footprint with
  | nil => exact ⟨.nil⟩
  | cons entry rest ih =>
    obtain ⟨origin⟩ := ledger.origin (resources entry.1 entry.2 (by simp))
    obtain ⟨tail⟩ := ih (fun index need member => resources index need (by simp [member]))
    exact ⟨.cons origin tail⟩

private theorem Answers.supply
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (answers : Answers env U registry Γ realization Payload required)
    (locals : List Nat) (available : Valuation)
    (included : ∀ entry ∈ answers.ledger,
      entry.2.need ∈ available entry.1) :
    Nonempty (GradedSupply env U registry Γ locals realization .id available required) := by
  induction answers with
  | nil => exact ⟨.nil⟩
  | @cons index need rest answer tail ih =>
    have value : GradedResult env U registry Γ locals realization available (.bvar index)
        need.profile := {
      rank := answer.entry.need.rank
      bound := answer.bound
      raw := answer.entry.need.profile
      footprint := [(index, answer.entry.need)]
      observation := .var locals realization index answer.entry.need.profile
      adapter := answer.adapter
      resources := by
        intro i n member
        obtain he := List.mem_singleton.mp member
        cases he
        exact included ⟨index, answer.entry⟩ (by simp [Answers.ledger])
      live := answer.entry.related.live henv hscoped hΓ }
    obtain ⟨tailSupply⟩ := ih (fun entry member => included entry (by
      simp only [Answers.ledger, List.mem_cons]
      exact Or.inr member))
    exact ⟨.cons value tailSupply⟩

/-- The re-cut result is an actual observer reconstructed by the checked
core substitution algorithm. Its ledger is finite and every returned leaf is
interpretable from one of the original raw descendant results. -/
structure Result (ledger : Ledger env U registry Γ realization Payload)
    (locals : List Nat) (expression : VExpr) (requested : Profile n) where
  value : GradedResult env U registry Γ locals realization ledger.available expression requested
  origins : ReturnLedger ledger value.footprint

theorem reify
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {realization : Subst} {Payload : Nat → Need → Type}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {expression : VExpr} {requested : Profile n} {required : Footprint}
    (observation : Obs env U registry Γ locals realization expression requested required)
    (answers : Answers env U registry Γ realization Payload required) :
    Nonempty (Result answers.ledger locals expression requested) := by
  obtain ⟨supply⟩ := answers.supply henv hscoped hΓ locals answers.ledger.available (by
    intro entry member
    apply Valuation.mem_atomize
    apply mem_valuation.mpr
    exact List.mem_map.mpr ⟨entry, member, rfl⟩)
  obtain ⟨result⟩ := observation.substitute henv hscoped hΓ .id realization
    (by rfl) locals answers.ledger.available answers.ledger.closed supply
  rw [subst_id] at result
  obtain ⟨origins⟩ := ReturnLedger.of_available result.resources
  exact ⟨⟨result, origins⟩⟩

/-- Native domain guards and returned type certificates use the same finite
ledger. Their demanded code profile is preserved exactly by reconstruction. -/
structure CodeResult (ledger : Ledger env U registry Γ realization Payload)
    (locals : List Nat) (expression : VExpr) (requested : Profile n) where
  footprint : Footprint
  certificate : CodeCert env U registry Γ locals realization expression requested footprint
  origins : ReturnLedger ledger footprint
  resources : footprint.Available ledger.available

theorem reifyCode
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {realization : Subst} {Payload : Nat → Need → Type}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    {locals : List Nat} {expression : VExpr} {requested : Profile n} {required : Footprint}
    (certificate : CodeCert env U registry Γ locals realization expression requested required)
    (answers : Answers env U registry Γ realization Payload required) :
    Nonempty (CodeResult answers.ledger locals expression requested) := by
  obtain ⟨supply⟩ := answers.supply henv hscoped hΓ locals answers.ledger.available (by
    intro entry member
    apply Valuation.mem_atomize
    apply mem_valuation.mpr
    exact List.mem_map.mpr ⟨entry, member, rfl⟩)
  obtain ⟨result⟩ := certificate.substitute henv hscoped hΓ .id realization
    (by rfl) locals answers.ledger.available answers.ledger.closed supply
  rw [subst_id] at result
  obtain ⟨origins⟩ := ReturnLedger.of_available result.resources
  exact ⟨⟨result.footprint, result.certificate, origins, result.resources⟩⟩

end Recut
end Lean4Lean.AnchoredSource.Adapted
