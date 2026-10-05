import Lean4Lean.Theory.Typing.AnchoredDomainChainTransport
import Lean4Lean.Theory.Typing.AnchoredAdapterNormalization
import Lean4Lean.Theory.Typing.AnchoredNativeSeededSpine

/-! A record field may keep its value query while changing the concrete
request used by a constructor application. Both requests remain explicit.
The new seed admission fixes its anchor and support; finite domain alignment
transports the old field pair without synthesizing source typing evidence.
-/
namespace Lean4Lean.AnchoredSemantics.RankedData
open VExpr VEnv AnchoredProfiles
set_option backward.isDefEq.respectTransparency false

/-- Adapt the field pair and reattach the new request's actual seed anchor.
Raw domain equality alone is insufficient: every conversion edge retains
its finite semantic support in the supplied domain chain. -/
theorem RequestAdmission.retagField
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {oldRequest newRequest : DataRequest (Profile n)}
    {left right : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (adapter : NormalProfileAdapter env U registry Γ oldRequest.input newRequest.input)
    (alignment : DomainChain env U registry Γ newRequest.input oldRequest.domain newRequest.domain)
    (seed : RequestAdmission env U (relations env U registry n) Γ newRequest left left)
    (old : RequestAdmission env U (relations env U registry n) Γ oldRequest left right) :
    RequestAdmission env U (relations env U registry n) Γ newRequest left right := by
  obtain ⟨_, _, oldSupport, typedBefore, _, codeBefore, _, _⟩ :=
    (alignment.symm henv).admission henv seed.toAdmission
  obtain ⟨anchor, _, typed, formed, code, anchorTerm, _⟩ := seed
  obtain ⟨_, pair, _, _, _, _, pairTerm⟩ := old
  have adapted := adapter.termMap henv hscoped hΓ typedBefore codeBefore pairTerm
  exact ⟨anchor, alignment.path.cast pair, typed, formed, code, anchorTerm,
    alignment.related henv typed code adapted⟩


/-- One concrete old field request for each atom of the new input. Different
atoms may originate from unrelated request tuples; the list is finite and
contains all adapters, alignments and actual pair evidence explicitly. -/
inductive FieldRequestRows (env : VEnv) (U : Nat) (registry : CanonicalHead.Registry)
    (Γ : List VExpr) (left right : VExpr) (newRequest : DataRequest (Profile n)) :
    List (Atom n) → Type where
  | nil : FieldRequestRows env U registry Γ left right newRequest []
  | cons (oldRequest : DataRequest (Profile n))
      (adapter : NormalProfileAdapter env U registry Γ oldRequest.input (.singleton atom))
      (alignment : DomainChain env U registry Γ (.singleton atom)
        oldRequest.domain newRequest.domain)
      (pair : RequestAdmission env U (relations env U registry n) Γ oldRequest left right)
      (tail : FieldRequestRows env U registry Γ left right newRequest atoms) :
      FieldRequestRows env U registry Γ left right newRequest (atom :: atoms)

/-- Restrict a fixed request to one of its actual input atoms. Its domain,
anchor and support stay literal. -/
theorem RequestAdmission.singleton
    {request : DataRequest (Profile n)}
    (admitted : RequestAdmission env U (relations env U registry n) Γ request left right)
    (member : atom ∈ request.input.atoms) :
    RequestAdmission env U (relations env U registry n) Γ
      { request with input := .singleton atom } left right := by
  obtain ⟨anchor, pair, typed, formed, code, first, second⟩ := admitted
  exact ⟨anchor, pair, typed.singleton_of_mem member, formed, code,
    Related.singleton_of_mem first member, Related.singleton_of_mem second member⟩

/-- Select one actual row and attach the new request's exact singleton. -/
theorem FieldRequestRows.memberAdmission
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {newRequest : DataRequest (Profile n)} {left right : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (seed : RequestAdmission env U (relations env U registry n) Γ newRequest left left)
    (rows : FieldRequestRows env U registry Γ left right newRequest atoms)
    (present : atom ∈ atoms) (member : atom ∈ newRequest.input.atoms) :
    RequestAdmission env U (relations env U registry n) Γ
      { newRequest with input := .singleton atom } left right := by
  induction rows with
  | nil => cases present
  | cons oldRequest adapter alignment previous tail ih =>
    rcases List.mem_cons.mp present with equal | later
    · subst atom
      exact RequestAdmission.retagField henv hscoped hΓ adapter alignment
        (RequestAdmission.singleton seed member) previous
    · exact ih later

/-- Coalesce the actual per-atom field rows into the whole constructor input,
including the union of the original seed and all retained type cuts. The raw
pair also handles an empty input, whose row list contains no pair evidence. -/
theorem RequestAdmission.retagFields
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {newRequest : DataRequest (Profile n)} {left right : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (seed : RequestAdmission env U (relations env U registry n) Γ newRequest left left)
    (rows : FieldRequestRows env U registry Γ left right newRequest newRequest.input.atoms)
    (pair : env.IsDefEq U Γ left right newRequest.domain) :
    RequestAdmission env U (relations env U registry n) Γ newRequest left right := by
  have final : Related env U registry Γ left right newRequest.domain newRequest.input newRequest.support := by
    apply Related.of_singletons
    intro atom member
    exact (rows.memberAdmission henv hscoped hΓ seed member member).2.2.2.2.2.2
  obtain ⟨anchor, _, typed, formed, code, first, _⟩ := seed
  exact ⟨anchor, pair, typed, formed, code, first, final⟩

/-- A nonempty input obtains its raw pair from an actual selected row. -/
theorem RequestAdmission.retagNonemptyFields
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {Γ : List VExpr} {newRequest : DataRequest (Profile n)} {left right : VExpr}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (seed : RequestAdmission env U (relations env U registry n) Γ newRequest left left)
    (rows : FieldRequestRows env U registry Γ left right newRequest newRequest.input.atoms)
    (meaningful : newRequest.input.Nonempty) :
    RequestAdmission env U (relations env U registry n) Γ newRequest left right := by
  obtain ⟨atom, member⟩ := List.exists_mem_of_ne_nil _ meaningful
  exact RequestAdmission.retagFields henv hscoped hΓ seed rows
    (rows.memberAdmission henv hscoped hΓ seed member member).2.1

end Lean4Lean.AnchoredSemantics.RankedData

namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

/-- The constructor application's actual finite frame already contains
this seed admission. Producing it needs no second interpretation of the
projected argument and no original argument at a declared header domain. -/
theorem SeededApplicationCodeInput.fieldSeedAdmission
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B a : VExpr} {result : Profile n} {before : Footprint}
    (henv : env.Ordered)
    (frame : SeededApplicationCodeInput env U registry target locals σ available A B a result before) :
    RankedData.RequestAdmission env U (relations env U registry frame.collected.rank) target
      (⟨frame.key, frame.support⟩ : DataRequest (Profile frame.collected.rank))
      (a.subst σ) (a.subst σ) := by
  obtain ⟨anchor, pair, _, _, _, _, anchorTerm, pairTerm⟩ := frame.guard.anchor
  exact ⟨anchor, pair, frame.guard.inputTyped, frame.guard.formed,
    frame.guard.domains.left_diagonal,
    Related.retag henv frame.guard.inputTyped frame.guard.domains.left_diagonal anchorTerm,
    Related.retag henv frame.guard.inputTyped frame.guard.domains.left_diagonal pairTerm⟩

end Lean4Lean.AnchoredSource.Adapted
