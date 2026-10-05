import Lean4Lean.Theory.Typing.AnchoredOriginalEqualityGradedReplay
import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalReplay

/-! Finite query operations on original equality answers. Intrinsic typing
and the actual assigned support are retained while the concrete right query
follows the same adapter. No new original certificate is synthesized. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail

structure OriginalSupportedEqualityResult
    (original : Derivation sourceEnv U source left right assigned)
    (env : VEnv) (registry : CanonicalHead.Registry) (target : List VExpr)
    (locals : List Nat) (σ τ : Subst) (available : Valuation) (profile : Profile n)
    extends OriginalEqualityQueryResult original env registry target locals σ τ available profile where
  typed : profile.HasType support
  typeCode : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) support

namespace OriginalSupportedEqualityResult
variable {original : Derivation sourceEnv U source left right assigned}

def empty : OriginalSupportedEqualityResult original env registry target locals σ τ available (.empty : Profile n) where
  support := .empty
  related := Related.of_singletons (fun _ h => nomatch h)
  rightQuery := .empty
  typed := Profile.HasType.empty Profile.WF.empty
  typeCode := TypeRelated.of_singletons (fun _ h => nomatch h)

noncomputable def pad (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : OriginalSupportedEqualityResult original env registry target locals σ τ available profile) :
    OriginalSupportedEqualityResult original env registry target locals σ τ available profile.pad where
  support := answer.support.pad
  related := answer.related.pad henv
  rightQuery := answer.rightQuery.pad henv hscoped formed
  typed := answer.typed.pad
  typeCode := answer.typeCode.pad henv

def unpad (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (answer : OriginalSupportedEqualityResult original env registry target locals σ τ available profile.pad) :
    OriginalSupportedEqualityResult original env registry target locals σ τ available profile where
  support := answer.support.down
  related := answer.related.unpad henv formed
  rightQuery := answer.rightQuery.unpad
  typed := answer.typed.pad_inv
  typeCode := answer.typeCode.down henv

noncomputable def union (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (left : OriginalSupportedEqualityResult original env registry target locals σ τ available p)
    (right : OriginalSupportedEqualityResult original env registry target locals σ τ available q) :
    OriginalSupportedEqualityResult original env registry target locals σ τ available (p.union q) := by
  have wf := left.typed.wf_type.union right.typed.wf_type
  have lt := left.typed.enlarge (Profile.le_union_left _ _) wf
  have rt := right.typed.enlarge (Profile.le_union_right _ _) wf
  have code : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) (left.support.union right.support) := by
    apply TypeRelated.of_singletons
    intro atom member
    exact (List.mem_append.mp member).elim
      (fun h => left.typeCode.singleton h) (fun h => right.typeCode.singleton h)
  exact {
    support := left.support.union right.support
    related := (Related.retag henv lt code left.related).union (Related.retag henv rt code right.related)
    rightQuery := left.rightQuery.union henv hscoped formed right.rightQuery
    typed := lt.union rt
    typeCode := code }

theorem action (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : OriginalSupportedEqualityResult original env registry target locals σ τ available (.singleton a))
    (action : AtomAction env U registry target a b) :
    Nonempty (OriginalSupportedEqualityResult original env registry target locals σ τ available (.singleton b)) := by
  obtain ⟨query⟩ := answer.rightQuery.action henv hscoped formed action
  exact ⟨{
    support := action.support.apply answer.support
    related := action.termMap henv hscoped formed answer.typed answer.related
    rightQuery := query
    typed := action.typed answer.typed
    typeCode := action.support.codeMap henv hscoped answer.typeCode }⟩

theorem codeAdapter (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : OriginalSupportedEqualityResult original env registry target locals σ τ available profile)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (sorted : profile.HasType (.sort relevant)) :
    Nonempty (OriginalSupportedEqualityResult original env registry target locals σ τ available output) := by
  exact ⟨{
    support := answer.support.flatSortsAt _
    related := action.termMap henv hscoped formed sorted answer.typed answer.typeCode answer.related
    rightQuery := answer.rightQuery.codeAdapter henv hscoped formed action sorted
    typed := action.typedAtSorts (sorted.flatSorts answer.typed)
    typeCode := answer.typeCode.flatSortsAt henv }⟩

noncomputable def restrict
    (answer : OriginalSupportedEqualityResult original env registry target locals σ τ available (input : Profile n))
    (included : ∀ atom ∈ (requested : Profile n).atoms, atom ∈ input.atoms) :
    OriginalSupportedEqualityResult original env registry target locals σ τ available requested where
  support := answer.support
  related := Related.of_singletons (fun atom member => answer.related.singleton_of_mem (included atom member))
  rightQuery := answer.rightQuery.restrict included
  typed := typed_subset included answer.typed
  typeCode := answer.typeCode

end OriginalSupportedEqualityResult
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
