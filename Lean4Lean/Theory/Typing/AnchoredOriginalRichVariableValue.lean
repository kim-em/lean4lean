import Lean4Lean.Theory.Typing.AnchoredOriginalRichTail
import Lean4Lean.Theory.Typing.AnchoredOriginalRichFlatSorts
import Lean4Lean.Theory.Typing.AnchoredSortableCodeActionInterpretation
import Lean4Lean.Theory.Typing.AnchoredAtomActionInterpretation

namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false

structure RichSupportedValue
    (sourceEnv env : VEnv) (U : Nat) (registry : CanonicalHead.Registry) (target : List VExpr)
    {source : List VExpr} {value assigned : VExpr}
    (owner : EndpointState sourceEnv U source value assigned)
    (locals : List Nat) (σ τ : Subst) (available : Valuation) (input : Profile n)
    extends RichBinderValue sourceEnv env U registry target owner locals σ τ available input where
  typeCode : TypeRelated env U registry target (assigned.subst σ) (assigned.subst σ) support

namespace RichSupportedValue

def empty : RichSupportedValue sourceEnv env U registry target owner locals σ τ available (.empty : Profile n) where
  support := .empty
  footprint := []
  certificate := .legacy (.seed .empty (Profile.HasType.empty (Profile.WF.sort true)))
  resources := fun _ _ h => nomatch h
  typed := Profile.HasType.empty (Profile.WF.empty)
  related := Related.of_singletons (fun _ h => nomatch h)
  typeCode := TypeRelated.of_singletons (fun _ h => nomatch h)

def pad (henv : env.Ordered)
    (result : RichSupportedValue sourceEnv env U registry target owner locals σ τ available profile) :
    RichSupportedValue sourceEnv env U registry target owner locals σ τ available profile.pad where
  support := result.support.pad
  footprint := result.footprint
  certificate := .pad result.certificate
  resources := result.resources
  typed := result.typed.pad
  related := result.related.pad henv
  typeCode := result.typeCode.pad henv

def unpad (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (result : RichSupportedValue sourceEnv env U registry target owner locals σ τ available profile.pad) :
    RichSupportedValue sourceEnv env U registry target owner locals σ τ available profile where
  support := result.support.down
  footprint := result.footprint
  certificate := .down result.certificate
  resources := result.resources
  typed := result.typed.pad_inv
  related := result.related.unpad henv formed
  typeCode := result.typeCode.down henv

noncomputable def action (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichSupportedValue sourceEnv env U registry target owner locals σ τ available (.singleton a))
    (action : AtomAction env U registry target a b) :
    RichSupportedValue sourceEnv env U registry target owner locals σ τ available (.singleton b) where
  support := action.support.apply result.support
  footprint := result.footprint
  certificate := .support action.support result.certificate
  resources := result.resources
  typed := action.typed result.typed
  related := action.termMap henv hscoped formed result.typed result.related
  typeCode := action.support.codeMap henv hscoped result.typeCode

theorem code (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (result : RichSupportedValue sourceEnv env U registry target owner locals σ τ available profile)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (sorted : profile.HasType (.sort relevant)) :
    Nonempty (RichSupportedValue sourceEnv env U registry target owner locals σ τ available output) := by
  obtain ⟨_, ⟨certificate⟩, resources⟩ := result.certificate.flatSortsAt (m := _) result.resources
  exact ⟨{
    support := result.support.flatSortsAt _
    footprint := _
    certificate := certificate
    resources := resources
    typed := action.typedAtSorts (sorted.flatSorts result.typed)
    related := action.termMap henv hscoped formed sorted result.typed result.typeCode result.related
    typeCode := result.typeCode.flatSortsAt henv }⟩

def union {owner : EndpointState sourceEnv U source value assigned} (henv : env.Ordered)
    (left : RichSupportedValue sourceEnv env U registry target owner locals σ τ available p)
    (right : RichSupportedValue sourceEnv env U registry target owner locals σ τ available q) :
    RichSupportedValue sourceEnv env U registry target owner locals σ τ available (p.union q) := by
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
    footprint := left.footprint ++ right.footprint
    certificate := .union left.certificate right.certificate
    resources := fun i need hm => (List.mem_append.mp hm).elim
      (left.resources i need) (right.resources i need)
    typed := lt.union rt
    related := (Related.retag henv lt code left.related).union (Related.retag henv rt code right.related)
    typeCode := code }

end RichSupportedValue
end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
