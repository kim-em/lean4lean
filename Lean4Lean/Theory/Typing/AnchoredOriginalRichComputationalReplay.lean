import Lean4Lean.Theory.Typing.AnchoredOriginalRichComputationalValue

/-! Query actions preserve both computational channels: the original
assigned certificate and the concrete right observation. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure
set_option backward.isDefEq.respectTransparency false
open private typed_subset from Lean4Lean.Theory.Typing.AnchoredOriginalHeterogeneousTail

noncomputable def RichComputationalValue.pad
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available (profile : Profile n)) :
    RichComputationalValue sourceEnv env U registry target node locals σ τ available profile.pad :=
  { answer.toRichSupportedValue.pad henv with rightQuery := answer.rightQuery.pad henv hscoped formed }

def RichComputationalValue.unpad
    (henv : env.Ordered) (formed : OnCtx target (env.IsType U))
    (answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available (profile : Profile n).pad) :
    RichComputationalValue sourceEnv env U registry target node locals σ τ available profile :=
  { answer.toRichSupportedValue.unpad henv formed with rightQuery := answer.rightQuery.unpad }

theorem RichComputationalValue.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available (.singleton a))
    (action : AtomAction env U registry target a b) :
    Nonempty (RichComputationalValue sourceEnv env U registry target node locals σ τ available (.singleton b)) := by
  obtain ⟨query⟩ := answer.rightQuery.action henv hscoped formed action
  exact ⟨{ answer.toRichSupportedValue.action henv hscoped formed action with rightQuery := query }⟩

theorem RichComputationalValue.codeAdapter
    (henv : env.Ordered) (hscoped : registry.Scoped) (formed : OnCtx target (env.IsType U))
    (answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available profile)
    (action : SortableCodeAction env U registry target relevant profile next output)
    (sorted : profile.HasType (.sort relevant)) :
    Nonempty (RichComputationalValue sourceEnv env U registry target node locals σ τ available output) := by
  obtain ⟨value⟩ := answer.toRichSupportedValue.code henv hscoped formed action sorted
  exact ⟨{ value with rightQuery := answer.rightQuery.codeAdapter henv hscoped formed action sorted }⟩

noncomputable def RichComputationalValue.restrict
    (answer : RichComputationalValue sourceEnv env U registry target node locals σ τ available (input : Profile n))
    (included : ∀ atom ∈ (requested : Profile n).atoms, atom ∈ input.atoms) :
    RichComputationalValue sourceEnv env U registry target node locals σ τ available requested where
  support := answer.support
  footprint := answer.footprint
  certificate := answer.certificate
  resources := answer.resources
  typed := typed_subset included answer.typed
  related := Related.of_singletons (fun atom member => answer.related.singleton_of_mem (included atom member))
  typeCode := answer.typeCode
  rightQuery := answer.rightQuery.restrict included

end Lean4Lean.AnchoredSource.Adapted.OriginalRecordSource
