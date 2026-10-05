import Lean4Lean.Theory.Typing.AnchoredSortableTransferClosures
import Lean4Lean.Theory.Typing.AnchoredSortableGradedAction
import Lean4Lean.Theory.Typing.AnchoredAtomActionInterpretation

/-! Hereditary F answers close under finite output actions while retaining
both the requested query and the actual returned query's source type support. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false

private theorem code_union
    (first : TypeRelated env U registry Γ A B p)
    (second : TypeRelated env U registry Γ A B q) :
    TypeRelated env U registry Γ A B (p.union q) := by
  apply TypeRelated.of_singletons
  intro atom member
  exact (List.mem_append.mp member).elim
    (fun h => first.singleton h) (fun h => second.singleton h)

theorem SortableComputationalTransferResult.action
    (henv : env.Ordered) (hscoped : registry.Scoped) (hΓ : OnCtx Γ (env.IsType U))
    (_closed : available.AtomClosed)
    {a b : Atom n} (action : AtomAction env U registry Γ a b)
    (result : SortableComputationalTransferResult env U registry Γ locals σ τ available
      left right assigned (.singleton a)) :
    Nonempty (SortableComputationalTransferResult env U registry Γ locals σ τ available
      left right assigned (.singleton b)) := by
  let requestedSupport := action.support.apply (lowerProfile n result.bound result.support)
  have requestTyped := action.typed result.requestedTyped
  have requestCode := action.support.codeMap henv hscoped
    (result.typeCode.lower henv result.bound)
  have requestRelated := action.termMap henv hscoped hΓ result.requestedTyped
    (result.requestedRelated henv hΓ)
  have highTyped := Profile.HasType.raise result.bound requestTyped
  have highCode := requestCode.raise henv result.bound
  have highRelated := requestRelated.raise henv result.bound
  have wf := result.rawTyped.wf_type.union highTyped.wf_type
  have typed := highTyped.enlarge (Profile.le_union_right _ _) wf
  have rawTyped := result.rawTyped.enlarge (Profile.le_union_left _ _) wf
  have code := code_union result.typeCode highCode
  have step : GeneralNormalProfileAdapter env U registry Γ (.singleton a) (.singleton b) :=
    .cons (List.mem_singleton_self _) (action.toGeneralAdapter henv hscoped hΓ) (.nil _)
  exact ⟨{
    rank := result.rank
    bound := result.bound
    raw := result.raw
    footprint := result.footprint
    observation := result.observation
    adapter := result.adapter.comp (GeneralNormalProfileAdapter.raise henv hscoped hΓ result.bound step)
    resources := result.resources
    live := result.live
    support := result.support.union (raiseProfile result.rank result.bound requestedSupport)
    typeFootprint := result.typeFootprint ++ result.typeFootprint
    typeCertificate := .union result.typeCertificate
      ((SortableCert.support action.support result.requestedCertificate).raise result.bound)
    typeAvailable := fun i need member => (List.mem_append.mp member).elim
      (result.typeAvailable i need) (result.typeAvailable i need)
    typed := typed
    rawTyped := rawTyped
    typeCode := code
    related := Related.retag henv typed code highRelated
    rawRelated := Related.retag henv rawTyped code result.rawRelated }⟩

end Lean4Lean.AnchoredSource.Adapted
