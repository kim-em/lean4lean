import Lean4Lean.Theory.Typing.AnchoredSortableBudgetComposition
/-! Transport a finite hereditary computation answer along an actual assigned-
type transfer, retaining its returned observation and exact support. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics
set_option backward.isDefEq.respectTransparency false
theorem HereditaryBudgeted.Transfer.convertAnswer
    {env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped)
    {target : List VExpr} {locals : List Nat} {σ τ : Subst}
    {available : Valuation} {left right A B : VExpr}
    (closed : available.AtomClosed) (hTarget : OnCtx target (env.IsType U))
    (producer : HereditaryBudgeted.Transfer budgets env U registry target locals σ σ available A B (.sort level))
    (originalTerm : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available left right A) :
    HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available left right B := by
  intro n demand footprint observation bounded resources
  obtain ⟨value⟩ := originalTerm observation bounded resources
  obtain ⟨type⟩ := HereditaryBudgeted.Transfer.sortable henv hscoped hTarget closed producer value.typeCertificate value.certificateBound value.typeAvailable
  exact ⟨{
    rank := value.rank
    bound := value.bound
    raw := value.raw
    adapter := value.adapter
    footprint := value.footprint
    observation := value.observation
    resources := value.resources
    support := value.support
    typeFootprint := type.footprint
    typeCertificate := type.certificate
    typeAvailable := type.available
    typed := value.typed
    rawTyped := value.rawTyped
    typeCode := TypeRelated.left_diagonal (TypeRelated.symm henv value.typed.wf_type type.related)
    rawRelated := Related.convert henv value.rawTyped type.related value.rawRelated
    related := Related.convert henv value.typed type.related value.related
    live := value.live
    observationBound := value.observationBound
    certificateBound := type.valueBound }⟩

end Lean4Lean.AnchoredSource.Adapted
