import Lean4Lean.Theory.Typing.AnchoredOriginalSortableEtaVisitors
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableEtaExpansion
import Lean4Lean.Theory.Typing.AnchoredOriginalTailEta

/-! The complete original hereditary function eta rule. Its only semantic
calls are the original domain, codomain, and function children; their strict
closure schedule is `OriginalTail.eta_schedule`. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
theorem OriginalTail.DerivationHereditaryFundamental.eta
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A B f : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (body : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (liftedBody : Derivation sourceEnv U (A.lift :: A :: source)
      (B.liftN 1 1) (B.liftN 1 1) (.sort bodyLevel))
    (function : Derivation sourceEnv U source f f (.forallE A B))
    (liftedFunction : Derivation sourceEnv U (A :: source) f.lift f.lift
      (.forallE A.lift (B.liftN 1 1)))
    (liftedDomain : Derivation sourceEnv U (A :: source) A.lift A.lift (.sort domainLevel))
    (domainIH : DerivationHereditaryFundamental env registry context domain)
    (bodyIH : DerivationHereditaryFundamental env registry (.cons context (.left domain)) body)
    (functionIH : DerivationHereditaryFundamental env registry context function) :
    DerivationHereditaryFundamental env registry context
      (.eta domainWF bodyWF domain body liftedBody function liftedFunction liftedDomain) := by
  have domainState : StateHereditaryFundamental env registry context (.ref (.left domain)) := by
    intro target locals σ τ available closed hTarget substitutions fits
    exact (domainIH target locals σ τ available closed hTarget substitutions fits).1
  have bodyState : StateHereditaryFundamental env registry (.cons context (.left domain)) (.ref (.left body)) := by
    intro target locals σ τ available closed hTarget substitutions fits
    exact (bodyIH target locals σ τ available closed hTarget substitutions fits).1
  have domainSortable := domainState.sortable henv hscoped
  have bodySortable := bodyState.sortable henv hscoped
  intro target locals σ τ available closed hTarget substitutions fits
  have functionChild : SortableComputationalTransfer env U registry target locals σ τ available f f (.forallE A B) :=
    (functionIH target locals σ τ available closed hTarget substitutions fits).1
  have forward : SortableComputationalTransfer env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) := by
    intro n demand footprint observation resources
    exact SortableObs.etaContractHereditary henv hscoped hle context (.left domain) (.ref (.left body))
      domainSortable bodySortable functionChild
      (domain.forget.defeq.mono hle) (body.forget.defeq.mono hle) (function.forget.defeq.mono hle)
      closed hTarget substitutions fits observation resources
  have backward : SortableComputationalTransfer env U registry target locals σ τ available
      f (.lam A (.app f.lift (.bvar 0))) (.forallE A B) := by
    intro n demand footprint observation resources
    obtain ⟨result⟩ := functionChild observation resources
    exact result.etaExpandOriginal henv hscoped hle context (.left domain) (.ref (.left body))
      domainSortable bodySortable
      (domain.forget.defeq.mono hle) (body.forget.defeq.mono hle) (function.forget.defeq.mono hle)
      closed hTarget substitutions fits
  exact ⟨forward, backward⟩


end Lean4Lean.AnchoredSource.Adapted
