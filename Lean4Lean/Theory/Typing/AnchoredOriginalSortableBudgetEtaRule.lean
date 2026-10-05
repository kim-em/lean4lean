import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetEtaVisitors
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetEtaExpansion
import Lean4Lean.Theory.Typing.AnchoredOriginalTailEta

/-! The complete original hereditary function eta rule. Its only semantic
calls are the original domain, codomain, and function children; their strict
closure schedule is `OriginalTail.eta_schedule`. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false
theorem HereditaryBudgeted.FundamentalAt.eta
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
    (domainIH : HereditaryBudgeted.FundamentalAt budgets env registry context domain)
    (bodyIH : HereditaryBudgeted.FundamentalAt budgets env registry (.cons context (.left domain)) body)
    (functionIH : HereditaryBudgeted.FundamentalAt budgets env registry context function) :
    HereditaryBudgeted.FundamentalAt budgets env registry context
      (.eta domainWF bodyWF domain body liftedBody function liftedFunction liftedDomain) := by
  have domainState : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref (.left domain)) := by
    intro target locals σ τ available closed hTarget substitutions fits frameBound
    exact (domainIH target locals σ τ available closed hTarget substitutions fits frameBound).1
  have bodyState : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context (.left domain)) (.ref (.left body)) := by
    intro target locals σ τ available closed hTarget substitutions fits frameBound
    exact (bodyIH target locals σ τ available closed hTarget substitutions fits frameBound).1
  intro target locals σ τ available closed hTarget substitutions fits frameBound
  have functionChild : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available f f (.forallE A B) :=
    (functionIH target locals σ τ available closed hTarget substitutions fits frameBound).1
  have forward : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      (.lam A (.app f.lift (.bvar 0))) f (.forallE A B) := by
    intro n demand footprint observation bounded resources
    exact SortableObs.etaContractBudgeted henv hscoped hle context (.left domain) (.ref (.left body))
      domainState bodyState functionChild
      (domain.forget.defeq.mono hle) (body.forget.defeq.mono hle) (function.forget.defeq.mono hle)
      closed hTarget substitutions fits frameBound observation bounded resources
  have backward : HereditaryBudgeted.Transfer budgets env U registry target locals σ τ available
      f (.lam A (.app f.lift (.bvar 0))) (.forallE A B) := by
    intro n demand footprint observation bounded resources
    obtain ⟨result⟩ := functionChild observation bounded resources
    exact result.etaExpandBudgetedOriginal henv hscoped hle context (.left domain) (.ref (.left body))
      domainState bodyState
      (domain.forget.defeq.mono hle) (body.forget.defeq.mono hle) (function.forget.defeq.mono hle)
      closed hTarget substitutions fits frameBound
  exact ⟨forward, backward⟩


/-- Compatibility with the stronger all-budget interface. -/
theorem HereditaryBudgeted.DerivationFundamental.eta
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
    (domainIH : HereditaryBudgeted.DerivationFundamental env registry context domain)
    (bodyIH : HereditaryBudgeted.DerivationFundamental env registry (.cons context (.left domain)) body)
    (functionIH : HereditaryBudgeted.DerivationFundamental env registry context function) :
    HereditaryBudgeted.DerivationFundamental env registry context
      (.eta domainWF bodyWF domain body liftedBody function liftedFunction liftedDomain) := by
  intro budgets
  exact HereditaryBudgeted.FundamentalAt.eta henv hscoped hle context domainWF bodyWF domain body liftedBody function liftedFunction liftedDomain
    (domainIH budgets) (bodyIH budgets) (functionIH budgets)

end Lean4Lean.AnchoredSource.Adapted
