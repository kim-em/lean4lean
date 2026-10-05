import Lean4Lean.Theory.Typing.AnchoredSortableHeaderPhase
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetApplicationRule
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetEtaRule
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetBetaRule
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetLambdaRule
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableBudgetVariable

/-! The six original hereditary rules preserve exactly the caller controls of
one header phase. The selected active fuel never becomes an unrestricted
all-budget induction hypothesis. These are the hereditary Sortable rules;
they do not assert the separate Rich projection/header interpretation. -/
namespace Lean4Lean.AnchoredSource.Adapted
open VExpr VEnv AnchoredProfiles AnchoredSemantics OriginalClosureMeasure OriginalTail
set_option backward.isDefEq.respectTransparency false

theorem HereditaryBudgeted.HeaderPhase.appDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A B f g a b : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (body : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (function : Derivation sourceEnv U source f g (.forallE A B))
    (argument : Derivation sourceEnv U source a b A)
    (result : Derivation sourceEnv U source (B.inst a) (B.inst b) (.sort bodyLevel))
    (domainIH : HereditaryBudgeted.HeaderPhase base current env registry context domain)
    (bodyIH : HereditaryBudgeted.HeaderPhase base current env registry (.cons context (.left domain)) body)
    (functionIH : HereditaryBudgeted.HeaderPhase base current env registry context function)
    (argumentIH : HereditaryBudgeted.HeaderPhase base current env registry context argument)
    (resultIH : HereditaryBudgeted.HeaderPhase base current env registry context result) :
    HereditaryBudgeted.HeaderPhase base current env registry context (.appDF domainWF bodyWF domain body function argument result) := by
  intro budgets quiet fuel
  exact HereditaryBudgeted.FundamentalAt.appDF henv hscoped hle context domainWF bodyWF domain body function argument result
    (domainIH budgets quiet fuel) (bodyIH budgets quiet fuel) (functionIH budgets quiet fuel)
    (argumentIH budgets quiet fuel) (resultIH budgets quiet fuel)

theorem HereditaryBudgeted.HeaderPhase.eta
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
    (domainIH : HereditaryBudgeted.HeaderPhase base current env registry context domain)
    (bodyIH : HereditaryBudgeted.HeaderPhase base current env registry (.cons context (.left domain)) body)
    (functionIH : HereditaryBudgeted.HeaderPhase base current env registry context function) :
    HereditaryBudgeted.HeaderPhase base current env registry context
      (.eta domainWF bodyWF domain body liftedBody function liftedFunction liftedDomain) := by
  intro budgets quiet fuel
  exact HereditaryBudgeted.FundamentalAt.eta henv hscoped hle context domainWF bodyWF domain body liftedBody function liftedFunction liftedDomain
    (domainIH budgets quiet fuel) (bodyIH budgets quiet fuel) (functionIH budgets quiet fuel)

theorem HereditaryBudgeted.HeaderPhase.forallEDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    {source : List VExpr} {A A' B B' : VExpr} {u v : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (hu : u.WF U) (hv : v.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort u))
    (body : Derivation sourceEnv U (A :: source) B B' (.sort v))
    (body' : Derivation sourceEnv U (A' :: source) B B' (.sort v))
    (domainIH : HereditaryBudgeted.HeaderPhase base current env registry context domain)
    (bodyIH : HereditaryBudgeted.HeaderPhase base current env registry (.cons context (.left domain)) body)
    (bodyIH' : HereditaryBudgeted.HeaderPhase base current env registry (.cons context (.right domain)) body') :
    HereditaryBudgeted.HeaderPhase base current env registry context (.forallEDF hu hv domain body body') := by
  intro budgets quiet fuel
  exact HereditaryBudgeted.FundamentalAt.forallEDF henv hscoped below context hu hv domain body body'
    (domainIH budgets quiet fuel) (bodyIH budgets quiet fuel) (bodyIH' budgets quiet fuel)

theorem HereditaryBudgeted.HeaderPhase.lamDF
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A A' B body other : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A' (.sort domainLevel))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (codomain' : Derivation sourceEnv U (A' :: source) B B (.sort bodyLevel))
    (bodies : Derivation sourceEnv U (A :: source) body other B)
    (bodies' : Derivation sourceEnv U (A' :: source) body other B)
    (domainIH : HereditaryBudgeted.HeaderPhase base current env registry context domain)
    (codomainIH : HereditaryBudgeted.HeaderPhase base current env registry (.cons context (.left domain)) codomain)
    (codomainIH' : HereditaryBudgeted.HeaderPhase base current env registry (.cons context (.right domain)) codomain')
    (bodyIH : HereditaryBudgeted.HeaderPhase base current env registry (.cons context (.left domain)) bodies)
    (bodyIH' : HereditaryBudgeted.HeaderPhase base current env registry (.cons context (.right domain)) bodies') :
    HereditaryBudgeted.HeaderPhase base current env registry context
      (.lamDF domainWF bodyWF domain codomain codomain' bodies bodies') := by
  intro budgets quiet fuel
  exact HereditaryBudgeted.FundamentalAt.lamDF henv hscoped hle context domainWF bodyWF domain codomain codomain' bodies bodies'
    (domainIH budgets quiet fuel) (codomainIH budgets quiet fuel) (codomainIH' budgets quiet fuel)
    (bodyIH budgets quiet fuel) (bodyIH' budgets quiet fuel)

theorem HereditaryBudgeted.HeaderPhase.beta
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    (henv : env.Ordered) (hscoped : registry.Scoped) (hle : sourceEnv ≤ env)
    {source : List VExpr} {A B body argument : VExpr} {domainLevel bodyLevel : VLevel}
    (context : ContextDerivation sourceEnv U source)
    (domainWF : domainLevel.WF U) (bodyWF : bodyLevel.WF U)
    (domain : Derivation sourceEnv U source A A (.sort domainLevel))
    (codomain : Derivation sourceEnv U (A :: source) B B (.sort bodyLevel))
    (bodyRef : Derivation sourceEnv U (A :: source) body body B)
    (argumentRef : Derivation sourceEnv U source argument argument A)
    (result : Derivation sourceEnv U source (B.inst argument) (B.inst argument) (.sort bodyLevel))
    (instantiated : Derivation sourceEnv U source (body.inst argument) (body.inst argument) (B.inst argument))
    (domainIH : HereditaryBudgeted.HeaderPhase base current env registry context domain)
    (codomainIH : HereditaryBudgeted.HeaderPhase base current env registry (.cons context (.left domain)) codomain)
    (bodyIH : HereditaryBudgeted.HeaderPhase base current env registry (.cons context (.left domain)) bodyRef)
    (argumentIH : HereditaryBudgeted.HeaderPhase base current env registry context argumentRef)
    (instantiatedIH : HereditaryBudgeted.HeaderPhase base current env registry context instantiated) :
    HereditaryBudgeted.HeaderPhase base current env registry context
      (.beta domainWF bodyWF domain codomain bodyRef argumentRef result instantiated) := by
  intro budgets quiet fuel
  exact HereditaryBudgeted.FundamentalAt.beta henv hscoped hle context domainWF bodyWF domain codomain bodyRef argumentRef result instantiated
    (domainIH budgets quiet fuel) (codomainIH budgets quiet fuel) (bodyIH budgets quiet fuel)
    (argumentIH budgets quiet fuel) (instantiatedIH budgets quiet fuel)

theorem HereditaryBudgeted.HeaderPhase.bvar
    (henv : env.Ordered) (hscoped : registry.Scoped)
    (context : ContextDerivation sourceEnv U source)
    (domains : ∀ budgets, HereditaryBudgeted.Quiet base budgets → ∀ fuel,
      HereditaryBudgeted.ContextFundamentalsAt ((current, fuel) :: budgets) env registry context)
    (lookup : Lookup source index A) (levelWF : level.WF U)
    (formation : Derivation sourceEnv U source A A (.sort level)) :
    HereditaryBudgeted.HeaderPhase base current env registry context (.bvar lookup levelWF formation) := by
  intro budgets quiet fuel
  exact HereditaryBudgeted.FundamentalAt.bvar henv hscoped context
    (domains budgets quiet fuel) lookup levelWF formation

end Lean4Lean.AnchoredSource.Adapted
