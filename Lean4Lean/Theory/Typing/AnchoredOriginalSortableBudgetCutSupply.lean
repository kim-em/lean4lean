import Lean4Lean.Theory.Typing.AnchoredSortableDepthInstantiation
import Lean4Lean.Theory.Typing.AnchoredSortableBudgetPiExtraction
import Lean4Lean.Theory.Typing.AnchoredOriginalSortableApplicationPreparation

/-! Actual mixed cuts become native substitution supplies using the fixed
original argument child. Current hereditary queries are source-type-unindexed:
the checked reflection theorem supplies the genuine argument query. This does
not assert reflection for the separate typed projection-metadata grammar. -/
namespace Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
open VExpr VEnv AnchoredProfiles AnchoredSemantics
open OriginalClosureMeasure OriginalEndpointFactor OriginalTail
set_option backward.isDefEq.respectTransparency false

/-- Reanchor the selected exact row through its two original formation
children, then substitute the actual returned argument query. -/
theorem rowInstantiateSortableBudgetedOriginal
    {sourceEnv env : VEnv} {U : Nat} {registry : CanonicalHead.Registry}
    {source target : List VExpr} {locals : List Nat} {σ : Subst} {available : Valuation}
    {A B argument : VExpr} {domainLevel bodyLevel : VLevel}
    (henv : env.Ordered) (hscoped : registry.Scoped) (below : sourceEnv ≤ env)
    (formed : OnCtx target (env.IsType U)) (closed : available.AtomClosed)
    (context : ContextDerivation sourceEnv U source)
    (originalDomain : EndpointRef sourceEnv U source A (.sort domainLevel))
    (originalBody : EndpointState sourceEnv U (A :: source) B (.sort bodyLevel))
    (substitutions : Ctx.SubstEq env U target σ σ source)
    (tail : SortableTailFits sourceEnv env U registry target source locals σ σ available)
    (tailBound : HereditaryBudgeted.Within budgets tail.nativeDepth)
    (domainF : HereditaryBudgeted.StateFundamentalAt budgets env registry context (.ref originalDomain))
    (bodyF : HereditaryBudgeted.StateFundamentalAt budgets env registry (.cons context originalDomain) originalBody)
    (row : BudgetPiRowCertificate budgets env U registry target locals σ available relevant A B key result)
    (admitted : Admitted env U registry target key (argument.subst σ) (argument.subst σ))
    (argumentResult : SortableGradedResult env U registry target locals σ available argument key.input)
    (argumentBound : HereditaryBudgeted.Within budgets argumentResult.observation.nativeDepth) :
    ∃ answer : SortableCertificateResult env U registry target locals σ available
      (B.inst argument) relevant result, HereditaryBudgeted.Within budgets answer.certificate.nativeDepth := by
  obtain ⟨anchored⟩ := row.reanchorBudgeted henv hscoped below formed closed
    context originalDomain originalBody substitutions tail tailBound domainF bodyF admitted
  have domain := originalDomain.sound.defeq.mono below
  have body := originalBody.sound.defeq.mono below
  have scope := body.closedN henv
    (CtxWF.closed henv ⟨substitutions.wf, domainLevel, domain⟩)
  have live := tail.leavesLive henv hscoped formed anchored.outsideAvailable
    (anchored.pack.scoped (anchored.body.scoped scope))
  obtain ⟨answer, answerDepth⟩ := anchored.body.instantiate_allDepth henv hscoped formed closed argumentResult
    anchored.pack anchored.covered anchored.outsideAvailable live
  exact ⟨answer, fun current fuel member => Nat.le_trans (answerDepth current)
    (Nat.max_le.mpr ⟨anchored.bodyBound current fuel member, argumentBound current fuel member⟩)⟩


end Lean4Lean.AnchoredSource.Adapted.OriginalFactorCut
