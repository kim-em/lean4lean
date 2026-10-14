import Lean4Lean.Theory.Typing.Strengthening.QuotPrefixFreshAbstraction

/-! # Prefix roots beneath function eta

A checked singleton or quotient prefix consuming a supplied fresh argument can
be computed before function eta. The only final comparison aligns the restored
lambda domain with the given function domain. These are root lemmas: arbitrary
compatible prefix computation still needs a separate fresh-argument theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Changing only a lambda's displayed domain to the domain of its Pi typing
is an ordinary normal comparison, with the body retained literally. -/
theorem normal_lam_domain_of_pi (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.lam domain body) (.forallE A B)) :
    NormalEq Γ (.lam domain body) (.lam A body) := by
  obtain ⟨⟨_, hD⟩, _, hb⟩ := ht.lam_inv henv hΓ
  obtain ⟨⟨_, hDA⟩, _⟩ := ((hD.lam hb).uniqU henv hΓ ht).forallE_inv henv hΓ
  exact .lamDF hDA.hasType.1 hDA (.refl hb)

/-- A singleton-prefix contraction at the fresh eta argument is reflected by
one actual prefix contraction of the original function and a normal comparison.
This includes indexed singletons and uses no assumption about guard descent. -/
theorem prefix_eta_body_reflection {name : Name} {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (mkApps (.const name levels) args) (.forallE A B))
    (H : PrefixUnfold env univs registry (A :: Γ) name levels
      (args.map VExpr.lift ++ [VExpr.bvar 0]) out) :
    ∃ f', PrefixUnfold env univs registry Γ name levels args f' ∧
      NormalEq Γ f' (.lam A out) := by
  obtain ⟨domain, _, Hr⟩ := prefixUnfold_fresh_argument henv hΓ hf H
  have ht : env.HasType univs Γ (.lam domain out) (.forallE A B) :=
    ((Hr.defeq henv hΓ).of_l henv hΓ hf).hasType.2
  exact ⟨_, Hr, normal_lam_domain_of_pi hΓ ht⟩

/-- The quotient-prefix root also commutes back across a fresh eta argument
using one actual quotient-prefix contraction. -/
theorem quotPrefix_eta_body_reflection {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (mkApps (.const ``Quot.lift levels) args) (.forallE A B))
    (H : QuotPrefixUnfold env univs (A :: Γ) levels
      (args.map VExpr.lift ++ [VExpr.bvar 0]) out) :
    ∃ f', QuotPrefixUnfold env univs Γ levels args f' ∧
      NormalEq Γ f' (.lam A out) := by
  obtain ⟨domain, _, Hr⟩ := quotPrefixUnfold_fresh_argument henv hΓ hf H
  have ht : env.HasType univs Γ (.lam domain out) (.forallE A B) :=
    ((Hr.defeq henv hΓ).of_l henv hΓ hf).hasType.2
  exact ⟨_, Hr, normal_lam_domain_of_pi hΓ ht⟩

end Lean4Lean.VEnv.Strengthening
