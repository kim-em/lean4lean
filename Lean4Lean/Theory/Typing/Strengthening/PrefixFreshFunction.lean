import Lean4Lean.Theory.Typing.Strengthening.PrefixFreshContraction
import Lean4Lean.Theory.Typing.PrefixUnfolding.QuotLiftRenaming

/-! # Reflecting a prefix on the function side of a fresh application

A prefix step on `f↑` under the domain of `f` can be reflected to `f`.
The ambient domain is identified with the first residual domain by uniqueness,
and the duplicated residual binder is then contracted by typed substitution.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature RecursorData
variable {env : VEnv}

/-- Reflect a singleton prefix on the function side of its own fresh argument.
Unlike arbitrary prefix strengthening, the added binder must be the domain of
the given Pi typing of the whole prefix. The generated output reflects exactly. -/
theorem prefixUnfold_fresh_function {name : Name} {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ (mkApps (.const name levels) args) (.forallE A B))
    (H : PrefixUnfold env U registry (A :: Γ) name levels (args.map VExpr.lift) out) :
    ∃ lower, PrefixUnfold env U registry Γ name levels args lower ∧ out = lower.lift := by
  cases H with
  | @intro data program hreg hr hname hlarge hlevels hzero hg hc =>
    obtain ⟨lower, hgl⟩ := singletonUnfolding_anyArity (args' := args) hg (by
      simpa only [List.length_map] using (singletonUnfolding_spec hg).1)
    have hex : ∃ type, data.recursorType = some type := by
      cases hh : data.recursorType with
      | some type => exact ⟨type, rfl⟩
      | none =>
        unfold singletonUnfolding at hg
        split at hg <;> simp [hh] at hg
    obtain ⟨type, htype⟩ := hex
    have hback := singletonUnfolding_lift' (ρ := .skip .refl) henv hr hlarge hzero
      htype (hr.recursorType_closed henv htype) hgl
    simp only [← lift_eq_lift'] at hback
    have he := singletonUnfolding_unique hg hback
    subst program
    have ht := hr.prefixType henv hΓ hlevels hgl (by
      simpa only [hname] using
        (show VExpr.WF env U Γ (mkApps (.const name levels) args) from ⟨_, hf⟩))
    rw [hname] at ht
    have hn := (singletonUnfolding_spec hgl).2.1
    cases hd : lower.domains with
    | nil => exact (hn hd).elim
    | cons domain ds =>
      have ht' : env.HasType U Γ (mkApps (.const name levels) args)
          (.forallE domain (wrapForalls ds lower.result)) := by
        simpa only [PrefixUnfolding.type, hd, wrapForalls, List.foldr_cons] using ht
      obtain ⟨⟨_, hdom⟩, _⟩ := (hf.uniqU henv hΓ ht').forallE_inv henv hΓ
      have hc' := hc.defeqDFC henv hΓ (.succ .zero hdom)
      have hlower := unfoldingCheck_contract_fresh henv ht hd (by
        simpa only [lift, liftN_mkApps, liftN] using hc')
      refine ⟨lower.rhs, .intro hreg hr hname hlarge hlevels hzero hgl hlower, ?_⟩
      have hs : lower.equationBody.rhs.ClosedN lower.captures.length := by
        simpa only [PrefixUnfolding.rename, List.length_map] using (hc.templateScope henv).2.1
      simpa only [← lift_eq_lift'] using PrefixUnfolding.rename_rhs (ρ := .skip .refl) hs

/-- Quotient-prefix reflection on a lifted function under its own domain uses
the same residual-binder contraction and retains the exact generated output. -/
theorem quotPrefixUnfold_fresh_function {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.HasType U Γ (mkApps (.const ``Quot.lift levels) args) (.forallE A B))
    (H : QuotPrefixUnfold env U (A :: Γ) levels (args.map VExpr.lift) out) :
    ∃ lower, QuotPrefixUnfold env U Γ levels args lower ∧ out = lower.lift := by
  cases H with
  | @intro program hr hlevels hzero hg hc =>
    obtain ⟨lower, hgl⟩ := QuotPrefixUnfolding.generate_anyArity (args' := args) hg (by
      simpa only [List.length_map] using (QuotPrefixUnfolding.generate_spec hg).2.1)
    have hback := QuotPrefixUnfolding.generate_rename (ρ := .skip .refl) hgl
    simp only [← lift_eq_lift'] at hback
    have he := QuotPrefixUnfolding.generate_unique hg hback
    subst program
    have ht := quotRegistered_prefixType henv hΓ hr hlevels hgl ⟨_, hf⟩
    have hn := (QuotPrefixUnfolding.generate_spec hgl).2.2.1
    cases hd : lower.domains with
    | nil => exact (hn hd).elim
    | cons domain ds =>
      have ht' : env.HasType U Γ (mkApps (.const ``Quot.lift levels) args)
          (.forallE domain (wrapForalls ds lower.result)) := by
        simpa only [PrefixUnfolding.type, hd, wrapForalls, List.foldr_cons] using ht
      obtain ⟨⟨_, hdom⟩, _⟩ := (hf.uniqU henv hΓ ht').forallE_inv henv hΓ
      have hc' := hc.defeqDFC henv hΓ (.succ .zero hdom)
      have hlower := unfoldingCheck_contract_fresh henv ht hd (by
        simpa only [lift, liftN_mkApps, liftN] using hc')
      refine ⟨lower.rhs, .intro hr hlevels hzero hgl hlower, ?_⟩
      have hs : lower.equationBody.rhs.ClosedN lower.captures.length := by
        simpa only [PrefixUnfolding.rename, List.length_map] using (hc.templateScope henv).2.1
      simpa only [← lift_eq_lift'] using PrefixUnfolding.rename_rhs (ρ := .skip .refl) hs

end Lean4Lean.VEnv.Strengthening

namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A prefix contraction in the immediate function of a fresh application can
be postponed before eta, retaining the target application in normal comparison. -/
theorem prefix_function_eta_body_reflection {name : Name} {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (mkApps (.const name levels) args) (.forallE A B))
    (H : PrefixUnfold env univs registry (A :: Γ) name levels (args.map VExpr.lift) out) :
    ∃ lower, PrefixUnfold env univs registry Γ name levels args lower ∧
      NormalEq Γ lower (.lam A (.app out (.bvar 0))) := by
  obtain ⟨lower, Hr, rfl⟩ := prefixUnfold_fresh_function henv hΓ hf H
  have ht := ((Hr.defeq henv hΓ).of_l henv hΓ hf).hasType.2
  exact ⟨_, Hr, .etaR ht (.refl (HasType.app (ht.weak henv) (.bvar .zero)))⟩

/-- The corresponding immediate-function quotient contraction postpones before
eta using one actual quotient prefix below. -/
theorem quotPrefix_function_eta_body_reflection {levels : List VLevel}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ (mkApps (.const ``Quot.lift levels) args) (.forallE A B))
    (H : QuotPrefixUnfold env univs (A :: Γ) levels (args.map VExpr.lift) out) :
    ∃ lower, QuotPrefixUnfold env univs Γ levels args lower ∧
      NormalEq Γ lower (.lam A (.app out (.bvar 0))) := by
  obtain ⟨lower, Hr, rfl⟩ := quotPrefixUnfold_fresh_function henv hΓ hf H
  have ht := ((Hr.defeq henv hΓ).of_l henv hΓ hf).hasType.2
  exact ⟨_, Hr, .etaR ht (.refl (HasType.app (ht.weak henv) (.bvar .zero)))⟩

end Lean4Lean.VEnv.Strengthening
