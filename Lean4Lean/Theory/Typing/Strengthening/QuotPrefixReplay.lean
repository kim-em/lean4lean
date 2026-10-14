import Lean4Lean.Theory.Typing.Strengthening.PrefixFreshFunction
import Lean4Lean.Theory.Typing.Confluence.QuotCoverage

/-! # Source-typed replay of every quotient prefix

At a Prop source, every admissible quotient prefix is checked from its source
alone. Open fresh arguments until the known five-argument rule applies, then
reabstract them with the actual generator identities. No strengthening is used.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature RecursorData
variable {env : VEnv}

/-- Every typed quotient prefix at a Prop source has an actual generated rule.
The proof opens at most five fresh binders, checks the five-argument prefix,
and reabstracts those binders; it does not infer checks from a mere equality. -/
theorem quotPrefixUnfold_exists (henv : env.WF) (hr : QuotRegistered env)
    (hu : u.WF U) (hv : v.WF U) (hz : u ≈ .zero)
    (hΓ : OnCtx Γ (env.IsType U)) (hlen : args.length ≤ 5)
    (ht : VExpr.WF env U Γ (mkApps (.const ``Quot.lift [u,v]) args)) :
    ∃ out, QuotPrefixUnfold env U Γ [u,v] args out := by
  generalize hn : 5 - args.length = n
  induction n using Nat.strongRecOn generalizing Γ args with
  | ind n ih =>
    by_cases hfull : args.length = 5
    · rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩ <;>
        simp only [List.length_nil, List.length_cons] at hfull
      all_goals try omega
      have hrnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst rest
      exact ⟨_, QuotPrefixUnfold.atFive henv hΓ hr hu hv hz ht⟩
    · have hg0 : ∃ zero, QuotPrefixUnfolding.generate [u,v] [] = some zero := by
        simp [QuotPrefixUnfolding.generate, supplyType, quotLiftConst, quotDefEq,
          instL, VLevel.inst, takeForalls, RecursorSchema.EquationBody.extract]
      obtain ⟨zero, hg0⟩ := hg0
      obtain ⟨program, hg⟩ := QuotPrefixUnfolding.generate_anyArity hg0 hlen
      have hf := quotRegistered_prefixType henv hΓ hr (by simp_all) hg ht
      have hne := (QuotPrefixUnfolding.generate_spec hg).2.2.1
      cases hd : program.domains with
      | nil => exact (hne hd).elim
      | cons A ds =>
        have hf' : env.HasType U Γ (mkApps (.const ``Quot.lift [u,v]) args)
            (.forallE A (wrapForalls ds program.result)) := by
          simpa only [PrefixUnfolding.type, hd, wrapForalls, List.foldr_cons] using hf
        have hA := (hf'.isType henv hΓ).forallE_inv henv |>.1
        have hΓ' : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, hA⟩
        have ht' : VExpr.WF env U (A :: Γ)
            (mkApps (.const ``Quot.lift [u,v]) (args.map VExpr.lift ++ [VExpr.bvar 0])) := by
          have hh := HasType.app (hf'.weak henv) (HasType.bvar Lookup.zero)
          refine ⟨wrapForalls ds program.result, ?_⟩
          change env.HasType U (A :: Γ) _ (wrapForalls ds program.result)
          simpa only [mkApps_snoc, lift, liftN_mkApps, liftN, Nat.zero_add, inst_liftN_bvar] using hh
        have hlen' : (args.map VExpr.lift ++ [VExpr.bvar 0]).length ≤ 5 := by
          simp only [List.length_append, List.length_map, List.length_singleton]; omega
        have hsmall : 5 - (args.map VExpr.lift ++ [VExpr.bvar 0]).length < n := by
          simp only [List.length_append, List.length_map, List.length_singleton]; omega
        obtain ⟨out, Hout⟩ := ih _ hsmall hΓ' hlen' ht' rfl
        obtain ⟨domain, _, Hlower⟩ := quotPrefixUnfold_fresh_argument henv hΓ hf' Hout
        exact ⟨_, Hlower⟩

/-- At any admissible prefix, source typing checks the exact generated output. -/
theorem quotPrefixUnfold_of_generated {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hr : QuotRegistered env)
    (hw : ∀ l ∈ levels, l.WF U) (hz : levels[0]?.getD .zero ≈ .zero)
    (hg : QuotPrefixUnfolding.generate levels args = some program)
    (ht : VExpr.WF env U Γ (mkApps (.const ``Quot.lift levels) args)) :
    QuotPrefixUnfold env U Γ levels args program.rhs := by
  obtain ⟨hlen, hargs, _⟩ := QuotPrefixUnfolding.generate_spec hg
  rcases levels with _ | ⟨u, _ | ⟨v, rest⟩⟩ <;>
    simp only [List.length_nil, List.length_cons] at hlen
  all_goals try omega
  have hrnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst rest
  have hu : u.WF U := hw _ (by simp)
  have hv : v.WF U := hw _ (by simp)
  obtain ⟨out, H⟩ := quotPrefixUnfold_exists henv hr hu hv hz hΓ hargs ht
  cases H with
  | intro hr' hw' hz' hg' hc =>
    cases QuotPrefixUnfolding.generate_unique hg hg'
    exact .intro hr' hw' hz' hg hc

/-- Quotient prefixes reflect arbitrary renamings from source typing alone.
This is actual lower-rule replay, with no endpoint or witnessed front. -/
theorem quotPrefixUnfold_replay {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (R : QuotPrefixUnfold env U Γ' levels (args.map (·.lift' ρ)) rhs)
    (ht : env.HasType U Γ (mkApps (.const ``Quot.lift levels) args) T) :
    ∃ out, QuotPrefixUnfold env U Γ levels args out ∧ rhs = out.lift' ρ := by
  cases R with
  | intro hr hw hz hg hc =>
    obtain ⟨lower, hgl⟩ := QuotPrefixUnfolding.generate_anyArity (args' := args) hg (by
      simpa only [List.length_map] using (QuotPrefixUnfolding.generate_spec hg).2.1)
    have hback := QuotPrefixUnfolding.generate_rename (ρ := ρ) hgl
    have he := QuotPrefixUnfolding.generate_unique hg hback
    have Hlower := quotPrefixUnfold_of_generated henv hΓ hr hw hz hgl ⟨_, ht⟩
    refine ⟨lower.rhs, Hlower, ?_⟩
    rw [he]
    have hs : lower.equationBody.rhs.ClosedN lower.captures.length := by
      simpa only [he, PrefixUnfolding.rename, List.length_map] using (hc.templateScope henv).2.1
    exact PrefixUnfolding.rename_rhs hs

end Lean4Lean.VEnv.Strengthening
