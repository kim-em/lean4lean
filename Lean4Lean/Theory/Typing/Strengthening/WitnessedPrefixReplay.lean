import Lean4Lean.Theory.Typing.Strengthening.WitnessedPrefixDescent

/-! # Actual prefix replay from the witnessed front

The existing witnessed descent theorem returns a lower equality. Here the same
argument reconstructs the actual lower PrefixUnfold rule and its exact lifted
output. The witnessed front remains a hypothesis, not a proved principle.
-/
namespace Lean4Lean.VEnv.Strengthening.GuardedSingleton
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature PropElim Params
variable [Params]

/-- A witnessed family front reconstructs the actual generated rule below a
binder insertion. This is operational replay, retaining registration and every
check; no reduction of the lower target or target-typing premise is used. -/
theorem prefix_rule_replay_witnessed (heq : env.HasCanonicalEq)
    (hfront : WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hW : Ctx.Lift' ρ Γ Γ') (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ' : OnCtx Γ' (env.IsType univs))
    (R : PrefixUnfold env univs registry Γ' name levels (args.map (·.lift' ρ)) rhs)
    (ht : env.HasType univs Γ (mkApps (.const name levels) args) T) :
    ∃ out, PrefixUnfold env univs registry Γ name levels args out ∧ rhs = out.lift' ρ := by
  cases R with
  | intro hreg hr hn hl hw hz hg HC =>
    subst hn
    obtain ⟨S, E, hS, hE, _⟩ := RecursorData.singletonUnfolding_layout hg
    obtain ⟨_, _, hlv, hlen, hseq, _⟩ := RecursorData.singletonUnfolding_spec hg
    obtain ⟨index, ho, _⟩ := RecursorData.singletonEquation_eq hseq
    rw [hlv] at hlen
    have hlen := hlen.trans (RecursorData.singletonEquation_uvars hseq)
    have HG : FamilyGuard (fun Δ a b => env.IsDefEqU univs Δ a b)
        Γ' _ levels (args.map (·.lift' ρ)) _ S E :=
      ⟨_, family_conversion_of_check henv heq hΓ' hr hl hz hw hlen ho hS hE hg HC⟩
    obtain ⟨lower, hgl⟩ := RecursorData.singletonUnfolding_sameArity hg (args' := args) (by simp)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrt, _⟩ :=
      RecursorData.singleton_equation_syntax hr hl hz hlen ho hS hE
    have hback := RecursorData.singletonUnfolding_lift' henv hr hl hz hrt
      (hr.recursorType_closed henv hrt) hgl (ρ := ρ)
    have hprogram := RecursorData.singletonUnfolding_unique hg hback
    rw [hprogram] at HG ⊢
    have hguard := family_guard_below_witnessed heq hfront hW hΓ hΓ' hr hl hz hw hlen ho hS hE hgl ⟨_, ht⟩ HG
    have Hlower := check_of_family_conversion henv heq hΓ hr hl hz hw hlen ho hS hE hgl ⟨_, ht⟩ hguard
    exact ⟨lower.rhs, .intro hreg hr rfl hl hw hz hgl Hlower,
      RecursorData.PrefixUnfolding.rename_rhs (Hlower.templateScope henv).2.1⟩

end Lean4Lean.VEnv.Strengthening.GuardedSingleton
