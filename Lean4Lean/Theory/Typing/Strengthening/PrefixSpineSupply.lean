import Lean4Lean.Theory.Typing.Strengthening.PrefixCheckedSupply

/-! # Checked prefix supply along an argument spine

Any additional typed spine that stops before the major preserves the actual
prefix rule. This lets a prefix contraction inside such a function spine meet
an actual lower contraction under a fresh eta binder, by beta specialization.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr InductiveSignature RecursorData
variable {env : VEnv}

/-- Supply an arbitrary typed spine while leaving the singleton major unsupplied.
All intermediate prefix checks are actual checks of the installed declaration. -/
theorem prefixUnfold_supply_spine {name : Name} {levels : List VLevel} {data : RecursorData}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hreg : registry name = some data)
    (hbound : args.length + tail.length ≤ data.majorOffset)
    (H : PrefixUnfold env U registry Γ name levels args out)
    (ht : VExpr.WF env U Γ (mkApps (.const name levels) (args ++ tail))) :
    ∃ out', PrefixUnfold env U registry Γ name levels (args ++ tail) out' ∧
      BetaRed (mkApps out tail) out' := by
  induction tail using List.snoc_induction with
  | nil => exact ⟨out, by simpa only [List.append_nil] using H, .refl⟩
  | snoc tail arg ih =>
    have ht' : VExpr.WF env U Γ (.app (mkApps (.const name levels) (args ++ tail)) arg) := by
      simpa only [← List.append_assoc, mkApps_snoc] using ht
    obtain ⟨T, htt⟩ := ht'
    obtain ⟨_, _, hf, _⟩ := HasType.app_inv henv hΓ htt
    have hb : args.length + tail.length + 1 ≤ data.majorOffset := by
      simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using hbound
    obtain ⟨middle, Hmiddle, Rmiddle⟩ := ih (by omega) ⟨_, hf⟩
    obtain ⟨last, Hlast, Rlast⟩ := prefixUnfold_supply_one henv hΓ hreg
      (args := args ++ tail) (by simpa only [List.length_append] using hb) Hmiddle
      (by simpa only [mkApps_snoc] using (show VExpr.WF env U Γ _ from ⟨T, htt⟩))
    refine ⟨last, by simpa only [List.append_assoc] using Hlast, ?_⟩
    rw [mkApps_snoc]
    exact (BetaRed.app Rmiddle .refl).trans Rlast

/-- Checked quotient prefixes specialize along every admissible typed spine. -/
theorem quotPrefixUnfold_supply_spine {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hbound : args.length + tail.length ≤ 5)
    (H : QuotPrefixUnfold env U Γ levels args out)
    (ht : VExpr.WF env U Γ (mkApps (.const ``Quot.lift levels) (args ++ tail))) :
    ∃ out', QuotPrefixUnfold env U Γ levels (args ++ tail) out' ∧
      BetaRed (mkApps out tail) out' := by
  induction tail using List.snoc_induction with
  | nil => exact ⟨out, by simpa only [List.append_nil] using H, .refl⟩
  | snoc tail arg ih =>
    have ht' : VExpr.WF env U Γ (.app (mkApps (.const ``Quot.lift levels) (args ++ tail)) arg) := by
      simpa only [← List.append_assoc, mkApps_snoc] using ht
    obtain ⟨T, htt⟩ := ht'
    obtain ⟨_, _, hf, _⟩ := HasType.app_inv henv hΓ htt
    have hb : args.length + tail.length + 1 ≤ 5 := by
      simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using hbound
    obtain ⟨middle, Hmiddle, Rmiddle⟩ := ih (by omega) ⟨_, hf⟩
    obtain ⟨last, Hlast, Rlast⟩ := quotPrefixUnfold_supply_one henv hΓ
      (args := args ++ tail) (by simpa only [List.length_append] using hb) Hmiddle
      (by simpa only [mkApps_snoc] using (show VExpr.WF env U Γ _ from ⟨T, htt⟩))
    refine ⟨last, by simpa only [List.append_assoc] using Hlast, ?_⟩
    rw [mkApps_snoc]
    exact (BetaRed.app Rmiddle .refl).trans Rlast

/-- A prefix contraction inside a lifted function spine meets a lower actual
prefix after beta specialization, provided the supplied spine stops before the
major. Only the complete function needs Pi typing with the ambient domain. -/
theorem prefixUnfold_fresh_spine_join {name : Name} {levels : List VLevel} {data : RecursorData}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hreg : registry name = some data)
    (hbound : args.length + tail.length ≤ data.majorOffset)
    (hf : env.HasType U Γ (mkApps (.const name levels) (args ++ tail)) (.forallE A B))
    (H : PrefixUnfold env U registry (A :: Γ) name levels (args.map VExpr.lift) out) :
    ∃ lower, PrefixUnfold env U registry Γ name levels (args ++ tail) lower ∧
      BetaRed (mkApps out (tail.map VExpr.lift)) lower.lift := by
  obtain ⟨hA, _⟩ := (hf.isType henv hΓ).forallE_inv henv
  have hΓ' : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, hA⟩
  have hweak : VExpr.WF env U (A :: Γ)
      (mkApps (.const name levels) (args.map VExpr.lift ++ tail.map VExpr.lift)) := by
    simpa only [lift, liftN_mkApps, liftN, List.map_append] using
      (show VExpr.WF env U (A :: Γ) ((mkApps (.const name levels) (args ++ tail)).lift) from
        ⟨_, hf.weak henv⟩)
  obtain ⟨upper, Hupper, R⟩ := prefixUnfold_supply_spine henv hΓ' hreg
    (by simpa only [List.length_map] using hbound) H hweak
  rw [← List.map_append] at Hupper
  obtain ⟨lower, Hlower, he⟩ := prefixUnfold_fresh_function henv hΓ hf Hupper
  exact ⟨lower, Hlower, he ▸ R⟩

/-- The corresponding quotient prefix overlap also joins by pure beta after
supplying the already present arguments and contracting the duplicated domain. -/
theorem quotPrefixUnfold_fresh_spine_join {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hbound : args.length + tail.length ≤ 5)
    (hf : env.HasType U Γ (mkApps (.const ``Quot.lift levels) (args ++ tail)) (.forallE A B))
    (H : QuotPrefixUnfold env U (A :: Γ) levels (args.map VExpr.lift) out) :
    ∃ lower, QuotPrefixUnfold env U Γ levels (args ++ tail) lower ∧
      BetaRed (mkApps out (tail.map VExpr.lift)) lower.lift := by
  obtain ⟨hA, _⟩ := (hf.isType henv hΓ).forallE_inv henv
  have hΓ' : OnCtx (A :: Γ) (env.IsType U) := ⟨hΓ, hA⟩
  have hweak : VExpr.WF env U (A :: Γ)
      (mkApps (.const ``Quot.lift levels) (args.map VExpr.lift ++ tail.map VExpr.lift)) := by
    simpa only [lift, liftN_mkApps, liftN, List.map_append] using
      (show VExpr.WF env U (A :: Γ) ((mkApps (.const ``Quot.lift levels) (args ++ tail)).lift) from
        ⟨_, hf.weak henv⟩)
  obtain ⟨upper, Hupper, R⟩ := quotPrefixUnfold_supply_spine henv hΓ'
    (by simpa only [List.length_map] using hbound) H hweak
  rw [← List.map_append] at Hupper
  obtain ⟨lower, Hlower, he⟩ := quotPrefixUnfold_fresh_function henv hΓ hf Hupper
  exact ⟨lower, Hlower, he ▸ R⟩

end Lean4Lean.VEnv.Strengthening
