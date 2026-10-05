import Lean4Lean.Theory.Typing.QuotPrefixRenaming
import Lean4Lean.Theory.Typing.NativePrefixStrengthening

/-! Exact strengthening of checked primitive quotient prefixes. -/

namespace Lean4Lean.QuotPrefixProgram
open VExpr InductiveSignature.NativeRecursorData

theorem generate_isSome_rename {levels : List VLevel} (args : List VExpr) (ρ : Lift) :
    (generate levels (args.map (·.lift' ρ))).isSome = (generate levels args).isSome := by
  have hclosed : quotLiftConst.type.Closed := by decide
  have hs := supplyType_rename args (quotLiftConst.type.instL levels) ρ
  rw [hclosed.instL.lift'_eq Lift.Fixes.zero] at hs
  unfold generate
  simp only [List.length_map]
  split <;> try rfl
  simp only [bind, hs]
  cases hsupply : supplyType args (quotLiftConst.type.instL levels) with
  | none => rfl
  | some residual =>
    simp only [Option.map_some, Option.bind_some, takeForalls_rename]
    cases htake : InductiveSignature.NativeRecursorData.takeForalls (6 - args.length) residual <;> simp
    cases InductiveSignature.CaseSchema.EquationBody.extract quotDefEq.lhs quotDefEq.rhs quotDefEq.type <;> rfl

/-- Both success and failure of the concrete quotient generator commute
with renaming its supplied argument spine. -/
theorem generate_map_rename {levels : List VLevel} (args : List VExpr) (ρ : Lift) :
    generate levels (args.map (·.lift' ρ)) = (generate levels args).map (·.rename ρ) := by
  cases h : generate levels args with
  | none =>
    have hi := generate_isSome_rename (levels := levels) args ρ
    rw [h] at hi
    cases he : generate levels (args.map (·.lift' ρ)) <;> simp_all
  | some program => exact generate_rename h

end Lean4Lean.QuotPrefixProgram

namespace Lean4Lean.VEnv
open VExpr InductiveSignature.NativeRecursorData
open private case_lift'_mkApps from Lean4Lean.Theory.Typing.CaseReduction

theorem QuotDeltaRule.weak'_inv {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ' (env.IsType U)) (W : Ctx.Lift' ρ Γ Γ')
    (H : QuotDeltaRule env U Γ' levels (arguments.map (·.lift' ρ)) rhs) :
    ∃ smallRhs, QuotDeltaRule env U Γ levels arguments smallRhs ∧ rhs = smallRhs.lift' ρ := by
  cases H with
  | intro hr hw hz hg replay =>
    rw [QuotPrefixProgram.generate_map_rename] at hg
    obtain ⟨small, hsmall, he⟩ := Option.map_eq_some_iff.mp hg
    cases he
    have hreplay : NativePrefixReplay env U Γ
        (mkApps (.const ``Quot.lift levels) arguments) small := by
      apply NativePrefixReplay.weak'_inv henv hΓ W
      simpa only [case_lift'_mkApps, VExpr.lift'] using replay
    exact ⟨small.rhs, .intro hr hw hz hsmall hreplay,
      PrefixProgram.rename_rhs (hreplay.templateScope henv).2.1⟩

theorem QuotDeltaRule.weakN_inv {levels : List VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ')
    (H : QuotDeltaRule env U Γ' levels (arguments.map (·.liftN n k)) rhs) :
    ∃ smallRhs, QuotDeltaRule env U Γ levels arguments smallRhs ∧ rhs = smallRhs.liftN n k := by
  simpa only [lift'_consN_skipN] using
    QuotDeltaRule.weak'_inv henv hΓ (Ctx.liftN_iff_lift'.mp W)
      (by simpa only [lift'_consN_skipN] using H)

end Lean4Lean.VEnv
