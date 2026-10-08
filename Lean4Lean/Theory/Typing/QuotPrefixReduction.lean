import Lean4Lean.Theory.Inductive.QuotPrefixUnfolding
import Lean4Lean.Theory.Typing.NativePrefixWeakening
import Lean4Lean.Theory.Typing.QuotLemmas

namespace Lean4Lean.VEnv
open InductiveSignature

/-- Exact primitive quotient declarations and their actual equation. -/
structure QuotRegistered (env : VEnv) : Prop where
  quotient : env.constants ``Quot = some quotConst
  constructor : env.constants ``Quot.mk = some quotMkConst
  lift : env.constants ``Quot.lift = some quotLiftConst
  induction : env.constants ``Quot.ind = some quotIndConst
  equation : env.defeqs quotDefEq

/-- Checked zero-source unfolding at a primitive quotient-lift prefix.
The selector is Quot.ind, and all replay data come from quotDefEq. -/
inductive QuotDeltaRule (env : VEnv) (U : Nat) (Γ : List VExpr) :
    List VLevel → List VExpr → VExpr → Prop where
  | intro {program : NativeRecursorData.PrefixProgram} :
      QuotRegistered env → (∀ level ∈ levels, level.WF U) →
      levels[0]?.getD .zero ≈ .zero →
      QuotPrefixProgram.generate levels arguments = some program →
      NativePrefixReplay env U Γ (VExpr.mkApps (.const ``Quot.lift levels) arguments) program →
      QuotDeltaRule env U Γ levels arguments program.rhs

theorem QuotDeltaRule.registered (H : QuotDeltaRule env U Γ levels arguments rhs) :
    QuotRegistered env := by
  cases H with | intro hr _ _ _ _ => exact hr

theorem QuotDeltaRule.unique (H : QuotDeltaRule env U Γ levels args rhs)
    (H' : QuotDeltaRule env U Γ levels args rhs') : rhs = rhs' := by
  cases H with | intro _ _ _ hg _ =>
    cases H' with | intro _ _ _ hg' _ =>
      cases QuotPrefixProgram.generate_unique hg hg'
      rfl

theorem QuotDeltaRule.defeq (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (H : QuotDeltaRule env U Γ levels args rhs) :
    IsDefEqU env U Γ (VExpr.mkApps (.const ``Quot.lift levels) args) rhs := by
  cases H with | intro _ _ _ _ replay => exact ⟨_, replay.defeq henv hΓ⟩

theorem QuotDeltaRule.defeqDFC (henv : env.WF)
    (hΓ : OnCtx Γ₀ (env.IsType U)) (W : IsDefEqCtx env U Γ₀ Γ₁ Γ₂)
    (H : QuotDeltaRule env U Γ₁ levels args rhs) : QuotDeltaRule env U Γ₂ levels args rhs := by
  cases H with
  | intro hr hw hz hg replay => exact .intro hr hw hz hg (replay.defeqDFC henv hΓ W)

end Lean4Lean.VEnv
