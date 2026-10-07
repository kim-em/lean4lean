import Lean4Lean.Theory.Inductive.QuotPrefixProgram
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

theorem QuotRegistered.mono (h : env ≤ env') (H : QuotRegistered env) : QuotRegistered env' :=
  ⟨h.constants H.quotient, h.constants H.constructor, h.constants H.lift,
    h.constants H.induction, h.defeqs H.equation⟩

theorem QuotRegistered.of_addQuot {env env' : VEnv} (h : env.addQuot = some env') : QuotRegistered env' :=
  ⟨addQuot_quot h, addQuot_quotMk h, addQuot_quotLift h, addQuot_quotInd h, addQuot_defeq h⟩

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

/-- The quotient generator and registration discharge every structural
replay check; only the occurrence's ordinary typing checks remain. -/
theorem QuotDeltaRule.ofGenerated
    (hr : QuotRegistered env) (hw : ∀ level ∈ levels, level.WF U)
    (hz : levels[0]?.getD .zero ≈ .zero)
    (hg : QuotPrefixProgram.generate levels args = some program)
    (hsource : HasType env U Γ (VExpr.mkApps (.const ``Quot.lift levels) args) program.type)
    (hcaptures : ∀ j (hj : j < program.captures.length)
        (hd : j < program.equationBody.domains.length),
      HasType env U (program.domains.reverse ++ Γ) program.captures[j]
        ((program.equationBody.domains[j].instL program.levels).instOuter (program.captures.take j)))
    (hmajor : ∃ proposition,
      HasType env U (program.domains.reverse ++ Γ) proposition (.sort .zero) ∧
      HasType env U (program.domains.reverse ++ Γ) (.bvar 0) proposition ∧
      HasType env U (program.domains.reverse ++ Γ) program.constructor proposition)
    (hmatch : NativeSpineMatch env U (program.domains.reverse ++ Γ)
      (.app (nativeEtaBody (program.domains.length - 1)
        (VExpr.mkApps (.const ``Quot.lift levels) args)).lift program.constructor)
      ((program.equationBody.lhs.instL program.levels).instOuter program.captures)) :
    QuotDeltaRule env U Γ levels args program.rhs := by
  obtain ⟨hl, _, hn, hlevels, heq, hbody, hcapturesLength⟩ := QuotPrefixProgram.generate_spec hg
  refine .intro hr hw hz hg {
    source_typed := hsource
    remaining_nonempty := hn
    equation_present := heq.symm ▸ hr.equation
    equation_body := hbody
    levels_wf := hlevels ▸ hw
    levels_length := ?_
    captures_length := hcapturesLength
    captures_typed := hcaptures
    major_prop := hmajor
    native_lhs := hmatch }
  rw [hlevels, heq]
  exact hl

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
