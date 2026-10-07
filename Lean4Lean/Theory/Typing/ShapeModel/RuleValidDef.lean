import Lean4Lean.Theory.Typing.ShapeModel.RuleValidCore
import Lean4Lean.Theory.Typing.ShapeModel.EnvSigSyntax

/-!
# Validity of definition rules

A definition `v` contributes the rule `defRule v` (no binders, no arguments, no major) and the
equation `v.toDefEq : const v.name (params) ≡ v.value`. Both sides are closed; the approximations
of the constant are produced by the rule clause (the only rule of its head, `no_major_eq`), whose
right-hand side is the value, and conversely an approximation of the value is below one typed at
an approximation of the definition's type (its record), which is the constant's type, so the
rule clause and the typing filter of `Interp.const` produce it.
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

set_option linter.unusedSectionVars false

noncomputable section

variable {env : VEnv} [SemSig] [SemSig.Coherent]

/-- `SoundEq` in the empty context is equality of the approximations at the base valuation. -/
theorem SoundEq.nil_of (H : ∀ m, Interp env .nil m M ↔ Interp env .nil m N) :
    SoundEq env [] M N := by
  intro Γ₀ ρ W m
  cases W with
  | nil => exact H m

theorem Valuation.Fits.nil_inv (W : Valuation.Fits env Γ₀ [] ρ) : Γ₀ = [] ∧ ρ = .nil := by
  cases W with
  | nil => exact ⟨rfl, rfl⟩

/-- The validity of a definition rule. -/
theorem extraValid_def {v : VDefVal} (hr : SemSig.rules (defRule v))
    (hci : env.constants v.name = some v.toVConstant) (hvcl : v.value.Closed) :
    ExtraValid env v.toDefEq := by
  intro ls u hls _ _ hR
  simp only [VDefVal.toDefEq] at hls hR ⊢
  have hlsc : VExpr.instL ls (.const v.name (VLevel.params v.uvars)) = .const v.name ls := by
    simp only [VExpr.instL, VLevel.inst_map_id hls]
  rw [hlsc]
  have hterm : Terminal (.const v.name) 0 := .inr ⟨_, hr, rfl, by simp [Rule.arity, defRule]⟩
  have hrule : ∀ r, SemSig.rules r → r.head = .const v.name → r = defRule v := by
    intro r h1 h2
    have ⟨_, hmaj⟩ := SemSig.Coherent.same_shape h1 hr h2
    cases hm : r.major with
    | some _ => simp [hm, defRule] at hmaj
    | none => exact SemSig.Coherent.no_major_eq h1 hr h2 hm rfl
  refine SoundEq.nil_of fun m => ⟨fun h => ?_, fun h => ?_⟩
  · cases h with
    | bot => exact .bot
    | const h1 h2 h3 h4 h5 h6 h7 =>
      refine Interp.mono h3 ?_
      clear h3 h4 h5
      cases h6 with
      | bot => exact .bot
      | lam hf hle => exact .mono (hle.trans (Const.lam_le_bot_of_terminal hf hterm)) .bot
      | ctor e1 e2 =>
        cases e1; exact absurd rfl (SemSig.Coherent.ctor_no_rule e2 hr)
      | rigid e1 _ e3 => cases e1; exact absurd rfl (e3 _ hr)
      | rule e1 e2 _ _ _ e6 =>
        cases hrule _ e1 e2
        have := h7 _ _ _ e6
        exact (Interp.closed_iff hvcl.instL).1 this
      | ruleC e1 e2 _ e4 =>
        cases hrule _ e1 e2; cases e4
  · obtain ⟨m₁, a, hle, h₁, ha, hty⟩ := hR.sound Valuation.Fits.nil h
    refine Interp.mono hle (.const (k := 0) hci hls .rfl hty ?_ ?_ fun _ _ _ h => h)
    · simpa using ha
    · refine Const.rule (r := defRule v) (rargs := ([] : List (WShape 0))) hr rfl hls rfl rfl ?_
      exact (Interp.closed_iff hvcl.instL).1 h₁

end

end Lean4Lean.ShapeModel
