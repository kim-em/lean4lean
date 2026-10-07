import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.Inductive.ChoiceCanonicalForms

/-! # Realizability of canonical choice

`VEnv.HasCanonicalChoice` (`Theory/CanonicalChoice.lean`) asks for the constants `Nonempty`,
`Nonempty.intro` and `Classical.choice` with explicit abstract types. This file connects them
to the declarations `Init.Prelude` submits.

* `Lean4Lean/Verify/Inductive/ChoiceCanonicalForms.lean` states the production types literally
  (`nonemptyBootstrapType`, `nonemptyBootstrapIntroType`, `choiceBootstrapType`, generic only
  in binder and universe-parameter names). It proves that every `TrExprS` translation of each
  is the corresponding stored term.
* `VEnvs.WF.hasCanonicalChoice` (below): every well-formed model of an environment whose
  production `Nonempty`, `Nonempty.intro` and `Classical.choice` have the production types
  satisfies `HasCanonicalChoice` at every safety. Every later environment keeps these
  constants, and `VEnv.HasCanonicalChoice.mono` transports the property along model
  extensions.
* `Lean4Lean/Tests/CanonicalChoice.lean` checks that the declarations of `Init.Prelude` have
  the production types and that the executable installs them unchanged.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

private theorem vconstant_ext' {a b : VConstant} (huvars : a.uvars = b.uvars)
    (htype : a.type = b.type) : a = b := by
  cases a; cases b; simp_all

/-- The translated constant of a safe production constant whose type translates uniquely. -/
private theorem VEnvs.WF.constant_of_production' {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) {name : Name} {ci : ConstantInfo} {uvars : Nat} {type : VExpr}
    (hfind : env.find? name = some ci) (hsafe : ci.safety = .safe)
    (huvars : ci.levelParams.length = uvars)
    (htype : ∀ {venv e}, TrExprS venv ci.levelParams [] ci.type e → e = type)
    (safety : DefinitionSafety) :
    (ves.venv safety).constants name = some ⟨uvars, type⟩ := by
  rcases (wf.tr (safety := safety)).find? hfind
      (by rw [hsafe]; exact DefinitionSafety.le_safe) with
    ⟨ci', hci', -, hciUvars, hciType⟩
  rw [hci']
  exact congrArg some (vconstant_ext' (hciUvars.symm.trans huvars) (htype hciType))

/-- **Canonical choice is realized** in every well-formed model of an environment containing
the production `Nonempty`, `Nonempty.intro` and `Classical.choice`. -/
theorem VEnvs.WF.hasCanonicalChoice {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) {neInfo introInfo choiceInfo : ConstantInfo}
    (hNe : env.find? ``Nonempty = some neInfo) (hNeProd : IsProductionNonempty neInfo)
    (hIntro : env.find? ``Nonempty.intro = some introInfo)
    (hIntroProd : IsProductionNonemptyIntro introInfo)
    (hChoice : env.find? ``Classical.choice = some choiceInfo)
    (hChoiceProd : IsProductionChoice choiceInfo)
    (safety : DefinitionSafety) :
    (ves.venv safety).HasCanonicalChoice := by
  rcases hNeProd with ⟨hNeSafe, u, a, hNeLps, hNeType⟩
  rcases hIntroProd with ⟨hIntroSafe, u', a', b', hIntroLps, hIntroType⟩
  rcases hChoiceProd with ⟨hChoiceSafe, u'', a'', b'', hChoiceLps, hChoiceType⟩
  refine ⟨wf.constant_of_production' hNe hNeSafe (by simp [hNeLps]) ?_ safety,
    wf.constant_of_production' hIntro hIntroSafe (by simp [hIntroLps]) ?_ safety,
    wf.constant_of_production' hChoice hChoiceSafe (by simp [hChoiceLps]) ?_ safety⟩
  · intro _ _ H
    rw [hNeLps, hNeType] at H
    exact TrExprS.eq_canonicalNonemptyType H
  · intro _ _ H
    rw [hIntroLps, hIntroType] at H
    exact TrExprS.eq_canonicalNonemptyIntroType H
  · intro _ _ H
    rw [hChoiceLps, hChoiceType] at H
    exact TrExprS.eq_canonicalChoiceType H

end Lean4Lean
