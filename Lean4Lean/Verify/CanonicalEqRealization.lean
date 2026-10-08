import Lean4Lean.Verify.Environment

/-! # Realizability of canonical equality

`VEnv.HasCanonicalEq` stores explicit abstract terms for `Eq`, `Eq.refl`,
`Eq.rec` and the iota rule of `Eq.rec`.  This file connects them to the
declaration `Init.Prelude` submits.

* `Lean4Lean/Verify/Inductive/EqCanonicalForms.lean` states the production
  expressions literally (`eqBootstrapType`, `eqBootstrapReflType`,
  `eqRecTypeExpr`, `eqRecRuleRhsExpr`, `eqRecRuleLhsExpr`, `eqRecRuleTypeExpr`,
  generic only in binder and universe-parameter names) and proves that every
  `TrExprS` translation of each is the corresponding stored term
  (`TrExprS.eq_canonicalEq*`).
* `InductiveSignature.Compiles.eqRecRules`
  (`Lean4Lean/Theory/Inductive/CanonicalEqSignature.lean`): an ordinary
  compilation of the declaration generates exactly the stored iota rule once its
  recursor has the stored type.
* `addDecl.eqBootstrapHasCanonicalEq` (below): checked addition of the bootstrap
  declaration (`EqBootstrapShape`) produces abstract environments satisfying
  `HasCanonicalEq`, provided the executable installs `Eq.rec` with the
  production type (`IsProductionEqRec`).  The executable recursor construction
  is not modelled syntactically, so this is a hypothesis on the output;
  `Lean4Lean/Tests/CanonicalEq.lean` checks it for the declaration of
  `Init.Prelude`.
* `VEnvs.WF.canonicalEq_constants` (below): in any well-formed model of an
  environment whose production `Eq`, `Eq.refl` and `Eq.rec` have the production
  types, the three constant clauses of `HasCanonicalEq` hold at every safety.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

private theorem vconstant_ext {a b : VConstant} (huvars : a.uvars = b.uvars)
    (htype : a.type = b.type) : a = b := by
  cases a; cases b; simp_all

/-- The translated constant of a safe production constant whose type
translates uniquely. -/
private theorem VEnvs.WF.constant_of_production {env : Environment} {ves : VEnvs}
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
  exact congrArg some (vconstant_ext (hciUvars.symm.trans huvars) (htype hciType))

/-- The constant clauses of `HasCanonicalEq` hold in every well-formed model of
an environment containing the production `Eq`, `Eq.refl` and `Eq.rec`. -/
theorem VEnvs.WF.canonicalEq_constants {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) {eqInfo reflInfo recInfo : ConstantInfo}
    (hEq : env.find? ``Eq = some eqInfo) (hEqProd : IsProductionEq eqInfo)
    (hRefl : env.find? ``Eq.refl = some reflInfo) (hReflProd : IsProductionEqRefl reflInfo)
    (hRec : env.find? ``Eq.rec = some recInfo) (hRecProd : IsProductionEqRec recInfo)
    (safety : DefinitionSafety) :
    (ves.venv safety).constants ``Eq = some ⟨1, canonicalEqType⟩ ∧
    (ves.venv safety).constants ``Eq.refl = some ⟨1, canonicalEqReflType⟩ ∧
    (ves.venv safety).constants ``Eq.rec = some ⟨2, canonicalEqRecType⟩ := by
  rcases hEqProd with ⟨hEqSafe, u, a, b, c, hEqLps, hEqType⟩
  rcases hReflProd with ⟨hReflSafe, u', a', b', hReflLps, hReflType⟩
  rcases hRecProd with ⟨hRecSafe, v, w, n, hvw, hRecLps, hRecType⟩
  refine ⟨wf.constant_of_production hEq hEqSafe (by simp [hEqLps]) ?_ safety,
    wf.constant_of_production hRefl hReflSafe (by simp [hReflLps]) ?_ safety,
    wf.constant_of_production hRec hRecSafe (by simp [hRecLps]) ?_ safety⟩
  · intro _ _ H
    rw [hEqLps, hEqType] at H
    exact TrExprS.eq_canonicalEqType H
  · intro _ _ H
    rw [hReflLps, hReflType] at H
    exact TrExprS.eq_canonicalEqReflType H
  · intro _ _ H
    rw [hRecLps, hRecType] at H
    exact TrExprS.eq_canonicalEqRecType hvw H

/-- Checked addition of Lean's bootstrap `Eq` declaration realizes canonical
equality: the output environment has well-formed abstract models extending the
input ones, and these satisfy `HasCanonicalEq` (including the iota rule of
`Eq.rec`) as soon as the executable has installed `Eq.rec` with the production
type.  Only the absence of `Eq` is assumed of the input, together with canonical choice
(`VEnv.HasCanonicalChoice`) at every safety level. -/
theorem addDecl.eqBootstrapHasCanonicalEq {env : Environment} {ves : VEnvs}
    (wf : ves.WF env) (hch : ∀ safety, (ves.venv safety).HasCanonicalChoice)
    (hAbsent : env.constants.find? ``Eq = none)
    {lparams : List Name} {nparams : Nat} {types : List InductiveType} {isUnsafe : Bool}
    (Hshape : VerifyInductive.EqBootstrapShape lparams nparams types isUnsafe)
    (fuel : FuelConfig := {}) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe) (check := true)
      (fuel := fuel)).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WF outEnv ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        ∀ ci, outEnv.find? ``Eq.rec = some ci → IsProductionEqRec ci →
          ves'.HasCanonicalEq :=
  (VerifyInductive.addInductiveDeclaration.eqBootstrapFinalEnvironmentWF env lparams
      nparams types isUnsafe fuel ves wf hch hAbsent Hshape).mono
    fun _ ⟨ves', wf', _, hle, _, hcanonical⟩ => ⟨ves', wf', hle, hcanonical⟩

end Lean4Lean
