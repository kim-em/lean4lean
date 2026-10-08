import Lean4Lean.Verify.Environment

/-! # Realizability of canonical equality

`VEnv.HasCanonicalEq` stores explicit abstract terms for `Eq`, `Eq.refl`,
`Eq.rec` and the iota rule of `Eq.rec`.  This file connects them to the
declaration `Init.Prelude` submits.

* `Lean4Lean/Verify/Inductive/EqCanonicalForms.lean` states the production
  expressions literally (`eqBootstrapType`, `eqBootstrapReflType`,
  `eqRecTypeExpr`, `eqRecRuleRhsExpr`, `eqRecRuleLhsExpr`, `eqRecRuleTypeExpr`,
  generic only in binder and universe-parameter names) and proves that every
  `TrExprS` translation of each of the three types is the corresponding stored
  term (`TrExprS.eq_canonicalEq*`).
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
* `VEnvs.WFCore.canonicalEq_constants` (below): in any well-formed model of an
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
private theorem VEnvs.WFCore.constant_of_production {env : Environment} {ves : VEnvs}
    (wf : ves.WFCore env) {name : Name} {ci : ConstantInfo} {uvars : Nat} {type : VExpr}
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
theorem VEnvs.WFCore.canonicalEq_constants {env : Environment} {ves : VEnvs}
    (wf : ves.WFCore env) {eqInfo reflInfo recInfo : ConstantInfo}
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
type.  Only the absence of `Eq` is assumed of the input, together with the constructor telescope
certificates at every safety level. -/
theorem addDecl.eqBootstrapHasCanonicalEq {env : Environment} {ves : VEnvs}
    (wf : ves.WFCore env) (hcorner : ∀ safety, CtorTelescopes safety env (ves.venv safety))
    (hAbsent : env.constants.find? ``Eq = none)
    {lparams : List Name} {nparams : Nat} {types : List InductiveType} {isUnsafe : Bool}
    (Hshape : VerifyInductive.EqBootstrapShape lparams nparams types isUnsafe)
    (fuel : FuelConfig := {}) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe) (check := true)
      (fuel := fuel)).WF fun outEnv =>
      ∃ ves' : VEnvs, ves'.WFCore outEnv ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        ∀ ci, outEnv.find? ``Eq.rec = some ci → IsProductionEqRec ci →
          ves'.HasCanonicalEq :=
  (VerifyInductive.addInductiveDeclaration.eqBootstrapFinalEnvironmentWF env lparams
      nparams types isUnsafe fuel ves wf hcorner hAbsent Hshape).mono
    fun _ ⟨ves', wf', _, hle, _, hcanonical⟩ => ⟨ves', wf', hle, hcanonical⟩


/-! ### Replays -/

/-- The prelude's `Eq`, `Eq.refl` and `Eq.rec` are declared in `env` with their production
types. -/
def HasProductionEq (env : Environment) : Prop :=
  ∃ eqInfo reflInfo recInfo,
    env.find? ``Eq = some eqInfo ∧ IsProductionEq eqInfo ∧
    env.find? ``Eq.refl = some reflInfo ∧ IsProductionEqRefl reflInfo ∧
    env.find? ``Eq.rec = some recInfo ∧ IsProductionEqRec recInfo

/-- A replay: the declarations `ds` added one after another by the checked `addDecl`, from
`env` to `env'`. A `quotDecl` step records that the prelude's `Eq` is already present
(`HasProductionEq`): `quotDecl` is modelled by an abstract rule that types `Quot.lift` against
`Eq`, so before `Eq` exists it has no model (and the executable rejects it, `checkEqType`). -/
inductive Replay : Environment → List Declaration → Environment → Prop
  | nil (env : Environment) : Replay env [] env
  | cons {env env₁ env₂ : Environment} {d : Declaration} {ds : List Declaration} :
    addDecl env d (check := true) (fuel := {}) = .ok env₁ →
    (d = .quotDecl → HasProductionEq env) →
    Replay env₁ ds env₂ → Replay env (d :: ds) env₂

/-- Every step of a replay preserves `VEnvs.WF`. -/
theorem Replay.WF {env env' : Environment} {ds : List Declaration}
    (H : Replay env ds env') {ves : VEnvs} (wf : ves.WF env) :
    ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  induction H generalizing ves with
  | nil => exact ⟨ves, wf, fun _ => VEnv.LE.rfl⟩
  | @cons env env₁ env₂ d ds hadd hquot _ ih =>
    have hq : d = .quotDecl → ∀ safety, (ves.venv safety).QuotReady := fun hd safety => by
      obtain ⟨_, _, _, hEq, hEqP, hRefl, hReflP, hRec, hRecP⟩ := hquot hd
      exact (wf.toWFCore.canonicalEq_constants hEq hEqP hRefl hReflP hRec hRecP safety).1
    obtain ⟨ves₁, wf₁, hle₁, hcert⟩ :=
      addDecl.WF_quotReadyAt wf.toWFCore wf.ctorCert d hq _ hadd
    obtain ⟨ves₂, wf₂, hle₂⟩ := ih ⟨wf₁, hcert wf.ctorCert⟩
    exact ⟨ves₂, wf₂, fun safety => (hle₁ safety).trans (hle₂ safety)⟩

/-- **Replay from the empty environment.** Every environment reached by a replay from the
empty environment the executable starts from (`lake exe lean4lean --fresh`) is modelled by
well-formed abstract environments. -/
theorem Replay.WF_empty {m : Name} {s : Bool} {ds : List Declaration} {env : Environment}
    (H : Replay (Kernel.Environment.empty m s) ds env) :
    ∃ ves : VEnvs, ves.WF env :=
  let ⟨ves, wf, _⟩ := H.WF (VEnvs.WF.empty m s)
  ⟨ves, wf⟩

end Lean4Lean
