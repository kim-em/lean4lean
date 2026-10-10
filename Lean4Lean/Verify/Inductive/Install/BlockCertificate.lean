import Lean4Lean.Verify.Inductive.Rules.RuleTranslations
import Lean4Lean.Verify.Inductive.Install.Result

/-! # The block certificate and its installation into the environment model

`BlockCertificate` is what a complete run of the ordinary pipeline certifies at the checked
safety level: the installed declaration is well formed (`VInductDecl.WF`), PR #43's `AddInduct`
relates the source and output environments (so `TrEnv'.induct` applies), and the facts
`InstalledBlocks.addInduct` (wave 1B) reads of the output. `RecursorCheck.blockCertificate`
assembles it from the recursor and rule phases; `BlockCertificate.extendSafeExact` and
`extendUnsafeExact` install it into the safety-indexed model `VEnvs` ("Assembly" in section 3.2
of the design notes).

Wave 2 scaffold: owned by the `Install/`+`Primitive/`+`Prelude/` agent (source branch:
`Install/{BlockCertificate,Environments,Lookups,Metadata,LiteralNames}.lean`, rewritten against
`AddInduct`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The certificate of an installed block at the checked safety level `safety`. -/
structure BlockCertificate (safety : DefinitionSafety) (env : Environment) (venv : VEnv)
    (decl : VInductDecl) (outEnv : Environment) (outVEnv : VEnv) where
  wf : decl.WF venv
  add : AddInduct safety env.constants venv decl outEnv.constants outVEnv
  quotInit_eq : outEnv.quotInit = env.quotInit
  checking : CheckingEnv.Valid safety outEnv outVEnv
  closed : MutualInductivesClosed outEnv
  constructorOwners : ConstructorOwnersPresent outEnv
  inductInfosFromDecl : InductInfosFromDecl env.constants outEnv.constants decl
  cover : ∀ T ∈ decl.types,
    ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ env.find? T.name = none
  recMajor : ∀ {n r}, outEnv.find? n = some (.recInfo r) → env.find? n = none →
    ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info)
  constructorParameterAlignment : ConstructorParameterAlignment safety env venv →
    ConstructorParameterAlignment safety outEnv outVEnv
  recK : ∀ {n r}, outEnv.find? n = some (.recInfo r) → env.find? n = none →
    KLikeRecursor outEnv.constants outVEnv r

namespace BlockCertificate

variable {safety : DefinitionSafety} {env outEnv : Environment} {venv outVEnv : VEnv}
  {decl : VInductDecl}

theorem installed (H : BlockCertificate safety env venv decl outEnv outVEnv) :
    venv.addInduct decl = some outVEnv := H.add.env_eq

theorem le (H : BlockCertificate safety env venv decl outEnv outVEnv) : venv ≤ outVEnv :=
  H.add.le

theorem inductInstalled (H : BlockCertificate safety env venv decl outEnv outVEnv) :
    outVEnv.InductInstalled decl :=
  VEnv.InductInstalled.of_addInduct H.wf H.installed

/-- The output of a certified block is a valid checking environment with the installed blocks of
the source and the new one: wave 1B's `InstalledBlocks.addInduct`. -/
theorem installedBlocks (H : BlockCertificate safety env venv decl outEnv outVEnv)
    (hblocks : InstalledBlocks safety env venv .complete) (hwf : env.constants.WF)
    (hvisible : safety ≤ (if decl.isUnsafe then DefinitionSafety.unsafe else .safe))
    (hparams : ConstructorParameterAlignment safety env venv) :
    InstalledBlocks safety outEnv outVEnv .complete := by
  refine InstalledBlocks.addInduct hblocks hwf H.checking.tr ?_ H.le H.inductInfosFromDecl
    H.cover H.closed H.constructorOwners (fun h1 h2 => H.recMajor h1 h2)
    (fun _ => ⟨H.wf, H.installed⟩) (fun h => absurd hvisible h)
    (fun _ => H.constructorParameterAlignment hparams) (fun h1 h2 _ => H.recK h1 h2)
  -- WAVE 2 STUB (Install): `hpres`, every constant of `env` is a constant of `outEnv`, from
  -- `AddInduct.map_eq`/`fresh` (`insertConsts_find?_mono_of_fresh`).
  sorry

/-- Replay a certified safe block in a larger model at a lower safety level: the names are
fresh there too (both environments are aligned with the same constant map), the translations
are monotone, and the stages succeed on the same abstract constants. -/
theorem rebase (H : BlockCertificate .safe env venv decl outEnv outVEnv)
    {safety : DefinitionSafety} {venv' : VEnv} (hvalid : CheckingEnv.Valid safety env venv')
    (hle : venv ≤ venv') :
    ∃ outVEnv', Nonempty (BlockCertificate safety env venv' decl outEnv outVEnv') ∧
      outVEnv ≤ outVEnv' := by
  -- WAVE 2 STUB (Install): the source branch's `BlockCertificate.rebaseAddInductSafe`
  -- (`Install/BlockCertificate.lean`), now on `AddInduct`.
  have := H; have := hvalid; have := hle; sorry

/-- A certified safe block extends the whole safety-indexed model: the block is replayed at
every safety level (`rebase`) and `VEnvs.WF.extendInductExact` assembles the models. -/
theorem extendSafeExact {ves : VEnvs}
    (H : BlockCertificate .safe env (ves.venv .safe) decl outEnv outVEnv)
    (wf : ves.WF env) (hsafe : decl.isUnsafe = false) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      ves'.venv .safe = outVEnv := by
  -- WAVE 2 STUB (Install): `rebase` at `.partial` and `.unsafe`, then
  -- `VEnvs.WF.extendInductExact` with `installedBlocks` at each level.
  have := H; have := wf; have := hsafe; sorry

/-- A certified unsafe block extends the unsafe model and is hidden from the partial and safe
observers (`VEnvs.WF.extendUnsafeExact`): every inserted constant is unsafe, so the other two
translations are extended by `TrEnv'.ignore`. -/
theorem extendUnsafeExact {ves : VEnvs}
    (H : BlockCertificate .unsafe env (ves.venv .unsafe) decl outEnv outVEnv)
    (wf : ves.WF env) (hunsafe : decl.isUnsafe = true) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      ves'.venv .unsafe = outVEnv := by
  -- WAVE 2 STUB (Install): the source branch's `BlockCertificate.extendUnsafeOfHiddenExact`.
  have := H; have := wf; have := hunsafe; sorry

end BlockCertificate

/-- The environment after the rules are registered: the output of `addInduct` for the
recursor check's declaration (`RecursorCheck.decl'`), given that `addRules` succeeds
(`rules_closed`). -/
def RecursorCheck.outVEnv'
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) : VEnv :=
  ((decl.withRecs H.recs).addRules H.outVEnv).getD H.outVEnv

/-- The source branch's `OrdinaryInstallation.extend*Exact` read the block certificate off the
recursor check and the rule translations: this is that assembly. The installed declaration is
`H.decl'` (the constructor phase's declaration with the generated recursors). -/
theorem RecursorCheck.blockCertificate
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {ctorEnv outEnv : Environment}
    {R : ConstructorCheck c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : RecursorCheck R outEnv) (T : RuleTranslations H)
    (hnonempty : indTypes.toList ≠ []) :
    Nonempty (BlockCertificate c.safety c.env sourceEnv H.decl' outEnv H.outVEnv') := by
  -- WAVE 2 STUB (Install): `decl'.WF` from `R.formation.wf` (`FormationCertificate.wf`, the
  -- source judgment by `TrInductDeclCore.sourceWF_ofNonempty`, the recursor half by
  -- `T.recursorsWF`); `AddInduct` from the stages (`R.core`, `R.trTypes`, `H.recsAdded`,
  -- `H.trRecs`, `addRules` of closed reducts, which makes `outVEnv'` the output of
  -- `addRules`), `order := consts`, `map_eq` from the three `insertConsts` equations and
  -- `fresh` from the three freshness facts.
  have := T; have := hnonempty; sorry

end VerifyInductive
end Lean4Lean
