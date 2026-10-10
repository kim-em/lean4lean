import Lean4Lean.Verify.Inductive.Nested.Equations.Rules

/-! # The environment-side facts of a restored block and its block certificate (owner: Install)

`RestoredBlock.Installed` collects what `InstalledBlocks.addInduct` and `BlockCertificate` read
of the output environment beyond the restored block's own data: the checking invariant of the
output over the output model, closure, constructor owners, the origin of every new header
(`InductInfosFromDecl`), the cover of the declaration's families, the majors of the new
recursors and the constructor parameter alignment. `RestoredBlock.installedFacts` produces it (the
stub of this file); `RestoredBlock.blockCertificate` assembles PR #43's `BlockCertificate`
from it, the restored block and the Equations owner's rule typing (proved), after which the
ordinary path's `BlockCertificate.extendSafeExact`/`extendUnsafeExact` install the block.

Source branch: `Nested/Install/{BlockCertificate,FromRun,DependencyOrder,ConstructorCoherence,
Result}.lean` (`RestoredBlockCertificate.inductInfosFromDecl`, `.cover`,
`NestedRestorationFolds.constructorOwnersPresentOfContext`,
`NestedInstalledRun.constructorParameterDomainsDefEqOfSource`, the `CheckingEnv.Valid` of the
restored output through `InstalledBlocks.addCtorStage`-style staging). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace RestoredBlock

variable {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
  {res : ElimNestedInductive.Result} {loweredEnv : Environment}
  {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
  {sourceTypes : List InductiveType} {isUnsafe : Bool} {outEnv : Environment}

/-- The environment-side facts of a restored block (see the module documentation). -/
structure Installed (B : RestoredBlock L sourceTypes isUnsafe outEnv) : Prop where
  checking : CheckingEnv.Valid c.safety outEnv B.outVEnv
  closed : MutualInductivesClosed outEnv
  constructorOwners : ConstructorOwnersPresent outEnv
  inductInfosFromDecl : InductInfosFromDecl c.env.constants outEnv.constants B.decl
  cover : ∀ T ∈ B.decl.types,
    ∃ v, outEnv.find? T.name = some (.inductInfo v) ∧ c.env.find? T.name = none
  recMajor : ∀ {n r}, outEnv.find? n = some (.recInfo r) → c.env.find? n = none →
    ∃ info, outEnv.find? r.getMajorInduct = some (.inductInfo info)
  constructorParameterAlignment : ConstructorParameterAlignment c.safety c.env Hc.venv →
    ConstructorParameterAlignment c.safety outEnv B.outVEnv

/-- **The installation boundary theorem**: the output of a nested restoration is a valid
checking environment with the environment-side facts of the restored block. -/
theorem installedFacts (B : RestoredBlock L sourceTypes isUnsafe outEnv)
    (hsource : sourceTypes ≠ [])
    (hvisible : c.safety ≤ (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    B.Installed := by
  -- WAVE 3 STUB (Install): `CheckingEnv.Valid` of the restored output over the rule stage
  -- (`Hc.checking` extended along `B.addInduct`, as `RecursorCheck.blockCertificate` does with
  -- `CheckingEnv.Valid.addRules` and `TrEnv'.induct` of `B.wf'`), closure and owners from the
  -- restored `inductInfo`s (`all := the source names`, `order`), `InductInfosFromDecl` and
  -- `cover` from `B.trTypes`/`B.map_eq`, the majors from `B.trRecs`, the alignment from the
  -- source constructor types (`validateSourceConstructorTypes`) and the source model's.
  have := B; have := hsource; have := hvisible; sorry

/-- A new constant of the output is one of the block's (`B.addInduct.find?`). -/
theorem newRec (B : RestoredBlock L sourceTypes isUnsafe outEnv) (I : B.Installed)
    {n : Name} {r : RecursorVal} (h1 : outEnv.find? n = some (.recInfo r))
    (h2 : c.env.find? n = none) : r ∈ B.rvals := by
  have hwf : c.env.constants.WF := Hc.map_wf
  have houtWF : outEnv.constants.WF := I.checking.tr.map_wf
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?] at h1
  rw [Lean.Kernel.Environment.find?, hwf.find?'_eq_find?] at h2
  rcases B.addInduct.find? hwf h1 with hold | ⟨hmem, -⟩
  · rw [h2] at hold; cases hold
  · rcases AddInduct.mem_consts.1 hmem with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ | ⟨rval, hrval, h⟩
    · cases h
    · cases h
    · cases h; exact hrval

/-- **The block certificate of a restored block.** -/
def blockCertificate (B : RestoredBlock L sourceTypes isUnsafe outEnv) (I : B.Installed)
    (hsource : sourceTypes ≠ []) :
    BlockCertificate c.safety c.env Hc.venv B.decl outEnv B.outVEnv where
  wf := B.wf' hsource
  add := B.addInduct
  quotInit_eq := B.quotInit_eq
  checking := I.checking
  closed := I.closed
  constructorOwners := I.constructorOwners
  inductInfosFromDecl := I.inductInfosFromDecl
  cover := I.cover
  recMajor := I.recMajor
  constructorParameterAlignment := I.constructorParameterAlignment
  recK h1 h2 := B.recK _ (B.newRec I h1 h2)
  compiled := B.compiledWF
  newUnsafe ci hci := by rw [B.isUnsafe_eq]; exact B.newUnsafe ci hci
  recShapes h1 h2 := B.recShapes _ (B.newRec I h1 h2)

end RestoredBlock
end VerifyInductive
end Lean4Lean
