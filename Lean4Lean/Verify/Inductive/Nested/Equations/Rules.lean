import Lean4Lean.Verify.Inductive.Nested.Restoration.Certificate
import Lean4Lean.Theory.Inductive.RestorationInterpretation
import Lean4Lean.Theory.Typing.RestorationShapes
import Lean4Lean.Theory.Inductive.RestorationHead

/-! # The typing of the restored rules (owner: Equations+Install)

The restored ι rules are typed by transport along the restoration interpretation
(`Theory/Inductive/RestorationInterpretation.lean`): the lowered run's rules are typed in its
recursor stage (`RuleTranslations.rules_wf`, `equationsWF`), the restoration substitution from
the lowered recursor stage `L.recursors.outVEnv` into the restored recursor stage `B.envR`
(`Restoration.Substitution`, with `PatClause` for the lowered rules as `RestoredPattern`s)
carries them to their restorations (`Restoration.equation_wf`), and the restored rules are
the restored equations (`RestoredBlock.rules_ofRestoredEquation`). Source branch:
`Nested/Restoration/Equations/{WF,RestoredRules,RestoredRulesBase,GeneratedGuard,RuleRhs,
SourceIota,SourceIotaFamilies,AuxiliaryConstructors,ProjNames,ProjectionRenaming}.lean`,
stated for `VDefEq`; here the `PatTyped` restatement follows the ordinary path
(`Rules/IotaPatTyped.lean`). -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

namespace RestoredBlock

variable {c : AddInductive.Context} {Hc : ContextWF c} {nparams : Nat}
  {res : ElimNestedInductive.Result} {loweredEnv : Environment}
  {L : LoweredRun Hc nparams res.types.toArray loweredEnv}
  {sourceTypes : List InductiveType} {isUnsafe : Bool} {outEnv : Environment}

/-- `VInductDecl.WF.rules_wf` for the restored rules, in the restored recursor stage. -/
theorem rulesWF (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    ∀ r ∈ B.decl.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
      B.envR.PatTyped
        (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
        (SimplePattern.iotaRHS r.name ru.ctor r.numParams r.numMotives r.numMinors
          r.numIndices ru.ctorParams ru.nfields ru.rhs hc, .true) := by
  -- WAVE 3 STUB (Equations+Install): the restoration substitution
  -- (`NestedRun.restoredEquationSubstitution`, `restoredEquationsWF_of_substitutionPremises`
  -- of the source branch's `Equations/WF.lean`, with `RestoredPattern.clause` in place of the
  -- eliminator clause) transports `L.rules.rules_wf`; `Instance.equation_patTyped`
  -- (`Rules/IotaPatTyped.lean`) restates the typed restored equation as `PatTyped`.
  have := B; sorry

/-- The restored block is well formed: its equations are typed in the restored recursor
stage. -/
theorem blockWF (B : RestoredBlock L sourceTypes isUnsafe outEnv) : B.block.WF Hc.venv := by
  -- WAVE 3 STUB (Equations+Install): `Restoration.equation_wf` along the restoration
  -- substitution for each `L.rules.equationsWF`, with the stages of `B.addInduct` and
  -- `CompilationData.types/ctors/projections/recursors`.
  have := B; sorry

/-- `VInductDecl.WF` of the restored declaration. -/
theorem wf' (B : RestoredBlock L sourceTypes isUnsafe outEnv) (hsource : sourceTypes ≠ []) :
    B.decl.WF Hc.venv :=
  B.wf hsource B.rulesWF

/-- The compiled block with its typing, for `BlockCertificate.compiled`. -/
theorem compiledWF (B : RestoredBlock L sourceTypes isUnsafe outEnv) :
    ∃ block, B.decl.CompilesTo Hc.venv block ∧ B.decl.RecsOf block ∧ block.WF Hc.venv :=
  ⟨B.block, B.compilesTo, B.recsOf, B.blockWF⟩

end RestoredBlock
end VerifyInductive
end Lean4Lean
