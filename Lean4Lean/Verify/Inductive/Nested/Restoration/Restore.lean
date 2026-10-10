import Lean4Lean.Verify.Inductive.Nested.Restoration.Certificate
import Lean4Lean.Verify.Inductive.Nested.Restoration.Validation.Passes
import Lean4Lean.Verify.Inductive.Nested.Restoration.RunOfRestoration
import Lean4Lean.Verify.Inductive.Nested.Restoration.SourceParametersRun
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyBase
import Lean4Lean.Verify.Inductive.Nested.Restoration.TableAgreement
import Lean4Lean.Verify.Inductive.Nested.Restoration.KernelData
import Lean4Lean.Verify.Inductive.Nested.Restoration.FormationWithRecs
import Lean4Lean.Verify.Inductive.Nested.Restoration.ViewCast
import Lean4Lean.Verify.Inductive.Nested.Restoration.AssemblyTypes

/-! # The restored block of a nested run (owner: Restoration-B)

The boundary theorem of the restoration: a lowered run `L` on the lowered block, a successful
restoration `V` and the lowering's certificate `Hout` yield the `RestoredBlock`. The source
branch's material is `Nested/Restoration/**` minus `Equations/` and the Restoration-A files:
the refinement of the restoration folds (`Steps.lean`: `restoreNestedDeclarations_refines`,
`FreshExtension`, `NestedRestorationFolds`), the restored source declaration
(`SourceDeclaration`, `SourceHeaders`, `SourceConstructors`, `SourceConstructorTypes`,
`SourceTranslations`, `HeaderRenaming`, `InstalledFamilyLookups`, `InstalledConstructorTypes`),
the specialization table (`Tables`, `TableAgreement`, `ContainerSpecializations`,
`AuxiliaryHeaders`, `AuxiliaryConstructors`, `AuxiliaryProjections`, `ExpansionInverse`,
`Commutation*`, `TranslationPreservation`, `Translations`, `HeadTranslation`), the restored
recursors (`Recursors`, `RecursorTypes`, `RecursorRenaming`, `RecursorShape`,
`RecursorAlignment`, `AuxiliaryRecursorsWF`, `TrRestoredRecursorVal`, `LoweredRuleAvoidance`,
`Nonprimitive`), the compilation data (`CompilationData`, `CompilationDataConstructors`,
`ConstructorTelescopes`, `ConstructorTranslations`, `FreshExtensions`, `ExprReplace`,
`ParameterOpening`), and `Install/{Permutation,RecursorTranslations,DependencyOrder,
ConstructorCoherence}.lean` for the kernel order and the recursor translations. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The checker context of the nested branch: the executable's own
(`Environment.addInductiveAfterLowering`, with `allowPrimitive := false`). -/
abbrev nestedContext (env : Environment) (lparams : List Name) (isUnsafe : Bool)
    (fuel : FuelConfig) : AddInductive.Context :=
  initialContext env lparams (if isUnsafe then .unsafe else .safe) false fuel

/-- **The restoration boundary theorem.** -/
theorem nestedRestoredBlock {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {lparams : List Name} {nparams : Nat} {sourceTypes : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {res : ElimNestedInductive.Result} {loweredEnv outEnv : Environment}
    (Hsources : SourceSyntaxChecks env sourceTypes)
    (Hout : NestedLoweringOutput env fuel.inductiveFuel nparams sourceTypes lparams res)
    (hnested : res.aux2nested.size ≠ 0)
    (L : LoweredRun (ContextWF.initial wf (if isUnsafe then .unsafe else .safe) lparams false
      fuel) nparams res.types.toArray loweredEnv)
    (V : RestorationRun res loweredEnv env lparams sourceTypes
      (if isUnsafe then .unsafe else .safe) false fuel outEnv) :
    Nonempty (RestoredBlock L sourceTypes isUnsafe outEnv) := by
  have := hnested
  obtain ⟨runDecl, E, hloweredEnv, hlowered⟩ := NestedRun.ofRestoration wf Hsources Hout hnested L V
  have Hchecked := checkInductiveSources_refines env sourceTypes _ Hsources
  have Hparameters := E.sourceParameterWF wf Hchecked
  obtain ⟨⟨B, hBlowered, hBperm⟩⟩ := E.assemblyBase wf rfl Hsources Hparameters (by cases isUnsafe <;> decide)
  obtain ⟨hperm, hfresh, hmap, hquot⟩ :=
    E.restoration.kernelOrder (ContextWF.initial wf (if isUnsafe then .unsafe else .safe) lparams
      false fuel).map_wf
  have hdeclLowered : E.lowered.loweredDecl = L.loweredDecl :=
    LoweredView.heq_field hloweredEnv hlowered (·.loweredDecl)
  -- WAVE 3 STUB (restB): the restored recursors (`AssemblyRecursors`, in progress).
  obtain ⟨recs⟩ : Nonempty (List VRecursor) := sorry
  refine ⟨{
    decl := runDecl.withRecs recs
    envTypes := E.sourceCore.envTypes
    envCtors := E.sourceCore.envCtors
    source := ?source
    formation := VerifyInductive.NestedFormationWF.withRecs recs B.formationAssembly.formation
    auxiliaries := ?auxiliaries
    containers := ?containers
    block := ?block
    compiled := ?compiled
    recsOf := ?recsOf
    ivals := E.restoration.ivals
    rvals := E.restoration.rvals
    trTypes := E.trTypes B hBlowered
    envR := ?envR
    recsAdded := ?recsAdded
    trRecs := ?trRecs
    order := E.restoration.entries
    order_perm := hperm
    fresh := hfresh
    map_eq := hmap
    quotInit_eq := hquot
    newUnsafe := ?newUnsafe
    recs_wf := ?recs_wf
    rec_shape := ?rec_shape
    rules_nodup := ?rules_nodup
    rules_ctor := ?rules_ctor
    rules_ctorParams := ?rules_ctorParams
    rule_shape := ?rule_shape
    rules_closed := ?rules_closed
    outVEnv := ?outVEnv
    rulesAdded := ?rulesAdded
    recShapes := ?recShapes
    recK := ?recK
    runDecl := runDecl
    run := E
    run_decl := ?run_decl
    sourceSyntaxChecked := Hchecked
    constructorArityPrefix := ?arity
    run_loweredEnv := hloweredEnv
    run_lowered := hlowered
    recMajor := ?recMajor
    constructorParameterAlignment := ?alignment }⟩
  case arity =>
    have h := B.formationAssembly.constructorArityPrefix
    rw [B.formationExpanded, hBlowered, hdeclLowered] at h
    exact h
  case run_decl => simp [VInductDecl.withRecs]
  case source =>
    have h := E.sourceCore.core
    rw [E.sourceCoreDecl_eq] at h
    exact TrInductDeclCore.withRecs h recs
  -- WAVE 3 STUB (restB): `trTypes`/`newUnsafe` (`AssemblyTypes`) and the recursor, rule and
  -- compilation fields (`AssemblyRecursors`), in progress.
  all_goals sorry

end VerifyInductive
end Lean4Lean
