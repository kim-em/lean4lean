import Lean4Lean.Verify.Inductive.Nested.EquationRestorationRhs
import Lean4Lean.Verify.Inductive.Nested.EquationRestorationSeeds

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Exact join between a canonical generated equation and the source
endpoint selected while interpreting its production restoration trace.

These equalities must be fixed when the restoration package is constructed:
translation of projections is only definitionally-equal unique, which is not
enough to transport the syntactic guarded-iota judgment after the fact. -/
structure GeneratedEquationRestorationAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {generatedRule : VDefEq}
    (G : H.GeneratedEquationWitness Us owner howner i hctor generatedRule)
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {auxRec : NameMap Name}
    {oldRecName newRecName : Name}
    {oldConcreteRule newConcreteRule : RecursorRule}
    {Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldConcreteRule newConcreteRule}
    {sourceEnv targetEnv : VEnv}
    (Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us) :
    Prop where
  source_context : G.translation.domains.reverse = Hrhs.sourceScope.toCtx
  source_body : G.translation.rhsBody = Hrhs.sourceBody

/-- The exact generated-equation join transports its independently proved
body typing to the restoration source endpoint. -/
theorem GeneratedEquationRestorationAlignment.sourceTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {generatedRule : VDefEq}
    {G : H.GeneratedEquationWitness Us owner howner i hctor generatedRule}
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {auxRec : NameMap Name}
    {oldRecName newRecName : Name}
    {oldConcreteRule newConcreteRule : RecursorRule}
    {Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldConcreteRule newConcreteRule}
    {sourceEnv targetEnv : VEnv}
    {Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us}
    (A : GeneratedEquationRestorationAlignment G Hrhs)
    (henv : H.outVEnv ≤ sourceEnv) :
    sourceEnv.HasType generatedRule.uvars Hrhs.sourceScope.toCtx
      Hrhs.sourceBody G.translation.typeBody := by
  have Htyped := (G.openRhsTyping).2.mono henv
  simpa only [A.source_context, A.source_body] using Htyped

/-- Exact join between the staged old-recursor semantics and the source body
chosen for restoration.  This is the guardedness counterpart of
`GeneratedEquationRestorationAlignment`. -/
structure StagedEquationRestorationAlignment
    (Hgenerated : BoundGeneratedRecursorRule indTypes stats motives minors
      lvls sourceCtor minorIdx sourceConcreteRule)
    (Hstaged : Hgenerated.StagedIotaRuleTranslation trEnv Us Δ semanticEnv
      decl oldBlock owner ctor generatedRule)
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {auxRec : NameMap Name}
    {oldRecName newRecName : Name}
    {oldConcreteRule newConcreteRule : RecursorRule}
    {Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldConcreteRule newConcreteRule}
    {sourceEnv targetEnv : VEnv}
    (Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us)
    (sourceRecursors : List Name) :
    Prop where
  source_recursors : sourceRecursors = oldBlock.recursors.map (·.name)
  source_body : Hstaged.equation.shape.rhsBody = Hrhs.sourceBody

/-- The staged join supplies syntactic guardedness of the exact restoration
source body against the old generated recursor names. -/
theorem StagedEquationRestorationAlignment.sourceGuarded
    (A : StagedEquationRestorationAlignment Hgenerated Hstaged Hrhs
      sourceRecursors) :
    Nonempty (∃ fieldVars,
      Hrhs.sourceBody.GuardedIota
        sourceRecursors fieldVars 0) := by
  rcases Hgenerated.stagedRhsGuarded Hstaged with
    ⟨fieldVars, Hguarded⟩
  exact ⟨fieldVars, by
    simpa only [A.source_recursors, A.source_body] using Hguarded⟩

end VerifyInductive
end Lean4Lean
