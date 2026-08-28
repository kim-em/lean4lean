import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaTrace
import Lean4Lean.Verify.Typing.EnvironmentRestriction

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Source typing for restored primary iota rules

This module isolates the two legitimate ways in which typing of the generated
left-hand side can be reused after nested restoration.

The target telescope produced by the restoration trace directly supplies
context well-formedness.  Typing of the left-hand side may be transported from
the generated equation only when the particular derivations avoid every
constant whose interpretation changed and the remaining environment is
preserved.  This derivation-scoped condition is deliberately weaker than
environment inclusion, and does not assert the generally false relation from
the lowered output environment to the restored one.
-/

/-- Dependency evidence for every typehood derivation in an `OnCtx` proof. -/
def OnCtxIsTypeUsesOnly {env : VEnv} {uvars : Nat}
    (changed : Name → Prop) {Γ : List VExpr}
    (H : OnCtx Γ (env.IsType uvars)) : Prop :=
  match Γ with
  | [] => True
  | _ :: _ =>
      OnCtxIsTypeUsesOnly changed H.1 ∧ H.2.UsesOnly changed

/-- Rebase a well-formed context across an environment replacement, provided
the exact retained derivations avoid all replaced constants. -/
theorem rebaseOnCtxExcept
    (E : VEnv.LEExcept changed sourceEnv targetEnv)
    : ∀ {Γ}, (H : OnCtx Γ (sourceEnv.IsType uvars)) →
      OnCtxIsTypeUsesOnly changed H →
      OnCtx Γ (targetEnv.IsType uvars)
  | [], _, _ => trivial
  | _ :: _, H, HU =>
    ⟨rebaseOnCtxExcept E H.1 HU.1, H.2.rebaseExcept E HU.2⟩

/-- The target telescope already present in structural restoration evidence
discharges source-context well-formedness after the exact domain and universe
alignments.  Only LHS typing remains to construct the source-typing package. -/
theorem RestoredPrimaryIotaSourceTyping.ofTargetScopeLhs
    {decl : VInductDecl} {block : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {sourceRule : VDefEq}
    {Hsource : decl.NestedIotaRule block owner ctor sourceRule}
    {targetEnv : VEnv} {Us : List Name} {targetScope : VLCtx}
    (HtargetContext :
      (abstractForallContext [] targetScope).WF targetEnv Us.length)
    (huvars : Us.length = sourceRule.uvars)
    (hdomains : targetScope.toCtx.reverse = Hsource.domains)
    (Hlhs : targetEnv.HasType sourceRule.uvars Hsource.domains.reverse
      Hsource.lhsBody Hsource.typeBody) :
    RestoredPrimaryIotaSourceTyping targetEnv Hsource := by
  have hscope : targetScope.toCtx = Hsource.domains.reverse := by
    simpa using congrArg List.reverse hdomains
  have Hctx : OnCtx targetScope.toCtx
      (targetEnv.IsType Us.length) := by
    simpa using HtargetContext.toCtx
  exact {
    contextWF := by simpa [hscope, huvars] using Hctx
    lhsTyping := Hlhs }

/-- Exact generated-facing residual for source typing.  The restoration trace
checks the target telescope, while `GeneratedNestedIotaSource` identifies all
three generated bodies with the independently specified source bodies.
Consequently the sole remaining judgment is typing the generated LHS in the
restored target environment.

This theorem is useful when that judgment is reconstructed from the restored
recursor and constructor certificates: the caller need not separately prove
context well-formedness or repeat any body-alignment rewrites. -/
theorem RecursorPhasesResult.GeneratedNestedIotaSource.sourceTypingOfTargetLhs
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {generatedOwner : Nat}
    {howner : generatedOwner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[generatedOwner]!.ctors.length}
    {generatedRule : VDefEq}
    {G : H.GeneratedEquationWitness Us generatedOwner howner i hctor
      generatedRule}
    {sourceDecl : VInductDecl} {sourceBlock : VInductBlock}
    {sourceOwner : VInductiveType} {sourceCtor : VConstVal}
    (S : H.GeneratedNestedIotaSource G sourceDecl sourceBlock sourceOwner
      sourceCtor)
    {targetEnv : VEnv} {targetScope : VLCtx}
    (HtargetContext :
      (abstractForallContext [] targetScope).WF targetEnv Us.length)
    (hdomains : targetScope.toCtx.reverse = S.source.domains)
    (Hlhs : targetEnv.HasType generatedRule.uvars
      G.translation.domains.reverse G.translation.lhsBody
      G.translation.typeBody) :
    RestoredPrimaryIotaSourceTyping targetEnv S.source := by
  apply RestoredPrimaryIotaSourceTyping.ofTargetScopeLhs
    HtargetContext S.uvars hdomains
  simpa only [S.domains, S.lhsBody, S.typeBody, S.uvars] using Hlhs

/-- Non-monotone, derivation-scoped transport of the generated open context
and LHS typing.  `LEExcept` preserves definitional equations and lookups away
from `changed`; the two `UsesOnly` witnesses certify that these particular
typing derivations never inspect a changed lookup.

This is the strongest valid generic transport theorem for a generated nested
iota source.  Plain body equality cannot change the environment indexing a
typing judgment. -/
theorem RecursorPhasesResult.GeneratedNestedIotaSource.sourceTypingOfRebase
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {generatedOwner : Nat}
    {howner : generatedOwner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[generatedOwner]!.ctors.length}
    {generatedRule : VDefEq}
    {G : H.GeneratedEquationWitness Us generatedOwner howner i hctor
      generatedRule}
    {sourceDecl : VInductDecl} {sourceBlock : VInductBlock}
    {sourceOwner : VInductiveType} {sourceCtor : VConstVal}
    (S : H.GeneratedNestedIotaSource G sourceDecl sourceBlock sourceOwner
      sourceCtor)
    {targetEnv : VEnv} {changed : Name → Prop}
    (E : VEnv.LEExcept changed H.outVEnv targetEnv)
    (HctxUses : OnCtxIsTypeUsesOnly changed G.openRhsTyping.1)
    (HlhsUses : G.openLhsTyping.UsesOnly changed) :
    RestoredPrimaryIotaSourceTyping targetEnv S.source := by
  have Hctx := rebaseOnCtxExcept E G.openRhsTyping.1 HctxUses
  have Hlhs := G.openLhsTyping.rebaseExcept E HlhsUses
  exact {
    contextWF := by
      simpa only [S.domains, S.uvars] using Hctx
    lhsTyping := by
      simpa only [S.domains, S.lhsBody, S.typeBody, S.uvars] using Hlhs }

/-- Combine the exact target telescope from an RHS restoration with the
derivation-scoped generated LHS transport.  This version does not ask for a
dependency certificate for the generated context, because the target trace
has already checked that context in the correct restored environment. -/
theorem RecursorPhasesResult.GeneratedNestedIotaSource.sourceTypingOfTargetScope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {generatedOwner : Nat}
    {howner : generatedOwner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[generatedOwner]!.ctors.length}
    {generatedRule : VDefEq}
    {G : H.GeneratedEquationWitness Us generatedOwner howner i hctor
      generatedRule}
    {sourceDecl : VInductDecl} {sourceBlock : VInductBlock}
    {sourceOwner : VInductiveType} {sourceCtor : VConstVal}
    (S : H.GeneratedNestedIotaSource G sourceDecl sourceBlock sourceOwner
      sourceCtor)
    {result : Lean4Lean.ElimNestedInductive.Result}
    {prodEnv : Environment} {auxRec : NameMap Name}
    {oldRecName newRecName : Name}
    {oldConcreteRule newConcreteRule : RecursorRule}
    {Hrule : RuleRestoration result prodEnv auxRec oldRecName newRecName
      oldConcreteRule newConcreteRule}
    {sourceEnv targetEnv : VEnv}
    {Hrhs : RestoredRuleRhsTranslation result prodEnv auxRec oldRecName
      newRecName oldConcreteRule newConcreteRule Hrule sourceEnv targetEnv Us}
    (HtargetContext :
      (abstractForallContext [] Hrhs.targetScope).WF targetEnv Us.length)
    (hdomains : Hrhs.targetScope.toCtx.reverse = S.source.domains)
    {changed : Name → Prop}
    (E : VEnv.LEExcept changed H.outVEnv targetEnv)
    (HlhsUses : G.openLhsTyping.UsesOnly changed) :
    RestoredPrimaryIotaSourceTyping targetEnv S.source := by
  have Hlhs := G.openLhsTyping.rebaseExcept E HlhsUses
  exact S.sourceTypingOfTargetLhs HtargetContext hdomains Hlhs

end VerifyInductive
end Lean4Lean
