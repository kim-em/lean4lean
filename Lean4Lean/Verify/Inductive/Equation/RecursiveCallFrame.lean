import Lean4Lean.Verify.Inductive.Equation.Motive

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Final-environment recursor package selected by one generated recursive
call.  Besides the checked call semantics, it retains the literal earlier-
hypothesis suffix from the producer.  Thus the call origin is related to the
rule root by executable allocation history, not by an assumed context
equality. -/
structure
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) where
  originRoot : AddInductive.Context
  originContext : RecursorContextWF originRoot
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
  priorHypotheses : Array Expr
  originRecent : RecursorRecentBoundFVarArray A.semantics.context
    originContext priorHypotheses
  priorHypotheses_size : priorHypotheses.size = j
  callDepth : Nat
  semantic : SemanticBoundGeneratedRecursiveCall indTypes stats
    (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
    (AddInductive.getRecLevels H.elimLevel stats.levels)
    originContext decl callDepth
    A.rule.recursiveArgs[j] A.rule.recursiveResults[j]!
  root_scope : semantic.rootScope = fun fv =>
    fv ∈ A.semantics.fieldOpening.fvars ∨
      fv ∈ ExprArrayFVarIds stats.params
  entry_lt : semantic.generated.ownerIdx < H.entries.length
  telescope : GeneratedRecursorTelescopeTranslation H.outVEnv
    (AddInductive.getRecLevelParams H.elimLevel c.lparams)
    (H.generated.entry semantic.generated.ownerIdx entry_lt).info.type
    H.entries[semantic.generated.ownerIdx].2.type
    stats.params.size (H.recInfos.map (·.motive)).size
    (H.recInfos.flatMap (·.minors)).size
    H.recInfos[semantic.generated.ownerIdx]!.indices.size
    semantic.generated.ownerIdx
  typing :
    let recursor := H.entries[semantic.generated.ownerIdx].2
    H.outVEnv.HasType recursor.uvars []
      (.const recursor.name (VLevel.params recursor.uvars)) recursor.type

/-- The generic extension view is derived from the retained producer trace.
It is not a field or premise of the call frame. -/
def RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.originExtension
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {A : H.GeneratedRuleAlignment owner howner i hctor}
    {j : Nat} {hj : j < A.rule.recursiveArgs.size}
    (F : A.RecursiveCallRecursorFrame j hj) :
    RecursorContextExtension A.semantics.context F.originContext :=
  F.originRecent.contextExtension

theorem
    RecursorPhasesResult.GeneratedRuleAlignment.recursiveCallRecursorFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) :
    Nonempty (A.RecursiveCallRecursorFrame j hj) := by
  rcases A.motiveEvidence with ⟨Hproducer⟩
  rcases Hproducer.calls.entries j hj hj with
    ⟨originRoot, Rorigin, priorHypotheses, Hrecent,
      hpriorSize, callDepth, S, hscope⟩
  have hrecInfo : S.generated.ownerIdx < H.recInfos.size := by
    rw [H.cardinality.records]
    exact S.validated.target_lt
  have hentry : S.generated.ownerIdx < H.entries.length := by
    simpa [H.generated.length] using hrecInfo
  rcases H.finalRecursorTelescopeTranslationAt
      S.generated.ownerIdx hentry with ⟨T⟩
  exact ⟨{
    originRoot := originRoot
    originContext := Rorigin
    priorHypotheses := priorHypotheses
    originRecent := Hrecent
    priorHypotheses_size := hpriorSize
    callDepth := callDepth
    semantic := S
    root_scope := hscope
    entry_lt := hentry
    telescope := T
    typing := H.recursorTypingAt S.generated.ownerIdx hentry }⟩

end VerifyInductive

end Lean4Lean
