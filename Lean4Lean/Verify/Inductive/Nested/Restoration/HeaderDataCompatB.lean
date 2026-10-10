import Lean4Lean.Verify.Inductive.Nested.Restoration.Lookups

/-! # Source-branch accessors of the lowered run (fork B)

The source branch's `HeaderEnvironment.commonParameterContext` (`Install/ParameterContext.lean`)
on the target's `HeaderData`, and the source's `LoweredRun.Phases`/`NestedRun.phases`
(`Lowering/Phases.lean`, `Install/RunView.lean`) on `LoweredView`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The common parameter context recorded by the header phase of a block
(in context order). -/
def HeaderData.commonParameterContext
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams : Nat} {isUnsafe : Bool} {depth : Nat}
    {sourceEnv : VEnv} {indTypes : Array InductiveType} {outEnv : Environment}
    (H : HeaderData c stats decl nparams isUnsafe depth sourceEnv indTypes outEnv) :
    List VExpr :=
  H.sourceStatsWF.parameterScope.toCtx

/-- The lowered phases at a family array. -/
structure LoweredView.Phases {outEnv : Environment} (P : LoweredView outEnv)
    (indTypes : Array InductiveType) where
  constructors : RecursorInput P.c P.stats P.loweredDecl P.nparams P.isUnsafe P.depth
    P.initialEnv indTypes P.ctorEnv
  check : RecursorCheck constructors outEnv

namespace LoweredView.Phases

variable {outEnv : Environment} {P : LoweredView outEnv} {indTypes : Array InductiveType}

abbrev recursors (Q : P.Phases indTypes) : RecursorInstallation Q.constructors outEnv :=
  Q.check.installation

abbrev headers (Q : P.Phases indTypes) :
    HeaderData P.c P.stats P.loweredDecl P.nparams P.isUnsafe P.depth P.initialEnv indTypes
      Q.constructors.headerEnv :=
  Q.constructors.headers

end LoweredView.Phases

/-- The phases stored by the view. -/
def LoweredView.phases {outEnv : Environment} (P : LoweredView outEnv) : P.Phases P.indTypes :=
  ⟨P.constructors, P.check⟩

/-- Transport the phases across an equality of family arrays. -/
def LoweredView.phasesAt {outEnv : Environment} (P : LoweredView outEnv)
    {indTypes : Array InductiveType} (h : P.indTypes = indTypes) : P.Phases indTypes :=
  Eq.mp (congrArg P.Phases h) P.phases

theorem LoweredView.phasesAt_commonParameterContext {outEnv : Environment}
    (P : LoweredView outEnv) {indTypes : Array InductiveType} (h : P.indTypes = indTypes) :
    (P.phasesAt h).headers.commonParameterContext = P.headers.commonParameterContext := by
  cases h
  rfl

/-- The lowered phases indexed by the nested lowering's result families. -/
def NestedRun.phases
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) : E.lowered.Phases res.types.toArray :=
  E.lowered.phasesAt E.lowered_indTypes

theorem NestedRun.phases_commonParameterContext
    (E : NestedRun res sourceProdEnv sourceTypes sourceEnv decl lparams
      nparams isUnsafe safety outEnv) :
    E.phases.headers.commonParameterContext =
      E.lowered.headers.commonParameterContext :=
  E.lowered.phasesAt_commonParameterContext E.lowered_indTypes

end VerifyInductive
end Lean4Lean
