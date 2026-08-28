import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaGenerated

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-! # Transport of nested iota evidence between block presentations

The source nested equation depends on its containing block only through
membership of the selected recursor and the list of recursor names used by
the guardedness judgment.  This module records that narrow dependency so an
equation can first be recovered against the exact ordinary production block
and transported to the canonical restored block only after endpoint layout
has been established.
-/

/-- Reindex one nested iota rule along equality of the block recursor-name
lists.  No type, constructor, equation-body, or typing evidence changes. -/
def VInductDecl.NestedIotaRule.reblock
    {decl : VInductDecl} {sourceBlock targetBlock : VInductBlock}
    {owner : VInductiveType} {ctor : VConstVal} {rule : VDefEq}
    (H : decl.NestedIotaRule sourceBlock owner ctor rule)
    (hmem : H.recursor ∈ targetBlock.recursors)
    (hnames : targetBlock.recursors.map (·.name) =
      sourceBlock.recursors.map (·.name)) :
    decl.NestedIotaRule targetBlock owner ctor rule := by
  refine { H with
    recursor_mem := hmem
    rhs_guarded := ?_ }
  rw [hnames]
  exact H.rhs_guarded

namespace VerifyInductive

/-- Transport a generated source equation without reopening its ordinary
equation proof.  The retained translation-body equalities are definitionally
unchanged by `reblock`. -/
def RecursorPhasesResult.GeneratedNestedIotaSource.reblock
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {initialEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth initialEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {H : RecursorPhasesResult R outEnv} {Us : List Name}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    {generatedRule : VDefEq}
    {G : H.GeneratedEquationWitness Us owner howner i hctor generatedRule}
    {sourceDecl : VInductDecl} {sourceBlock targetBlock : VInductBlock}
    {sourceOwner : VInductiveType} {sourceCtor : VConstVal}
    (S : H.GeneratedNestedIotaSource G sourceDecl sourceBlock sourceOwner
      sourceCtor)
    (hmem : S.source.recursor ∈ targetBlock.recursors)
    (hnames : targetBlock.recursors.map (·.name) =
      sourceBlock.recursors.map (·.name)) :
    H.GeneratedNestedIotaSource G sourceDecl targetBlock sourceOwner
      sourceCtor := by
  let Hsource := S.source.reblock hmem hnames
  exact {
    source := Hsource
    domains := S.domains
    lhsBody := S.lhsBody
    typeBody := S.typeBody
    uvars := S.uvars }

end VerifyInductive
end Lean4Lean
