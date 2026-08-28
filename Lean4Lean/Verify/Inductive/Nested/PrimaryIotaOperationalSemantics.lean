import Lean4Lean.Verify.Inductive.Nested.PrimaryIotaConstructorAlignment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Source semantics indexed by the primary-iota operational trace

The ordinary source semantic trace and the lowering/restoration trace used to
be consumed independently.  That loses the proof that a translated abstract
constructor came from the very restoration step used by the corresponding
primary equation.  This module joins them once, at family scope, and exposes a
pointwise selector which preserves that identity.
-/

/-- Family semantics retaining the complete operational recursor alignment
and a lockstep constructor trace whose source translation is indexed by the
same lowering/restoration step. -/
structure RestoredPrimaryOperationalFamilySemantics
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv canonicalEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv}
    (A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep)
    (owner : VInductiveType)
    (Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
      Hstep.restored.recursor canonicalEnv) : Prop where
  constructors : RestoredConstructorSemanticMappingTrace result
    loweredSourceEnv loweredEnv result.params nparams c.safety c.lparams
      canonicalEnv sourceTypes[familyIdx].ctors A.stepState A.target.ctors
        A.loweredState Hstep.restored.headerEnv
          Hstep.restored.constructorEnv owner.ctors

/-- Re-run the already established source translations over the exact
operational constructor trace.  No semantic witness is selected afresh: the
result is indexed by `A.constructors`, hence by the same `Hstep` and lowering
state as the restored primary recursor. -/
theorem RestoredPrimaryOperationalFamilyAlignment.withSourceSemantics
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv canonicalEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv}
    (A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep)
    (owner : VInductiveType)
    (Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
      Hstep.restored.recursor canonicalEnv)
    (Hconstructors : RestoredSourceConstructorTrace result loweredEnv c.lparams c.safety
      canonicalEnv Hstep.oldInfo.ctors Hstep.restored.headerEnv
        Hstep.restored.constructorEnv sourceTypes[familyIdx].ctors owner.ctors)
    (Hsyntax : SourceConstructorSyntaxes sourceTypes[familyIdx].ctors)
    (Hdisjoint : ∀ source ∈ sourceTypes[familyIdx].ctors,
      RestoreSourceDisjoint result loweredEnv source.type)
    (hresultNParams : result.nparams = nparams) :
    RestoredPrimaryOperationalFamilySemantics A owner Hrecursor := by
  refine { constructors := ?_ }
  apply A.constructors.sourceSemanticMapping Hconstructors.forall₂ Hsyntax
    Hdisjoint rfl A.fvars A.params A.paramsNodup hresultNParams

/-- Select one constructor while retaining all three identities at once:
the original source constructor, its lowered/restored operational step, and
the independently translated abstract source constructor. -/
theorem RestoredPrimaryOperationalFamilySemantics.constructorAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {loweredDecl sourceDecl : VInductDecl} {depth : Nat} {isUnsafe : Bool}
    {sourceVEnv canonicalEnv : VEnv} {headerEnv ctorEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats loweredDecl nparams isUnsafe
      depth sourceVEnv result.types.toArray headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    {initialState : Lean4Lean.ElimNestedInductive.State}
    {Hlowering : NestedLoweringResultClosed loweredSourceEnv fuel nparams
      sourceTypes { initialState with newTypes := sourceTypes.toArray } result}
    {Hprod : RecursorPhasesResult R loweredEnv}
    {familyIdx : Nat} {hfamily : familyIdx < sourceTypes.length}
    {hentry : familyIdx < Hprod.entries.length}
    {Hstep : RestoredInductiveStep result loweredEnv auxRec allIndNames
      sourceTypes[familyIdx] sourceProdEnv targetProdEnv}
    {A : RestoredPrimaryOperationalFamilyAlignment Hlowering Hprod familyIdx
      hfamily hentry Hstep}
    {owner : VInductiveType}
    {Hrecursor : RestoredPrimaryRecursorSemantics sourceDecl owner c.safety
      Hstep.restored.recursor canonicalEnv}
    (F : RestoredPrimaryOperationalFamilySemantics A owner Hrecursor)
    (i : Nat) (hsource : i < sourceTypes[familyIdx].ctors.length)
    (htarget : i < A.target.ctors.length)
    (hconstructor : i < owner.ctors.length) :
    ∃ before after stepSource stepTarget,
      ∃ _Hmapping : LoweredConstructorMapping loweredSourceEnv result.params
          nparams result sourceTypes[familyIdx].ctors[i] before
            (A.target.ctors[i], after),
      ∃ HctorStep : RestoredConstructorStep result loweredEnv
          A.target.ctors[i].name stepSource stepTarget,
      ∃ Hsemantic : RestoredSourceConstructorSemantics c.lparams c.safety
          canonicalEnv HctorStep sourceTypes[familyIdx].ctors[i],
        Hsemantic.constructor = owner.ctors[i] :=
  F.constructors.at i hsource htarget hconstructor

end VerifyInductive
end Lean4Lean
