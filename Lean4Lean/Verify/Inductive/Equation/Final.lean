import Lean4Lean.Verify.Inductive.Equation.Lhs

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Synchronize the independently reconstructed equation LHS with the
production-shaped RHS.  Both sides use the same narrowed field frame,
recursor telescope, and literal equation context; only the semantic alignment
of `lhsType` and `rhsType` remains before constructing a
`GeneratedEquationWitness`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalEquationBodies
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
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ equationFields : List VExpr,
      ∃ lhsBody rhsBody lhsType rhsType : VExpr,
        equationFields.length = A.rule.allArgs.size ∧
        equationFields =
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse ∧
        let inserted := T.motives ++ T.minors
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFields
        OnCtx equationDomains.reverse (H.outVEnv.IsType Us.length) ∧
          TrExprS H.outVEnv Us (abstractForallContext equationDomains [])
            (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody ∧
          TrExprS H.outVEnv Us (abstractForallContext equationDomains [])
            (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody ∧
          H.outVEnv.HasType Us.length equationDomains.reverse
            lhsBody lhsType ∧
          H.outVEnv.IsType Us.length equationDomains.reverse lhsType ∧
          H.outVEnv.HasType Us.length equationDomains.reverse
            rhsBody rhsType ∧
          TrExprS H.outVEnv Us (abstractForallContext equationDomains [])
            ((Expr.app
              (mkAppN H.recInfos[owner]!.motive
                (AddInductive.getIIndices stats A.rule.target).2)
              A.rule.sourceConstructorMajor).abstractList A.rule.binders)
            lhsType := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalCanonicalRhs with
    ⟨B, T, C, equationFields, rhsBody, rhsType,
      hfields, hequationFields, HrhsCtx, HrhsTranslation, HrhsTyping⟩
  let inserted := T.motives ++ T.minors
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFields
  rcases A.finalFixedCanonicalLhsBodyFor B T with
    ⟨lhsBody, lhsType, HlhsCtx, HlhsTranslation, HlhsTyping,
      HlhsType, HexpectedTranslation⟩
  have HlhsCtx' : OnCtx equationDomains.reverse
      (H.outVEnv.IsType Us.length) := by
    simpa [equationDomains, inserted, hequationFields, H.parameterDecls]
      using HlhsCtx
  have HlhsTranslation' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody := by
    simpa [equationDomains, inserted, hequationFields, H.parameterDecls]
      using HlhsTranslation
  have HlhsTyping' : H.outVEnv.HasType Us.length equationDomains.reverse
      lhsBody lhsType := by
    simpa [equationDomains, inserted, hequationFields, H.parameterDecls]
      using HlhsTyping
  have HlhsType' : H.outVEnv.IsType Us.length equationDomains.reverse
      lhsType := by
    simpa [equationDomains, inserted, hequationFields, H.parameterDecls]
      using HlhsType
  have HexpectedTranslation' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      ((Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats A.rule.target).2)
        A.rule.sourceConstructorMajor).abstractList A.rule.binders)
      lhsType := by
    simpa [equationDomains, inserted, hequationFields, H.parameterDecls]
      using HexpectedTranslation
  have HrhsCtx' : OnCtx equationDomains.reverse
      (H.outVEnv.IsType Us.length) := by
    simpa [equationDomains, inserted, abstractForallContext_toCtx,
      VLCtx.toCtx, List.reverse_append, List.append_assoc]
      using HrhsCtx
  have HrhsTyping' : H.outVEnv.HasType Us.length equationDomains.reverse
      rhsBody rhsType := by
    simpa [equationDomains, inserted, abstractForallContext_toCtx,
      VLCtx.toCtx, List.reverse_append, List.append_assoc]
      using HrhsTyping
  exact ⟨B, T, C, equationFields, lhsBody, rhsBody, lhsType, rhsType,
    hfields, hequationFields, HlhsCtx', HlhsTranslation', HrhsTranslation,
    HlhsTyping', HlhsType', HrhsTyping', HexpectedTranslation'⟩

end VerifyInductive
end Lean4Lean
