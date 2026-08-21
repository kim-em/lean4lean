import Lean4Lean.Verify.Inductive.Equation.Lhs

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Applying a complete telescope to as many arguments as it has domains
undoes a weakening of the residual by those binders.  The domain values may
be dependent; they disappear from the conclusion because the weakened
residual does not depend on any of the newly inserted variables. -/
theorem VExpr.applyForallType_wrapForalls_liftN
    (domains args : List VExpr) (result : VExpr)
    (hlength : args.length = domains.length) :
    VExpr.applyForallType
        (VExpr.wrapForalls domains (result.liftN domains.length 0)) args =
      result := by
  induction args generalizing domains result with
  | nil =>
      have hdomains : domains = [] :=
        List.eq_nil_of_length_eq_zero hlength.symm
      subst domains
      simp [VExpr.applyForallType, VExpr.wrapForalls]
  | cons arg args ih =>
      cases domains with
      | nil => simp at hlength
      | cons domain domains =>
          have htail : args.length = domains.length := by
            simpa using Nat.succ.inj hlength
          change VExpr.applyForallType
            ((VExpr.wrapForalls domains
              (result.liftN (domains.length + 1) 0)).inst arg) args = result
          rw [VExpr.inst_wrapForalls]
          simp only [Nat.zero_add]
          rw [VExpr.liftN_succ_inst_at_length]
          simpa only [VExpr.instForallDomains_length] using
            ih (VExpr.instForallDomains domains arg 0) result (by
              simpa using htail)

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

/-- Positive-arity generated rules satisfy the abstract equation judgment.
The selected production minor is first aligned with the independently
reconstructed constructor motive while its recursive hypotheses remain open.
Those hypotheses are then converted to the canonical recursive-result types,
closed, and consumed by the generated recursive bodies. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalPositiveEquationWitness
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
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ rule : VDefEq,
      Nonempty (H.GeneratedEquationWitness Us owner howner i hctor rule) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalCanonicalRhsPositiveArityDetailed hpositive with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      equationFields, rhsBody, _rhsType, hfields, hhypotheses,
      hminorType, hequationFieldsLength, hequationFields, _hrhsType,
      hrhsBody, Hpartial, Hfield, Hctx, HrhsTranslation, _HrhsTyping⟩
  subst equationFields
  let equationFields :=
    (liftContextPrefix (T.motives ++ T.minors).length
      B.fieldDomains.reverse).reverse
  let inserted := T.motives ++ T.minors
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFields
  let later := T.minors.drop (minorIdx + 1)
  let remaining := T.minors.drop minorIdx
  let installedFields :=
    (liftContextPrefix remaining.length fieldDomains.reverse).reverse
  let installedHypotheses :=
    (liftContextPrefixAt remaining.length fieldDomains.length
      hypothesisDomains.reverse).reverse
  let installedResidual := targetResidual.liftN remaining.length
    (fieldDomains.length + hypothesisDomains.length)
  let canonicalDomains := VExpr.liftClosedDomains C.bodyTypes 0
  let expected := Expr.app
    (mkAppN H.recInfos[owner]!.motive
      (AddInductive.getIIndices stats A.rule.target).2)
    A.rule.sourceConstructorMajor
  rcases A.finalFixedCanonicalLhsBodyFor B T with
    ⟨lhsBody, lhsType, HlhsCtx, HlhsTranslation, HlhsTyping,
      HlhsType, HexpectedTranslation⟩
  have HlhsCtx' : OnCtx equationDomains.reverse
      (H.outVEnv.IsType Us.length) := by
    simpa [equationDomains, equationFields, inserted, H.parameterDecls]
      using HlhsCtx
  have HlhsTranslation' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody := by
    simpa [equationDomains, equationFields, inserted, H.parameterDecls]
      using HlhsTranslation
  have HlhsTyping' : H.outVEnv.HasType Us.length equationDomains.reverse
      lhsBody lhsType := by
    simpa [equationDomains, equationFields, inserted, H.parameterDecls]
      using HlhsTyping
  have HexpectedTranslation' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (expected.abstractList A.rule.binders) lhsType := by
    simpa [equationDomains, equationFields, inserted, H.parameterDecls,
      expected] using HexpectedTranslation
  rcases A.finalSelectedMinorPositiveAlignedResidual hpositive with
    ⟨Tsource, S, traversal, HS, _hypothesisOrigins,
      sourceFieldDomains, sourceHypothesisDomains, sourceResidual,
      _hhypothesisStats, _hhypothesisRecInfos, hconstructor,
      htraversalFields, hfieldFVars, hclosedTargets, _hselectedOwner,
      hvalid, hmotiveApp, hsourceFields, hsourceHypotheses,
      hsourceFieldDomains, hsourceHypothesisDomains, hsourceMinorType,
      HsourceResidual, HsourceResidualType⟩
  have hTsource : Tsource = T := Tsource.eq T
  subst Tsource
  have hsourceDomains :
      sourceFieldDomains ++ sourceHypothesisDomains =
        fieldDomains ++ hypothesisDomains := by
    exact VExpr.wrapForalls_prefix_domains_eq
      (n := A.rule.allArgs.size + A.rule.recursiveArgs.size)
      (suffix := [])
      (by simp [hsourceFieldDomains, hsourceHypothesisDomains])
      (by simp [hfields, hhypotheses])
      (by simpa using hsourceMinorType.symm.trans hminorType)
  have hsourceFieldsDomains : sourceFieldDomains = fieldDomains :=
    List.append_inj_left hsourceDomains
      (hsourceFieldDomains.trans hfields.symm)
  have hsourceHypothesesDomains :
      sourceHypothesisDomains = hypothesisDomains :=
    List.append_inj_right hsourceDomains
      (hsourceFieldDomains.trans hfields.symm)
  subst sourceFieldDomains
  subst sourceHypothesisDomains
  have hsourceResidual : sourceResidual = targetResidual := by
    apply VExpr.wrapForalls_left_cancel (fieldDomains ++ hypothesisDomains)
    rw [← hsourceMinorType, ← hminorType]
  subst sourceResidual
  have hfieldClosure := A.alignedMotiveAppFieldClosure S traversal
    hconstructor htraversalFields hfieldFVars hclosedTargets hvalid
      hmotiveApp hsourceFields
  have hsourceAligned := A.alignedPositiveResidualSource S HS traversal
    hmotiveApp hfieldClosure hsourceFields hsourceHypotheses
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hremaining : remaining = T.minors[minorIdx] :: later := by
    simpa [remaining, later] using List.drop_eq_getElem_cons hminor
  have hremainingLength : remaining.length = later.length + 1 := by
    simp [hremaining]
  have hremainingSourceLength :
      (A.rule.minors_bound.fvars.drop minorIdx).length = remaining.length := by
    simp [remaining, A.rule.minors_bound.length_fvars, T.minors_length]
  let sourceOuter := T.params ++ T.motives ++ T.minors.take minorIdx
  have HsourceResidual' : TrExprS H.outVEnv Us
      (abstractForallContext
        (sourceOuter ++ (fieldDomains ++ hypothesisDomains)) [])
      (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size).abstractList
          (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take minorIdx)
          (A.rule.allArgs.size + A.rule.recursiveArgs.size))
      targetResidual := by
    simpa [sourceOuter, abstractForallContext, List.reverse_append,
      List.map_append, List.append_assoc] using HsourceResidual
  have Hinserted₀ := Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
    (outer := sourceOuter) (inner := fieldDomains ++ hypothesisDomains)
    H.outVEnvWF.ordered HsourceResidual' remaining
  have houterRemaining : sourceOuter ++ remaining =
      T.params ++ T.motives ++ T.minors := by
    simp [sourceOuter, remaining, List.append_assoc]
  have hliftedInner :
      (liftContextPrefix remaining.length
        (fieldDomains ++ hypothesisDomains).reverse).reverse =
        installedFields ++ installedHypotheses := by
    simpa [installedFields, installedHypotheses] using
      liftContextPrefix_reverse_append remaining.length fieldDomains
        hypothesisDomains
  have Hinserted : TrExprS H.outVEnv Us
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors ++ installedFields ++
          installedHypotheses) [])
      ((expected.abstractList A.rule.binders).liftLooseBVars' 0
        A.rule.recursiveArgs.size)
      installedResidual := by
    have hinnerLength : (fieldDomains ++ hypothesisDomains).length =
        A.rule.allArgs.size + A.rule.recursiveArgs.size := by
      simp [hfields, hhypotheses]
    have hsourceAligned' := hsourceAligned
    simp only [minorIdx, hremainingSourceLength] at hsourceAligned'
    rw [hinnerLength] at Hinserted₀
    rw [hsourceAligned'] at Hinserted₀
    dsimp only at Hinserted₀
    rw [houterRemaining, hliftedInner] at Hinserted₀
    simpa [installedResidual, expected, Expr.abstractList_app,
      hinnerLength.symm, List.append_assoc] using Hinserted₀
  have Hparams := H.finalRecursorParameterContextFor howner T
  have Hparams' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse H.parameterSuffix.parameterDecls.toCtx := by
    simpa only [Us, ← H.parameterDecls] using Hparams
  let equationPrefix := equationFields.reverse ++ inserted.reverse
  let installedPrefix := installedFields.reverse ++ inserted.reverse
  have Hfield' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (equationPrefix ++ H.parameterSuffix.parameterDecls.toCtx)
      (installedPrefix ++ H.parameterSuffix.parameterDecls.toCtx) := by
    simpa [Us, equationPrefix, installedPrefix, installedFields,
      equationFields, inserted, later, minorIdx, hremainingLength,
      List.append_assoc]
      using Hfield
  have HfieldT : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (equationPrefix ++ T.params.reverse)
      (installedPrefix ++ T.params.reverse) := by
    have Hrebased := VEnv.IsDefEqCtx.rebaseCommonSuffix
      H.outVEnvWF Hparams' Hfield'
    simpa [equationPrefix, installedPrefix, installedFields,
      List.append_assoc] using Hrebased
  have HequationParams := VEnv.IsDefEqCtx.extendSamePrefix
    Hparams' HfieldT.isType
  have HbaseMixed := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    (HfieldT.symm H.outVEnvWF.ordered) HequationParams
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
      equationDomains.reverse := by
    simpa [equationPrefix, installedPrefix, equationDomains,
      equationFields, inserted, List.reverse_append, List.append_assoc]
      using HbaseMixed
  have Hpartial' : H.outVEnv.HasType Us.length equationDomains.reverse
      (VExpr.mkApps (.bvar (equationFields.length + later.length))
        (recursorCanonicalVars equationFields.length))
      (VExpr.wrapForalls installedHypotheses installedResidual) := by
    simpa [equationDomains, installedHypotheses, installedResidual,
      equationFields, hremainingLength, later, remaining, inserted,
      abstractForallContext_toCtx, VLCtx.toCtx, List.append_assoc]
      using Hpartial
  have HpartialTypeInstalled : H.outVEnv.IsType Us.length
      (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
      (VExpr.wrapForalls installedHypotheses installedResidual) :=
    (Hpartial'.isType H.outVEnvWF HlhsCtx').defeqDFC
      H.outVEnvWF.ordered (Hbase.symm H.outVEnvWF.ordered)
  have HopenedInstalled := VEnv.IsType.wrapForalls_inv
    H.outVEnvWF.ordered Hbase.isType HpartialTypeInstalled
  have HfullBase := VEnv.IsDefEqCtx.extendSamePrefix Hbase
    HopenedInstalled.1
  have HinsertedExact : TrExpr H.outVEnv Us
      (abstractForallContext (equationDomains ++ installedHypotheses) [])
      ((expected.abstractList A.rule.binders).liftLooseBVars' 0
        A.rule.recursiveArgs.size)
      installedResidual := by
    have HfullBase' : VEnv.IsDefEqCtx H.outVEnv Us.length []
        (T.params ++ T.motives ++ T.minors ++ installedFields ++
          installedHypotheses).reverse
        (equationDomains ++ installedHypotheses).reverse := by
      simpa [List.reverse_append, List.append_assoc] using HfullBase
    have Hvlctx := abstractForallContext.isDefEq HfullBase'
    simpa [abstractForallContext, List.reverse_append, List.map_append,
      List.append_assoc] using Hinserted.defeqDFC' H.outVEnvWF Hvlctx
  have Hhypotheses := A.finalCanonicalRecursiveHypothesisContext B T C
    fieldDomains hypothesisDomains targetResidual hfields hhypotheses
      hminorType (by simpa [minorIdx, remaining, installedFields,
        equationDomains, equationFields, inserted, List.append_assoc]
        using Hbase)
  have Hhypotheses' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++ equationDomains.reverse)
      (canonicalDomains.reverse ++ equationDomains.reverse) := by
    simpa [installedHypotheses, canonicalDomains, equationDomains,
      equationFields, inserted, remaining, minorIdx,
      abstractForallContext_toCtx,
      VLCtx.toCtx, List.reverse_append, List.append_assoc]
      using Hhypotheses
  have HexpectedWeak : TrExprS H.outVEnv Us
      (abstractForallContext (equationDomains ++ canonicalDomains) [])
      ((expected.abstractList A.rule.binders).liftLooseBVars' 0
        canonicalDomains.length)
      (lhsType.liftN canonicalDomains.length 0) := by
    have W := abstractForallContext.bvLift canonicalDomains
      (abstractForallContext equationDomains [])
    simpa [abstractForallContext, List.reverse_append, List.map_append,
      List.append_assoc] using
      HexpectedTranslation'.weakBV H.outVEnvWF.ordered W
  have hcanonicalLength : canonicalDomains.length =
      A.rule.recursiveArgs.size := by
    simp [canonicalDomains]
  rw [hcanonicalLength] at HexpectedWeak
  have HhypothesesDomains : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (equationDomains ++ installedHypotheses).reverse
      (equationDomains ++ canonicalDomains).reverse := by
    simpa [List.reverse_append, List.append_assoc] using Hhypotheses'
  have HhypothesesV := abstractForallContext.isDefEq HhypothesesDomains
  have HexpectedWeak' := HexpectedWeak.trExpr H.outVEnvWF.ordered
    (HhypothesesV.symm H.outVEnvWF).wf
  have HresidualU := HinsertedExact.uniq H.outVEnvWF
    HhypothesesV HexpectedWeak'
  have HresidualU' : H.outVEnv.IsDefEqU Us.length
      (installedHypotheses.reverse ++ equationDomains.reverse)
      installedResidual (lhsType.liftN A.rule.recursiveArgs.size 0) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append, List.append_assoc] using HresidualU
  rcases HopenedInstalled.2 with
    ⟨residualLevel, HinstalledResidualType⟩
  have HinstalledResidualType' : H.outVEnv.HasType Us.length
      (installedHypotheses.reverse ++ equationDomains.reverse)
      installedResidual (.sort residualLevel) :=
    HinstalledResidualType.defeqDFC H.outVEnvWF.ordered HfullBase
  have Hresidual : H.outVEnv.IsDefEq Us.length
      (installedHypotheses.reverse ++ equationDomains.reverse)
      installedResidual (lhsType.liftN A.rule.recursiveArgs.size 0)
      (.sort residualLevel) :=
    HresidualU'.of_l H.outVEnvWF Hhypotheses'.isType
      HinstalledResidualType'
  rcases VEnv.IsDefEqCtx.closeHeads Hhypotheses'
      A.rule.recursiveArgs.size
      (by simp [installedHypotheses, hhypotheses]) Hresidual with
    ⟨closedLevel, Hclosed⟩
  have Hwhole : H.outVEnv.IsDefEqU Us.length equationDomains.reverse
      (VExpr.wrapForalls installedHypotheses installedResidual)
      (VExpr.wrapForalls canonicalDomains
        (lhsType.liftN canonicalDomains.length 0)) := by
    refine ⟨.sort closedLevel, ?_⟩
    simpa [installedHypotheses, canonicalDomains, hcanonicalLength,
      hhypotheses] using Hclosed
  have HfnCanonical : H.outVEnv.HasType Us.length equationDomains.reverse
      (VExpr.mkApps (.bvar (equationFields.length + later.length))
        (recursorCanonicalVars equationFields.length))
      (VExpr.wrapForalls canonicalDomains
        (lhsType.liftN canonicalDomains.length 0)) :=
    Hpartial'.defeqU_r H.outVEnvWF HlhsCtx' Hwhole
  have HbodyTypings : List.Forall₂
      (H.outVEnv.HasType Us.length equationDomains.reverse)
      C.bodies C.bodyTypes := by
    simpa [equationDomains, equationFields, inserted,
      abstractForallContext_toCtx, VLCtx.toCtx, List.reverse_append,
      List.append_assoc] using C.bodyTypings
  rcases VEnv.TypedApplicationSpine.liftClosedDomains
      H.outVEnvWF.ordered HfnCanonical HbodyTypings with
    ⟨finalType, Hspine⟩
  have hfinalType : finalType = lhsType := by
    rw [Hspine.result_eq_applyForallType]
    exact VExpr.applyForallType_wrapForalls_liftN canonicalDomains
      C.bodies lhsType (by simp [canonicalDomains])
  have HrhsAtLhs : H.outVEnv.HasType Us.length equationDomains.reverse
      rhsBody lhsType := by
    rw [hrhsBody]
    rw [← hfinalType]
    simpa [equationFields, later, inserted, equationDomains,
      List.append_assoc]
      using Hspine.hasType
  have hdomains := A.cachedEquationDomains_length T equationFields
    hequationFieldsLength
  have huvars := A.recursorUvars
  let rule := A.abstractEquation equationDomains lhsBody rhsBody lhsType
  refine ⟨rule, ⟨?_⟩⟩
  apply A.equationWitnessOfBodies equationDomains lhsBody rhsBody lhsType
      (by simpa [equationDomains, inserted,
        H.parameterDecls] using hdomains)
      HlhsTranslation' HrhsTranslation
  · simpa only [Us, huvars] using HlhsCtx'
  · simpa only [Us, huvars] using HlhsTyping'
  · simpa only [Us, huvars] using HrhsAtLhs

/-- Degenerate generated rules have no constructor fields or recursive
results.  Their selected minor is already the complete RHS, but its consumed
source still has to be identified with the independently reconstructed
constructor-motive type. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalZeroEquationWitness
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
    (hzero : A.rule.allArgs.size + A.rule.recursiveArgs.size = 0) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ rule : VDefEq,
      Nonempty (H.GeneratedEquationWitness Us owner howner i hctor rule) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  have hfieldsZero : A.rule.allArgs.size = 0 := by omega
  have hhypothesesZero : A.rule.recursiveArgs.size = 0 := by omega
  rcases A.finalCanonicalMinorApplicationZeroArity hzero with
    ⟨B, T, C, targetResidual, hbodies, hminorType, Hctx, Hminor⟩
  have hframeFields : B.fieldDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (B.fieldDomains_length.trans hfieldsZero)
  let inserted := T.motives ++ T.minors
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted
  let later := T.minors.drop (minorIdx + 1)
  let remaining := T.minors.drop minorIdx
  let rhsBody : VExpr := .bvar later.length
  let installedResidual := targetResidual.liftN remaining.length 0
  let expected := Expr.app
    (mkAppN H.recInfos[owner]!.motive
      (AddInductive.getIIndices stats A.rule.target).2)
    A.rule.sourceConstructorMajor
  have Hctx' : OnCtx equationDomains.reverse
      (H.outVEnv.IsType Us.length) := by
    simpa [equationDomains, inserted, hframeFields, liftContextPrefix,
      liftContextPrefixAt, abstractForallContext_toCtx, VLCtx.toCtx,
      List.append_assoc] using Hctx
  rcases A.finalFixedCanonicalLhsBodyFor B T with
    ⟨lhsBody, lhsType, HlhsCtx, HlhsTranslation, HlhsTyping,
      HlhsType, HexpectedTranslation⟩
  have HlhsTranslation' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceLhsBody.abstractList A.rule.binders) lhsBody := by
    simpa [equationDomains, inserted, hframeFields, liftContextPrefix,
      liftContextPrefixAt, H.parameterDecls] using HlhsTranslation
  have HlhsTyping' : H.outVEnv.HasType Us.length equationDomains.reverse
      lhsBody lhsType := by
    simpa [equationDomains, inserted, hframeFields, liftContextPrefix,
      liftContextPrefixAt, H.parameterDecls] using HlhsTyping
  have HlhsType' : H.outVEnv.IsType Us.length equationDomains.reverse
      lhsType := by
    simpa [equationDomains, inserted, hframeFields, liftContextPrefix,
      liftContextPrefixAt, H.parameterDecls] using HlhsType
  have HexpectedTranslation' : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (expected.abstractList A.rule.binders) lhsType := by
    simpa [equationDomains, inserted, hframeFields, liftContextPrefix,
      liftContextPrefixAt, H.parameterDecls, expected]
      using HexpectedTranslation
  rcases A.finalSelectedMinorAlignedResidual with
    ⟨Tsource, S, traversal, HS, _hypothesisOrigins,
      sourceFieldDomains, sourceHypothesisDomains, sourceResidual,
      _hhypothesisStats, _hhypothesisRecInfos, hconstructor,
      htraversalFields, hfieldFVars, hclosedTargets, _hselectedOwner,
      hvalid, hmotiveApp, hsourceFields, hsourceHypotheses,
      hsourceFieldDomains, hsourceHypothesisDomains, hsourceMinorType,
      HsourceResidual, _HsourceResidualType⟩
  have hTsource : Tsource = T := Tsource.eq T
  subst Tsource
  have hsourceFieldDomainsZero : sourceFieldDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (hsourceFieldDomains.trans hfieldsZero)
  have hsourceHypothesisDomainsZero : sourceHypothesisDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (hsourceHypothesisDomains.trans hhypothesesZero)
  subst sourceFieldDomains
  subst sourceHypothesisDomains
  have hsourceResidual : sourceResidual = targetResidual := by
    simpa [VExpr.wrapForalls] using
      hsourceMinorType.symm.trans hminorType
  subst sourceResidual
  have hfieldClosure := A.alignedMotiveAppFieldClosure S traversal
    hconstructor htraversalFields hfieldFVars hclosedTargets hvalid
      hmotiveApp hsourceFields
  have hsourceAligned := A.alignedPositiveResidualSource S HS traversal
    hmotiveApp hfieldClosure hsourceFields hsourceHypotheses
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hremaining : remaining = T.minors[minorIdx] :: later := by
    simpa [remaining, later] using List.drop_eq_getElem_cons hminor
  have hremainingLength : remaining.length = later.length + 1 := by
    simp [hremaining]
  have hremainingSourceLength :
      (A.rule.minors_bound.fvars.drop minorIdx).length = remaining.length := by
    simp [remaining, A.rule.minors_bound.length_fvars, T.minors_length]
  let sourceOuter := T.params ++ T.motives ++ T.minors.take minorIdx
  have HsourceResidual' : TrExprS H.outVEnv Us
      (abstractForallContext (sourceOuter ++ []) [])
      (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size).abstractList
          (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take minorIdx) 0)
      targetResidual := by
    simpa [sourceOuter, hzero, abstractForallContext,
      List.reverse_append, List.map_append, List.append_assoc]
      using HsourceResidual
  have Hinserted₀ := Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
    (outer := sourceOuter) (inner := []) H.outVEnvWF.ordered
      HsourceResidual' remaining
  have houterRemaining : sourceOuter ++ remaining =
      T.params ++ T.motives ++ T.minors := by
    simp [sourceOuter, remaining, List.append_assoc]
  have Hinserted : TrExprS H.outVEnv Us
      (abstractForallContext (T.params ++ T.motives ++ T.minors) [])
      (expected.abstractList A.rule.binders) installedResidual := by
    have hsourceAligned' := hsourceAligned
    simp [minorIdx, hfieldsZero, hhypothesesZero,
      hremainingSourceLength] at hsourceAligned'
    rw [← List.append_assoc] at hsourceAligned'
    dsimp only [minorIdx] at Hinserted₀
    simp only [List.length_nil] at Hinserted₀
    rw [hsourceAligned'] at Hinserted₀
    simp [liftContextPrefix, liftContextPrefixAt] at Hinserted₀
    rw [houterRemaining] at Hinserted₀
    simpa [installedResidual, expected, Expr.abstractList_app,
      List.append_assoc] using Hinserted₀
  have Hparams := H.finalRecursorParameterContextFor howner T
  have Hparams' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse H.parameterSuffix.parameterDecls.toCtx := by
    simpa only [Us, ← H.parameterDecls] using Hparams
  have HctxPlain : OnCtx
      (inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx)
      (H.outVEnv.IsType Us.length) := by
    simpa [equationDomains, inserted, List.reverse_append,
      List.append_assoc] using Hctx'
  have HequationToGenerated := VEnv.IsDefEqCtx.extendSamePrefix
    (Hparams'.symm H.outVEnvWF.ordered) HctxPlain
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (T.params ++ T.motives ++ T.minors).reverse
      equationDomains.reverse := by
    have Hbase' := HequationToGenerated.symm H.outVEnvWF.ordered
    simpa [equationDomains, inserted, List.reverse_append,
      List.append_assoc] using Hbase'
  have HinsertedExact : TrExpr H.outVEnv Us
      (abstractForallContext equationDomains [])
      (expected.abstractList A.rule.binders) installedResidual :=
    Hinserted.defeqDFC' H.outVEnvWF
      (abstractForallContext.isDefEq Hbase)
  have Hrefl : VEnv.IsDefEqCtx H.outVEnv Us.length []
      equationDomains.reverse equationDomains.reverse :=
    VEnv.IsDefEqCtx.refl Hctx'
  have HreflV := abstractForallContext.isDefEq Hrefl
  have Hexpected' := HexpectedTranslation'.trExpr
    H.outVEnvWF.ordered HreflV.wf
  have HtypeU₀ := HinsertedExact.uniq H.outVEnvWF HreflV Hexpected'
  have HtypeU : H.outVEnv.IsDefEqU Us.length equationDomains.reverse
      installedResidual lhsType := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HtypeU₀
  rcases HlhsType' with ⟨lhsLevel, HlhsSort⟩
  have Htype : H.outVEnv.IsDefEq Us.length equationDomains.reverse
      installedResidual lhsType (.sort lhsLevel) :=
    HtypeU.of_r H.outVEnvWF Hctx' HlhsSort
  have Hminor' : H.outVEnv.HasType Us.length equationDomains.reverse
      rhsBody installedResidual := by
    simpa [rhsBody, installedResidual, equationDomains, inserted,
      remaining, later, hremainingLength, hframeFields,
      liftContextPrefix, liftContextPrefixAt,
      abstractForallContext_toCtx, VLCtx.toCtx, List.append_assoc]
      using Hminor
  have HrhsAtLhs : H.outVEnv.HasType Us.length equationDomains.reverse
      rhsBody lhsType :=
    Hminor'.defeqU_r H.outVEnvWF Hctx' ⟨.sort lhsLevel, Htype⟩
  have hminorVar : later.length < equationDomains.length := by
    dsimp only [later, equationDomains, inserted]
    simp only [List.length_append, List.length_drop]
    omega
  have HvarTranslation : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (.bvar later.length) rhsBody :=
    TrExprS.bvar_of_abstractForallContext equationDomains []
      later.length hminorVar
  have hallArgs : A.rule.allArgs = #[] :=
    Array.eq_empty_of_size_eq_zero hfieldsZero
  have hrecursiveResultsSize : A.rule.recursiveResults.size = 0 := by
    rw [A.rule.recursive_calls.size]
    exact hhypothesesZero
  have hrecursiveResults : A.rule.recursiveResults = #[] :=
    Array.eq_empty_of_size_eq_zero hrecursiveResultsSize
  have hsourceMinor :
      A.rule.allArgs.size +
          ((H.recInfos.flatMap (·.minors)).size - 1 - minorIdx) =
        later.length := by
    dsimp only [later]
    simp only [List.length_drop, T.minors_length]
    omega
  have hsourceShape := A.rule.abstractedSourceRhsAtMinorArray
  rw [hsourceMinor] at hsourceShape
  have hsourceRhs : A.rule.sourceRhsBody.abstractList A.rule.binders =
      .bvar later.length := by
    simpa [hallArgs, hrecursiveResults, Expr.mkAppN_eq_mkAppList,
      Expr.mkAppList] using hsourceShape
  have HrhsTranslation : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody := by
    rw [hsourceRhs]
    exact HvarTranslation
  have hdomains := A.cachedEquationDomains_length T [] (by simp [hfieldsZero])
  have huvars := A.recursorUvars
  let rule := A.abstractEquation equationDomains lhsBody rhsBody lhsType
  refine ⟨rule, ⟨?_⟩⟩
  apply A.equationWitnessOfBodies equationDomains lhsBody rhsBody lhsType
      (by simpa [equationDomains, inserted, hframeFields,
        liftContextPrefix, liftContextPrefixAt, H.parameterDecls]
        using hdomains)
      HlhsTranslation' HrhsTranslation
  · simpa only [Us, huvars] using Hctx'
  · simpa only [Us, huvars] using HlhsTyping'
  · simpa only [Us, huvars] using HrhsAtLhs

/-- Every generated constructor rule now has an independently reconstructed,
well-formed abstract equation, regardless of constructor arity. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalEquationWitness
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
    ∃ rule : VDefEq,
      Nonempty (H.GeneratedEquationWitness Us owner howner i hctor rule) := by
  dsimp only
  by_cases hzero : A.rule.allArgs.size + A.rule.recursiveArgs.size = 0
  · exact A.finalCanonicalZeroEquationWitness hzero
  · exact A.finalCanonicalPositiveEquationWitness
      (Nat.pos_of_ne_zero hzero)

end VerifyInductive
end Lean4Lean
