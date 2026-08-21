import Lean4Lean.Verify.Inductive.Equation.DependentFold

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- One dependent recursive-hypothesis step, after the already-consumed
hypotheses have been aligned.  Syntactic uniqueness of the selected minor
telescope identifies the caller's installed domains with the domains used by
the source replay; the common residual translation then closes the complete
higher-order domain on both sides. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorHypothesisCanonicalWholeDomainDefEq
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
    (installedFieldDomains installedHypothesisDomains : List VExpr)
    (installedResidual : VExpr)
    (hinstalledFields : installedFieldDomains.length = A.rule.allArgs.size)
    (hinstalledHypotheses :
      installedHypothesisDomains.length = A.rule.recursiveArgs.size)
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (htarget :
      T.minors[recursorMinorOffset indTypes owner + i]! =
        VExpr.wrapForalls
          (installedFieldDomains ++ installedHypothesisDomains)
          installedResidual)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (E : A.CanonicalRecursiveResultAt T B j hj)
    (canonicalPrevious : List VExpr)
    (hcanonicalPreviousLength : canonicalPrevious.length = j)
    (Hbase :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let position := A.rule.allArgs.size + j
      let prior :=
        (installedFieldDomains ++ installedHypothesisDomains).take position
      let remaining := T.minors.drop minorIdx
      let liftedPrior :=
        (liftContextPrefix remaining.length prior.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (T.params ++ T.motives ++ T.minors ++ liftedPrior).reverse
        (equationDomains ++ canonicalPrevious).reverse) :
    ∃ hypothesisLocalDomains : List VExpr,
    ∃ hypothesisResidual : VExpr,
      installedHypothesisDomains[j]! =
        VExpr.wrapForalls hypothesisLocalDomains hypothesisResidual ∧
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let position := A.rule.allArgs.size + j
      let prior :=
        (installedFieldDomains ++ installedHypothesisDomains).take position
      let remaining := T.minors.drop minorIdx
      let liftedPrior :=
        (liftContextPrefix remaining.length prior.reverse).reverse
      let liftedHypothesisLocals :=
        (liftContextPrefixAt remaining.length position
          hypothesisLocalDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      let liftedCanonicalLocals :=
        (liftContextPrefix canonicalPrevious.length
          E.localDomains.reverse).reverse
      ∃ level, H.outVEnv.IsDefEq Us.length
        (T.params ++ T.motives ++ T.minors ++ liftedPrior).reverse
        (VExpr.wrapForalls liftedHypothesisLocals
          (hypothesisResidual.liftN remaining.length
            (position + hypothesisLocalDomains.length)))
        (VExpr.wrapForalls liftedCanonicalLocals
          (E.resultType.liftN canonicalPrevious.length
            E.localDomains.length)) (.sort level) := by
  dsimp only at Hbase ⊢
  rcases A.finalSelectedMinorHypothesisCanonicalWholeDomains j hj B T E with
    ⟨S, hypothesisOrigins, fieldDomains, hypothesisDomains,
      targetResidual, D, originRoot, sourceType, O,
      hypothesisLocalDomains, hypothesisResidual,
      hfields, hhypotheses, htarget', hliftedPrior,
      hlocal, hhypothesisDomain, Hinstalled, _HcanonicalInstalled,
      Hprefix, HinstalledResidual, _HcanonicalResidualInstalled,
      _HcanonicalResidualTypeInstalled⟩
  have hdomains : fieldDomains ++ hypothesisDomains =
      installedFieldDomains ++ installedHypothesisDomains := by
    apply VExpr.wrapForalls_prefix_domains_eq
      (n := A.rule.allArgs.size + A.rule.recursiveArgs.size)
      (suffix := [])
    · simp [hfields, hhypotheses]
    · simp [hinstalledFields, hinstalledHypotheses]
    · simpa [VExpr.wrapForalls_append] using htarget'.symm.trans htarget
  have hfieldDomains : fieldDomains = installedFieldDomains := by
    have Htake := congrArg
      (List.take A.rule.allArgs.size) hdomains
    simpa [hfields, hinstalledFields] using Htake
  subst fieldDomains
  have hhypothesisDomains :
      hypothesisDomains = installedHypothesisDomains := by
    have Hdrop := congrArg
      (List.drop A.rule.allArgs.size) hdomains
    simpa [hfields, hinstalledFields] using Hdrop
  subst hypothesisDomains
  refine ⟨hypothesisLocalDomains, hypothesisResidual,
    hhypothesisDomain, ?_⟩
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let liftedCanonicalLocals :=
    (liftContextPrefix canonicalPrevious.length
      E.localDomains.reverse).reverse
  have Hcanonical := E.fullForallTranslationAfter canonicalPrevious
  have HcanonicalResidual₀ : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (equationDomains ++ E.localDomains) [])
      (E.frame.semantic.generated.outerAbstractedMotiveApp A.rule.binders)
      E.resultType := by
    simpa [equationDomains] using E.result_type_translation
  have HcanonicalResidualInserted :=
    Lean4Lean.VerifyInductive.TrExprS.insertBeforeInner
      (outer := equationDomains) (inner := E.localDomains)
      H.outVEnvWF.ordered HcanonicalResidual₀ canonicalPrevious
  have HcanonicalResidual : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (equationDomains ++ canonicalPrevious ++ liftedCanonicalLocals) [])
      ((E.frame.semantic.generated.outerAbstractedMotiveApp
        A.rule.binders).liftLooseBVars'
          E.frame.semantic.generated.localArgs.size canonicalPrevious.length)
      (E.resultType.liftN canonicalPrevious.length E.localDomains.length) := by
    simpa [liftedCanonicalLocals, E.local_length,
      List.append_assoc] using HcanonicalResidualInserted
  have Wcanonical : Ctx.LiftN canonicalPrevious.length E.localDomains.length
      (abstractForallContext
        (equationDomains ++ E.localDomains) []).toCtx
      (abstractForallContext
        (equationDomains ++ canonicalPrevious ++ liftedCanonicalLocals) []).toCtx := by
    have W := Ctx.LiftN.insertAfterPrefix E.localDomains.reverse
      canonicalPrevious.reverse equationDomains.reverse
    simpa [liftedCanonicalLocals, List.reverse_append,
      abstractForallContext_toCtx, VLCtx.toCtx, List.append_assoc] using W
  have HcanonicalResidualType : H.outVEnv.IsType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        (equationDomains ++ canonicalPrevious ++ liftedCanonicalLocals) []).toCtx
      (E.resultType.liftN canonicalPrevious.length E.localDomains.length) :=
    E.result_type_isType.weakN H.outVEnvWF.ordered Wcanonical
  have Hprefix' := Hprefix
  simp only [List.length_reverse, liftContextPrefixAt_length,
    List.length_take, hinstalledHypotheses,
    Nat.min_eq_left (Nat.le_of_lt hj), hcanonicalPreviousLength] at Hprefix'
  exact Hprefix'.translatedWholeTargetsOfResidualRightSort
    H.outVEnvWF Hbase
      (by simpa using Hinstalled)
      (by simpa [equationDomains, liftedCanonicalLocals,
        hcanonicalPreviousLength] using Hcanonical)
      (by simpa using hlocal) (by simp)
      (by simpa using HinstalledResidual)
      (by simpa [equationDomains, liftedCanonicalLocals,
        hcanonicalPreviousLength] using HcanonicalResidual)
      (by simpa [equationDomains, liftedCanonicalLocals] using
        HcanonicalResidualType)

/-- All recursive results of one generated rule, chosen in their production
array order and fixed to one recursor telescope and one narrowed field frame. -/
structure
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults
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
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.NarrowFieldRuntimeFrame) where
  resultAt : ∀ j (hj : j < A.rule.recursiveArgs.size),
    A.CanonicalRecursiveResultAt T B j hj

def
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodies
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B) : List VExpr :=
  List.ofFn fun j : Fin A.rule.recursiveArgs.size =>
    let E := C.resultAt j j.isLt
    VExpr.wrapLams E.localDomains E.resultBody

/-- The closed dependent types corresponding pointwise to `bodies`.  Keeping
this as a parallel list makes the later minor-application fold explicit:
each recursive-result term is consumed at exactly the same ordinal as the
installed minor hypothesis it discharges. -/
def
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTypes
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B) : List VExpr :=
  List.ofFn fun j : Fin A.rule.recursiveArgs.size =>
    let E := C.resultAt j j.isLt
    VExpr.wrapForalls E.localDomains E.resultType

@[simp] theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodies_length
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B) :
    C.bodies.length = A.rule.recursiveArgs.size := by
  simp [CanonicalRecursiveResults.bodies]

@[simp] theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTypes_length
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B) :
    C.bodyTypes.length = A.rule.recursiveArgs.size := by
  simp [CanonicalRecursiveResults.bodyTypes]

/-- Exact pointwise typing of the two parallel recursive-result lists in the
fixed equation context.  This is stronger than `bodyWF`: the latter is useful
for translation constructors, while this theorem retains the dependent type
required by the application spine. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTyping
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    let hjType : j < C.bodyTypes.length := by simpa using hj
    H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      C.bodies[j]
      (C.bodyTypes)[j] := by
  let E := C.resultAt j (by simpa using hj)
  simpa [CanonicalRecursiveResults.bodies,
    CanonicalRecursiveResults.bodyTypes, E] using E.closed_typing

/-- Ordered list-level form of `bodyTyping`, ready for the generic closed
domain application fold. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTypings
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    List.Forall₂
      (H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx)
      C.bodies C.bodyTypes := by
  dsimp only
  apply Lean4Lean.VerifyInductive.List.forall₂_of_getElem
  · simp
  · intro j hjBodies hjTypes
    simpa using C.bodyTyping j hjBodies

/-- The chronological `j`th closed-domain entry is exactly the canonical
higher-order result type weakened below the `j` earlier hypotheses. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.liftClosedBodyType_getElem
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B)
    (j : Nat) (hj : j < C.bodyTypes.length) :
    let E := C.resultAt j (by simpa using hj)
    (VExpr.liftClosedDomains C.bodyTypes 0)[j]'(by simpa using hj) =
      VExpr.wrapForalls
        (liftContextPrefix j E.localDomains.reverse).reverse
        (E.resultType.liftN j E.localDomains.length) := by
  dsimp only
  let E := C.resultAt j (by simpa using hj)
  rw [VExpr.liftClosedDomains_getElem C.bodyTypes 0 j hj]
  have hbodyType : C.bodyTypes[j] =
      VExpr.wrapForalls E.localDomains E.resultType := by
    simp [CanonicalRecursiveResults.bodyTypes, E]
  rw [hbodyType, VExpr.liftN_wrapForalls]
  simp [E, liftContextPrefix, liftContextPrefixAt, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc]

/-- Inductively align the complete installed recursive-hypothesis telescope
with the canonical closed result types.  At ordinal `j`, the induction
hypothesis is exactly the base-context conversion required by
`finalSelectedMinorHypothesisCanonicalWholeDomainDefEq`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalRecursiveHypothesisContext
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (C : A.CanonicalRecursiveResults T B)
    (fieldDomains hypothesisDomains : List VExpr)
    (targetResidual : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hhypotheses : hypothesisDomains.length = A.rule.recursiveArgs.size)
    (htarget :
      T.minors[recursorMinorOffset indTypes owner + i]! =
        VExpr.wrapForalls (fieldDomains ++ hypothesisDomains) targetResidual)
    (Hbase :
      let minorIdx := recursorMinorOffset indTypes owner + i
      let remaining := T.minors.drop minorIdx
      let installedFields :=
        (liftContextPrefix remaining.length fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
        equationDomains.reverse) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let remaining := T.minors.drop minorIdx
    let installedHypotheses :=
      (liftContextPrefixAt remaining.length fieldDomains.length
        hypothesisDomains.reverse).reverse
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++ equationDomains.reverse)
      ((VExpr.liftClosedDomains C.bodyTypes 0).reverse ++
        equationDomains.reverse) := by
  dsimp only at Hbase ⊢
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let remaining := T.minors.drop minorIdx
  let installedFields :=
    (liftContextPrefix remaining.length fieldDomains.reverse).reverse
  let installedHypotheses :=
    (liftContextPrefixAt remaining.length fieldDomains.length
      hypothesisDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  let installedBase :=
    (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
  let canonicalDomains := VExpr.liftClosedDomains C.bodyTypes 0
  have hinstalledLength : installedHypotheses.length =
      A.rule.recursiveArgs.size := by
    simp [installedHypotheses, hhypotheses]
  have hcanonicalLength : canonicalDomains.length =
      A.rule.recursiveArgs.size := by
    simp [canonicalDomains]
  have go : ∀ n, n ≤ A.rule.recursiveArgs.size →
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        ((installedHypotheses.take n).reverse ++ installedBase)
        ((canonicalDomains.take n).reverse ++ equationDomains.reverse) := by
    intro n hn
    induction n with
    | zero =>
      simpa [Us, remaining, installedFields, installedBase,
        equationDomains] using Hbase
    | succ n ih =>
      have hnlt : n < A.rule.recursiveArgs.size := by omega
      have Hprior := ih (by omega)
      let E := C.resultAt n hnlt
      let canonicalPrevious := canonicalDomains.take n
      have hcanonicalPreviousLength : canonicalPrevious.length = n := by
        exact List.length_take_of_le (by rw [hcanonicalLength]; omega)
      have hpriorSplit :
          (fieldDomains ++ hypothesisDomains).take
              (A.rule.allArgs.size + n) =
            fieldDomains ++ hypothesisDomains.take n := by
        rw [← hfields, List.take_length_add_append]
      have hnHypotheses : n ≤ hypothesisDomains.length := by
        rw [hhypotheses]
        omega
      have hinstalledPrevious : installedHypotheses.take n =
          (liftContextPrefixAt remaining.length fieldDomains.length
            (hypothesisDomains.take n).reverse).reverse := by
        have Htake := liftContextPrefixAt_reverse_append_take_left
          remaining.length fieldDomains.length
          (hypothesisDomains.take n) (hypothesisDomains.drop n)
        rw [List.take_append_drop n hypothesisDomains] at Htake
        simpa only [installedHypotheses,
          List.length_take_of_le hnHypotheses] using Htake
      have HpointBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
          (T.params ++ T.motives ++ T.minors ++
            (liftContextPrefix remaining.length
              ((fieldDomains ++ hypothesisDomains).take
                (A.rule.allArgs.size + n)).reverse).reverse).reverse
          (equationDomains ++ canonicalPrevious).reverse := by
        rw [hpriorSplit, liftContextPrefix_reverse_append,
          ← hinstalledPrevious]
        simpa [installedFields, installedBase, equationDomains,
          canonicalPrevious,
          List.reverse_append, List.append_assoc] using Hprior
      rcases A.finalSelectedMinorHypothesisCanonicalWholeDomainDefEq
          fieldDomains hypothesisDomains targetResidual hfields hhypotheses
          B T htarget n hnlt E canonicalPrevious hcanonicalPreviousLength
          HpointBase with
        ⟨localDomains, residual, hhypothesisDomain, Hdomain⟩
      have hinstalledDomain : installedHypotheses[n] =
          VExpr.wrapForalls
            ((liftContextPrefixAt remaining.length
              (A.rule.allArgs.size + n) localDomains.reverse).reverse)
            (residual.liftN remaining.length
              (A.rule.allArgs.size + n + localDomains.length)) := by
        rw [← getElem!_pos installedHypotheses n (by
          rw [hinstalledLength]; exact hnlt)]
        simp only [installedHypotheses]
        rw [liftContextPrefixAt_reverse_getElem
          remaining.length fieldDomains.length hypothesisDomains n
          (by simpa [hhypotheses] using hnlt),
          hhypothesisDomain, VExpr.liftN_wrapForalls]
        simp [hfields, Nat.add_assoc]
      have hcanonicalDomain : canonicalDomains[n] =
          VExpr.wrapForalls
            (liftContextPrefix n E.localDomains.reverse).reverse
            (E.resultType.liftN n E.localDomains.length) := by
        simpa [canonicalDomains, E] using
          C.liftClosedBodyType_getElem n (by
            simpa [canonicalDomains, hcanonicalLength] using hnlt)
      have Hdomain' : ∃ level, H.outVEnv.IsDefEq Us.length
          ((installedHypotheses.take n).reverse ++ installedBase)
          installedHypotheses[n] canonicalDomains[n] (.sort level) := by
        rw [hinstalledDomain, hcanonicalDomain]
        have hliftedPriorCtx := congrArg List.reverse
          (liftContextPrefix_reverse_append remaining.length fieldDomains
            (hypothesisDomains.take n))
        dsimp only at Hdomain
        rw [hpriorSplit] at Hdomain
        simp only [List.reverse_append, List.reverse_reverse] at Hdomain hliftedPriorCtx
        rw [hliftedPriorCtx] at Hdomain
        simpa [Us, remaining, hinstalledPrevious, installedFields, installedBase,
          equationDomains, canonicalPrevious, hcanonicalPreviousLength,
          E, List.reverse_append, List.append_assoc] using Hdomain
      rcases Hdomain' with ⟨level, Hdomain'⟩
      have Hnext := VEnv.IsDefEqCtx.succ Hprior Hdomain'
      have hinstalledTakeSucc : installedHypotheses.take (n + 1) =
          installedHypotheses.take n ++ [installedHypotheses[n]] :=
        List.take_succ_eq_append_getElem (by
          rw [hinstalledLength]; exact hnlt)
      have hcanonicalTakeSucc : canonicalDomains.take (n + 1) =
          canonicalDomains.take n ++ [canonicalDomains[n]] :=
        List.take_succ_eq_append_getElem (by
          rw [hcanonicalLength]; exact hnlt)
      rw [hinstalledTakeSucc]
      rw [hcanonicalTakeSucc]
      simp only [List.reverse_append, List.reverse_singleton,
        List.singleton_append]
      exact Hnext
  have Hmixed := go A.rule.recursiveArgs.size (by omega)
  have HmixedFull : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++ installedBase)
      (canonicalDomains.reverse ++ equationDomains.reverse) := by
    have hinstalledTake : installedHypotheses.take
        A.rule.recursiveArgs.size = installedHypotheses :=
      by rw [← hinstalledLength, List.take_length]
    have hcanonicalTake : canonicalDomains.take
        A.rule.recursiveArgs.size = canonicalDomains :=
      by rw [← hcanonicalLength, List.take_length]
    simpa only [hinstalledTake, hcanonicalTake] using Hmixed
  have Hleft := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
    Hbase HmixedFull.isType
  have Hresult := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.transEmpty
    H.outVEnvWF (Hleft.symm H.outVEnvWF.ordered) HmixedFull
  simpa [remaining, installedHypotheses, canonicalDomains, equationDomains,
    installedBase, hinstalledLength, hcanonicalLength,
    List.append_assoc] using Hresult

/-- Pointwise strict source translation for the canonical result list, once
the shared lambda-domain template has been translated in the fixed equation
context.  The same `resultAt` witness determines the source array position,
the target body, and the retained typing used by `bodyTyping`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTranslationOfTemplate
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length)
    (templateTarget : VExpr)
    (Htemplate :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++
          T.motives ++ T.minors ++
            (liftContextPrefix (T.motives ++ T.minors).length
              B.fieldDomains.reverse).reverse
      let hjArg : j < A.rule.recursiveArgs.size := by simpa using hj
      let E := C.resultAt j hjArg
      TrExprS H.outVEnv Us
        (abstractForallContext equationDomains [])
        ((E.frame.semantic.generated.current.lctx.mkLambda
            E.frame.semantic.generated.localArgs
            (mkAppN (A.rule.recursiveArgs)[j]
              E.frame.semantic.generated.localArgs)).abstractList
          A.rule.binders)
        (VExpr.wrapLams E.localDomains templateTarget)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      C.bodies[j] := by
  let hjArg : j < A.rule.recursiveArgs.size := by simpa using hj
  let E := C.resultAt j hjArg
  have Hfull := E.fullTranslationOfTemplate templateTarget (by
    simpa only [E] using Htemplate)
  simpa [CanonicalRecursiveResults.bodies, E] using Hfull

/-- Pointwise strict translation of a generated recursive result to its
canonical closed body in the fixed equation context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTranslation
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      C.bodies[j] := by
  let hjArg : j < A.rule.recursiveArgs.size := by simpa using hj
  let E := C.resultAt j hjArg
  apply C.bodyTranslationOfTemplate j hj E.templateTarget
  simpa only [E] using E.templateTranslation

/-- List-level strict translation for the complete generated recursive-result
spine. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyTranslations
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    List.Forall₂
      (TrExprS H.outVEnv Us (abstractForallContext equationDomains []))
      (A.rule.recursiveResults.toList.map
        (fun result => result.abstractList A.rule.binders))
      C.bodies := by
  apply List.forall₂_of_getElem
  · simp [C.bodies_length, A.rule.recursive_calls.size]
  · intro j hsource htarget
    have hj : j < C.bodies.length := htarget
    have hresult : j < A.rule.recursiveResults.size := by
      rw [A.rule.recursive_calls.size]
      simpa [C.bodies_length] using hj
    have Htranslation := C.bodyTranslation j hj
    rw [getElem!_pos A.rule.recursiveResults j hresult] at Htranslation
    simpa using Htranslation

/-- Every selected recursive-result body is already well formed in the one
fixed equation context shared by the entire rule.  This is the list-level
typing invariant consumed by the minor-application fold. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.CanonicalRecursiveResults.bodyWF
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
    {T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner}
    {B : A.NarrowFieldRuntimeFrame}
    (C : A.CanonicalRecursiveResults T B)
    (j : Nat) (hj : j < C.bodies.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++
        T.motives ++ T.minors ++
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse
    VExpr.WF H.outVEnv Us.length
      (abstractForallContext equationDomains []).toCtx C.bodies[j] := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++
      T.motives ++ T.minors ++
        (liftContextPrefix (T.motives ++ T.minors).length
          B.fieldDomains.reverse).reverse
  have hj' : j < A.rule.recursiveArgs.size := by
    simpa using hj
  let E := C.resultAt j hj'
  have hbody : C.bodies[j] =
      VExpr.wrapLams E.localDomains E.resultBody := by
    simp [CanonicalRecursiveResults.bodies, E]
  rw [hbody]
  refine ⟨VExpr.wrapForalls E.localDomains E.resultType, ?_⟩
  change H.outVEnv.HasType Us.length
    (abstractForallContext equationDomains []).toCtx
    (VExpr.wrapLams E.localDomains E.resultBody)
    (VExpr.wrapForalls E.localDomains E.resultType)
  simpa only [Us, equationDomains] using E.closed_typing

theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalRecursiveResults
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
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (B : A.NarrowFieldRuntimeFrame) :
    Nonempty (A.CanonicalRecursiveResults T B) := by
  classical
  exact ⟨{
    resultAt := fun j hj => Classical.choice
      (A.canonicalRecursiveResultAt T B j hj) }⟩

/-- Synchronize the selected minor and every canonical recursive result on one
recursor telescope, one narrowed field frame, and one literal anonymous
equation context.  No existential witness chosen by a pointwise theorem may
drift after this boundary. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMinorApplicationFrame
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ fieldDomains hypothesisDomains : List VExpr,
      ∃ targetResidual : VExpr,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        let inserted := T.motives ++ T.minors
        let equationFieldDomains :=
          (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFieldDomains
        let later := T.minors.drop (minorIdx + 1)
        let minorVar := equationFieldDomains.length + later.length
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          (∃ checkedDomains checkedEquationFieldDomains : List VExpr,
            checkedDomains.length = A.rule.allArgs.size ∧
            checkedEquationFieldDomains =
              (liftContextPrefix inserted.length
                checkedDomains.reverse).reverse ∧
            VEnv.IsDefEqCtx H.outVEnv Us.length []
              (checkedEquationFieldDomains.reverse ++
                (T.params ++ inserted).reverse)
              (abstractForallContext equationDomains []).toCtx) ∧
          H.outVEnv.HasType Us.length
          (abstractForallContext equationDomains []).toCtx
            (.bvar minorVar)
            ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
              targetResidual).liftN
                (later.length + 1 + equationFieldDomains.length) 0) ∧
          (∀ j (hj : j < C.bodies.length),
            let hjType : j < C.bodyTypes.length := by simpa using hj
            H.outVEnv.HasType Us.length
              (abstractForallContext equationDomains []).toCtx C.bodies[j]
              (C.bodyTypes)[j]) ∧
          (∀ j (hj : j < A.rule.recursiveArgs.size),
            let E := C.resultAt j hj
            OnCtx
                (E.localDomains.reverse ++
                  (abstractForallContext equationDomains []).toCtx)
                (H.outVEnv.IsType Us.length) ∧
              H.outVEnv.HasType Us.length
                (E.localDomains.reverse ++
                  (abstractForallContext equationDomains []).toCtx)
                E.resultBody E.resultType) ∧
          ∀ j (hj : j < C.bodies.length),
            VExpr.WF H.outVEnv Us.length
              (abstractForallContext equationDomains []).toCtx C.bodies[j] := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.narrowFieldRuntimeFrame with ⟨B⟩
  rcases A.finalNarrowSelectedMinorTypeFrame B with
    ⟨T, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, hminorType, HfixedContext, Hminor⟩
  rcases A.canonicalRecursiveResults T B with ⟨C⟩
  let inserted := T.motives ++ T.minors
  let equationFieldDomains :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFieldDomains
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := equationFieldDomains.length + later.length
  have hequationContext :
      (abstractForallContext equationDomains []).toCtx =
        (liftContextPrefix inserted.length B.fieldDomains.reverse) ++
          inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx := by
    rw [abstractForallContext_toCtx]
    simp [equationDomains, equationFieldDomains, List.reverse_append,
      List.append_assoc, VLCtx.toCtx]
  have HfixedEquationContext : OnCtx
      (abstractForallContext equationDomains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    rw [hequationContext]
    simpa only [inserted] using HfixedContext
  rcases A.finalCheckedNarrowEquationContextAlignmentFor B T with
    ⟨checkedDomains, checkedEquationFieldDomains, hchecked,
      hcheckedEquationFields, HcheckedEquation⟩
  have HcheckedEquation' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (checkedEquationFieldDomains.reverse ++
        (T.params ++ inserted).reverse)
      (abstractForallContext equationDomains []).toCtx := by
    rw [hequationContext]
    simpa only [inserted, List.append_assoc] using HcheckedEquation
  refine ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
    hfields, hhypotheses, hminorType, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact HfixedEquationContext
  · exact ⟨checkedDomains, checkedEquationFieldDomains, hchecked,
      by simpa only [inserted] using hcheckedEquationFields,
      HcheckedEquation'⟩
  · rw [hequationContext]
    simpa only [inserted, equationFieldDomains, later, minorVar,
      List.length_reverse] using Hminor
  · intro j hj
    simpa only [Us, equationDomains, inserted, equationFieldDomains,
      List.append_assoc] using C.bodyTyping j hj
  · intro j hj
    let E := C.resultAt j hj
    have Hclosed : H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx
        (VExpr.wrapLams E.localDomains E.resultBody)
        (VExpr.wrapForalls E.localDomains E.resultType) := by
      simpa only [equationDomains, inserted, equationFieldDomains,
        List.append_assoc] using E.closed_typing
    have Hopen := VEnv.HasType.wrapLams_inv H.outVEnvWF
      HfixedEquationContext Hclosed
    simpa only [Us, equationDomains, inserted, equationFieldDomains,
      List.append_assoc] using Hopen
  · intro j hj
    simpa only [Us, equationDomains, inserted, equationFieldDomains,
      List.append_assoc] using C.bodyWF j hj

/-- A well-formed canonical application of the selected minor to the fixed
equation fields forces those fields to agree with the installed field
telescope.  The selected minor is stored outside the equation fields, so its
lookup typing is first recognized as a common weakening of the still-open
installed telescope; `canonicalApplicationContext_of_weakened` then performs
the dependent binder-by-binder inversion. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMinorFieldContextOfApplication
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains hypothesisDomains : List VExpr)
    (targetResidual : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (Hctx :
      let inserted := T.motives ++ T.minors
      let equationFieldDomains :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFieldDomains
      OnCtx (abstractForallContext equationDomains []).toCtx
        (H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hminor :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFieldDomains :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFieldDomains
      let later := T.minors.drop (minorIdx + 1)
      let minorVar := equationFieldDomains.length + later.length
      H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx
        (.bvar minorVar)
        ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
          targetResidual).liftN
            (later.length + 1 + equationFieldDomains.length) 0))
    (Happlication :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFieldDomains :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFieldDomains
      let later := T.minors.drop (minorIdx + 1)
      let minorVar := equationFieldDomains.length + later.length
      VExpr.WF H.outVEnv Us.length
        (abstractForallContext equationDomains []).toCtx
        (VExpr.mkApps (.bvar minorVar)
          (recursorCanonicalVars equationFieldDomains.length))) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let inserted := T.motives ++ T.minors
    let equationFieldDomains :=
      (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
    let outer := inserted.reverse ++
      H.parameterSuffix.parameterDecls.toCtx
    let later := T.minors.drop (minorIdx + 1)
    let shift := later.length + 1
    let installedEquationFields :=
      (liftContextPrefix shift fieldDomains.reverse).reverse
    let installedEquationHypotheses :=
      (liftContextPrefixAt shift fieldDomains.length
        hypothesisDomains.reverse).reverse
    let installedEquationResidual := targetResidual.liftN shift
      (fieldDomains.length + hypothesisDomains.length)
    VEnv.IsDefEqCtx H.outVEnv Us.length []
        (equationFieldDomains.reverse ++ outer)
        (installedEquationFields.reverse ++ outer) ∧
      H.outVEnv.HasType Us.length
        (equationFieldDomains.reverse ++ outer)
        (VExpr.mkApps (.bvar
          (equationFieldDomains.length + later.length))
          (recursorCanonicalVars equationFieldDomains.length))
        (VExpr.wrapForalls installedEquationHypotheses
          installedEquationResidual) := by
  dsimp only at Hctx Hminor Happlication ⊢
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let inserted := T.motives ++ T.minors
  let equationFieldDomains :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let outer := inserted.reverse ++
    H.parameterSuffix.parameterDecls.toCtx
  let later := T.minors.drop (recursorMinorOffset indTypes owner + i + 1)
  let shift := later.length + 1
  let installedEquationFields :=
    (liftContextPrefix shift fieldDomains.reverse).reverse
  let installedEquationHypotheses :=
    (liftContextPrefixAt shift fieldDomains.length
      hypothesisDomains.reverse).reverse
  let installedEquationResidual := targetResidual.liftN shift
    (fieldDomains.length + hypothesisDomains.length)
  have hequationLength : equationFieldDomains.length =
      fieldDomains.length := by
    simp [equationFieldDomains, hfields, B.fieldDomains_length]
  have hctxShape :
      (abstractForallContext
        (H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFieldDomains) []).toCtx =
        equationFieldDomains.reverse ++ outer := by
    simp [abstractForallContext_toCtx, equationFieldDomains, outer,
      List.reverse_append, List.append_assoc, VLCtx.toCtx]
  rw [hctxShape] at Hctx Hminor Happlication
  have htypeShape :
      ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
          targetResidual).liftN
        (later.length + 1 + equationFieldDomains.length) 0) =
      ((VExpr.wrapForalls installedEquationFields
          (VExpr.wrapForalls installedEquationHypotheses
            installedEquationResidual)).liftN
        equationFieldDomains.length 0) := by
    rw [← VExpr.liftN_liftN]
    rw [VExpr.liftN_wrapForalls]
    simp only [Nat.zero_add]
    have hprefix : liftContextPrefixAt (later.length + 1) 0
        (fieldDomains ++ hypothesisDomains).reverse =
        liftContextPrefix (later.length + 1)
          (fieldDomains ++ hypothesisDomains).reverse := rfl
    rw [hprefix]
    rw [liftContextPrefix_reverse_append]
    simp [shift, installedEquationFields, installedEquationHypotheses,
      installedEquationResidual, VExpr.wrapForalls_append,
      equationFieldDomains, Nat.add_assoc]
  rw [htypeShape] at Hminor
  have htermShape :
      (VExpr.bvar later.length).liftN equationFieldDomains.length 0 =
        .bvar (equationFieldDomains.length + later.length) := by
    simp [VExpr.liftN, Nat.add_comm]
  rw [← htermShape] at Hminor Happlication
  have HfieldContext :=
    VEnv.HasType.canonicalApplicationContext_of_weakened
    H.outVEnvWF equationFieldDomains installedEquationFields outer Hctx
      Hminor (by simpa [installedEquationFields] using hequationLength)
      Happlication
  have W : Ctx.LiftN equationFieldDomains.length 0 outer
      (equationFieldDomains.reverse ++ outer) := by
    exact Ctx.LiftN.zero equationFieldDomains.reverse (by simp)
  have HminorBase : H.outVEnv.HasType Us.length outer
      (.bvar later.length)
      (VExpr.wrapForalls installedEquationFields
        (VExpr.wrapForalls installedEquationHypotheses
          installedEquationResidual)) :=
    (VEnv.HasType.weakN_iff H.outVEnvWF Hctx W).mp Hminor
  have HminorBase' : H.outVEnv.HasType Us.length outer
      (.bvar later.length)
      (VExpr.wrapForalls
        (installedEquationFields ++ installedEquationHypotheses)
        installedEquationResidual) := by
    rw [VExpr.wrapForalls_append]
    exact HminorBase
  have HpartialInstalled :=
    VEnv.HasType.mkApps_wrapForalls_prefix_canonical
      H.outVEnvWF.ordered
      (initial := installedEquationFields)
      (suffix := installedEquationHypotheses) HminorBase'
  have HpartialFixed := HpartialInstalled.defeqDFC
    H.outVEnvWF.ordered (HfieldContext.symm H.outVEnvWF.ordered)
  exact ⟨HfieldContext, by
    simpa [Us, inserted, equationFieldDomains, outer, later, shift,
      installedEquationFields, installedEquationHypotheses,
      installedEquationResidual, hequationLength, hfields,
      B.fieldDomains_length, VExpr.liftN, recursorCanonicalVars,
      List.length_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      HpartialFixed⟩

/-- Positive-arity selected minors admit their canonical field application
in the one fixed equation context shared by all recursive results.  The
application is first typed using the source-stable outer telescope, then
transported through the exact same checked field frame to the narrowed
equation fields.  Inverting that well-formed application additionally
identifies those fixed fields with the selected minor's installed fields. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMinorApplicationPositiveArity
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ fieldDomains hypothesisDomains : List VExpr,
      ∃ targetResidual : VExpr,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        let inserted := T.motives ++ T.minors
        let equationFieldDomains :=
          (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFieldDomains
        let later := T.minors.drop (minorIdx + 1)
        let minorVar := equationFieldDomains.length + later.length
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            (.bvar minorVar)
            ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
              targetResidual).liftN
                (later.length + 1 + equationFieldDomains.length) 0) ∧
          VExpr.WF H.outVEnv Us.length
            (abstractForallContext equationDomains []).toCtx
            (VExpr.mkApps (.bvar minorVar)
              (recursorCanonicalVars equationFieldDomains.length)) ∧
          let outer := inserted.reverse ++
            H.parameterSuffix.parameterDecls.toCtx
          let shift := later.length + 1
          let installedEquationFields :=
            (liftContextPrefix shift fieldDomains.reverse).reverse
          let installedEquationHypotheses :=
            (liftContextPrefixAt shift fieldDomains.length
              hypothesisDomains.reverse).reverse
          let installedEquationResidual := targetResidual.liftN shift
            (fieldDomains.length + hypothesisDomains.length)
          VEnv.IsDefEqCtx H.outVEnv Us.length []
              (equationFieldDomains.reverse ++ outer)
              (installedEquationFields.reverse ++ outer) ∧
            H.outVEnv.HasType Us.length
              (abstractForallContext equationDomains []).toCtx
              (VExpr.mkApps (.bvar minorVar)
                (recursorCanonicalVars equationFieldDomains.length))
              (VExpr.wrapForalls installedEquationHypotheses
                installedEquationResidual) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalCanonicalMinorApplicationFrame with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, hminorType, HfixedContext,
      _HcheckedFrame, Hminor, _HbodyTyping, _HopenTyping, _HbodyWF⟩
  let inserted := T.motives ++ T.minors
  let equationFieldDomains :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFieldDomains
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := equationFieldDomains.length + later.length
  rcases A.finalSelectedOuterRuntimeFieldAlignmentFor B T hpositive with
    ⟨selectedScope, Hselected, outerScope, Houter,
      selectedFields, outerFields, applicationHypotheses,
      applicationResidual, outerResidual,
      _hselectedScope, _hselectedShift, houterScope, houterShift,
      hscopeSplit, _hfactor, hrelative, hselectedFields, houterFields,
      _happlicationHypotheses, HouterTail, HselectedPrefix, HouterPrefix,
      Happlication, Hnatural, _Hruntime⟩
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hremainingLength :
      (H.bindings.flatMinors.fvars.drop minorIdx).length =
        (T.minors.drop minorIdx).length := by
    simp only [List.length_drop]
    rw [H.bindings.flatMinors.length_fvars, T.minors_length]
  have hdrop : T.minors.drop minorIdx = T.minors[minorIdx] :: later := by
    simpa [later] using List.drop_eq_getElem_cons hminor
  have hgeneratedRemaining : (T.minors.drop minorIdx).length =
      later.length + 1 := by
    simp [hdrop]
  have Hnatural' := Hnatural
  rw [hrelative, liftForallDomains_skipN_consN_refl,
    hremainingLength, hgeneratedRemaining] at Hnatural'
  have HselectedOuter := VEnv.IsDefEqCtx.rebaseCommonSuffix H.outVEnvWF
    (HouterPrefix.symm H.outVEnvWF.ordered) Hnatural'
  have HouterApplication := Happlication.defeqDFC H.outVEnvWF.ordered
    HselectedOuter
  rcases A.finalCheckedConstructorFieldFrame with
    ⟨T₁, checkedDomains, checkedResidual, _introTarget, hparams,
      hchecked, Hchecked, _HcheckedResidual, _HcheckedType,
      _HcheckedTypeT, HcheckedContext, _HintroType, _Hintro,
      _HintroShape⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparamsT, hmotivesT, hminorsT,
      _hindicesT, _hmajorT, _hresultT⟩
  rw [hparamsT] at hparams HcheckedContext
  have hparams' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      T.params.reverse H.parameterSuffix.parameterDecls.toCtx := by
    simpa only [← H.parameterDecls] using hparams
  have Hchecked' : TrExprS H.outVEnv Us
      H.parameterSuffix.parameterDecls A.semantics.parameterTail
      (VExpr.wrapForalls checkedDomains checkedResidual) := by
    simpa only [← H.parameterDecls] using Hchecked
  rcases A.finalOuterCheckedEquationFieldAlignmentFor T outerScope Houter
      outerFields outerResidual houterScope houterShift houterFields
      HouterTail HouterPrefix checkedDomains checkedResidual hchecked
      Hchecked' with
    ⟨outerCheckedFields, houterCheckedFields, HouterChecked⟩
  rcases A.finalCheckedNarrowEquationContextAlignmentFromFrameFor B T
      checkedDomains checkedResidual hparams' hchecked Hchecked'
      HcheckedContext with
    ⟨checkedEquationFields, hcheckedEquationFields, HcheckedFixed⟩
  rw [houterCheckedFields] at HouterChecked
  rw [hcheckedEquationFields] at HcheckedFixed
  have HouterFixed := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HouterChecked HcheckedFixed
  have HfixedApplication := HouterApplication.defeqDFC
    H.outVEnvWF.ordered HouterFixed
  have hequationContext :
      (abstractForallContext equationDomains []).toCtx =
        equationFieldDomains.reverse ++ inserted.reverse ++
          H.parameterSuffix.parameterDecls.toCtx := by
    rw [abstractForallContext_toCtx]
    simp [equationDomains, equationFieldDomains, List.reverse_append,
      List.append_assoc, VLCtx.toCtx]
  have HapplicationWF : VExpr.WF H.outVEnv Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.mkApps (.bvar minorVar)
        (recursorCanonicalVars equationFieldDomains.length)) := by
    rw [hequationContext]
    let applicationType := VExpr.wrapForalls
      (liftContextPrefixAt (later.length + 1) selectedFields.length
        applicationHypotheses.reverse).reverse
      (applicationResidual.liftN (later.length + 1)
        (selectedFields.length + applicationHypotheses.length))
    refine ⟨applicationType, ?_⟩
    change H.outVEnv.HasType Us.length
      (equationFieldDomains.reverse ++ inserted.reverse ++
        H.parameterSuffix.parameterDecls.toCtx)
      (VExpr.mkApps (.bvar minorVar)
        (recursorCanonicalVars equationFieldDomains.length))
      applicationType
    simpa [applicationType, minorVar, minorIdx, equationFieldDomains,
      inserted, later, VExpr.liftN, hselectedFields, houterFields,
      B.fieldDomains_length, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using HfixedApplication
  have HinstalledFields :=
    A.finalCanonicalMinorFieldContextOfApplication B T fieldDomains
      hypothesisDomains targetResidual hfields HfixedContext Hminor
      HapplicationWF
  have HinstalledTyping : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.mkApps (.bvar minorVar)
        (recursorCanonicalVars equationFieldDomains.length))
      (VExpr.wrapForalls
        (liftContextPrefixAt (later.length + 1) fieldDomains.length
          hypothesisDomains.reverse).reverse
        (targetResidual.liftN (later.length + 1)
          (fieldDomains.length + hypothesisDomains.length))) := by
    rw [hequationContext]
    simpa only [Us, minorIdx, equationFieldDomains, inserted, later,
      minorVar, List.append_assoc] using HinstalledFields.2
  exact ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
    hfields, hhypotheses, hminorType, HfixedContext, Hminor,
    HapplicationWF, HinstalledFields.1, HinstalledTyping⟩

/-- Apply all canonical recursive results to a selected minor that has
already been applied to the fixed equation fields. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMinorRecursiveApplicationOfContext
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
    (B : A.NarrowFieldRuntimeFrame)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (C : A.CanonicalRecursiveResults T B)
    (fieldDomains hypothesisDomains : List VExpr)
    (targetResidual : VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hhypotheses : hypothesisDomains.length = A.rule.recursiveArgs.size)
    (htarget : T.minors[recursorMinorOffset indTypes owner + i]! =
      VExpr.wrapForalls (fieldDomains ++ hypothesisDomains) targetResidual)
    (Hctx :
      let inserted := T.motives ++ T.minors
      let equationFields :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFields
      OnCtx (abstractForallContext equationDomains []).toCtx
        (H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hfield :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFields :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let later := T.minors.drop (minorIdx + 1)
      let installedFields :=
        (liftContextPrefix (later.length + 1) fieldDomains.reverse).reverse
      let outer := inserted.reverse ++ H.parameterSuffix.parameterDecls.toCtx
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (equationFields.reverse ++ outer)
        (installedFields.reverse ++ outer))
    (Hpartial :
      let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
      let minorIdx := recursorMinorOffset indTypes owner + i
      let inserted := T.motives ++ T.minors
      let equationFields :=
        (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
      let equationDomains :=
        H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
          equationFields
      let later := T.minors.drop (minorIdx + 1)
      let installedHypotheses :=
        (liftContextPrefixAt (later.length + 1) fieldDomains.length
          hypothesisDomains.reverse).reverse
      let installedResidual := targetResidual.liftN (later.length + 1)
        (fieldDomains.length + hypothesisDomains.length)
      H.outVEnv.HasType Us.length
        (abstractForallContext equationDomains []).toCtx
        (VExpr.mkApps (.bvar (equationFields.length + later.length))
          (recursorCanonicalVars equationFields.length))
        (VExpr.wrapForalls installedHypotheses installedResidual)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    let inserted := T.motives ++ T.minors
    let equationFields :=
      (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
    let equationDomains :=
      H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
        equationFields
    let later := T.minors.drop (minorIdx + 1)
    let fn := VExpr.mkApps
      (.bvar (equationFields.length + later.length))
      (recursorCanonicalVars equationFields.length)
    let finalType := VExpr.applyForallType
      (VExpr.wrapForalls (VExpr.liftClosedDomains C.bodyTypes 0)
        (targetResidual.liftN (later.length + 1)
          (fieldDomains.length + hypothesisDomains.length)))
      C.bodies
    H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx
      (VExpr.mkApps fn C.bodies) finalType := by
  dsimp only at Hctx Hfield Hpartial ⊢
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let inserted := T.motives ++ T.minors
  let equationFields :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++ equationFields
  let later := T.minors.drop (minorIdx + 1)
  let remaining := T.minors.drop minorIdx
  let installedFields :=
    (liftContextPrefix remaining.length fieldDomains.reverse).reverse
  let installedHypotheses :=
    (liftContextPrefixAt remaining.length fieldDomains.length
      hypothesisDomains.reverse).reverse
  let installedResidual := targetResidual.liftN remaining.length
    (fieldDomains.length + hypothesisDomains.length)
  let fn := VExpr.mkApps
    (.bvar (equationFields.length + later.length))
    (recursorCanonicalVars equationFields.length)
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hremaining : remaining = T.minors[minorIdx] :: later := by
    simpa [remaining, later] using List.drop_eq_getElem_cons hminor
  have hremainingLength : remaining.length = later.length + 1 := by
    simp [hremaining]
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
      equationFields, inserted, later, hremainingLength,
      List.append_assoc] using Hfield
  have HfieldT : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (equationPrefix ++ T.params.reverse)
      (installedPrefix ++ T.params.reverse) := by
    have Hrebased := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.rebaseCommonSuffix
      H.outVEnvWF Hparams' Hfield'
    simpa [equationPrefix, installedPrefix, installedFields,
      hremainingLength, List.append_assoc] using Hrebased
  have HequationParams :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      Hparams' HfieldT.isType
  have HbaseMixed := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.transEmpty
    H.outVEnvWF (HfieldT.symm H.outVEnvWF.ordered) HequationParams
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (T.params ++ T.motives ++ T.minors ++ installedFields).reverse
      equationDomains.reverse := by
    simpa [equationPrefix, installedPrefix, equationDomains,
      equationFields, inserted, List.reverse_append,
      List.append_assoc] using HbaseMixed
  have Hhypotheses := A.finalCanonicalRecursiveHypothesisContext B T C
    fieldDomains hypothesisDomains targetResidual hfields hhypotheses
      htarget (by simpa [Us, minorIdx, remaining, installedFields,
        equationDomains, equationFields, inserted,
        List.append_assoc] using Hbase)
  have Hhypotheses' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (installedHypotheses.reverse ++
        (abstractForallContext equationDomains []).toCtx)
      ((VExpr.liftClosedDomains C.bodyTypes 0).reverse ++
        (abstractForallContext equationDomains []).toCtx) := by
    simpa [remaining, installedHypotheses, equationDomains,
      equationFields, inserted, abstractForallContext_toCtx,
      VLCtx.toCtx, List.reverse_append, List.append_assoc] using Hhypotheses
  have Hpartial' : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx fn
      (VExpr.wrapForalls installedHypotheses installedResidual) := by
    simpa [remaining, installedHypotheses, installedResidual,
      hremainingLength, equationDomains, equationFields, inserted,
      later, fn] using Hpartial
  have HbodyTypings := C.bodyTypings
  have Hexact := VEnv.HasType.mkApps_of_defeqLiftClosedDomains_exact
    (installedDomains := installedHypotheses)
    (resultType := installedResidual) (types := C.bodyTypes)
    (args := C.bodies) H.outVEnvWF Hctx Hpartial' Hhypotheses' (by
      simpa only [Us, equationDomains, inserted, equationFields,
        List.append_assoc] using HbodyTypings)
  simpa [installedResidual, hremainingLength, fn, later, equationFields,
    inserted, B.fieldDomains_length] using Hexact

/-- Degenerate generated rules need no application fold: when the selected
constructor has neither fields nor recursive hypotheses, the selected minor
variable itself is the complete RHS and is already typed in the fixed
equation context.  Isolating this case lets the positive-arity replay theorem
remain honest about the nonempty telescope premise it uses. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalMinorApplicationZeroArity
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ targetResidual : VExpr,
        C.bodies = [] ∧
        let inserted := T.motives ++ T.minors
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted
        let later := T.minors.drop (minorIdx + 1)
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            (.bvar later.length)
            (targetResidual.liftN (later.length + 1) 0) := by
  dsimp only
  have hfieldsZero : A.rule.allArgs.size = 0 := by omega
  have hhypothesesZero : A.rule.recursiveArgs.size = 0 := by omega
  rcases A.finalCanonicalMinorApplicationFrame with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, _hminorType, Hctx, _HcheckedEquation, Hminor,
      _HbodyTyping, _HopenBodyTyping, _HbodyWF⟩
  have hfieldDomains : fieldDomains = [] :=
    List.eq_nil_of_length_eq_zero (hfields.trans hfieldsZero)
  have hhypothesisDomains : hypothesisDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (hhypotheses.trans hhypothesesZero)
  have hframeFields : B.fieldDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (B.fieldDomains_length.trans hfieldsZero)
  have hbodies : C.bodies = [] :=
    List.eq_nil_of_length_eq_zero (by
      rw [C.bodies_length, hhypothesesZero])
  subst fieldDomains
  subst hypothesisDomains
  exact ⟨B, T, C, targetResidual, hbodies,
    by simpa [hframeFields, liftContextPrefix, liftContextPrefixAt,
      List.append_assoc] using Hctx,
    by simpa [hframeFields, liftContextPrefix, liftContextPrefixAt,
      VExpr.wrapForalls, VLCtx.toCtx, List.append_assoc] using Hminor⟩

/-- Positive-arity generated RHS in its fixed narrowed equation context.
The selected minor, constructor fields, and generated recursive results are
all translated strictly to the same application spine that is independently
typed by the canonical minor fold. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalRhsPositiveArity
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
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ equationFields : List VExpr,
      ∃ rhsBody typeBody : VExpr,
        equationFields.length = A.rule.allArgs.size ∧
        equationFields =
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse ∧
        let inserted := T.motives ++ T.minors
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFields
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          TrExprS H.outVEnv Us
            (abstractForallContext equationDomains [])
            (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            rhsBody typeBody := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalCanonicalMinorApplicationPositiveArity hpositive with
    ⟨B, T, C, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, hminorType, Hctx, _Hminor, HpartialWF,
      Hfield, Hpartial⟩
  let inserted := T.motives ++ T.minors
  let equationFields :=
    (liftContextPrefix inserted.length B.fieldDomains.reverse).reverse
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFields
  let later := T.minors.drop (minorIdx + 1)
  let minorVar := equationFields.length + later.length
  let fn := VExpr.mkApps (.bvar minorVar)
    (recursorCanonicalVars equationFields.length)
  have Hrhs := A.finalCanonicalMinorRecursiveApplicationOfContext B T C
      fieldDomains hypothesisDomains targetResidual hfields hhypotheses
      hminorType Hctx Hfield Hpartial
  let finalType := VExpr.applyForallType
    (VExpr.wrapForalls (VExpr.liftClosedDomains C.bodyTypes 0)
      (targetResidual.liftN (later.length + 1)
        (fieldDomains.length + hypothesisDomains.length)))
    C.bodies
  let rhsBody := VExpr.mkApps fn C.bodies
  have HrhsTyped : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx rhsBody finalType := by
    simpa only [Us, minorIdx, inserted, equationFields, equationDomains,
      later, minorVar, fn, rhsBody, List.append_assoc] using Hrhs
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hminorVar : minorVar < equationDomains.length := by
    dsimp only [minorVar, equationDomains, equationFields, inserted, later]
    simp only [List.length_append, List.length_reverse,
      liftContextPrefix_length, List.length_drop]
    omega
  have HminorTr : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (.bvar minorVar) (.bvar minorVar) :=
    TrExprS.bvar_of_abstractForallContext equationDomains [] minorVar hminorVar
  have HfieldsTr := A.finalNarrowEquationFieldTranslationsFor B T
  have HpartialTr := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx HminorTr HfieldsTr HpartialWF
  have HresultsTr : List.Forall₂
      (TrExprS H.outVEnv Us
        (abstractForallContext equationDomains []))
      ((A.rule.recursiveResults.map fun result =>
        result.abstractList A.rule.binders).toList) C.bodies := by
    simpa only [Us, equationDomains, inserted, equationFields,
      Array.toList_map, List.append_assoc] using C.bodyTranslations
  have HrhsTr₀ := checkPositivityStep.TrExprS.mkAppList
    H.outVEnvWF.ordered Hctx HpartialTr HresultsTr
      (show VExpr.WF H.outVEnv Us.length
        (abstractForallContext equationDomains []).toCtx rhsBody from
          ⟨finalType, HrhsTyped⟩)
  have hsourceMinor :
      A.rule.allArgs.size +
          ((H.recInfos.flatMap (·.minors)).size - 1 - minorIdx) =
        minorVar := by
    dsimp only [minorVar, equationFields, inserted, later]
    simp only [List.length_reverse, liftContextPrefix_length,
      List.length_drop, B.fieldDomains_length, T.minors_length]
    omega
  have hsourceShape := A.rule.abstractedSourceRhsAtMinorArray
  rw [hsourceMinor] at hsourceShape
  have HrhsTr : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody := by
    rw [hsourceShape]
    simpa [rhsBody, fn, Expr.mkAppN_eq_mkAppList, equationFields,
      equationDomains, inserted, B.fieldDomains_length,
      List.append_assoc] using HrhsTr₀
  exact ⟨B, T, C, equationFields, rhsBody, finalType,
    by simp [equationFields, B.fieldDomains_length], rfl, Hctx, HrhsTr,
    HrhsTyped⟩

/-- Zero-arity counterpart of `finalCanonicalRhsPositiveArity`.  Both
application arrays are empty, so the complete source RHS and canonical RHS
are the selected minor variable itself. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalRhsZeroArity
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
    ∃ B : A.NarrowFieldRuntimeFrame,
      ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
          (H.generated.entry owner howner).info.type H.entries[owner].2.type
          stats.params.size (H.recInfos.map (·.motive)).size
          (H.recInfos.flatMap (·.minors)).size
          H.recInfos[owner]!.indices.size owner,
      ∃ C : A.CanonicalRecursiveResults T B,
      ∃ equationFields : List VExpr,
      ∃ rhsBody typeBody : VExpr,
        equationFields.length = A.rule.allArgs.size ∧
        equationFields =
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse ∧
        let inserted := T.motives ++ T.minors
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFields
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          TrExprS H.outVEnv Us
            (abstractForallContext equationDomains [])
            (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            rhsBody typeBody := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  have hfieldsZero : A.rule.allArgs.size = 0 := by omega
  have hresultsZero : A.rule.recursiveArgs.size = 0 := by omega
  rcases A.finalCanonicalMinorApplicationZeroArity hzero with
    ⟨B, T, C, targetResidual, hbodies, Hctx, Hminor⟩
  let inserted := T.motives ++ T.minors
  let equationFields : List VExpr := []
  let equationDomains :=
    H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
      equationFields
  let later := T.minors.drop (minorIdx + 1)
  let rhsBody : VExpr := .bvar later.length
  let typeBody := targetResidual.liftN (later.length + 1) 0
  have Hctx' : OnCtx (abstractForallContext equationDomains []).toCtx
      (H.outVEnv.IsType Us.length) := by
    simpa only [Us, inserted, equationFields, equationDomains,
      List.append_nil] using Hctx
  have HrhsTyped : H.outVEnv.HasType Us.length
      (abstractForallContext equationDomains []).toCtx rhsBody typeBody := by
    simpa only [Us, minorIdx, inserted, equationFields, equationDomains,
      later, rhsBody, typeBody, List.append_nil] using Hminor
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hminorVar : later.length < equationDomains.length := by
    dsimp only [later, equationDomains, equationFields, inserted]
    simp only [List.length_append, List.length_drop, List.length_nil,
      Nat.add_zero]
    omega
  have HvarTr : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (.bvar later.length) rhsBody := by
    exact TrExprS.bvar_of_abstractForallContext equationDomains []
      later.length hminorVar
  have hallArgs : A.rule.allArgs = #[] :=
    Array.eq_empty_of_size_eq_zero hfieldsZero
  have hrecursiveResultsSize : A.rule.recursiveResults.size = 0 := by
    rw [A.rule.recursive_calls.size]
    exact hresultsZero
  have hrecursiveResults : A.rule.recursiveResults = #[] :=
    Array.eq_empty_of_size_eq_zero hrecursiveResultsSize
  have hframeFields : B.fieldDomains = [] :=
    List.eq_nil_of_length_eq_zero
      (B.fieldDomains_length.trans hfieldsZero)
  have hsourceMinor :
      A.rule.allArgs.size +
          ((H.recInfos.flatMap (·.minors)).size - 1 - minorIdx) =
        later.length := by
    dsimp only [later]
    simp only [List.length_drop, T.minors_length]
    omega
  have hsourceShape := A.rule.abstractedSourceRhsAtMinorArray
  rw [hsourceMinor] at hsourceShape
  have hsource : A.rule.sourceRhsBody.abstractList A.rule.binders =
      .bvar later.length := by
    simpa [hallArgs, hrecursiveResults, Expr.mkAppN_eq_mkAppList,
      Expr.mkAppList] using hsourceShape
  have HrhsTr : TrExprS H.outVEnv Us
      (abstractForallContext equationDomains [])
      (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody := by
    rw [hsource]
    exact HvarTr
  exact ⟨B, T, C, equationFields, rhsBody, typeBody,
    by simp [equationFields, hfieldsZero], by
      simp [equationFields, hframeFields, liftContextPrefix,
        liftContextPrefixAt],
    Hctx', HrhsTr, HrhsTyped⟩

/-- Arity-independent endpoint for the generated right-hand side.  The
positive and degenerate production paths expose the same semantic payload:
an exact recursor telescope, the canonical constructor-field suffix, a
strict translation of the retained source RHS, and its typing derivation.
Keeping the arithmetic split internal is important for the final equation
builder, which traverses rules uniformly. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalRhs
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
      ∃ rhsBody typeBody : VExpr,
        equationFields.length = A.rule.allArgs.size ∧
        equationFields =
          (liftContextPrefix (T.motives ++ T.minors).length
            B.fieldDomains.reverse).reverse ∧
        let inserted := T.motives ++ T.minors
        let equationDomains :=
          H.parameterSuffix.parameterDecls.toCtx.reverse ++ inserted ++
            equationFields
        OnCtx (abstractForallContext equationDomains []).toCtx
            (H.outVEnv.IsType Us.length) ∧
          TrExprS H.outVEnv Us
            (abstractForallContext equationDomains [])
            (A.rule.sourceRhsBody.abstractList A.rule.binders) rhsBody ∧
          H.outVEnv.HasType Us.length
            (abstractForallContext equationDomains []).toCtx
            rhsBody typeBody := by
  dsimp only
  by_cases hzero : A.rule.allArgs.size + A.rule.recursiveArgs.size = 0
  · exact A.finalCanonicalRhsZeroArity hzero
  · exact A.finalCanonicalRhsPositiveArity (Nat.pos_of_ne_zero hzero)

/-- Rule-indexed existential specialization of
`canonicalRecursiveResultTypingFor`.  It remains convenient for pointwise
consumers that do not need to retain a common equation frame. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.canonicalRecursiveResultTyping
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
    (j : Nat) (hj : j < A.rule.recursiveArgs.size)
    (B : A.NarrowFieldRuntimeFrame :=
      Classical.choice A.narrowFieldRuntimeFrame) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ F : A.RecursiveCallRecursorFrame j hj,
      ∃ (equationDomains localDomains : List VExpr)
          (resultBody resultType : VExpr),
        equationDomains.length = A.rule.binders.length ∧
        localDomains.length = F.semantic.generated.localArgs.size ∧
        Expr.LambdaTelescope
          (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
          localDomains.length
          ((F.semantic.generated.body.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.binders F.semantic.generated.localArgs.size) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (equationDomains ++ localDomains) [])
          ((F.semantic.generated.body.abstractList
            F.semantic.generated.arguments_bound.fvars).abstractList
              A.rule.binders F.semantic.generated.localArgs.size)
          resultBody ∧
        H.outVEnv.HasType Us.length
          (abstractForallContext equationDomains []).toCtx
          (VExpr.wrapLams localDomains resultBody)
          (VExpr.wrapForalls localDomains resultType) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.recursiveCallRecursorFrame j hj with ⟨F⟩
  rcases A.finalRecursorTelescopeTranslation with ⟨T⟩
  rcases F.canonicalRecursiveCallBodyWF T (B := B) with
    ⟨equationDomains, localDomains, prefixTarget, indexTargets,
      majorTarget, ownerTarget, hlocal, _hequationFixed, hequation, _Hctx,
      _HlocalTemplate, Hbody,
      _HtemplateResidual, _HmotiveApplication, _HbodyType, Hclosed, _HbodyWF⟩
  let args := indexTargets ++ [majorTarget]
  let resultBody := VExpr.mkApps prefixTarget args
  let resultType := VExpr.mkApps ownerTarget args
  have Htelescope :=
    F.semantic.generated.outerAbstractedLambdaTelescope A.rule.binders
  have Htelescope' : Expr.LambdaTelescope
      (A.rule.recursiveResults[j]!.abstractList A.rule.binders)
      localDomains.length
      ((F.semantic.generated.body.abstractList
        F.semantic.generated.arguments_bound.fvars).abstractList
          A.rule.binders F.semantic.generated.localArgs.size) := by
    simpa [hlocal] using Htelescope
  exact ⟨F, equationDomains, localDomains, resultBody, resultType,
    hequation, hlocal, Htelescope', by simpa [resultBody, args] using Hbody,
    by simpa [resultBody, resultType, args] using Hclosed⟩

/-- Weaken the canonical recursive-call prefix beneath the higher-order
lambda domains and identify its source with the exact two-stage abstraction
performed by production. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.RecursiveCallRecursorFrame.outerAbstractedCommonPrefixTranslation
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
    (F : A.RecursiveCallRecursorFrame j hj)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains localDomains : List VExpr)
    (hfields : fieldDomains.length = A.rule.allArgs.size)
    (hlocal : localDomains.length = F.semantic.generated.localArgs.size)
    (Hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let equationDomains :=
      (T.params ++ T.motives ++ T.minors) ++ fieldDomains
    let localPrefix :=
      mkAppN
        (mkAppN
          (mkAppN
            (.const F.semantic.generated.recursorName
              (AddInductive.getRecLevels H.elimLevel stats.levels))
            (stats.params.map fun arg => arg.abstractList
              F.semantic.generated.arguments_bound.fvars))
          ((H.recInfos.map (·.motive)).map fun arg => arg.abstractList
            F.semantic.generated.arguments_bound.fvars))
        ((H.recInfos.flatMap (·.minors)).map fun arg => arg.abstractList
          F.semantic.generated.arguments_bound.fvars)
    let selectedOwner := F.semantic.generated.ownerIdx
    let recursor := (H.entries[selectedOwner]'F.entry_lt).2
    let target :=
      ((VExpr.mkApps
          ((VExpr.const recursor.name (VLevel.params Us.length)).liftN
            (T.params ++ T.motives ++ T.minors).length 0)
          (recursorCanonicalVars
            (T.params ++ T.motives ++ T.minors).length)).liftN
        fieldDomains.length 0)
    TrExprS H.outVEnv Us
      (abstractForallContext localDomains
        (abstractForallContext equationDomains []))
      (localPrefix.abstractList A.rule.binders
        F.semantic.generated.localArgs.size)
      (target.liftN localDomains.length 0) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let equationDomains :=
    (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  let localPrefix :=
    mkAppN
      (mkAppN
        (mkAppN
          (.const F.semantic.generated.recursorName
            (AddInductive.getRecLevels H.elimLevel stats.levels))
          (stats.params.map fun arg => arg.abstractList
            F.semantic.generated.arguments_bound.fvars))
        ((H.recInfos.map (·.motive)).map fun arg => arg.abstractList
          F.semantic.generated.arguments_bound.fvars))
      ((H.recInfos.flatMap (·.minors)).map fun arg => arg.abstractList
        F.semantic.generated.arguments_bound.fvars)
  let selectedOwner := F.semantic.generated.ownerIdx
  let recursor := (H.entries[selectedOwner]'F.entry_lt).2
  let target :=
    ((VExpr.mkApps
        ((VExpr.const recursor.name (VLevel.params Us.length)).liftN
          (T.params ++ T.motives ++ T.minors).length 0)
        (recursorCanonicalVars
          (T.params ++ T.motives ++ T.minors).length)).liftN
      fieldDomains.length 0)
  have Hbase := F.canonicalPrefixResidualTranslation
    T fieldDomains hfields Hctx
  have Hweak := Hbase.weakBV H.outVEnvWF.ordered
    (abstractForallContext.bvLift localDomains
      (abstractForallContext equationDomains []))
  have hsource := F.outerAbstractedCommonPrefix_eq_lift
  dsimp only at hsource
  dsimp only [Us, equationDomains, localPrefix, selectedOwner, recursor,
    target] at Hweak ⊢
  rw [hsource]
  simpa only [hlocal] using Hweak


end VerifyInductive
end Lean4Lean
