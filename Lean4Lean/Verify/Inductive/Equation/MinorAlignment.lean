import Lean4Lean.Verify.Inductive.Equation.MinorContext

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Recover the exact source construction behind this rule's flattened minor
domain.  In particular, the retained second-pass shape names the same source
family and constructor slot as rule generation, rather than merely occupying
the same flattened minor position. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorShape
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ D : BoundFVarDeclarationAt H.localContext
          (H.recInfos.flatMap (·.minors)) minorIdx,
        ∃ O : H.origins.FlatMinorOrigin D,
          ∃ S : RecInfoMinorTypeShape,
            S.origin = D.type ∧
            S.localIndex = i ∧
            S.sourceConstructors = indTypes[owner]!.ctors ∧
            S.constructor = indTypes[owner]!.ctors[i] ∧
            S.fields.size = A.rule.allArgs.size ∧
            Nonempty (RecInfoMinorSemanticSourceAt H.recursorWF S
              H.parameterSuffix.parameterDecls) ∧
            ∃ hypothesisOrigins,
              S.hypothesis_type_origins = some hypothesisOrigins ∧
              hypothesisOrigins.stats = stats ∧
              hypothesisOrigins.recInfos.map (·.motive) =
                H.recInfos.map (·.motive) ∧
              ∃ traversal : RecInfoMinorTraversalShape,
                S.traversal = some traversal ∧
                traversal.constructor = S.constructor ∧
                traversal.fields = S.fields ∧
                traversal.recursiveFields = S.recursiveFields ∧
                traversal.stats = stats ∧
                AddInductive.isValidIndApp? stats traversal.terminal = some
                  (AddInductive.getIIndices stats traversal.terminal).1 ∧
                S.motiveApp = (
                  let (motiveOwner, indices) :=
                    AddInductive.getIIndices stats traversal.terminal
                  Expr.app
                    (mkAppN H.recInfos[motiveOwner]!.motive indices)
                    (mkAppN
                      (mkAppN (.const S.constructor.name stats.levels)
                        stats.params)
                      S.fields)) ∧
                BindingContextLE traversal.rootContext H.localContext ∧
                BindingContextLE traversal.terminalContext H.localContext ∧
                BindingContextLE S.sourceFullContext H.localContext ∧
                let sourceBinders := H.params.fvars ++
                  H.bindings.motives.fvars ++
                    H.bindings.flatMinors.fvars.take minorIdx
                TrExprS H.outVEnv Us
                    (abstractForallContext
                      (T.params ++ T.motives ++ T.minors.take minorIdx) [])
                    (D.type.abstractList sourceBinders) T.minors[minorIdx]! ∧
                  H.outVEnv.IsType Us.length
                    (abstractForallContext
                      (T.params ++ T.motives ++
                        T.minors.take minorIdx) []).toCtx
                    T.minors[minorIdx]! := by
  dsimp only
  rcases A.finalSelectedMinorDomain with
    ⟨T, D, O, _discardedShape, Hdomain, HdomainType⟩
  have hposition := A.selectedMinorOriginPosition O
  have hsourceOwner : O.owner < indTypes.size := by
    rw [hposition.1]
    exact A.sourceOwner_lt
  have hshapeBound : O.localIndex <
      H.origins.minorTypes[O.owner]!.size := by
    rw [(H.origins.minors O.owner O.owner_lt).size_eq]
    simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt
  let S := H.origins.minorShapes O.owner O.owner_lt O.localIndex hshapeBound
  have Hsource : S.origin =
        H.origins.minorTypes[O.owner]![O.localIndex]! ∧
      S.localIndex = O.localIndex ∧
      S.sourceConstructors = indTypes[O.owner]!.ctors ∧
      S.HasHypothesisTypeOrigins stats H.recInfos ∧
        ∃ traversal, S.traversal = some traversal ∧
          traversal.constructor = S.constructor ∧
          traversal.fields = S.fields ∧
          traversal.recursiveFields = S.recursiveFields ∧
          traversal.stats = stats ∧
          AddInductive.isValidIndApp? stats traversal.terminal = some
            (AddInductive.getIIndices stats traversal.terminal).1 ∧
          S.motiveApp = (
            let (motiveOwner, indices) :=
              AddInductive.getIIndices stats traversal.terminal
            Expr.app
              (mkAppN H.recInfos[motiveOwner]!.motive indices)
              (mkAppN
                (mkAppN (.const S.constructor.name stats.levels)
                  stats.params)
                S.fields)) ∧
          BindingContextLE traversal.rootContext H.localContext ∧
          BindingContextLE traversal.terminalContext H.localContext ∧
          BindingContextLE S.sourceFullContext H.localContext := by
    simpa [S] using H.minorSources O.owner O.owner_lt hsourceOwner
      O.localIndex hshapeBound
  have horigin : S.origin = D.type :=
    Hsource.1.trans O.originType_eq.symm
  have hlocal : S.localIndex = i := Hsource.2.1.trans hposition.2
  have hconstructorsAtOrigin :
      S.sourceConstructors = indTypes[O.owner]!.ctors := by
    simpa [S] using Hsource.2.2.1
  have hconstructors :
      S.sourceConstructors = indTypes[owner]!.ctors := by
    simpa [hposition.1] using hconstructorsAtOrigin
  rcases Hsource.2.2.2 with
    ⟨HhypothesisOrigins, traversal, htraversal, htraversalConstructor,
      htraversalFields, htraversalRecursiveFields, hstats, hvalid,
      hmotiveApp,
      hrootContext, hterminalContext, hsourceContext⟩
  rcases S.hypothesisTypeOrigins_exists stats H.recInfos
      HhypothesisOrigins with
    ⟨hypothesisOrigins, hhypothesisOrigins, hhypothesisStats,
      hhypothesisRecInfos⟩
  have hconstructor : S.constructor = indTypes[owner]!.ctors[i] := by
    have hsourceConstructor := S.sourceConstructor
    rw [hconstructors, hlocal] at hsourceConstructor
    simpa [hctor] using hsourceConstructor.symm
  have hprefixTraversal := traversal.parameterPrefix
  rw [hstats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.semantics.parameterTail :=
    hprefixTraversal.tail_eq A.semantics.parameterPrefix
  have hsemanticResidual :
      A.semantics.fieldOpening.residual.isForall = false := by
    rw [← A.semantics.fieldOpening.closed, Expr.abstractList_isForall]
    exact A.semantics.target_not_forall
  have hfieldCount : S.fields.size = A.rule.allArgs.size := by
    have HtraversalTelescope := traversal.fieldTelescope
    rw [htraversalFields, hparameterTail] at HtraversalTelescope
    exact (HtraversalTelescope.eq_of_residual_not_forall
      A.semantics.fieldOpening.telescope
      traversal.fieldResidual_not_forall hsemanticResidual).1
  have Hsemantic :
      Nonempty (RecInfoMinorSemanticSourceAt H.recursorWF S
        H.parameterSuffix.parameterDecls) := by
    simpa [S] using
      H.minorSemantics O.owner O.owner_lt O.localIndex hshapeBound
  exact ⟨T, D, O, S, horigin, hlocal, hconstructors, hconstructor,
    hfieldCount, Hsemantic, hypothesisOrigins, hhypothesisOrigins,
    hhypothesisStats,
    hhypothesisRecInfos,
    traversal, htraversal, htraversalConstructor,
    htraversalFields, htraversalRecursiveFields, hstats, hvalid,
    hmotiveApp,
    hrootContext,
    hterminalContext, hsourceContext,
    Hdomain, HdomainType⟩

/-- The constructor target retained by the earlier minor-generation pass and
the target independently replayed while generating the rule have the same
alpha-closed normal form.  Consequently the executable classifier selects
the rule's canonical mutual-family owner, and the retained minor result is
literally the corresponding motive application. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorTargetAlignment
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
    ∃ S : RecInfoMinorTypeShape,
      ∃ traversal : RecInfoMinorTraversalShape,
        S.localIndex = i ∧
        S.traversal = some traversal ∧
        traversal.fields = S.fields ∧
        traversal.fieldFVars = S.fields_bound.fvars ∧
        traversal.terminal.abstractList S.fields_bound.fvars =
          A.rule.target.abstractList A.semantics.fieldOpening.fvars ∧
        (AddInductive.getIIndices stats traversal.terminal).1 = owner ∧
        S.motiveApp =
          Expr.app
            (mkAppN H.recInfos[owner]!.motive
              (AddInductive.getIIndices stats traversal.terminal).2)
            (mkAppN
              (mkAppN (.const S.constructor.name stats.levels) stats.params)
              S.fields) := by
  rcases A.finalSelectedMinorShape with
    ⟨_T, _D, _O, S, _horigin, hlocal, _hconstructors, hconstructor,
      _hfieldCount, _Hsemantic, _hypothesisOrigins, _hhypothesisOrigins,
      _hhypothesisStats, _hhypothesisRecInfos, traversal, htraversal,
      htraversalConstructor, htraversalFields,
      _htraversalRecursiveFields, hstats, hvalid, hmotiveApp,
      _hrootContext, _hterminalContext, _hsourceContext,
      _Hdomain, _HdomainType⟩
  have hprefixTraversal := traversal.parameterPrefix
  rw [hstats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.semantics.parameterTail :=
    hprefixTraversal.tail_eq A.semantics.parameterPrefix
  have HtraversalTelescope := traversal.fieldTelescope
  rw [htraversalFields, hparameterTail] at HtraversalTelescope
  have hsemanticResidual :
      A.semantics.fieldOpening.residual.isForall = false := by
    rw [← A.semantics.fieldOpening.closed, Expr.abstractList_isForall]
    exact A.semantics.target_not_forall
  have hfieldResidual : traversal.fieldResidual =
      A.semantics.fieldOpening.residual :=
    (HtraversalTelescope.eq_of_residual_not_forall
      A.semantics.fieldOpening.telescope
      traversal.fieldResidual_not_forall hsemanticResidual).2
  have hfieldFVars : traversal.fieldFVars = S.fields_bound.fvars := by
    have harrays : (traversal.fieldFVars.map Expr.fvar).toArray =
        (S.fields_bound.fvars.map Expr.fvar).toArray :=
      traversal.fields_eq.symm.trans <|
        htraversalFields.trans S.fields_bound.expressions
    have hlists : traversal.fieldFVars.map Expr.fvar =
        S.fields_bound.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList harrays
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlists
  have hterminalClosed :
      traversal.terminal.abstractList S.fields_bound.fvars =
        traversal.fieldResidual := by
    rw [← hfieldFVars]
    exact traversal.fieldClosed
  have hclosedTargets :
      traversal.terminal.abstractList S.fields_bound.fvars =
        A.rule.target.abstractList A.semantics.fieldOpening.fvars := by
    rw [hterminalClosed, A.semantics.fieldOpening.closed, hfieldResidual]
  let selectedOwner :=
    (AddInductive.getIIndices stats traversal.terminal).1
  have hselectedValid : AddInductive.isValidIndApp? stats traversal.terminal =
      some selectedOwner := by
    simpa [selectedOwner] using hvalid
  have hselectedDecl : selectedOwner < decl.types.length := by
    have hselectedStats :=
      (checkPositivityStep.isValidIndApp?_some hselectedValid).1
    rw [A.semantics.validStats.types_size] at hselectedStats
    exact hselectedStats
  have hselectedHead : traversal.terminal.getAppFn =
      .const (decl.types[selectedOwner]'hselectedDecl).name stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead
      (checkPositivityStep.isValidIndApp?_some hselectedValid).2
      (A.semantics.validStats.indConstAt hselectedDecl)
  have htargetValid : AddInductive.isValidIndAppIdx stats A.rule.target
      owner = true := by
    have h := (checkPositivityStep.isValidIndApp?_some
      A.semantics.target_valid).2
    simpa [A.semantic_owner] using h
  have htargetHead : A.rule.target.getAppFn =
      .const (decl.types[owner]'A.abstractOwner_lt).name stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead htargetValid
      (A.semantics.validStats.indConstAt A.abstractOwner_lt)
  have hname : (decl.types[selectedOwner]'hselectedDecl).name =
      (decl.types[owner]'A.abstractOwner_lt).name := by
    have heq := congrArg Expr.getAppFn hclosedTargets
    rw [Expr.getAppFn_abstractList, hselectedHead,
      Expr.getAppFn_abstractList, htargetHead] at heq
    simp [Expr.abstractList, Expr.abstract1] at heq
    exact heq
  have htypeNames : (decl.types.map (fun type => type.name)).Nodup := by
    have hprefix := (List.nodup_append.mp
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup
        R.core)).1
    simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductiveType.toVConstVal, Function.comp_def] using hprefix
  have hselectedOwner : selectedOwner = owner := by
    have hleft : selectedOwner <
        (decl.types.map (fun type => type.name)).length := by
      simpa using hselectedDecl
    have hright : owner <
        (decl.types.map (fun type => type.name)).length := by
      simpa using A.abstractOwner_lt
    apply (List.getElem_inj (h₀ := hleft) (h₁ := hright)
      htypeNames).mp
    simpa only [List.getElem_map] using hname
  have hselectedOwner' :
      (AddInductive.getIIndices stats traversal.terminal).1 = owner := by
    simpa [selectedOwner] using hselectedOwner
  have hmotiveApp' : S.motiveApp =
      Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats traversal.terminal).2)
        (mkAppN
          (mkAppN (.const S.constructor.name stats.levels) stats.params)
          S.fields) := by
    rw [hmotiveApp]
    rcases hindices : AddInductive.getIIndices stats traversal.terminal with
      ⟨motiveOwner, indices⟩
    have : motiveOwner = owner := by
      simpa [hindices] using hselectedOwner'
    subst motiveOwner
    rfl
  exact ⟨S, traversal, hlocal, htraversal, htraversalFields,
    hfieldFVars, hclosedTargets, hselectedOwner', hmotiveApp'⟩

/-- The earlier minor target and the independently generated rule carry the
same index spine after each pass closes its own fresh constructor fields.
This is the alpha-stable index payload used by the final motive comparison. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorIndexAlignment
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
    ∃ S : RecInfoMinorTypeShape,
      ∃ traversal : RecInfoMinorTraversalShape,
        S.localIndex = i ∧
        S.traversal = some traversal ∧
        (AddInductive.getIIndices stats traversal.terminal).2.map
            (fun index => index.abstractList S.fields_bound.fvars) =
          (AddInductive.getIIndices stats A.rule.target).2.map
            (fun index => index.abstractList
              A.semantics.fieldOpening.fvars) := by
  rcases A.finalSelectedMinorTargetAlignment with
    ⟨S, traversal, hlocal, htraversal, _hfields, _hfieldFVars,
      hclosedTargets, _howner, _hmotiveApp⟩
  have hindices := congrArg
    (fun target => (AddInductive.getIIndices stats target).2)
    hclosedTargets
  rw [checkPositivityStep.getIIndices.snd_abstractList,
    checkPositivityStep.getIIndices.snd_abstractList] at hindices
  exact ⟨S, traversal, hlocal, htraversal, hindices⟩

/-- Recover the exact translation-side context in which the selected minor
source was completed, together with its executable extension into the final
recursor context.  This is the semantic strengthening of the structural
`BindingContextLE` returned by `finalSelectedMinorShape`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorSemanticSource
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
    ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        S.localIndex = i ∧
        HS.semantic.traversal.parameterTail =
          A.semantics.parameterTail := by
  rcases A.finalSelectedMinorDomain with
    ⟨_T, _D, O, _discardedShape, _Hdomain, _HdomainType⟩
  have hposition := A.selectedMinorOriginPosition O
  have hsourceOwner : O.owner < indTypes.size := by
    rw [hposition.1]
    exact A.sourceOwner_lt
  have hshapeBound : O.localIndex <
      H.origins.minorTypes[O.owner]!.size := by
    rw [(H.origins.minors O.owner O.owner_lt).size_eq]
    simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt
  let S := H.origins.minorShapes O.owner O.owner_lt O.localIndex hshapeBound
  have Hsource := H.minorSources O.owner O.owner_lt hsourceOwner
    O.localIndex hshapeBound
  have hlocal : S.localIndex = i := Hsource.2.1.trans hposition.2
  have hconstructorsAtOrigin :
      S.sourceConstructors = indTypes[O.owner]!.ctors := by
    simpa [S] using Hsource.2.2.1
  have hconstructors :
      S.sourceConstructors = indTypes[owner]!.ctors := by
    simpa [hposition.1] using hconstructorsAtOrigin
  have hconstructor : S.constructor = indTypes[owner]!.ctors[i] := by
    have hsourceConstructor := S.sourceConstructor
    rw [hconstructors, hlocal] at hsourceConstructor
    simpa [hctor] using hsourceConstructor.symm
  rcases Hsource.2.2.2.2 with
    ⟨traversal, htraversal, htraversalConstructor, _htraversalFields,
      _htraversalRecursiveFields, hstats, _hrootContext,
      _hterminalContext, _hsourceContext⟩
  rcases H.minorSemantics O.owner O.owner_lt O.localIndex hshapeBound with
    ⟨HS⟩
  have hsemanticTraversal : HS.semantic.traversal = traversal :=
    Option.some.inj (HS.semantic.traversal_eq.symm.trans htraversal)
  have hprefixTraversal := traversal.parameterPrefix
  rw [hstats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.semantics.parameterTail :=
    hprefixTraversal.tail_eq A.semantics.parameterPrefix
  exact ⟨S, HS, hlocal, hsemanticTraversal.symm ▸ hparameterTail⟩

/-- Expose the whole selected minor source before abstraction over the common
recursor binders.  Annotation consumption translates the installed origin,
and the exact two-stage field/hypothesis replay is definitionally equal to
that consumed target in the retained source context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorReplayedSource
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
    ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        S.localIndex = i ∧
        HS.semantic.traversal.parameterTail =
          A.semantics.parameterTail ∧
        TrExprS H.recursorWF.venv Us HS.semantic.sourceWF.mlctx.vlctx
          S.origin HS.semantic.consumedTarget ∧
        H.recursorWF.venv.IsDefEqU Us.length
          HS.semantic.sourceWF.mlctx.vlctx.toCtx
          ((VExpr.wrapForalls HS.semantic.fieldDomains
            (VExpr.wrapForalls HS.semantic.hypothesisDomains
              HS.semantic.motiveTarget)).lift'
                ((HS.semantic.fieldsRecent.contextExtension.trans
                  HS.semantic.hypothesesRecent.contextExtension).shift.consN
                    0))
          HS.semantic.consumedTarget := by
  dsimp only
  rcases A.finalSelectedMinorSemanticSource with
    ⟨S, HS, hlocal, htail⟩
  have Hconsumed : TrExprS H.recursorWF.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      HS.semantic.sourceWF.mlctx.vlctx S.origin
      HS.semantic.consumedTarget := by
    rw [← S.consumed_eq]
    simpa only [HS.semantic.extension.venv_eq] using
      HS.semantic.consumption.consumed
  have Hreplayed : H.recursorWF.venv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      HS.semantic.sourceWF.mlctx.vlctx.toCtx
      ((VExpr.wrapForalls HS.semantic.fieldDomains
        (VExpr.wrapForalls HS.semantic.hypothesisDomains
          HS.semantic.motiveTarget)).lift'
            ((HS.semantic.fieldsRecent.contextExtension.trans
              HS.semantic.hypothesesRecent.contextExtension).shift.consN 0))
      HS.semantic.consumedTarget := by
    simpa only [HS.semantic.extension.venv_eq] using
      HS.semantic.replayedSourceDefEqConsumed
  exact ⟨S, HS, hlocal, htail, Hconsumed, Hreplayed⟩

/-- Transport the selected first-pass field-context conversion through the
complete executable extension to the final recursor context.  This packages
the exact composition through fields, recursive hypotheses, and the
remaining recursor declarations, so the installed-minor base comparison no
longer has to reconstruct that shift locally. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorTransportedFieldContext
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
    ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ sourceDomains sourceResidual consumedDomains consumedResidual,
          S.localIndex = i ∧
          HS.semantic.traversal.parameterTail =
            A.semantics.parameterTail ∧
          sourceDomains.length = A.rule.allArgs.size ∧
          consumedDomains.length = A.rule.allArgs.size ∧
          TrExprS H.recursorWF.venv Us H.recursorWF.mlctx.vlctx
            A.semantics.parameterTail
            (VExpr.wrapForalls sourceDomains sourceResidual) ∧
          (VExpr.wrapForalls HS.semantic.fieldDomains
            HS.semantic.terminalTarget).lift'
              ((((HS.semantic.fieldsRecent.contextExtension.trans
                HS.semantic.hypothesesRecent.contextExtension).trans
                  HS.semantic.extension).shift.consN 0)) =
            VExpr.wrapForalls consumedDomains consumedResidual ∧
          VEnv.IsDefEqCtx H.recursorWF.venv Us.length []
            (sourceDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
            (consumedDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorSemanticSource with
    ⟨S, HS, hlocal, htail⟩
  let Hext : RecursorContextExtension HS.semantic.rootWF H.recursorWF :=
    (HS.semantic.fieldsRecent.contextExtension.trans
      HS.semantic.hypothesesRecent.contextExtension).trans
        HS.semantic.extension
  rcases HS.semantic.fieldContextDefEqMono Hext with
    ⟨sourceDomains, sourceResidual, consumedDomains, consumedResidual,
      hsource, hconsumed, Hsource, hconsumedTarget, Hcontexts⟩
  have hfields : S.fields.size = A.rule.allArgs.size := by
    have htraversalFields := HS.semantic.traversal_fields
    have hsemanticFields := congrArg Array.size htraversalFields
    have hterminal := HS.semantic.traversal.fieldTelescope
    have hrule := A.semantics.fieldOpening.telescope
    rw [htail] at hterminal
    have hsemanticResidual :
        A.semantics.fieldOpening.residual.isForall = false := by
      rw [← A.semantics.fieldOpening.closed, Expr.abstractList_isForall]
      exact A.semantics.target_not_forall
    exact hsemanticFields.symm.trans
      (hterminal.eq_of_residual_not_forall hrule
        HS.semantic.traversal.fieldResidual_not_forall
        hsemanticResidual).1
  exact ⟨S, HS, sourceDomains, sourceResidual, consumedDomains,
    consumedResidual, hlocal, htail, hsource.trans hfields,
    hconsumed.trans hfields, by simpa [Us, htail] using Hsource,
    by simpa [Hext] using hconsumedTarget, Hcontexts⟩

/-- Witness-stable form of `finalSelectedMinorSemanticFieldAlignment`.
Callers that already retain the selected first-pass semantic source can join
it to the rule-generation field telescope without selecting a second shape
or semantic extension. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorSemanticFieldAlignmentFor
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
    (S : RecInfoMinorTypeShape)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF S
      H.parameterSuffix.parameterDecls)
    (htail : HS.semantic.traversal.parameterTail =
      A.semantics.parameterTail)
    (hfields : S.fields.size = A.rule.allArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ minorConsumedDomains : List VExpr,
      ∃ minorConsumedResidual,
      minorConsumedDomains.length = A.rule.allArgs.size ∧
      (VExpr.wrapForalls HS.semantic.fieldDomains
        HS.semantic.terminalTarget).lift'
          ((((HS.semantic.fieldsRecent.contextExtension.trans
            HS.semantic.hypothesesRecent.contextExtension).trans
              HS.semantic.extension).shift.consN 0)) =
          VExpr.wrapForalls minorConsumedDomains minorConsumedResidual ∧
      A.semantics.fieldTelescope.domains.length = A.rule.allArgs.size ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (minorConsumedDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
        (A.semantics.fieldTelescope.domains.reverse ++
          H.recursorWF.mlctx.vlctx.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let Hext : RecursorContextExtension HS.semantic.rootWF H.recursorWF :=
    (HS.semantic.fieldsRecent.contextExtension.trans
      HS.semantic.hypothesesRecent.contextExtension).trans
        HS.semantic.extension
  rcases HS.semantic.fieldContextDefEqMono Hext with
    ⟨minorSourceDomains, minorSourceResidual, minorConsumedDomains,
      minorConsumedResidual, hminorSource, hminorConsumed,
      HminorSource, hminorTarget, HminorContexts⟩
  rcases A.semantics.fieldContextDefEq with
    ⟨ruleSourceDomains, ruleSourceResidual, hruleSource,
      hparameterTarget, HruleContexts⟩
  let ruleSemanticDomains := A.semantics.fieldTelescope.domains
  have hruleSemantic : ruleSemanticDomains.length =
      A.rule.allArgs.size := A.semantics.fieldTelescope.domains_length
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  have HruleSource₀ : TrExprS A.semantics.fieldRootContext.venv Us
      A.semantics.fieldRootContext.mlctx.vlctx
      A.semantics.parameterTail
      (VExpr.wrapForalls ruleSourceDomains ruleSourceResidual) := by
    rw [← hparameterTarget]
    exact A.semantics.parameterTranslation
  have hsemanticRoot : A.semantics.fieldRootContext.venv =
      H.recursorWF.venv :=
    A.semantics.fieldsRecent.venv_eq.symm.trans A.semantics.context_venv
  rw [hsemanticRoot] at HruleSource₀ HruleContexts
  have HruleSource : TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
      A.semantics.parameterTail
      (VExpr.wrapForalls ruleSourceDomains ruleSourceResidual) := by
    have Hsource := HruleSource₀.mono hbase
    simpa [A.semantics.fieldRoot_vlctx] using Hsource
  have HminorSource' : TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
      A.semantics.parameterTail
      (VExpr.wrapForalls minorSourceDomains minorSourceResidual) := by
    have Hsource := HminorSource.mono hbase
    simpa only [htail] using Hsource
  have HrootWF : VLCtx.WF H.outVEnv Us.length
      H.recursorWF.mlctx.vlctx :=
    (H.recursorWF.mlctx_wf.mono hbase).tr.wf
  have HsourceTarget := HminorSource'.uniq H.outVEnvWF
    (.refl H.outVEnvWF HrootWF) HruleSource
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.recursorWF.mlctx.vlctx.toCtx H.recursorWF.mlctx.vlctx.toCtx :=
    .refl HrootWF.toCtx
  have HsourceContexts := VEnv.IsDefEqU.wrapForalls_context
    H.outVEnvWF Hbase
      ((hminorSource.trans hfields).trans hruleSource.symm) HsourceTarget
  have HminorContexts' := HminorContexts.mono hbase
  have HruleContexts' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (ruleSourceDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
      (ruleSemanticDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx) := by
    have Hcontexts := HruleContexts.mono hbase
    simpa [ruleSemanticDomains, A.semantics.fieldRoot_vlctx] using Hcontexts
  have HminorToSource := HminorContexts'.symm H.outVEnvWF.ordered
  have HminorToRuleSource := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HminorToSource HsourceContexts
  have Haligned := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HminorToRuleSource HruleContexts'
  exact ⟨minorConsumedDomains, minorConsumedResidual,
    hminorConsumed.trans hfields, hminorTarget, hruleSemantic, Haligned⟩

/-- Join the two executable passes at their consumed constructor-field
contexts.  Each pass first translates the same original constructor tail in
the final recursor root; translation uniqueness aligns those source-domain
contexts, after which the retained whole-target conversions reach the
literal consumed domains on each side. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorSemanticFieldAlignment
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
    ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ minorConsumedDomains : List VExpr,
          minorConsumedDomains.length = A.rule.allArgs.size ∧
          A.semantics.fieldTelescope.domains.length =
            A.rule.allArgs.size ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            (minorConsumedDomains.reverse ++
              H.recursorWF.mlctx.vlctx.toCtx)
            (A.semantics.fieldTelescope.domains.reverse ++
              H.recursorWF.mlctx.vlctx.toCtx) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorTransportedFieldContext with
    ⟨S, HS, minorSourceDomains, minorSourceResidual,
      minorConsumedDomains, _minorConsumedResidual, _hlocal, _htail,
      hminorSource, hminorConsumed, HminorSource, _hminorTarget,
      HminorContexts⟩
  rcases A.semantics.fieldContextDefEq with
    ⟨ruleSourceDomains, ruleSourceResidual, hruleSource,
      hparameterTarget, HruleContexts⟩
  let ruleSemanticDomains := A.semantics.fieldTelescope.domains
  have hruleSemantic : ruleSemanticDomains.length =
      A.rule.allArgs.size := by
    exact A.semantics.fieldTelescope.domains_length
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  have HruleSource₀ : TrExprS A.semantics.fieldRootContext.venv Us
      A.semantics.fieldRootContext.mlctx.vlctx
      A.semantics.parameterTail
      (VExpr.wrapForalls ruleSourceDomains ruleSourceResidual) := by
    rw [← hparameterTarget]
    exact A.semantics.parameterTranslation
  have hsemanticRoot : A.semantics.fieldRootContext.venv =
      H.recursorWF.venv := by
    exact A.semantics.fieldsRecent.venv_eq.symm.trans
      A.semantics.context_venv
  rw [hsemanticRoot] at HruleSource₀ HruleContexts
  have HruleSource : TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
      A.semantics.parameterTail
      (VExpr.wrapForalls ruleSourceDomains ruleSourceResidual) := by
    have Hsource := HruleSource₀.mono hbase
    simpa [A.semantics.fieldRoot_vlctx] using Hsource
  have HminorSource' := HminorSource.mono hbase
  have HrootWF : VLCtx.WF H.outVEnv Us.length
      H.recursorWF.mlctx.vlctx :=
    (H.recursorWF.mlctx_wf.mono hbase).tr.wf
  have HsourceTarget := HminorSource'.uniq H.outVEnvWF
    (.refl H.outVEnvWF HrootWF) HruleSource
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.recursorWF.mlctx.vlctx.toCtx H.recursorWF.mlctx.vlctx.toCtx :=
    .refl HrootWF.toCtx
  have HsourceContexts := VEnv.IsDefEqU.wrapForalls_context
    H.outVEnvWF Hbase (hminorSource.trans hruleSource.symm) HsourceTarget
  have HminorContexts' := HminorContexts.mono hbase
  have HruleContexts' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (ruleSourceDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
      (ruleSemanticDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx) := by
    have Hcontexts := HruleContexts.mono hbase
    simpa [ruleSemanticDomains, A.semantics.fieldRoot_vlctx] using Hcontexts
  have HminorToSource := HminorContexts'.symm H.outVEnvWF.ordered
  have HminorToRuleSource := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HminorToSource HsourceContexts
  have Haligned := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HminorToRuleSource HruleContexts'
  exact ⟨S, HS, minorConsumedDomains,
    hminorConsumed, hruleSemantic, Haligned⟩

/-- Transport the shared constructor tail retained by the first minor pass
into the exact parameter context and environment used by final rule
generation.  This is the first semantic join between the two executable
passes; the source expression is identified structurally, while its target
is preserved from the first pass. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorSharedTail
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
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ target,
          S.localIndex = i ∧
          HS.semantic.traversal.parameterTail =
            A.semantics.parameterTail ∧
          TrExprS H.outVEnv Us parameterDecls
            A.semantics.parameterTail target := by
  dsimp only
  rcases A.finalSelectedMinorSemanticSource with
    ⟨S, HS, hlocal, htail⟩
  rcases HS.semantic.parameterTranslationAtSuffix with
    ⟨target, Htarget⟩
  have hrootLE : HS.semantic.rootWF.venv ≤ H.outVEnv := by
    rw [← HS.semantic.fieldsRecent.contextExtension.venv_eq,
      ← HS.semantic.hypothesesRecent.contextExtension.venv_eq,
      ← HS.semantic.extension.venv_eq, H.recursorEnv,
      R.declared.contextVEnv]
    exact H.installed.le
  have Htarget' := Htarget.mono hrootLE
  have HtargetAtParameters : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.parameterSuffix.parameterDecls A.semantics.parameterTail target := by
    simpa only [HS.parameterDecls_eq, htail] using Htarget'
  have HtargetFinal : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
      A.semantics.parameterTail target := by
    simpa only [← H.parameterDecls] using HtargetAtParameters
  exact ⟨S, HS, target, hlocal, htail, HtargetFinal⟩

/-- The target retained from first-pass minor construction and the field
telescope reconstructed during final rule generation are definitionally
equal, because they translate the same constructor tail in the same exact
parameter context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorSharedTailDefEq
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
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ target fieldDomains fieldResult,
          S.localIndex = i ∧
          HS.semantic.traversal.parameterTail =
            A.semantics.parameterTail ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          TrExprS H.outVEnv Us parameterDecls
            A.semantics.parameterTail target ∧
          TrExprS H.outVEnv Us parameterDecls
            A.semantics.parameterTail
            (VExpr.wrapForalls fieldDomains fieldResult) ∧
          H.outVEnv.IsDefEqU Us.length parameterDecls.toCtx target
            (VExpr.wrapForalls fieldDomains fieldResult) := by
  dsimp only
  rcases A.finalSelectedMinorSharedTail with
    ⟨S, HS, target, hlocal, htail, Htarget⟩
  rcases A.finalCheckedConstructorFieldFrame with
    ⟨_T, fieldDomains, fieldResult, _introTarget, _hparams, hfields,
      Hfields, _HfieldResidual, _HtailType, _HtailTypeT,
      _HfieldContext, _HintroType, _Hintro, _HintroShape⟩
  have hbaseLE :
      (R.declared.context.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible).venv ≤ H.outVEnv := by
    rw [ContextWF.toAdmissibleRecursorContextWF_venv,
      R.declared.contextVEnv]
    exact H.installed.le
  have HparameterWF : VLCtx.WF H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterWF.mono hbaseLE
  have Hsame := Htarget.uniq H.outVEnvWF
    (.refl H.outVEnvWF HparameterWF) Hfields
  exact ⟨S, HS, target, fieldDomains, fieldResult, hlocal, htail,
    hfields, Htarget, Hfields, Hsame⟩

/-- Binder-by-binder form of the shared-tail equality.  It is deliberately a
context conversion rather than list equality: the first minor pass and the
later constructor check may translate annotation-consumed domains to
different, convertible representatives. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorSharedFieldContext
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
    let parameterDecls :=
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
        ∃ minorFieldDomains minorFieldResult checkedFieldDomains
            checkedFieldResult,
          S.localIndex = i ∧
          HS.semantic.traversal.parameterTail =
            A.semantics.parameterTail ∧
          minorFieldDomains.length = A.rule.allArgs.size ∧
          checkedFieldDomains.length = A.rule.allArgs.size ∧
          TrExprS H.outVEnv Us parameterDecls
            A.semantics.parameterTail
            (VExpr.wrapForalls minorFieldDomains minorFieldResult) ∧
          TrExprS H.outVEnv Us parameterDecls
            A.semantics.parameterTail
            (VExpr.wrapForalls checkedFieldDomains checkedFieldResult) ∧
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            (minorFieldDomains.reverse ++ parameterDecls.toCtx)
            (checkedFieldDomains.reverse ++ parameterDecls.toCtx) := by
  dsimp only
  rcases A.finalSelectedMinorSharedTailDefEq with
    ⟨S, HS, target, checkedFieldDomains, checkedFieldResult, hlocal,
      htail, hcheckedLength, Hminor, Hchecked, Hsame⟩
  rcases TrExprS.forallTelescope_shape A.semantics.fieldOpening.telescope
      Hminor with
    ⟨minorFieldDomains, minorFieldResult, hminorLength, htarget⟩
  have Hsame' : H.outVEnv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
      (VExpr.wrapForalls minorFieldDomains minorFieldResult)
      (VExpr.wrapForalls checkedFieldDomains checkedFieldResult) := by
    rw [← htarget]
    exact Hsame
  have hbaseLE :
      (R.declared.context.toAdmissibleRecursorContextWF
        H.elimLevelAdmissible).venv ≤ H.outVEnv := by
    rw [ContextWF.toAdmissibleRecursorContextWF_venv,
      R.declared.contextVEnv]
    exact H.installed.le
  have HparameterWF : VLCtx.WF H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls :=
    (R.materialized.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterWF.mono hbaseLE
  have Hbase : VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx
      (R.materialized.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls.toCtx :=
    .refl HparameterWF.toCtx
  have Hfields := VEnv.IsDefEqU.wrapForalls_context H.outVEnvWF Hbase
    (hminorLength.trans hcheckedLength.symm) Hsame'
  exact ⟨S, HS, minorFieldDomains, minorFieldResult,
    checkedFieldDomains, checkedFieldResult, hlocal, htail,
    hminorLength, hcheckedLength, by simpa [htarget] using Hminor,
    Hchecked, Hfields⟩

/-- Replaying the selected constructor telescope in the later rule context
preserves its alpha-independent recursive-field mask.  Consequently the
minor generated by the earlier pass has exactly one hypothesis for every
recursive result generated by this rule. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorMaskAlignment
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
    ∃ S : RecInfoMinorTypeShape,
      ∃ traversal : RecInfoMinorTraversalShape,
        S.localIndex = i ∧
        S.traversal = some traversal ∧
        traversal.recursivePositions = A.semantics.recursivePositions ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        BindingContextLE S.sourceFullContext H.localContext := by
  rcases A.finalSelectedMinorShape with
    ⟨_T, _D, _O, S, _horigin, hlocal, _hconstructors, hconstructor,
      _hfieldCount, _Hsemantic, _hypothesisOrigins, _hhypothesisOrigins,
      _hhypothesisStats, _hhypothesisRecInfos, traversal, htraversal,
      htraversalConstructor,
      _htraversalFields, htraversalRecursiveFields, hstats, _hvalid,
      _hmotiveApp,
      _hrootContext,
      hterminalContext, hsourceContext, _Hdomain, _HdomainType⟩
  have hprefixTraversal := traversal.parameterPrefix
  rw [hstats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.semantics.parameterTail :=
    hprefixTraversal.tail_eq A.semantics.parameterPrefix
  have HruleDecisions : RecursorFieldDecisions stats
      A.semantics.fieldRoot traversal.parameterTail A.rule.root
      A.rule.target A.rule.allArgs A.rule.recursiveArgs
      A.semantics.recursivePositions := by
    rw [hparameterTail]
    exact A.semantics.decisions
  have hterminalToRule : BindingContextLE traversal.terminalContext
      A.semantics.fieldRoot :=
    hterminalContext.trans A.semantics.fieldRootExtension.contextLE
  have HminorDecisions : RecursorFieldDecisions stats
      traversal.rootContext traversal.parameterTail traversal.terminalContext
      traversal.terminal traversal.fields traversal.recursiveFields
      traversal.recursivePositions := by
    simpa [hstats] using traversal.decisions
  have hpositions : traversal.recursivePositions =
      A.semantics.recursivePositions :=
    H.fieldReplay stats traversal.rootContext A.semantics.fieldRoot
      traversal.terminalContext A.rule.root traversal.parameterTail
      traversal.terminal A.rule.target traversal.fields
      traversal.recursiveFields A.rule.allArgs A.rule.recursiveArgs
      traversal.recursivePositions A.semantics.recursivePositions
      hterminalToRule traversal.parameterTail_fvars HminorDecisions
      HruleDecisions
  have hhypotheses : S.hypotheses.size = A.rule.recursiveArgs.size :=
    S.hypotheses_size_eq_rule traversal A.semantics
      htraversalRecursiveFields hpositions
  exact ⟨S, traversal, hlocal, htraversal, hpositions, hhypotheses,
    hsourceContext⟩

/-- Translating the selected installed minor preserves the complete boundary
between constructor fields and recursive hypotheses.  The resulting cached
minor type therefore exposes exactly the number of arguments supplied by the
generated RHS spine. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorTranslatedArity
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ domains residual,
        T.minors[minorIdx]!.takeForalls
            (A.rule.allArgs.size + A.rule.recursiveArgs.size) =
          some (domains, residual) ∧
        domains.length =
          A.rule.allArgs.size + A.rule.recursiveArgs.size := by
  dsimp only
  rcases A.finalSelectedMinorShape with
    ⟨T, D, _O, S, horigin, _hlocal, _hconstructors, hconstructor,
      hfieldCount, _Hsemantic, _hypothesisOrigins, _hhypothesisOrigins,
      _hhypothesisStats, _hhypothesisRecInfos, traversal, _htraversal,
      htraversalConstructor,
      _htraversalFields, htraversalRecursiveFields, hstats, _hvalid,
      _hmotiveApp,
      _hrootContext,
      hterminalContext, _hsourceContext, Hdomain, _HdomainType⟩
  have hprefixTraversal := traversal.parameterPrefix
  rw [hstats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.semantics.parameterTail :=
    hprefixTraversal.tail_eq A.semantics.parameterPrefix
  have HruleDecisions : RecursorFieldDecisions stats
      A.semantics.fieldRoot traversal.parameterTail A.rule.root
      A.rule.target A.rule.allArgs A.rule.recursiveArgs
      A.semantics.recursivePositions := by
    rw [hparameterTail]
    exact A.semantics.decisions
  have hterminalToRule : BindingContextLE traversal.terminalContext
      A.semantics.fieldRoot :=
    hterminalContext.trans A.semantics.fieldRootExtension.contextLE
  have HminorDecisions : RecursorFieldDecisions stats
      traversal.rootContext traversal.parameterTail traversal.terminalContext
      traversal.terminal traversal.fields traversal.recursiveFields
      traversal.recursivePositions := by
    simpa [hstats] using traversal.decisions
  have hpositions : traversal.recursivePositions =
      A.semantics.recursivePositions :=
    H.fieldReplay stats traversal.rootContext A.semantics.fieldRoot
      traversal.terminalContext A.rule.root traversal.parameterTail
      traversal.terminal A.rule.target traversal.fields
      traversal.recursiveFields A.rule.allArgs A.rule.recursiveArgs
      traversal.recursivePositions A.semantics.recursivePositions
      hterminalToRule traversal.parameterTail_fvars HminorDecisions
      HruleDecisions
  have hhypotheses : S.hypotheses.size = A.rule.recursiveArgs.size :=
    S.hypotheses_size_eq_rule traversal A.semantics
      htraversalRecursiveFields hpositions
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take
      (recursorMinorOffset indTypes owner + i)
  rcases S.originTelescope with ⟨sourceResidual, Hsource⟩
  have Habstract := Hsource.abstractList sourceBinders
  rw [horigin] at Habstract
  have harity : S.fields.size + S.hypotheses.size =
      A.rule.allArgs.size + A.rule.recursiveArgs.size := by
    rw [hfieldCount, hhypotheses]
  rw [harity] at Habstract
  rcases Habstract.translatedTakeForalls Hdomain with
    ⟨domains, residual, htake, hlength⟩
  exact ⟨T, domains, residual, htake, hlength⟩

/-- Split the translated minor telescope at the constructor-field boundary.
The suffix has exactly one domain for every recursive result selected by the
rule, so later pointwise arguments can index the two pieces independently. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorTranslatedSplit
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ fieldDomains hypothesisDomains residual,
        T.minors[minorIdx]!.takeForalls
            (A.rule.allArgs.size + A.rule.recursiveArgs.size) =
          some (fieldDomains ++ hypothesisDomains, residual) ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size := by
  dsimp only
  rcases A.finalSelectedMinorTranslatedArity with
    ⟨T, domains, residual, htake, hlength⟩
  let fieldDomains := domains.take A.rule.allArgs.size
  let hypothesisDomains := domains.drop A.rule.allArgs.size
  have hfieldsLE : A.rule.allArgs.size ≤ domains.length := by omega
  have hfields : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, List.length_take, Nat.min_eq_left hfieldsLE]
  have hhypotheses : hypothesisDomains.length =
      A.rule.recursiveArgs.size := by
    simp [hypothesisDomains, List.length_drop, hlength]
  have hdomains : domains = fieldDomains ++ hypothesisDomains := by
    exact (List.take_append_drop A.rule.allArgs.size domains).symm
  rw [hdomains] at htake
  exact ⟨T, fieldDomains, hypothesisDomains, residual, htake,
    hfields, hhypotheses⟩

/-- Binder-by-binder strengthening of the selected minor arity result.  The
complete consumed source telescope is retained together with the translation
and typehood of every abstract domain, so later applications can compare a
particular field or recursive-hypothesis domain rather than only their
cardinalities. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorTypedTelescope
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecInfoMinorTypeShape,
        ∃ hypothesisOrigins : RecInfoMinorHypothesisTypeOrigins
            S.sourceFullContext S.recursiveFields S.hypotheses,
        ∃ traversal : RecInfoMinorTraversalShape,
        S.hypothesis_type_origins = some hypothesisOrigins ∧
        hypothesisOrigins.stats = stats ∧
        hypothesisOrigins.recInfos.map (·.motive) =
          H.recInfos.map (·.motive) ∧
        S.traversal = some traversal ∧
        traversal.fields = S.fields ∧
        traversal.recursiveFields = S.recursiveFields ∧
        traversal.stats = stats ∧
        traversal.parameterTail = A.semantics.parameterTail ∧
        traversal.recursivePositions = A.semantics.recursivePositions ∧
        S.localIndex = i ∧
        S.fields.size = A.rule.allArgs.size ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        BindingContextLE S.sourceFullContext H.localContext ∧
        Nonempty (RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls) ∧
        let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
          H.bindings.flatMinors.fvars.take minorIdx
        Expr.ForallTelescopeTypeTranslation H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors.take minorIdx) [])
          (S.origin.abstractList sourceBinders)
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)
          T.minors[minorIdx]! := by
  dsimp only
  rcases A.finalSelectedMinorShape with
    ⟨T, D, _O, S, horigin, hlocal, _hconstructors, hconstructor,
      hfieldCount, Hsemantic, hypothesisOrigins, hhypothesisOrigins,
      hhypothesisStats, hhypothesisRecInfos, traversal, htraversal,
      htraversalConstructor,
      htraversalFields, htraversalRecursiveFields, hstats, _hvalid,
      _hmotiveApp,
      _hrootContext,
      hterminalContext, hsourceContext, Hdomain, HdomainType⟩
  have hprefixTraversal := traversal.parameterPrefix
  rw [hstats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.semantics.parameterTail :=
    hprefixTraversal.tail_eq A.semantics.parameterPrefix
  have HruleDecisions : RecursorFieldDecisions stats
      A.semantics.fieldRoot traversal.parameterTail A.rule.root
      A.rule.target A.rule.allArgs A.rule.recursiveArgs
      A.semantics.recursivePositions := by
    rw [hparameterTail]
    exact A.semantics.decisions
  have hterminalToRule : BindingContextLE traversal.terminalContext
      A.semantics.fieldRoot :=
    hterminalContext.trans A.semantics.fieldRootExtension.contextLE
  have HminorDecisions : RecursorFieldDecisions stats
      traversal.rootContext traversal.parameterTail traversal.terminalContext
      traversal.terminal traversal.fields traversal.recursiveFields
      traversal.recursivePositions := by
    simpa [hstats] using traversal.decisions
  have hpositions : traversal.recursivePositions =
      A.semantics.recursivePositions :=
    H.fieldReplay stats traversal.rootContext A.semantics.fieldRoot
      traversal.terminalContext A.rule.root traversal.parameterTail
      traversal.terminal A.rule.target traversal.fields
      traversal.recursiveFields A.rule.allArgs A.rule.recursiveArgs
      traversal.recursivePositions A.semantics.recursivePositions
      hterminalToRule traversal.parameterTail_fvars HminorDecisions
      HruleDecisions
  have hhypotheses : S.hypotheses.size = A.rule.recursiveArgs.size :=
    S.hypotheses_size_eq_rule traversal A.semantics
      htraversalRecursiveFields hpositions
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take
      (recursorMinorOffset indTypes owner + i)
  rcases S.originTelescope with ⟨sourceResidual, Hsource⟩
  have Habstract := Hsource.abstractList sourceBinders
  rw [hfieldCount, hhypotheses] at Habstract
  have Hdomain' : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives ++
          T.minors.take (recursorMinorOffset indTypes owner + i)) [])
      (S.origin.abstractList sourceBinders)
      T.minors[recursorMinorOffset indTypes owner + i]! := by
    rw [horigin]
    exact Hdomain
  exact ⟨T, S, hypothesisOrigins, traversal, hhypothesisOrigins,
    hhypothesisStats, hhypothesisRecInfos, htraversal, htraversalFields,
    htraversalRecursiveFields, hstats, hparameterTail, hpositions,
    hlocal, hfieldCount, hhypotheses, hsourceContext, Hsemantic,
    Expr.ForallTelescopeTypeTranslation.ofTrExprS
      Habstract Hdomain' HdomainType⟩
/-- Independently replay the complete selected-minor telescope in the exact
non-contiguous source scope, and close that scope around the original source
declaration.  The two certificates expose the same narrowed target both as a
body below the selected outer prefix and as a completely closed telescope.
This is the comparison frame used to relate the installed minor domains to
the semantic field and recursive-result domains. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorExactClosedTelescope
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
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
      ∃ narrowTarget,
      ∃ fullTarget,
        fullTarget = HS.semantic.consumedTarget.lift'
          (HS.semantic.extension.shift.consN 0) ∧
        S.fields.size = A.rule.allArgs.size ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        HS.semantic.traversal.parameterTail = A.semantics.parameterTail ∧
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
          S.origin fullTarget ∧
        H.outVEnv.IsDefEqU Us.length H.recursorWF.mlctx.vlctx.toCtx
          fullTarget (narrowTarget.lift' Hscope.shift) ∧
        Hscope.sources.closeSource S.origin =
          H.localContext.lctx.mkForall
            (sourceBinders.map Expr.fvar).toArray S.origin ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse ∧
        Expr.ForallTelescopeTypeTranslation H.outVEnv Us
          (abstractForallContext scope.toCtx.reverse [])
          (S.origin.abstractList sourceBinders)
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)
          narrowTarget ∧
        Expr.ForallTelescopeTypeTranslation H.outVEnv Us []
          (H.localContext.lctx.mkForall
            (sourceBinders.map Expr.fvar).toArray S.origin)
          scope.length
          (VExpr.wrapForalls scope.toCtx.reverse narrowTarget) ∧
        Expr.ForallTelescopeTypeTranslation H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors.take minorIdx) [])
          (S.origin.abstractList sourceBinders)
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)
          T.minors[minorIdx]! := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.finalSelectedMinorTypedTelescope with
    ⟨T, S, _hypothesisOrigins, traversal,
      _hhypothesisOrigins, _hhypothesisStats, _hhypothesisRecInfos,
      htraversal, _htraversalFields, _htraversalRecursiveFields,
      _htraversalStats, hparameterTail, _hpositions, _hlocal,
      hfields, hhypotheses, _hsourceContext, Hsemantic, Hinstalled⟩
  rcases Hsemantic with ⟨HS⟩
  have hsemanticTraversal : HS.semantic.traversal = traversal :=
    Option.some.inj (HS.semantic.traversal_eq.symm.trans htraversal)
  have hsemanticParameterTail :
      HS.semantic.traversal.parameterTail = A.semantics.parameterTail :=
    (congrArg RecInfoMinorTraversalShape.parameterTail
      hsemanticTraversal).trans hparameterTail
  rcases A.finalSelectedMinorPrefixDefEqCtx with
    ⟨T₀, scope, Hscope, hscope, hscopeShift, hscopeSource, Hprefix₀⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams, hmotives, hminors] at Hprefix₀
  have Hprefix : VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
      (T.params ++ T.motives ++ T.minors.take minorIdx).reverse := by
    simpa using Hprefix₀
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  have hscopeSourceOut : Hscope.sources.closeSource S.origin =
      H.localContext.lctx.mkForall
        (sourceBinders.map Expr.fvar).toArray S.origin := by
    exact hscopeSource S.origin
  have HsourceOrigin : TrExprS HS.semantic.sourceWF.venv Us
      HS.semantic.sourceWF.mlctx.vlctx S.origin
      HS.semantic.consumedTarget := by
    rw [← S.consumed_eq]
    simpa only [HS.semantic.extension.venv_eq] using
      HS.semantic.consumption.consumed
  have Hfull₀ := HS.semantic.extension.weakTrExprS HsourceOrigin
  let fullTarget := HS.semantic.consumedTarget.lift'
    (HS.semantic.extension.shift.consN 0)
  have Hfull : TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx S.origin
      fullTarget :=
    Hfull₀.mono hbase
  have hclosed : Closed S.origin 0 := by
    have h := Hfull.closed
    rw [H.recursorWF.mlctx.noBV] at h
    exact h
  have HabstractClosed :
      (S.origin.abstractList sourceBinders).FVarsIn (fun _ => False) := by
    have Hfvars := Hinstalled.translation.fvarsIn
    exact Hfvars.mono fun fv hfv => by simpa using hfv
  have HsourceScope : S.origin.FVarsIn (· ∈ scope.fvars) := by
    have Hraw := FVarsIn.of_abstractList HabstractClosed
    apply Hraw.mono
    intro fv hfv
    rcases hfv with hfv | hfalse
    · rw [hscope]
      exact List.mem_reverse.mpr hfv
    · exact False.elim hfalse
  rcases Hscope.restrictEq H.outVEnvWF Hfull hclosed HsourceScope with
    ⟨narrowTarget, Hnarrow, HfullEq⟩
  rcases S.originTelescope with ⟨sourceResidual, HsourceTelescope⟩
  have HsourceTelescope' : Expr.ForallTelescope S.origin
      (A.rule.allArgs.size + A.rule.recursiveArgs.size) sourceResidual := by
    simpa [hfields, hhypotheses] using HsourceTelescope
  have HnarrowType : H.outVEnv.IsType Us.length scope.toCtx narrowTarget :=
    TrExprS.isType_of_forallTelescope HsourceTelescope' hpositive Hnarrow
  have HabstractTelescope :=
    HsourceTelescope'.abstractList sourceBinders
  have HabstractTranslation := Hscope.abstractAll H.outVEnvWF Hnarrow
  rw [hscope, List.reverse_reverse] at HabstractTranslation
  have HabstractType : H.outVEnv.IsType Us.length
      (abstractForallContext scope.toCtx.reverse []).toCtx narrowTarget := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HnarrowType
  have HabstractTyped :=
    Expr.ForallTelescopeTypeTranslation.ofTrExprS
      HabstractTelescope HabstractTranslation HabstractType
  have HclosedTyped := Hscope.closeTypedTelescope H.outVEnvWF
    Hnarrow HnarrowType
  rw [hscopeSourceOut] at HclosedTyped
  exact ⟨T, S, HS, scope, Hscope, narrowTarget, fullTarget,
    rfl, hfields, hhypotheses, hsemanticParameterTail, hscope, hscopeShift,
    Hfull, HfullEq, hscopeSourceOut, Hprefix, HabstractTyped,
    HclosedTyped, Hinstalled⟩

/-- Turn the inverse-weakening equality retained by
`finalSelectedMinorExactClosedTelescope` into a conversion of the complete
dependent minor contexts.  The right-hand domains are the literal
free-variable weakening of the independent narrow target; the left-hand
domains are obtained by translating the same original minor in the full
executable recursor context. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorNarrowFullContextAlignment
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
    let arity := A.rule.allArgs.size + A.rule.recursiveArgs.size
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
      ∃ narrowDomains fullDomains weakenedDomains installedDomains,
      ∃ narrowResidual fullResidual weakenedResidual installedResidual,
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        S.fields.size = A.rule.allArgs.size ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        HS.semantic.traversal.parameterTail = A.semantics.parameterTail ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse ∧
        narrowDomains.length = arity ∧
        fullDomains.length = arity ∧
        weakenedDomains.length = arity ∧
        installedDomains.length = arity ∧
        HS.semantic.consumedTarget.lift'
            (HS.semantic.extension.shift.consN 0) =
          VExpr.wrapForalls fullDomains fullResidual ∧
        (VExpr.wrapForalls narrowDomains narrowResidual).lift' Hscope.shift =
          VExpr.wrapForalls weakenedDomains weakenedResidual ∧
        T.minors[minorIdx]! =
          VExpr.wrapForalls installedDomains installedResidual ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (narrowDomains.reverse ++ scope.toCtx)
          (installedDomains.reverse ++
            (T.params ++ T.motives ++ T.minors.take minorIdx).reverse) ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (fullDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
          (weakenedDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let arity := A.rule.allArgs.size + A.rule.recursiveArgs.size
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.finalSelectedMinorExactClosedTelescope hpositive with
    ⟨T, S, HS, scope, Hscope, narrowTarget, fullTarget, hfullTargetEq, hfields,
      hhypotheses, hparameterTail, hscope, hscopeShift, Hfull, HfullEq,
      _hscopeSource, Hprefix, Hnarrow, _Hclosed, Hinstalled⟩
  rcases Hnarrow.toWrapForalls with
    ⟨narrowDomains, narrowSourceResidual, narrowResidual,
      hnarrowLength, _HnarrowSource, hnarrowTarget,
      _HnarrowResidual, _HnarrowResidualType⟩
  rcases S.originTelescope with ⟨sourceResidual, HsourceTelescope⟩
  have HsourceTelescope' : Expr.ForallTelescope S.origin arity
      sourceResidual := by
    simpa [arity, hfields, hhypotheses] using HsourceTelescope
  have HfullType : H.outVEnv.IsType Us.length
      H.recursorWF.mlctx.vlctx.toCtx fullTarget :=
    TrExprS.isType_of_forallTelescope HsourceTelescope'
      (by simpa [arity] using hpositive) Hfull
  have HfullTyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    HsourceTelescope' Hfull HfullType
  rcases HfullTyped.toWrapForalls with
    ⟨fullDomains, fullSourceResidual, fullResidual,
      hfullLength, _HfullSource, hfullTarget,
      _HfullResidual, _HfullResidualType⟩
  rcases VExpr.lift'_wrapForalls_shape narrowDomains narrowResidual
      Hscope.shift with
    ⟨weakenedDomains, weakenedResidual, hweakenedLength,
      hweakenedTarget⟩
  rcases Hinstalled.toWrapForalls with
    ⟨installedDomains, installedSourceResidual, installedResidual,
      hinstalledLength, _HinstalledSource, hinstalledTarget,
      _HinstalledResidual, _HinstalledResidualType⟩
  have hweakenedLength' : weakenedDomains.length = arity :=
    hweakenedLength.trans hnarrowLength
  have Hwhole : H.outVEnv.IsDefEqU Us.length
      H.recursorWF.mlctx.vlctx.toCtx
      (VExpr.wrapForalls fullDomains fullResidual)
      (VExpr.wrapForalls weakenedDomains weakenedResidual) := by
    rw [← hfullTarget, ← hweakenedTarget, ← hnarrowTarget]
    exact HfullEq
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  have HruntimeWF : OnCtx H.recursorWF.mlctx.vlctx.toCtx
      (H.outVEnv.IsType Us.length) :=
    (H.recursorWF.mlctx_wf.mono hbase).tr.wf.toCtx
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.recursorWF.mlctx.vlctx.toCtx H.recursorWF.mlctx.vlctx.toCtx :=
    .refl HruntimeWF
  have Hcontexts := VEnv.IsDefEqU.wrapForalls_context
    H.outVEnvWF Hbase (hfullLength.trans hweakenedLength'.symm) Hwhole
  have HprefixBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (scope.toCtx.reverse).reverse
      (T.params ++ T.motives ++ T.minors.take minorIdx).reverse := by
    simpa using Hprefix
  have HnarrowInstalled :=
    Expr.ForallTelescopeTypeTranslation.commonPrefixDefEqCtxOver
      H.outVEnvWF HprefixBase Hnarrow Hinstalled
      narrowDomains installedDomains narrowResidual installedResidual
      hnarrowTarget hinstalledTarget hnarrowLength hinstalledLength
      arity (by simp [arity]) (by simp [arity]) (by
        intro position hposition _hiNarrow _hiInstalled
          domainNarrow domainInstalled HbinderNarrow HbinderInstalled
        exact HbinderNarrow.unique HbinderInstalled)
  have hnarrowTake : narrowDomains.take arity = narrowDomains := by
    rw [show arity = narrowDomains.length from hnarrowLength.symm]
    exact List.take_length
  have hinstalledTake : installedDomains.take arity = installedDomains := by
    rw [show arity = installedDomains.length from hinstalledLength.symm]
    exact List.take_length
  rw [hnarrowTake, hinstalledTake] at HnarrowInstalled
  exact ⟨T, S, HS, scope, Hscope, narrowDomains, fullDomains,
    weakenedDomains, installedDomains, narrowResidual, fullResidual,
    weakenedResidual, installedResidual,
    hscope, hscopeShift, hfields, hhypotheses, hparameterTail, Hprefix,
    hnarrowLength, hfullLength,
    hweakenedLength', hinstalledLength,
    hfullTargetEq.symm.trans hfullTarget, hweakenedTarget,
    hinstalledTarget, by simpa [List.append_assoc] using HnarrowInstalled,
    Hcontexts⟩

/-- Compare every field and recursive-hypothesis domain of the independently
replayed minor with the corresponding domain stored in the generated
recursor.  The source telescope is literally shared; only its independently
constructed outer contexts differ, and `finalSelectedMinorPrefixDefEqCtx`
supplies their conversion. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorIndependentInstalledContextAlignment
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecInfoMinorTypeShape,
      ∃ scope : VLCtx,
      ∃ narrowTarget : VExpr,
      ∃ narrowDomains installedDomains : List VExpr,
      ∃ narrowResidual installedResidual : VExpr,
        narrowDomains.length =
          A.rule.allArgs.size + A.rule.recursiveArgs.size ∧
        installedDomains.length =
          A.rule.allArgs.size + A.rule.recursiveArgs.size ∧
        narrowTarget = VExpr.wrapForalls narrowDomains narrowResidual ∧
        T.minors[minorIdx]! =
          VExpr.wrapForalls installedDomains installedResidual ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (narrowDomains.reverse ++ scope.toCtx)
          (installedDomains.reverse ++
            (T.params ++ T.motives ++ T.minors.take minorIdx).reverse) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.finalSelectedMinorExactClosedTelescope hpositive with
    ⟨T, S, _HS, scope, _Hscope, narrowTarget, _fullTarget,
      _hfullTargetEq, _hfields,
      _hhypotheses, _hparameterTail, _hscope, _hscopeShift, _Hfull, _HfullEq,
      _hscopeSource, Hprefix, Hnarrow, _Hclosed, Hinstalled⟩
  rcases Hnarrow.toWrapForalls with
    ⟨narrowDomains, narrowSourceResidual, narrowResidual,
      hnarrowLength, _HnarrowSource, hnarrowTarget,
      _HnarrowResidual, _HnarrowResidualType⟩
  rcases Hinstalled.toWrapForalls with
    ⟨installedDomains, installedSourceResidual, installedResidual,
      hinstalledLength, _HinstalledSource, hinstalledTarget,
      _HinstalledResidual, _HinstalledResidualType⟩
  let arity := A.rule.allArgs.size + A.rule.recursiveArgs.size
  have Hbase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (scope.toCtx.reverse).reverse
      (T.params ++ T.motives ++ T.minors.take minorIdx).reverse := by
    simpa using Hprefix
  have Haligned :=
    Expr.ForallTelescopeTypeTranslation.commonPrefixDefEqCtxOver
      H.outVEnvWF Hbase Hnarrow Hinstalled
      narrowDomains installedDomains narrowResidual installedResidual
      hnarrowTarget hinstalledTarget hnarrowLength hinstalledLength
      arity (by simp [arity]) (by simp [arity]) (by
        intro position hposition _hiNarrow _hiInstalled
          domainNarrow domainInstalled HbinderNarrow HbinderInstalled
        exact HbinderNarrow.unique HbinderInstalled)
  have hnarrowTake : narrowDomains.take arity = narrowDomains := by
    rw [show arity = narrowDomains.length from hnarrowLength.symm]
    exact List.take_length
  have hinstalledTake : installedDomains.take arity = installedDomains := by
    rw [show arity = installedDomains.length from hinstalledLength.symm]
    exact List.take_length
  rw [hnarrowTake, hinstalledTake] at Haligned
  exact ⟨T, S, scope, narrowTarget, narrowDomains, installedDomains,
    narrowResidual, installedResidual, hnarrowLength, hinstalledLength,
    hnarrowTarget, hinstalledTarget, by
      simpa [List.append_assoc] using Haligned⟩

/-- Field-prefix consequence of the complete independent/installed minor
alignment.  Dropping the newest recursive-hypothesis declarations leaves
exactly the constructor-field contexts on both sides. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorIndependentInstalledFieldAlignment
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ scope : VLCtx,
      ∃ independentFields installedFields installedHypotheses : List VExpr,
      ∃ installedResidual : VExpr,
        independentFields.length = A.rule.allArgs.size ∧
        installedFields.length = A.rule.allArgs.size ∧
        installedHypotheses.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (installedFields ++ installedHypotheses) installedResidual ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (independentFields.reverse ++ scope.toCtx)
          (installedFields.reverse ++
            (T.params ++ T.motives ++ T.minors.take minorIdx).reverse) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalSelectedMinorIndependentInstalledContextAlignment
      hpositive with
    ⟨T, _S, scope, _narrowTarget, narrowDomains, installedDomains,
      _narrowResidual, installedResidual, hnarrowLength,
      hinstalledLength, _hnarrowTarget, hinstalledTarget, Haligned⟩
  let independentFields := narrowDomains.take A.rule.allArgs.size
  let independentHypotheses := narrowDomains.drop A.rule.allArgs.size
  let installedFields := installedDomains.take A.rule.allArgs.size
  let installedHypotheses := installedDomains.drop A.rule.allArgs.size
  have hindependentFields : independentFields.length =
      A.rule.allArgs.size := by
    simp [independentFields, hnarrowLength]
  have hinstalledFields : installedFields.length =
      A.rule.allArgs.size := by
    simp [installedFields, hinstalledLength]
  have hindependentHypotheses : independentHypotheses.length =
      A.rule.recursiveArgs.size := by
    simp [independentHypotheses, hnarrowLength]
  have hinstalledHypotheses : installedHypotheses.length =
      A.rule.recursiveArgs.size := by
    simp [installedHypotheses, hinstalledLength]
  have hnarrowSplit : narrowDomains =
      independentFields ++ independentHypotheses := by
    exact (List.take_append_drop A.rule.allArgs.size narrowDomains).symm
  have hinstalledSplit : installedDomains =
      installedFields ++ installedHypotheses := by
    exact (List.take_append_drop A.rule.allArgs.size installedDomains).symm
  have Hfields :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.dropHeads Haligned
      A.rule.recursiveArgs.size
  have hnarrowDrop :
      (narrowDomains.reverse ++ scope.toCtx).drop
          A.rule.recursiveArgs.size =
        independentFields.reverse ++ scope.toCtx := by
    rw [hnarrowSplit, List.reverse_append]
    simpa [List.append_assoc, hindependentHypotheses] using
      List.drop_left' independentHypotheses.reverse
        (independentFields.reverse ++ scope.toCtx)
  have hinstalledDrop :
      (installedDomains.reverse ++
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse).drop
          A.rule.recursiveArgs.size =
        installedFields.reverse ++
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse := by
    rw [hinstalledSplit, List.reverse_append]
    simpa [List.append_assoc, hinstalledHypotheses] using
      List.drop_left' installedHypotheses.reverse
        (installedFields.reverse ++
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse)
  rw [hnarrowDrop, hinstalledDrop] at Hfields
  exact ⟨T, scope, independentFields, installedFields,
    installedHypotheses, installedResidual,
    hindependentFields, hinstalledFields, hinstalledHypotheses,
    by simpa [hinstalledSplit] using hinstalledTarget, Hfields⟩

/-- Rebase the independent/installed field conversion onto the literal
generated parameter/motive/earlier-minor prefix.  After this step both field
telescopes have the same outer suffix, so later generated declarations can be
inserted beneath them with `insertSameMiddle`. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorInstalledFieldAlignmentAtGeneratedPrefix
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ independentFields installedFields installedHypotheses : List VExpr,
      ∃ installedResidual : VExpr,
        independentFields.length = A.rule.allArgs.size ∧
        installedFields.length = A.rule.allArgs.size ∧
        installedHypotheses.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (installedFields ++ installedHypotheses) installedResidual ∧
        let base := T.params ++ T.motives ++ T.minors.take minorIdx
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (independentFields.reverse ++ base.reverse)
          (installedFields.reverse ++ base.reverse) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalSelectedMinorIndependentInstalledFieldAlignment
      hpositive with
    ⟨T, scope, independentFields, installedFields, installedHypotheses,
      installedResidual, hindependentFields, hinstalledFields,
      hinstalledHypotheses, hinstalledTarget, Hfields⟩
  let base := T.params ++ T.motives ++ T.minors.take minorIdx
  have Hprefix₀ :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.dropHeads Hfields
      A.rule.allArgs.size
  have hleftDrop :
      (independentFields.reverse ++ scope.toCtx).drop
          A.rule.allArgs.size = scope.toCtx := by
    simpa [hindependentFields] using
      List.drop_left' independentFields.reverse scope.toCtx
  have hrightDrop :
      (installedFields.reverse ++ base.reverse).drop
          A.rule.allArgs.size = base.reverse := by
    simpa [hinstalledFields] using
      List.drop_left' installedFields.reverse base.reverse
  rw [hleftDrop, hrightDrop] at Hprefix₀
  have HsameIndependent :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      Hprefix₀ Hfields.isType
  have HsameBase := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    (HsameIndependent.symm H.outVEnvWF.ordered) Hfields
  exact ⟨T, independentFields, installedFields, installedHypotheses,
    installedResidual, hindependentFields, hinstalledFields,
    hinstalledHypotheses, hinstalledTarget, by
      simpa [base] using HsameBase⟩

/-- Insert the selected minor and every later minor beneath the rebased field
conversion.  The resulting contexts are exactly the natural contexts in
which the selected minor is applied to canonical constructor variables. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorInstalledFieldAlignmentInFullPrefix
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ independentFields installedFields installedHypotheses : List VExpr,
      ∃ installedResidual : VExpr,
        independentFields.length = A.rule.allArgs.size ∧
        installedFields.length = A.rule.allArgs.size ∧
        installedHypotheses.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (installedFields ++ installedHypotheses) installedResidual ∧
        let base := T.params ++ T.motives ++ T.minors.take minorIdx
        let remaining := (T.minors.drop minorIdx).reverse
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (liftContextPrefix remaining.length independentFields.reverse ++
            remaining ++ base.reverse)
          (liftContextPrefix remaining.length installedFields.reverse ++
            remaining ++ base.reverse) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalSelectedMinorInstalledFieldAlignmentAtGeneratedPrefix
      hpositive with
    ⟨T, independentFields, installedFields, installedHypotheses,
      installedResidual, hindependentFields, hinstalledFields,
      hinstalledHypotheses, hinstalledTarget, Hfields⟩
  let base := T.params ++ T.motives ++ T.minors.take minorIdx
  let remaining := (T.minors.drop minorIdx).reverse
  have Hremaining : OnCtx (remaining ++ base.reverse)
      (H.outVEnv.IsType Us.length) := by
    have Hprefix := T.prefixContext H.outVEnvWF.ordered
    have hminors := List.take_append_drop minorIdx T.minors
    have hreverse : T.minors.reverse =
        (T.minors.drop minorIdx).reverse ++
          (T.minors.take minorIdx).reverse := by
      simpa only [List.reverse_append] using
        (congrArg List.reverse hminors).symm
    simp only [List.reverse_append] at Hprefix
    rw [hreverse] at Hprefix
    simpa [base, remaining, List.reverse_append, List.append_assoc] using
      Hprefix
  have Hfull := VEnv.IsDefEqCtx.insertSameMiddle
    H.outVEnvWF.ordered independentFields.reverse installedFields.reverse
      remaining base.reverse Hfields
      (by simp [hindependentFields, hinstalledFields]) Hremaining
  exact ⟨T, independentFields, installedFields, installedHypotheses,
    installedResidual, hindependentFields, hinstalledFields,
    hinstalledHypotheses, hinstalledTarget, by
      simpa [base, remaining] using Hfull⟩

/-- Expose the typed selected-minor telescope in the two semantic blocks used
by its eventual application: genuine constructor fields followed by recursive
hypotheses.  Unlike `finalSelectedMinorTranslatedSplit`, this retains the
binder-by-binder source/target translation certificate. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorTypedSplit
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecInfoMinorTypeShape,
        ∃ hypothesisOrigins : RecInfoMinorHypothesisTypeOrigins
            S.sourceFullContext S.recursiveFields S.hypotheses,
        ∃ traversal : RecInfoMinorTraversalShape,
        ∃ fieldDomains hypothesisDomains sourceResidual targetResidual,
          S.hypothesis_type_origins = some hypothesisOrigins ∧
          hypothesisOrigins.stats = stats ∧
          hypothesisOrigins.recInfos.map (·.motive) =
            H.recInfos.map (·.motive) ∧
          S.traversal = some traversal ∧
          traversal.fields = S.fields ∧
          traversal.recursiveFields = S.recursiveFields ∧
          traversal.stats = stats ∧
          traversal.parameterTail = A.semantics.parameterTail ∧
          traversal.recursivePositions = A.semantics.recursivePositions ∧
          S.localIndex = i ∧
          S.fields.size = A.rule.allArgs.size ∧
          S.hypotheses.size = A.rule.recursiveArgs.size ∧
          BindingContextLE S.sourceFullContext H.localContext ∧
          Nonempty (RecInfoMinorSemanticSourceAt H.recursorWF S
            H.parameterSuffix.parameterDecls) ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          hypothesisDomains.length = A.rule.recursiveArgs.size ∧
          T.minors[minorIdx]! = VExpr.wrapForalls
            (fieldDomains ++ hypothesisDomains) targetResidual ∧
          let sourceBinders := H.params.fvars ++
            H.bindings.motives.fvars ++
              H.bindings.flatMinors.fvars.take minorIdx
          Expr.ForallTelescope
            (S.origin.abstractList sourceBinders)
            (A.rule.allArgs.size + A.rule.recursiveArgs.size)
            sourceResidual ∧
          TrExprS H.outVEnv Us
            (abstractForallContext (fieldDomains ++ hypothesisDomains)
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) []))
            sourceResidual targetResidual ∧
          H.outVEnv.IsType Us.length
            (abstractForallContext (fieldDomains ++ hypothesisDomains)
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) [])).toCtx
            targetResidual ∧
          Expr.ForallTelescopeTypeTranslation H.outVEnv Us
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx) [])
            (S.origin.abstractList sourceBinders)
            (A.rule.allArgs.size + A.rule.recursiveArgs.size)
            T.minors[minorIdx]! := by
  dsimp only
  rcases A.finalSelectedMinorTypedTelescope with
    ⟨T, S, hypothesisOrigins, traversal,
      hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos, htraversal,
      htraversalFields, htraversalRecursiveFields, htraversalStats,
      hparameterTail, hpositions,
      hlocal, hsourceFields, hsourceHypotheses, hsourceContext,
      HminorSemantic, Htyped⟩
  rcases Htyped.toWrapForalls with
    ⟨domains, sourceResidual, targetResidual, hlength,
      Hsource, htarget, Hresidual, HresidualType⟩
  let fieldDomains := domains.take A.rule.allArgs.size
  let hypothesisDomains := domains.drop A.rule.allArgs.size
  have hfieldsLE : A.rule.allArgs.size ≤ domains.length := by omega
  have hfields : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, List.length_take, Nat.min_eq_left hfieldsLE]
  have hhypotheses : hypothesisDomains.length =
      A.rule.recursiveArgs.size := by
    simp [hypothesisDomains, List.length_drop, hlength]
  have hdomains : domains = fieldDomains ++ hypothesisDomains := by
    exact (List.take_append_drop A.rule.allArgs.size domains).symm
  rw [hdomains] at htarget Hresidual HresidualType
  exact ⟨T, S, hypothesisOrigins, traversal, fieldDomains,
    hypothesisDomains, sourceResidual, targetResidual,
    hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos, htraversal,
    htraversalFields, htraversalRecursiveFields, htraversalStats,
    hparameterTail, hpositions,
    hlocal, hsourceFields, hsourceHypotheses, hsourceContext, HminorSemantic,
    hfields, hhypotheses, htarget, Hsource, Hresidual,
    HresidualType, Htyped⟩

/-- In the positive-arity case annotation consumption cannot change the
minor source's leading forall telescope.  Consequently the residual source
retained by `finalSelectedMinorTypedSplit` is exactly the constructor's
independent motive application after abstraction over hypotheses, fields,
and the common recursor prefix. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorPositiveResidualTranslation
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
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecInfoMinorTypeShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
      ∃ fieldDomains hypothesisDomains targetResidual,
        S.localIndex = i ∧
        S.fields.size = A.rule.allArgs.size ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        HS.semantic.traversal.parameterTail =
          A.semantics.parameterTail ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (fieldDomains ++ hypothesisDomains)
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx) []))
          (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
            S.fields_bound.fvars S.hypotheses.size).abstractList
              sourceBinders
              (A.rule.allArgs.size + A.rule.recursiveArgs.size))
          targetResidual ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext (fieldDomains ++ hypothesisDomains)
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx) [])).toCtx
          targetResidual := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.finalSelectedMinorTypedSplit with
    ⟨T, S, _hypothesisOrigins, traversal, fieldDomains,
      hypothesisDomains, sourceResidual, targetResidual,
      _hhypothesisOrigins, _hhypothesisStats, _hhypothesisRecInfos,
      htraversal, _htraversalFields, _htraversalRecursiveFields,
      _htraversalStats, hparameterTail, _hpositions, hlocal,
      hsourceFields, hsourceHypotheses, _hsourceContext,
      ⟨HS⟩, hfields, hhypotheses, htarget, Hsource, Hresidual,
      HresidualType, _Htyped⟩
  have hconsume := S.sourceTelescope.consumeTypeAnnotations_eq_self_of_pos
    (by simpa [hsourceFields, hsourceHypotheses] using hpositive)
  have horigin : S.origin = S.sourceType :=
    S.consumed_eq.symm.trans hconsume
  have Hexpected := S.sourceTelescope.abstractList sourceBinders
  rw [← horigin] at Hexpected
  have hresidual : sourceResidual =
      (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size).abstractList
          sourceBinders
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)) := by
    apply Hsource.residual_eq
    simpa [sourceBinders, hsourceFields, hsourceHypotheses,
      List.append_assoc] using Hexpected
  rw [hresidual] at Hresidual
  have hsemanticTraversal : HS.semantic.traversal = traversal :=
    Option.some.inj (HS.semantic.traversal_eq.symm.trans htraversal)
  exact ⟨T, S, HS, fieldDomains, hypothesisDomains, targetResidual,
    hlocal, hsourceFields, hsourceHypotheses,
    by simpa [hsemanticTraversal] using hparameterTail,
    hfields, hhypotheses, htarget, Hresidual, HresidualType⟩

/-- Positive-arity selected-minor residual with all source-shape evidence
retained on one witness.  The ordinary residual endpoint intentionally hides
the first-pass constructor shape; the final equation type comparison needs
that shape to identify the residual motive application with the independently
reconstructed constructor motive on the LHS. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorPositiveAlignedResidual
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
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecInfoMinorTypeShape,
      ∃ traversal : RecInfoMinorTraversalShape,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
      ∃ hypothesisOrigins : RecInfoMinorHypothesisTypeOrigins
          S.sourceFullContext S.recursiveFields S.hypotheses,
      ∃ fieldDomains hypothesisDomains targetResidual,
        hypothesisOrigins.stats = stats ∧
        hypothesisOrigins.recInfos.map (·.motive) =
          H.recInfos.map (·.motive) ∧
        S.constructor = indTypes[owner]!.ctors[i] ∧
        traversal.fields = S.fields ∧
        traversal.fieldFVars = S.fields_bound.fvars ∧
        traversal.terminal.abstractList S.fields_bound.fvars =
          A.rule.target.abstractList A.semantics.fieldOpening.fvars ∧
        (AddInductive.getIIndices stats traversal.terminal).1 = owner ∧
        AddInductive.isValidIndApp? stats traversal.terminal = some owner ∧
        S.motiveApp =
          Expr.app
            (mkAppN H.recInfos[owner]!.motive
              (AddInductive.getIIndices stats traversal.terminal).2)
            (mkAppN
              (mkAppN (.const S.constructor.name stats.levels) stats.params)
              S.fields) ∧
        S.fields.size = A.rule.allArgs.size ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        TrExprS H.outVEnv Us
          (abstractForallContext (fieldDomains ++ hypothesisDomains)
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx) []))
          (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
            S.fields_bound.fvars S.hypotheses.size).abstractList
              sourceBinders
              (A.rule.allArgs.size + A.rule.recursiveArgs.size))
          targetResidual ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext (fieldDomains ++ hypothesisDomains)
            (abstractForallContext
              (T.params ++ T.motives ++ T.minors.take minorIdx) [])).toCtx
          targetResidual := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.finalSelectedMinorShape with
    ⟨T, D, _O, S, horigin, _hlocal, _hconstructors, hconstructor,
      hsourceFields, ⟨HS⟩, hypothesisOrigins,
      _hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos,
      traversal, htraversal, htraversalConstructor, htraversalFields,
      htraversalRecursiveFields, htraversalStats, hvalid, hmotiveApp,
      _hrootContext, hterminalContext, _hsourceContext, Hdomain,
      HdomainType⟩
  have hprefixTraversal := traversal.parameterPrefix
  rw [htraversalStats, htraversalConstructor, hconstructor] at hprefixTraversal
  have hparameterTail :
      traversal.parameterTail = A.semantics.parameterTail :=
    hprefixTraversal.tail_eq A.semantics.parameterPrefix
  have HruleDecisions : RecursorFieldDecisions stats
      A.semantics.fieldRoot traversal.parameterTail A.rule.root
      A.rule.target A.rule.allArgs A.rule.recursiveArgs
      A.semantics.recursivePositions := by
    rw [hparameterTail]
    exact A.semantics.decisions
  have hterminalToRule : BindingContextLE traversal.terminalContext
      A.semantics.fieldRoot :=
    hterminalContext.trans A.semantics.fieldRootExtension.contextLE
  have HminorDecisions : RecursorFieldDecisions stats
      traversal.rootContext traversal.parameterTail traversal.terminalContext
      traversal.terminal traversal.fields traversal.recursiveFields
      traversal.recursivePositions := by
    simpa [htraversalStats] using traversal.decisions
  have hpositions : traversal.recursivePositions =
      A.semantics.recursivePositions :=
    H.fieldReplay stats traversal.rootContext A.semantics.fieldRoot
      traversal.terminalContext A.rule.root traversal.parameterTail
      traversal.terminal A.rule.target traversal.fields
      traversal.recursiveFields A.rule.allArgs A.rule.recursiveArgs
      traversal.recursivePositions A.semantics.recursivePositions
      hterminalToRule traversal.parameterTail_fvars HminorDecisions
      HruleDecisions
  have hsourceHypotheses : S.hypotheses.size =
      A.rule.recursiveArgs.size :=
    S.hypotheses_size_eq_rule traversal A.semantics
      htraversalRecursiveFields hpositions
  rcases S.originTelescope with ⟨sourceResidual, Hsource⟩
  have Habstract := Hsource.abstractList sourceBinders
  rw [hsourceFields, hsourceHypotheses] at Habstract
  have Hdomain' : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives ++ T.minors.take minorIdx) [])
      (S.origin.abstractList sourceBinders) T.minors[minorIdx]! := by
    rw [horigin]
    exact Hdomain
  have Htyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    Habstract Hdomain' HdomainType
  rcases Htyped.toWrapForalls with
    ⟨domains, splitResidual, targetResidual, hdomainsLength,
      HsplitSource, htarget, Hresidual, HresidualType⟩
  let fieldDomains := domains.take A.rule.allArgs.size
  let hypothesisDomains := domains.drop A.rule.allArgs.size
  have hfieldsLE : A.rule.allArgs.size ≤ domains.length := by omega
  have hfields : fieldDomains.length = A.rule.allArgs.size := by
    simp [fieldDomains, List.length_take, Nat.min_eq_left hfieldsLE]
  have hhypotheses : hypothesisDomains.length =
      A.rule.recursiveArgs.size := by
    simp [hypothesisDomains, List.length_drop, hdomainsLength]
  have hdomains : domains = fieldDomains ++ hypothesisDomains :=
    (List.take_append_drop A.rule.allArgs.size domains).symm
  rw [hdomains] at htarget Hresidual HresidualType
  have hconsume := S.sourceTelescope.consumeTypeAnnotations_eq_self_of_pos
    (by simpa [hsourceFields, hsourceHypotheses] using hpositive)
  have hsourceType : S.origin = S.sourceType :=
    S.consumed_eq.symm.trans hconsume
  have Hexpected := S.sourceTelescope.abstractList sourceBinders
  rw [← hsourceType] at Hexpected
  have hresidualShape : splitResidual =
      (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size).abstractList
          sourceBinders
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)) := by
    apply HsplitSource.residual_eq
    simpa [sourceBinders, hsourceFields, hsourceHypotheses,
      List.append_assoc] using Hexpected
  rw [hresidualShape] at Hresidual
  have hfieldFVars : traversal.fieldFVars =
      S.fields_bound.fvars := by
    have harrays : (traversal.fieldFVars.map Expr.fvar).toArray =
        (S.fields_bound.fvars.map Expr.fvar).toArray :=
      traversal.fields_eq.symm.trans <|
        htraversalFields.trans S.fields_bound.expressions
    have hlists : traversal.fieldFVars.map Expr.fvar =
        S.fields_bound.fvars.map Expr.fvar := by
      simpa using congrArg Array.toList harrays
    exact (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp hlists
  have hterminalClosed :
      traversal.terminal.abstractList S.fields_bound.fvars =
        traversal.fieldResidual := by
    rw [← hfieldFVars]
    exact traversal.fieldClosed
  have HtraversalTelescope := traversal.fieldTelescope
  rw [htraversalFields, hparameterTail] at HtraversalTelescope
  have hsemanticResidual :
      A.semantics.fieldOpening.residual.isForall = false := by
    rw [← A.semantics.fieldOpening.closed, Expr.abstractList_isForall]
    exact A.semantics.target_not_forall
  have hfieldResidual : traversal.fieldResidual =
      A.semantics.fieldOpening.residual :=
    (HtraversalTelescope.eq_of_residual_not_forall
      A.semantics.fieldOpening.telescope
      traversal.fieldResidual_not_forall hsemanticResidual).2
  have hclosedTargets :
      traversal.terminal.abstractList S.fields_bound.fvars =
        A.rule.target.abstractList A.semantics.fieldOpening.fvars := by
    rw [hterminalClosed, A.semantics.fieldOpening.closed, hfieldResidual]
  let selectedOwner :=
    (AddInductive.getIIndices stats traversal.terminal).1
  have hselectedValid : AddInductive.isValidIndApp? stats
      traversal.terminal = some selectedOwner := by
    simpa [selectedOwner] using hvalid
  have hselectedDecl : selectedOwner < decl.types.length := by
    have hselectedStats :=
      (checkPositivityStep.isValidIndApp?_some hselectedValid).1
    rw [A.semantics.validStats.types_size] at hselectedStats
    exact hselectedStats
  have hselectedHead : traversal.terminal.getAppFn =
      .const (decl.types[selectedOwner]'hselectedDecl).name stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead
      (checkPositivityStep.isValidIndApp?_some hselectedValid).2
      (A.semantics.validStats.indConstAt hselectedDecl)
  have htargetValid : AddInductive.isValidIndAppIdx stats A.rule.target
      owner = true := by
    have h := (checkPositivityStep.isValidIndApp?_some
      A.semantics.target_valid).2
    simpa [A.semantic_owner] using h
  have htargetHead : A.rule.target.getAppFn =
      .const (decl.types[owner]'A.abstractOwner_lt).name stats.levels :=
    checkPositivityStep.isValidIndAppIdx.constHead htargetValid
      (A.semantics.validStats.indConstAt A.abstractOwner_lt)
  have hname : (decl.types[selectedOwner]'hselectedDecl).name =
      (decl.types[owner]'A.abstractOwner_lt).name := by
    have heq := congrArg Expr.getAppFn hclosedTargets
    rw [Expr.getAppFn_abstractList, hselectedHead,
      Expr.getAppFn_abstractList, htargetHead] at heq
    simp [Expr.abstractList, Expr.abstract1] at heq
    exact heq
  have htypeNames : (decl.types.map (fun type => type.name)).Nodup := by
    have hprefix := (List.nodup_append.mp
      (Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup
        R.core)).1
    simpa [VInductDecl.sourceNames, VInductDecl.typeConstants,
      VInductiveType.toVConstVal, Function.comp_def] using hprefix
  have hselectedOwner : selectedOwner = owner := by
    have hleft : selectedOwner <
        (decl.types.map (fun type => type.name)).length := by simpa
    have hright : owner <
        (decl.types.map (fun type => type.name)).length := by
      simpa using A.abstractOwner_lt
    apply (List.getElem_inj (h₀ := hleft) (h₁ := hright)
      htypeNames).mp
    simpa only [List.getElem_map] using hname
  have hselectedOwner' :
      (AddInductive.getIIndices stats traversal.terminal).1 = owner := by
    simpa [selectedOwner] using hselectedOwner
  have hmotiveApp' : S.motiveApp =
      Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats traversal.terminal).2)
        (mkAppN
          (mkAppN (.const S.constructor.name stats.levels) stats.params)
          S.fields) := by
    rw [hmotiveApp]
    rcases hindices : AddInductive.getIIndices stats traversal.terminal with
      ⟨motiveOwner, indices⟩
    have : motiveOwner = owner := by
      simpa [hindices] using hselectedOwner'
    subst motiveOwner
    rfl
  exact ⟨T, S, traversal, HS, hypothesisOrigins,
    fieldDomains, hypothesisDomains, targetResidual,
    hhypothesisStats, hhypothesisRecInfos,
    hconstructor, htraversalFields, hfieldFVars, hclosedTargets,
    hselectedOwner', by simpa [hselectedOwner'] using hvalid,
    hmotiveApp', hsourceFields, hsourceHypotheses,
    hfields, hhypotheses, htarget, Hresidual, HresidualType⟩

/-- After each constructor pass closes its own fresh field identifiers, the
minor result retained by `mkRecType` is literally the constructor-motive
application reconstructed for the generated iota rule.  The proof compares
parameter and index spines through the alpha-closed inductive targets and
normalizes both field arrays to the same de Bruijn sequence. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.alignedMotiveAppFieldClosure
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
    (S : RecInfoMinorTypeShape) (traversal : RecInfoMinorTraversalShape)
    (hconstructor : S.constructor = indTypes[owner]!.ctors[i])
    (htraversalFields : traversal.fields = S.fields)
    (hfieldFVars : traversal.fieldFVars = S.fields_bound.fvars)
    (hclosedTargets :
      traversal.terminal.abstractList S.fields_bound.fvars =
        A.rule.target.abstractList A.semantics.fieldOpening.fvars)
    (hvalid : AddInductive.isValidIndApp? stats traversal.terminal =
      some owner)
    (hmotiveApp : S.motiveApp =
      Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats traversal.terminal).2)
        (mkAppN
          (mkAppN (.const S.constructor.name stats.levels) stats.params)
          S.fields))
    (hfields : S.fields.size = A.rule.allArgs.size) :
    S.motiveApp.abstractList S.fields_bound.fvars =
      Expr.app
        (mkAppN
          (H.recInfos[owner]!.motive.abstractList S.fields_bound.fvars)
          ((AddInductive.getIIndices stats A.rule.target).2.map fun index =>
            index.abstractList A.rule.all_args_bound.fvars))
        (A.rule.sourceConstructorMajor.abstractList
          A.rule.all_args_bound.fvars) := by
  have hruleFieldFVars : A.semantics.fieldOpening.fvars =
      A.rule.all_args_bound.fvars :=
    A.semantics.fieldOpening.fvars_eq_bound A.rule.all_args_bound
  have hindices := congrArg
    (fun target => (AddInductive.getIIndices stats target).2)
    hclosedTargets
  rw [checkPositivityStep.getIIndices.snd_abstractList,
    checkPositivityStep.getIIndices.snd_abstractList,
    hruleFieldFVars] at hindices
  have htraversalValid : AddInductive.isValidIndAppIdx stats
      traversal.terminal owner = true :=
    (checkPositivityStep.isValidIndApp?_some hvalid).2
  have hruleValid : AddInductive.isValidIndAppIdx stats A.rule.target
      owner = true := by
    have h := (checkPositivityStep.isValidIndApp?_some
      A.semantics.target_valid).2
    simpa [A.semantic_owner] using h
  have htraversalPrefix :=
    A.semantics.validStats.sourceParameterPrefix htraversalValid
  have hrulePrefix := A.semantics.validStats.sourceParameterPrefix hruleValid
  have hargs := congrArg Expr.getAppArgs hclosedTargets
  rw [Expr.getAppArgs_abstractList, Expr.getAppArgs_abstractList] at hargs
  have hparams :
      stats.params.map (fun arg =>
        arg.abstractList S.fields_bound.fvars) =
      stats.params.map (fun arg =>
        arg.abstractList A.rule.all_args_bound.fvars) := by
    apply Array.toList_inj.mp
    have htake := congrArg (List.take stats.params.size)
      (congrArg Array.toList hargs)
    simp only [Array.toList_map] at htake
    have htake' :
        List.map (fun arg => arg.abstractList S.fields_bound.fvars)
            (List.take stats.params.size
              traversal.terminal.getAppArgsList) =
          List.map (fun arg =>
            arg.abstractList A.semantics.fieldOpening.fvars)
            (List.take stats.params.size A.rule.target.getAppArgsList) := by
      simpa only [List.map_take, Expr.getAppArgs_toList] using htake
    rw [htraversalPrefix, hrulePrefix, hruleFieldFVars] at htake'
    simpa only [Array.toList_map] using htake'
  have hsourceFields :
      S.fields.map (fun arg => arg.abstractList S.fields_bound.fvars) =
      A.rule.allArgs.map (fun arg =>
        arg.abstractList A.rule.all_args_bound.fvars) := by
    have hleft := congrArg
      (Array.map fun arg => arg.abstractList S.fields_bound.fvars)
      S.fields_bound.expressions
    have hright := congrArg
      (Array.map fun arg =>
        arg.abstractList A.rule.all_args_bound.fvars)
      A.rule.all_args_bound.expressions
    have hleftCanonical := Expr.abstractList_fvarArray
      S.fields_bound.fvars 0 S.fields_nodup
    have hrightCanonical := Expr.abstractList_fvarArray
      A.rule.all_args_bound.fvars 0 A.rule.all_args_nodup
    rw [hleftCanonical] at hleft
    rw [hrightCanonical] at hright
    have hlength : S.fields_bound.fvars.length =
        A.rule.all_args_bound.fvars.length :=
      S.fields_bound.length_fvars.trans <|
        hfields.trans A.rule.all_args_bound.length_fvars.symm
    rw [hlength] at hleft
    exact hleft.trans hright.symm
  rw [hmotiveApp, hconstructor]
  unfold BoundGeneratedRecursorRule.sourceConstructorMajor
  simp only [Expr.abstractList_app, Expr.abstractList_mkAppN,
    Expr.abstractList_const]
  rw [hindices, hparams, hsourceFields]

/-- Once the selected constructor fields are closed, the aligned motive
application can mention only the common parameter and motive binders.  In
particular it is independent of every minor binder which is inserted after
the selected minor type has been generated. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.alignedMotiveAppFieldClosureScope
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
    (S : RecInfoMinorTypeShape)
    (hfieldClosure :
      S.motiveApp.abstractList S.fields_bound.fvars =
        Expr.app
          (mkAppN
            (H.recInfos[owner]!.motive.abstractList S.fields_bound.fvars)
            ((AddInductive.getIIndices stats A.rule.target).2.map fun index =>
              index.abstractList A.rule.all_args_bound.fvars))
          (A.rule.sourceConstructorMajor.abstractList
            A.rule.all_args_bound.fvars)) :
    (S.motiveApp.abstractList S.fields_bound.fvars).FVarsIn fun fv =>
      fv ∈ A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars := by
  let outer := A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars
  let fieldFVars := A.rule.all_args_bound.fvars
  let P := fun fv => fv ∈ outer
  have hownerRecInfos : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfos
  rcases A.rule.motives_bound.getElem_eq_fvar owner hownerMotive with
    ⟨hownerMotiveFVars, hownerMotiveSource⟩
  let motiveFVar := A.rule.motives_bound.fvars[owner]
  have hmotive : H.recInfos[owner]!.motive = .fvar motiveFVar := by
    rw [getElem!_pos H.recInfos owner hownerRecInfos]
    simpa [motiveFVar] using hownerMotiveSource
  have Hmotive :
      (H.recInfos[owner]!.motive.abstractList
        S.fields_bound.fvars).FVarsIn P := by
    apply FVarsIn.abstractList_of
    rw [hmotive]
    change motiveFVar ∈ S.fields_bound.fvars ∨ P motiveFVar
    exact Or.inr <| List.mem_append_right _
      (List.getElem_mem hownerMotiveFVars)
  have hsemanticFields : A.semantics.fieldsRecent.fvars = fieldFVars :=
    BoundFVarArray.fvars_eq
      A.semantics.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      A.rule.all_args_bound rfl
  have hparameterFVars : ExprArrayFVarIds stats.params =
      A.rule.params_bound.fvars := by
    exact A.rule.params_bound.exprArrayFVarIds
  have Htarget : A.rule.target.FVarsIn fun fv =>
      fv ∈ fieldFVars ∨ P fv := by
    apply A.semantics.targetFVarsIn.mono
    intro fv hfv
    rcases hfv with hfield | hparam
    · rw [hsemanticFields] at hfield
      exact Or.inl hfield
    · rw [hparameterFVars] at hparam
      exact Or.inr <| List.mem_append_left _ hparam
  have Hindices : ∀ index ∈
      (AddInductive.getIIndices stats A.rule.target).2,
      (index.abstractList fieldFVars).FVarsIn P := by
    intro index hindex
    have hindexArgs : index ∈ A.rule.target.getAppArgsList := by
      have hsuffix :
          (AddInductive.getIIndices stats A.rule.target).2.toList =
            A.rule.target.getAppArgs.toList.drop stats.params.size := by
        change (A.rule.target.getAppArgs[stats.params.size:]).toList = _
        rw [List.drop_eq_drop_min]
        simp only [Subarray.toList_eq, Array.array_toSubarray,
          Array.start_toSubarray, Array.stop_toSubarray, Nat.min_self,
          Array.toList_extract, List.extract_eq_take_drop,
          Array.length_toList]
        apply List.take_of_length_le
        simp
      have hdrop : index ∈
          A.rule.target.getAppArgs.toList.drop stats.params.size := by
        rw [← hsuffix]
        exact Array.mem_toList_iff.mpr hindex
      simpa [Expr.getAppArgs_toList] using List.mem_of_mem_drop hdrop
    apply FVarsIn.abstractList_of
    exact (Htarget.getAppArgsList hindexArgs).mono fun fv hfv =>
      hfv
  have Hmajor :
      (A.rule.sourceConstructorMajor.abstractList fieldFVars).FVarsIn P := by
    have HconstructorScope := A.semantics.constructor_translation.fvarsIn
    unfold BoundGeneratedRecursorRule.sourceConstructorMajor at HconstructorScope
    rw [Expr.mkAppN_eq_mkAppList, Expr.mkAppN_eq_mkAppList] at HconstructorScope
    have HconstContext :=
      (FVarsIn.mkAppList.mp (FVarsIn.mkAppList.mp HconstructorScope).1).1
    have Hconst : (Expr.const indTypes[owner]!.ctors[i].name stats.levels).FVarsIn
        (fun fv => fv ∈ fieldFVars ∨ P fv) := by
      change ∀ level ∈ stats.levels, level.hasMVar' = false
      change ∀ level ∈ stats.levels, level.hasMVar' = false at HconstContext
      exact HconstContext
    apply FVarsIn.abstractList_of
    unfold BoundGeneratedRecursorRule.sourceConstructorMajor
    rw [Expr.mkAppN_eq_mkAppList, Expr.mkAppN_eq_mkAppList]
    apply FVarsIn.mkAppList.mpr
    constructor
    · apply FVarsIn.mkAppList.mpr
      constructor
      · exact Hconst
      · intro param hparam
        have hparam' : param ∈
            A.rule.params_bound.fvars.map Expr.fvar := by
          simpa [A.rule.params_bound.expressions] using hparam
        rcases List.mem_map.mp hparam' with ⟨fv, hfv, rfl⟩
        exact Or.inr <| List.mem_append_left _ hfv
    · intro field hfield
      have hfield' : field ∈ fieldFVars.map Expr.fvar := by
        simpa [fieldFVars, A.rule.all_args_bound.expressions] using hfield
      rcases List.mem_map.mp hfield' with ⟨fv, hfv, rfl⟩
      exact Or.inl hfv
  rw [hfieldClosure]
  change FVarsIn P (Expr.app _ _)
  constructor
  · rw [Expr.mkAppN_eq_mkAppList]
    apply FVarsIn.mkAppList.mpr
    constructor
    · exact Hmotive
    · intro index hindex
      rw [Array.toList_map] at hindex
      rcases List.mem_map.mp hindex with ⟨source, hsource, rfl⟩
      exact Hindices source (Array.mem_toList_iff.mp hsource)
  · simpa [fieldFVars] using Hmajor

/-- The selected motive is an outer binder and therefore is unaffected by
closing the fresh constructor fields used to assemble its application. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.alignedOwnerMotiveFieldClosure
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
    (S : RecInfoMinorTypeShape)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF S
      H.parameterSuffix.parameterDecls)
    (indices : Array Expr) (major : Expr)
    (hmotiveApp : S.motiveApp =
      Expr.app (mkAppN H.recInfos[owner]!.motive indices) major) :
    H.recInfos[owner]!.motive.abstractList S.fields_bound.fvars =
      H.recInfos[owner]!.motive := by
  have hownerRecInfos : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfos
  rcases A.rule.motives_bound.getElem_eq_fvar owner hownerMotive with
    ⟨hownerMotiveFVars, hownerMotiveSource⟩
  let motiveFVar := A.rule.motives_bound.fvars[owner]
  have hmotive : H.recInfos[owner]!.motive = .fvar motiveFVar := by
    rw [getElem!_pos H.recInfos owner hownerRecInfos]
    simpa [motiveFVar] using hownerMotiveSource
  rcases HS.semantic.motiveHeadRoot with ⟨headFVar, hhead, hheadRoot⟩
  have hheadEq := congrArg Expr.getAppFn hmotiveApp
  rw [hhead] at hheadEq
  have hheadFVar : headFVar = motiveFVar := by
    simpa [Expr.getAppFn, Expr.getAppFn_mkAppN, hmotive] using hheadEq
  subst headFVar
  have hheadRoot' : motiveFVar ∈
      HS.semantic.traversal.rootContext.lctx.fvars := by
    rw [← HS.semantic.rootWF.lctx_eq,
      HS.semantic.rootWF.mlctx_wf.tr.fvars_eq]
    exact hheadRoot
  have hfieldFVars : HS.semantic.fieldsRecent.fvars =
      S.fields_bound.fvars :=
    BoundFVarArray.fvars_eq_of_array_eq
      HS.semantic.fieldsRecent.toFreshBoundFVarArray.toBoundFVarArray
      S.fields_bound rfl
  have hnotField : motiveFVar ∉ S.fields_bound.fvars := by
    intro hfield
    rw [← hfieldFVars] at hfield
    exact HS.semantic.fieldsRecent.fresh motiveFVar hfield hheadRoot'
  rw [hmotive, Expr.abstractList_fvar_of_not_mem hnotField]

/-- Insert the selected and later minor binders into the positive-arity
residual source.  After the recursive-hypothesis holes are left open, the
result is exactly the independently reconstructed constructor-motive type
under the complete production rule binder list. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.alignedPositiveResidualSource
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
    (S : RecInfoMinorTypeShape)
    (HS : RecInfoMinorSemanticSourceAt H.recursorWF S
      H.parameterSuffix.parameterDecls)
    (traversal : RecInfoMinorTraversalShape)
    (hmotiveApp : S.motiveApp =
      Expr.app
        (mkAppN H.recInfos[owner]!.motive
          (AddInductive.getIIndices stats traversal.terminal).2)
        (mkAppN
          (mkAppN (.const S.constructor.name stats.levels) stats.params)
          S.fields))
    (hfieldClosure :
      S.motiveApp.abstractList S.fields_bound.fvars =
        Expr.app
          (mkAppN
            (H.recInfos[owner]!.motive.abstractList S.fields_bound.fvars)
            ((AddInductive.getIIndices stats A.rule.target).2.map fun index =>
              index.abstractList A.rule.all_args_bound.fvars))
          (A.rule.sourceConstructorMajor.abstractList
            A.rule.all_args_bound.fvars))
    (hfields : S.fields.size = A.rule.allArgs.size)
    (hhypotheses : S.hypotheses.size = A.rule.recursiveArgs.size) :
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    let remainingMinorFVars := A.rule.minors_bound.fvars.drop minorIdx
    let arity := A.rule.allArgs.size + A.rule.recursiveArgs.size
    let expected := Expr.app
      (mkAppN H.recInfos[owner]!.motive
        (AddInductive.getIIndices stats A.rule.target).2)
      A.rule.sourceConstructorMajor
    (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
      S.fields_bound.fvars S.hypotheses.size).abstractList
        sourceBinders arity).liftLooseBVars'
          arity remainingMinorFVars.length =
      (expected.abstractList A.rule.binders).liftLooseBVars' 0
        A.rule.recursiveArgs.size := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  let outer := A.rule.params_bound.fvars ++ A.rule.motives_bound.fvars
  let generatedPrefix := outer ++ A.rule.minors_bound.fvars.take minorIdx
  let remainingMinorFVars := A.rule.minors_bound.fvars.drop minorIdx
  let fieldClosed := S.motiveApp.abstractList S.fields_bound.fvars
  let expected := Expr.app
    (mkAppN H.recInfos[owner]!.motive
      (AddInductive.getIIndices stats A.rule.target).2)
    A.rule.sourceConstructorMajor
  have hsourceParams : H.params.fvars = A.rule.params_bound.fvars :=
    BoundFVarArray.fvars_eq_of_array_eq H.params A.rule.params_bound rfl
  have hsourceMotives : H.bindings.motives.fvars =
      A.rule.motives_bound.fvars :=
    BoundFVarArray.fvars_eq_of_array_eq H.bindings.motives
      A.rule.motives_bound rfl
  have hsourceMinors : H.bindings.flatMinors.fvars =
      A.rule.minors_bound.fvars :=
    BoundFVarArray.fvars_eq_of_array_eq H.bindings.flatMinors
      A.rule.minors_bound rfl
  have hsourceBinders : sourceBinders = generatedPrefix := by
    simp only [sourceBinders, generatedPrefix, outer]
    rw [hsourceParams, hsourceMotives, hsourceMinors]
  have hfieldsLength : S.fields_bound.fvars.length =
      A.rule.allArgs.size :=
    S.fields_bound.length_fvars.trans hfields
  have hhypothesesLength : S.hypotheses_bound.fvars.length =
      A.rule.recursiveArgs.size :=
    S.hypotheses_bound.length_fvars.trans hhypotheses
  have HmotiveClosed : Closed S.motiveApp 0 := by
    have Hclosed := HS.semantic.motivePreTranslation.closed
    rw [HS.semantic.terminalWF.mlctx.noBV] at Hclosed
    simpa using Hclosed
  have HfieldClosed : Closed fieldClosed A.rule.allArgs.size := by
    have Hclosed := Closed.abstractList_at
      (e := S.motiveApp) (fvars := S.fields_bound.fvars)
      (depth := 0) (outer := 0) HmotiveClosed
    simpa [fieldClosed, hfieldsLength] using Hclosed
  have hcloseHypotheses := HS.semantic.abstractHypotheses_motiveApp
  have hfieldShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := S.motiveApp) (fvars := S.fields_bound.fvars)
    (depth := 0) (extra := S.hypotheses.size)
    HmotiveClosed S.fields_nodup
  have hfieldShift' :
      S.motiveApp.abstractList S.fields_bound.fvars
          A.rule.recursiveArgs.size =
        fieldClosed.liftLooseBVars' 0 A.rule.recursiveArgs.size := by
    simpa [fieldClosed, hhypotheses] using hfieldShift
  have hfieldScope := A.alignedMotiveAppFieldClosureScope S hfieldClosure
  have hfieldAvoidsRemaining : fieldClosed.FVarsIn
      (fun fv => fv ∉ remainingMinorFVars) := by
    apply hfieldScope.mono
    intro fv houter hremaining
    have hminor : fv ∈ A.rule.minors_bound.fvars :=
      List.mem_of_mem_drop hremaining
    have hdisjoint := (List.nodup_append.mp
      A.rule.outer_binders_nodup).2.2
    exact hdisjoint fv houter fv hminor rfl
  have hremainingAbstract : fieldClosed.abstractList
      remainingMinorFVars A.rule.allArgs.size = fieldClosed :=
    hfieldAvoidsRemaining.abstractList_eq_self HfieldClosed
  have hprefixNodup : generatedPrefix.Nodup := by
    have hsub : generatedPrefix <+ outer ++ A.rule.minors_bound.fvars :=
      (List.Sublist.refl outer).append
        (List.take_sublist _ A.rule.minors_bound.fvars)
    exact A.rule.outer_binders_nodup.sublist <| by
      simpa [generatedPrefix, outer, List.append_assoc] using hsub
  have houterSplit : generatedPrefix ++ remainingMinorFVars =
      outer ++ A.rule.minors_bound.fvars := by
    simp [generatedPrefix, remainingMinorFVars, outer,
      List.append_assoc]
  have hfullOuterNodup :
      (generatedPrefix ++ remainingMinorFVars).Nodup := by
    rw [houterSplit]
    simpa [outer, List.append_assoc] using A.rule.outer_binders_nodup
  have hprefixShift := Expr.abstractList_add_eq_liftLooseBVars
    (e := fieldClosed) (fvars := generatedPrefix)
    (depth := A.rule.allArgs.size) (extra := remainingMinorFVars.length)
    HfieldClosed hprefixNodup
  have hprefixAppend := Expr.abstractList_after_inner
    (e := fieldClosed) (outer := generatedPrefix)
    (inner := remainingMinorFVars) (k := A.rule.allArgs.size)
    hfullOuterNodup
  rw [hremainingAbstract] at hprefixAppend
  have hprefixToFull :
      (fieldClosed.abstractList generatedPrefix A.rule.allArgs.size
        ).liftLooseBVars' A.rule.allArgs.size remainingMinorFVars.length =
      fieldClosed.abstractList (outer ++ A.rule.minors_bound.fvars)
        A.rule.allArgs.size := by
    have hcombined := hprefixShift.symm.trans hprefixAppend
    rw [houterSplit] at hcombined
    exact hcombined
  have hownerRecInfos : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfos
  rcases A.rule.motives_bound.getElem_eq_fvar owner hownerMotive with
    ⟨hownerMotiveFVars, hownerMotiveSource⟩
  let motiveFVar := A.rule.motives_bound.fvars[owner]
  have hmotive : H.recInfos[owner]!.motive = .fvar motiveFVar := by
    rw [getElem!_pos H.recInfos owner hownerRecInfos]
    simpa [motiveFVar] using hownerMotiveSource
  have hnotRuleField : motiveFVar ∉ A.rule.all_args_bound.fvars := by
    intro hfield
    apply A.rule.all_args_outer_fresh motiveFVar hfield
    exact List.mem_append_left _ <|
      List.mem_append_right _ (List.getElem_mem hownerMotiveFVars)
  have hmotiveRuleFields : H.recInfos[owner]!.motive.abstractList
      A.rule.all_args_bound.fvars = H.recInfos[owner]!.motive := by
    rw [hmotive, Expr.abstractList_fvar_of_not_mem hnotRuleField]
  have hmotiveSourceFields := A.alignedOwnerMotiveFieldClosure S HS
    (AddInductive.getIIndices stats traversal.terminal).2
    (mkAppN
      (mkAppN (.const S.constructor.name stats.levels) stats.params)
      S.fields) hmotiveApp
  have hfieldExpected : fieldClosed =
      expected.abstractList A.rule.all_args_bound.fvars := by
    dsimp only [fieldClosed, expected]
    rw [hfieldClosure]
    simp only [Expr.abstractList_app, Expr.abstractList_mkAppN]
    rw [hmotiveSourceFields, hmotiveRuleFields]
  have hfullExpected :
      fieldClosed.abstractList (outer ++ A.rule.minors_bound.fvars)
          A.rule.allArgs.size =
        expected.abstractList A.rule.binders := by
    rw [hfieldExpected]
    have Hclose := Expr.abstractList_after_inner
      (e := expected) (outer := outer ++ A.rule.minors_bound.fvars)
      (inner := A.rule.all_args_bound.fvars) (k := 0) (by
        simpa [outer, BoundGeneratedRecursorRule.binders,
          List.append_assoc] using A.rule.binders_nodup)
    simpa [outer, BoundGeneratedRecursorRule.binders,
      A.rule.all_args_bound.length_fvars, List.append_assoc] using Hclose
  have hsourcePrefix :
      (((S.motiveApp.abstractList S.hypotheses_bound.fvars).abstractList
        S.fields_bound.fvars S.hypotheses.size).abstractList
          sourceBinders
          (A.rule.allArgs.size + A.rule.recursiveArgs.size)) =
        (fieldClosed.abstractList generatedPrefix A.rule.allArgs.size
          ).liftLooseBVars' 0 A.rule.recursiveArgs.size := by
    rw [hcloseHypotheses, hsourceBinders]
    rw [show S.hypotheses.size = A.rule.recursiveArgs.size from hhypotheses]
    rw [hfieldShift']
    have hcommute := Expr.liftLooseBVars'_abstractList_add
      (e := fieldClosed) (fvars := generatedPrefix)
      (start := 0) (cutoff := A.rule.allArgs.size)
      (amount := A.rule.recursiveArgs.size) (by omega) hprefixNodup
    simpa [fieldClosed, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcommute
  rw [hsourcePrefix]
  have hcommute := Expr.liftLooseBVars_comm
    (fieldClosed.abstractList generatedPrefix A.rule.allArgs.size)
    remainingMinorFVars.length A.rule.recursiveArgs.size
    A.rule.allArgs.size 0 (by omega)
  calc
    _ = ((fieldClosed.abstractList generatedPrefix
            A.rule.allArgs.size).liftLooseBVars'
          A.rule.allArgs.size remainingMinorFVars.length
        ).liftLooseBVars' 0 A.rule.recursiveArgs.size := by
      have hcutoff : A.rule.recursiveArgs.size + A.rule.allArgs.size =
          A.rule.allArgs.size + A.rule.recursiveArgs.size := by omega
      rw [hcutoff] at hcommute
      exact hcommute.symm
    _ = _ := by rw [hprefixToFull, hfullExpected]

/-- Opening the selected minor's translated telescope yields a genuine
abstract context for every constructor field and recursive hypothesis.  The
older parameter/motive/minor prefix is recovered from the complete generated
recursor context, so no local-context well-formedness premise remains hidden
in the eventual minor application. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorTargetContext
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ fieldDomains hypothesisDomains targetResidual,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        let base := T.params ++ T.motives ++ T.minors.take minorIdx
        OnCtx ((fieldDomains ++ hypothesisDomains).reverse ++
            (abstractForallContext base []).toCtx)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.IsType Us.length
          ((fieldDomains ++ hypothesisDomains).reverse ++
            (abstractForallContext base []).toCtx)
          targetResidual := by
  dsimp only
  rcases A.finalSelectedMinorTypedSplit with
    ⟨T, _S, _hypothesisOrigins, _traversal, fieldDomains,
      hypothesisDomains, _sourceResidual, targetResidual,
      _hhypothesisOrigins, _hhypothesisStats, _hhypothesisRecInfos,
      _htraversal,
      _htraversalFields, _htraversalRecursiveFields, _htraversalStats,
      _hparameterTail, _hpositions,
      _hlocal, _hsourceFields, _hsourceHypotheses,
      _hsourceContext,
      _HminorSemantic,
      hfields, hhypotheses, htarget, _Hsource, _Hresidual,
      _HresidualType, Htyped⟩
  let minorIdx := recursorMinorOffset indTypes owner + i
  let base := T.params ++ T.motives ++ T.minors.take minorIdx
  have Hprefix := T.prefixContext H.outVEnvWF.ordered
  have hminorDecomp : T.minors = T.minors.take minorIdx ++
      T.minors.drop minorIdx :=
    (List.take_append_drop minorIdx T.minors).symm
  rw [hminorDecomp, List.reverse_append, List.reverse_append,
    List.reverse_append, List.append_assoc] at Hprefix
  have HbaseRaw := OnCtx.append_right
    (xs := (T.minors.drop minorIdx).reverse) Hprefix
  have Hbase : OnCtx (abstractForallContext base []).toCtx
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
    rw [abstractForallContext_toCtx]
    rw [show VLCtx.toCtx ([] : VLCtx) = [] by rfl]
    simpa [base, List.reverse_append, List.append_assoc] using HbaseRaw
  have HminorType := Htyped.isType
  rw [htarget] at HminorType
  have Hopened := VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
    Hbase HminorType
  exact ⟨T, fieldDomains, hypothesisDomains, targetResidual,
    hfields, hhypotheses, htarget, Hopened.1, Hopened.2⟩

/-- In the natural context induced by the selected minor type, apply its
bound variable to all canonical constructor-field variables.  The remaining
type is exactly the lifted recursive-hypothesis suffix; this is the first
actual application step of the generated rule RHS. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorFieldApplication
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ fieldDomains hypothesisDomains targetResidual,
        fieldDomains.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        T.minors[minorIdx]! = VExpr.wrapForalls
          (fieldDomains ++ hypothesisDomains) targetResidual ∧
        let later := T.minors.drop (minorIdx + 1)
        let shift := later.length + 1
        let liftedFields :=
          (liftContextPrefix shift fieldDomains.reverse).reverse
        let liftedHypotheses :=
          (liftContextPrefixAt shift fieldDomains.length
            hypothesisDomains.reverse).reverse
        H.outVEnv.HasType Us.length
          (liftedFields.reverse ++
            (T.params ++ T.motives ++ T.minors).reverse)
          (VExpr.mkApps
            ((.bvar later.length : VExpr).liftN liftedFields.length 0)
            (recursorCanonicalVars liftedFields.length))
          (VExpr.wrapForalls liftedHypotheses
            (targetResidual.liftN shift
              (fieldDomains.length + hypothesisDomains.length))) := by
  dsimp only
  rcases A.finalSelectedMinorTargetContext with
    ⟨T, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, htarget, _Hctx, _Hresidual⟩
  let minorIdx := recursorMinorOffset indTypes owner + i
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  let later := T.minors.drop (minorIdx + 1)
  let shift := later.length + 1
  let liftedFields :=
    (liftContextPrefix shift fieldDomains.reverse).reverse
  let liftedHypotheses :=
    (liftContextPrefixAt shift fieldDomains.length
      hypothesisDomains.reverse).reverse
  have Hminor := T.minorOuterBvarTyping minorIdx hminor
  have hselected : T.minors[minorIdx]'hminor = T.minors[minorIdx]! :=
    (getElem!_pos T.minors minorIdx hminor).symm
  have hliftedDomains :
      (liftContextPrefixAt shift 0
        (fieldDomains ++ hypothesisDomains).reverse).reverse =
        liftedFields ++ liftedHypotheses := by
    simpa [shift, liftedFields, liftedHypotheses, liftContextPrefix] using
      liftContextPrefix_reverse_append shift fieldDomains hypothesisDomains
  rw [hselected, htarget] at Hminor
  dsimp only at Hminor
  change H.outVEnv.HasType _ _ _
    ((VExpr.wrapForalls (fieldDomains ++ hypothesisDomains)
      targetResidual).liftN shift 0) at Hminor
  rw [VExpr.liftN_wrapForalls, hliftedDomains] at Hminor
  have Hpartial := VEnv.HasType.mkApps_wrapForalls_prefix_canonical
    H.outVEnvWF.ordered Hminor
  exact ⟨T, fieldDomains, hypothesisDomains, targetResidual,
    hfields, hhypotheses, htarget, by
      simpa [minorIdx, later, shift, liftedFields, liftedHypotheses,
        recursorCanonicalVars, Nat.add_assoc] using Hpartial⟩

/-- Transport the canonical field application from the installed minor's
field representatives to the independently replayed field context.  The
application term is unchanged; only the dependent field declarations in its
ambient context are converted. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorFieldApplicationInIndependentContext
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
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ independentFields hypothesisDomains : List VExpr,
      ∃ targetResidual : VExpr,
        independentFields.length = A.rule.allArgs.size ∧
        hypothesisDomains.length = A.rule.recursiveArgs.size ∧
        let later := T.minors.drop (minorIdx + 1)
        let shift := later.length + 1
        let liftedFields :=
          (liftContextPrefix shift independentFields.reverse).reverse
        let liftedHypotheses :=
          (liftContextPrefixAt shift independentFields.length
            hypothesisDomains.reverse).reverse
        OnCtx
            (liftedFields.reverse ++
              (T.params ++ T.motives ++ T.minors).reverse)
            (H.outVEnv.IsType Us.length) ∧
          H.outVEnv.HasType Us.length
            (liftedFields.reverse ++
              (T.params ++ T.motives ++ T.minors).reverse)
            (VExpr.mkApps
              ((.bvar later.length : VExpr).liftN liftedFields.length 0)
              (recursorCanonicalVars liftedFields.length))
            (VExpr.wrapForalls liftedHypotheses
              (targetResidual.liftN shift
                (independentFields.length + hypothesisDomains.length))) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalSelectedMinorInstalledFieldAlignmentInFullPrefix
      hpositive with
    ⟨T, independentFields, installedFields, installedHypotheses,
      installedResidual, hindependentFields, hinstalledFields,
      hinstalledHypotheses, hinstalledTarget, Hcontext⟩
  rcases A.finalSelectedMinorFieldApplication with
    ⟨T₁, fieldDomains, hypothesisDomains, targetResidual,
      hfields, hhypotheses, htarget, Happlication⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hminors] at htarget
  rw [hparams, hmotives, hminors] at Happlication
  have hfieldDomains : fieldDomains = installedFields := by
    apply VExpr.wrapForalls_prefix_domains_eq hfields hinstalledFields
    have hwhole := htarget.symm.trans hinstalledTarget
    simpa [VExpr.wrapForalls_append] using hwhole
  subst fieldDomains
  let later := T.minors.drop (minorIdx + 1)
  let shift := later.length + 1
  let liftedFields :=
    (liftContextPrefix shift independentFields.reverse).reverse
  let liftedHypotheses :=
    (liftContextPrefixAt shift independentFields.length
      hypothesisDomains.reverse).reverse
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hdrop : T.minors.drop minorIdx =
      T.minors[minorIdx] :: later := by
    simpa [later] using List.drop_eq_getElem_cons hminor
  have hremainingLength : (T.minors.drop minorIdx).reverse.length = shift := by
    simp [hdrop, shift]
  have hminorPrefix : (T.minors.drop minorIdx).reverse ++
      (T.minors.take minorIdx).reverse = T.minors.reverse := by
    simpa only [List.reverse_append] using congrArg List.reverse
      (List.take_append_drop minorIdx T.minors)
  have hfullContext : (T.minors.drop minorIdx).reverse ++
      (T.params ++ T.motives ++ T.minors.take minorIdx).reverse =
      (T.params ++ T.motives ++ T.minors).reverse := by
    simp only [List.reverse_append]
    rw [← List.append_assoc, hminorPrefix]
  have hfullContextNormalized : (T.minors.drop minorIdx).reverse ++
      (T.params ++ (T.motives ++ T.minors.take minorIdx)).reverse =
      (T.params ++ (T.motives ++ T.minors)).reverse := by
    simpa only [List.append_assoc] using hfullContext
  have Hcontext' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (liftedFields.reverse ++
        (T.params ++ T.motives ++ T.minors).reverse)
      (liftContextPrefix shift installedFields.reverse ++
        (T.params ++ T.motives ++ T.minors).reverse) := by
    dsimp only at Hcontext
    rw [hremainingLength] at Hcontext
    simp only [List.append_assoc] at Hcontext
    rw [hfullContextNormalized] at Hcontext
    simpa [liftedFields] using Hcontext
  simp only [List.reverse_reverse] at Happlication
  have Htransported := Happlication.defeqDFC H.outVEnvWF.ordered
    (Hcontext'.symm H.outVEnvWF.ordered)
  exact ⟨T, independentFields, hypothesisDomains, targetResidual,
    hindependentFields, hhypotheses, Hcontext'.isType, by
      simpa [later, shift, liftedFields, liftedHypotheses,
        hinstalledFields, hindependentFields] using Htransported⟩

/-- Witness-stable specialization of
`finalSelectedMinorFieldApplicationInIndependentContext`.  The fixed
equation frame already carries one translated recursor telescope, so the
independently replayed application must be transported to that exact
telescope before their field contexts can be compared. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorFieldApplicationInIndependentContextFor
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
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ independentFields hypothesisDomains : List VExpr,
    ∃ targetResidual : VExpr,
      independentFields.length = A.rule.allArgs.size ∧
      hypothesisDomains.length = A.rule.recursiveArgs.size ∧
      let later := T.minors.drop (minorIdx + 1)
      let shift := later.length + 1
      let liftedFields :=
        (liftContextPrefix shift independentFields.reverse).reverse
      let liftedHypotheses :=
        (liftContextPrefixAt shift independentFields.length
          hypothesisDomains.reverse).reverse
      OnCtx
          (liftedFields.reverse ++
            (T.params ++ T.motives ++ T.minors).reverse)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length
          (liftedFields.reverse ++
            (T.params ++ T.motives ++ T.minors).reverse)
          (VExpr.mkApps
            ((.bvar later.length : VExpr).liftN liftedFields.length 0)
            (recursorCanonicalVars liftedFields.length))
          (VExpr.wrapForalls liftedHypotheses
            (targetResidual.liftN shift
              (independentFields.length + hypothesisDomains.length))) := by
  dsimp only
  rcases A.finalSelectedMinorFieldApplicationInIndependentContext
      hpositive with
    ⟨T₁, independentFields, hypothesisDomains, targetResidual,
      hindependentFields, hhypotheses, HapplicationCtx, Happlication⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams, hmotives, hminors] at HapplicationCtx Happlication
  exact ⟨independentFields, hypothesisDomains, targetResidual,
    hindependentFields, hhypotheses, HapplicationCtx, Happlication⟩

/-- Rebase the independently replayed/installed field conversion onto an
arbitrary fixed semantic outer scope representing the complete generated
parameter/motive/minor prefix. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorInstalledFieldAlignmentInOuterScopeFor
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
    (outerScope : VLCtx)
    (HouterPrefix : VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      outerScope.toCtx (T.params ++ T.motives ++ T.minors).reverse)
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ independentFields installedFields installedHypotheses : List VExpr,
    ∃ installedResidual : VExpr,
      independentFields.length = A.rule.allArgs.size ∧
      installedFields.length = A.rule.allArgs.size ∧
      installedHypotheses.length = A.rule.recursiveArgs.size ∧
      T.minors[minorIdx]! = VExpr.wrapForalls
        (installedFields ++ installedHypotheses) installedResidual ∧
      let later := T.minors.drop (minorIdx + 1)
      let shift := later.length + 1
      let liftedIndependent :=
        (liftContextPrefix shift independentFields.reverse).reverse
      let liftedInstalled :=
        (liftContextPrefix shift installedFields.reverse).reverse
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        (liftedIndependent.reverse ++ outerScope.toCtx)
        (liftedInstalled.reverse ++ outerScope.toCtx) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalSelectedMinorInstalledFieldAlignmentInFullPrefix
      hpositive with
    ⟨T₁, independentFields, installedFields, installedHypotheses,
      installedResidual, hindependentFields, hinstalledFields,
      hinstalledHypotheses, hinstalledTarget, Hfields⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hminors] at hinstalledTarget
  rw [hparams, hmotives, hminors] at Hfields
  let later := T.minors.drop (minorIdx + 1)
  let shift := later.length + 1
  let liftedIndependent :=
    (liftContextPrefix shift independentFields.reverse).reverse
  let liftedInstalled :=
    (liftContextPrefix shift installedFields.reverse).reverse
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hdrop : T.minors.drop minorIdx =
      T.minors[minorIdx] :: later := by
    simpa [later] using List.drop_eq_getElem_cons hminor
  have hremainingLength :
      (T.minors.drop minorIdx).reverse.length = shift := by
    simp [hdrop, shift]
  have hfullContext : (T.minors.drop minorIdx).reverse ++
      (T.params ++ T.motives ++ T.minors.take minorIdx).reverse =
        (T.params ++ T.motives ++ T.minors).reverse := by
    have hminorPrefix : (T.minors.drop minorIdx).reverse ++
        (T.minors.take minorIdx).reverse = T.minors.reverse := by
      simpa only [List.reverse_append] using congrArg List.reverse
        (List.take_append_drop minorIdx T.minors)
    simp only [List.reverse_append]
    rw [← List.append_assoc, hminorPrefix]
  have hfullContextNormalized : (T.minors.drop minorIdx).reverse ++
      (T.params ++ (T.motives ++ T.minors.take minorIdx)).reverse =
        (T.params ++ (T.motives ++ T.minors)).reverse := by
    simpa only [List.append_assoc] using hfullContext
  have HfieldsFull : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (liftedIndependent.reverse ++
        (T.params ++ T.motives ++ T.minors).reverse)
      (liftedInstalled.reverse ++
        (T.params ++ T.motives ++ T.minors).reverse) := by
    dsimp only at Hfields
    rw [hremainingLength] at Hfields
    simp only [List.append_assoc] at Hfields
    rw [hfullContextNormalized] at Hfields
    simpa [liftedIndependent, liftedInstalled] using Hfields
  have HouterFields := VEnv.IsDefEqCtx.rebaseCommonSuffix
    H.outVEnvWF HouterPrefix HfieldsFull
  exact ⟨independentFields, installedFields, installedHypotheses,
    installedResidual, hindependentFields, hinstalledFields,
    hinstalledHypotheses, hinstalledTarget, by
      simpa [later, shift, liftedIndependent, liftedInstalled] using
        HouterFields⟩

/-- Transport the independently replayed canonical field application from
the generated parameter/motive/minor prefix into any fixed semantic outer
scope known to represent that prefix.  Parameterizing the scope lets later
alignment arguments reuse the exact witness carrying the translated
constructor telescope. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorFieldApplicationInOuterScopeFor
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
    (outerScope : VLCtx)
    (HouterPrefix : VEnv.IsDefEqCtx H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
      outerScope.toCtx (T.params ++ T.motives ++ T.minors).reverse)
    (hpositive : 0 < A.rule.allArgs.size + A.rule.recursiveArgs.size) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ independentFields hypothesisDomains : List VExpr,
    ∃ targetResidual : VExpr,
      independentFields.length = A.rule.allArgs.size ∧
      hypothesisDomains.length = A.rule.recursiveArgs.size ∧
      let later := T.minors.drop (minorIdx + 1)
      let shift := later.length + 1
      let liftedFields :=
        (liftContextPrefix shift independentFields.reverse).reverse
      let liftedHypotheses :=
        (liftContextPrefixAt shift independentFields.length
          hypothesisDomains.reverse).reverse
      OnCtx (liftedFields.reverse ++ outerScope.toCtx)
          (H.outVEnv.IsType Us.length) ∧
        H.outVEnv.HasType Us.length
          (liftedFields.reverse ++ outerScope.toCtx)
          (VExpr.mkApps
            ((.bvar later.length : VExpr).liftN liftedFields.length 0)
            (recursorCanonicalVars liftedFields.length))
          (VExpr.wrapForalls liftedHypotheses
            (targetResidual.liftN shift
              (independentFields.length + hypothesisDomains.length))) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalSelectedMinorFieldApplicationInIndependentContextFor
      T hpositive with
    ⟨independentFields, hypothesisDomains, targetResidual,
      hindependentFields, hhypotheses, HapplicationCtx, Happlication⟩
  let later := T.minors.drop
    (recursorMinorOffset indTypes owner + i + 1)
  let shift := later.length + 1
  let liftedFields :=
    (liftContextPrefix shift independentFields.reverse).reverse
  have Hfull :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      (HouterPrefix.symm H.outVEnvWF.ordered) HapplicationCtx
  have HouterCtx := (Hfull.symm H.outVEnvWF.ordered).isType
  have HapplicationOuter :=
    Happlication.defeqDFC H.outVEnvWF.ordered Hfull
  exact ⟨independentFields, hypothesisDomains, targetResidual,
    hindependentFields, hhypotheses, by
      simpa [later, shift, liftedFields] using HouterCtx, by
      simpa [later, shift, liftedFields] using HapplicationOuter⟩

/-- Weakening the source-stable constructor fields selected in the complete
outer scope back into the executable recursor context yields the same
dependent field context as the literal semantic field telescope.  This is
the full-runtime comparison point shared with the selected-minor replay. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalOuterConstructorFieldRuntimeAlignmentFor
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
      H.recInfos[owner]!.indices.size owner) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars
    ∃ outerScope,
    ∃ Houter : checkInductiveTypes.loopType.FVarNarrowScope
        H.outVEnv Us outerScope H.recursorWF.mlctx.vlctx,
    ∃ outerFields : List VExpr,
    ∃ outerResidual : VExpr,
      outerScope.fvars = outerBinders.reverse ∧
      Houter.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
        (· ∈ outerBinders) ∧
      outerFields.length = A.rule.allArgs.size ∧
      TrExprS H.outVEnv Us outerScope A.semantics.parameterTail
        (VExpr.wrapForalls outerFields outerResidual) ∧
      H.outVEnv.IsType Us.length outerScope.toCtx
        (VExpr.wrapForalls outerFields outerResidual) ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length [] outerScope.toCtx
        (T.params ++ T.motives ++ T.minors).reverse ∧
      VEnv.IsDefEqCtx H.outVEnv Us.length []
        ((liftForallDomains outerFields Houter.shift).reverse ++
          H.recursorWF.mlctx.vlctx.toCtx)
        (A.semantics.fieldTelescope.domains.reverse ++
          H.recursorWF.mlctx.vlctx.toCtx) := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars
  rcases A.finalOuterConstructorFieldTelescopeFor T with
    ⟨outerScope, Houter, outerFields, outerResidual, houterScope,
      houterShift, houterFields, HouterTail, HouterType, HouterPrefix⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  have hfieldRootEnv : A.semantics.fieldRootContext.venv =
      H.recursorWF.venv :=
    A.semantics.fieldsRecent.venv_eq.symm.trans
      A.semantics.context_venv
  have Hruntime : TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
      A.semantics.parameterTail A.semantics.parameterTarget := by
    have Htr := A.semantics.parameterTranslation
    rw [hfieldRootEnv, A.semantics.fieldRoot_vlctx] at Htr
    exact Htr.mono hbase
  have HruntimeWF : VLCtx.WF H.outVEnv Us.length
      H.recursorWF.mlctx.vlctx :=
    (H.recursorWF.mlctx_wf.mono hbase).tr.wf
  have Hwhole := Houter.fullTargetEq H.outVEnvWF HouterTail
    (Hruntime.trExpr H.outVEnvWF HruntimeWF)
  rcases A.semantics.fieldContextDefEq with
    ⟨sourceDomains, sourceResidual, hsourceDomains,
      hparameterTarget, HsourceSemantic₀⟩
  rw [VExpr.lift'_wrapForalls_exact, hparameterTarget] at Hwhole
  have HruntimeBase : VEnv.IsDefEqCtx H.outVEnv Us.length []
      H.recursorWF.mlctx.vlctx.toCtx H.recursorWF.mlctx.vlctx.toCtx :=
    .refl HruntimeWF.toCtx
  have HouterSource := VEnv.IsDefEqU.wrapForalls_context
    H.outVEnvWF HruntimeBase
      ((liftForallDomains_length outerFields Houter.shift).trans
        (houterFields.trans hsourceDomains.symm)) Hwhole
  have HsourceSemantic : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (sourceDomains.reverse ++ H.recursorWF.mlctx.vlctx.toCtx)
      (A.semantics.fieldTelescope.domains.reverse ++
        H.recursorWF.mlctx.vlctx.toCtx) := by
    rw [hfieldRootEnv, A.semantics.fieldRoot_vlctx] at HsourceSemantic₀
    exact HsourceSemantic₀.mono hbase
  have Haligned := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HouterSource HsourceSemantic
  exact ⟨outerScope, Houter, outerFields, outerResidual, houterScope,
    houterShift, houterFields, HouterTail, HouterType, HouterPrefix,
    Haligned⟩

/-- Select the translated minor domain corresponding to recursive-result
ordinal `j`.  The source binder is retained explicitly, and its abstract
target is literally the `j`th member of the hypothesis suffix. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorHypothesisDomainAt
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecInfoMinorTypeShape,
        ∃ hypothesisOrigins : RecInfoMinorHypothesisTypeOrigins
            S.sourceFullContext S.recursiveFields S.hypotheses,
        ∃ traversal : RecInfoMinorTraversalShape,
        ∃ fieldDomains hypothesisDomains targetResidual sourceDomain,
          S.hypothesis_type_origins = some hypothesisOrigins ∧
          hypothesisOrigins.stats = stats ∧
          hypothesisOrigins.recInfos.map (·.motive) =
            H.recInfos.map (·.motive) ∧
          S.traversal = some traversal ∧
          traversal.fields = S.fields ∧
          traversal.recursiveFields = S.recursiveFields ∧
          traversal.stats = stats ∧
          traversal.parameterTail = A.semantics.parameterTail ∧
          traversal.recursivePositions = A.semantics.recursivePositions ∧
          S.localIndex = i ∧
          S.fields.size = A.rule.allArgs.size ∧
          S.hypotheses.size = A.rule.recursiveArgs.size ∧
          BindingContextLE S.sourceFullContext H.localContext ∧
          Nonempty (RecInfoMinorSemanticSourceAt H.recursorWF S
            H.parameterSuffix.parameterDecls) ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          hypothesisDomains.length = A.rule.recursiveArgs.size ∧
          T.minors[minorIdx]! = VExpr.wrapForalls
            (fieldDomains ++ hypothesisDomains) targetResidual ∧
          let sourceBinders := H.params.fvars ++
            H.bindings.motives.fvars ++
              H.bindings.flatMinors.fvars.take minorIdx
          let position := A.rule.allArgs.size + j
          Expr.ForallBinderAt
            (S.origin.abstractList sourceBinders) position sourceDomain ∧
          TrExprS H.outVEnv Us
            (abstractForallContext
              ((fieldDomains ++ hypothesisDomains).take position)
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) []))
            sourceDomain hypothesisDomains[j]! ∧
          H.outVEnv.IsType Us.length
            (abstractForallContext
              ((fieldDomains ++ hypothesisDomains).take position)
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) [])).toCtx
            hypothesisDomains[j]! := by
  dsimp only
  rcases A.finalSelectedMinorTypedSplit with
    ⟨T, S, hypothesisOrigins, traversal, fieldDomains, hypothesisDomains,
      _sourceResidual, targetResidual, hhypothesisOrigins,
      hhypothesisStats, hhypothesisRecInfos, htraversal, htraversalFields,
      htraversalRecursiveFields, htraversalStats, hparameterTail, hpositions,
      hlocal, hsourceFields, hsourceHypotheses, hsourceContext,
      HminorSemantic,
      hfields, hhypotheses, htarget, _Hsource, _Hresidual,
      _HresidualType, Htyped⟩
  let position := A.rule.allArgs.size + j
  have hposition : position <
      A.rule.allArgs.size + A.rule.recursiveArgs.size := by
    dsimp only [position]
    omega
  have hdomains : (fieldDomains ++ hypothesisDomains).length =
      A.rule.allArgs.size + A.rule.recursiveArgs.size := by
    simp [hfields, hhypotheses]
  have hjHypothesis : j < hypothesisDomains.length := by
    rw [hhypotheses]
    exact hj
  rcases Htyped.binderAt_target
      (fieldDomains ++ hypothesisDomains) targetResidual htarget
      hdomains position hposition with
    ⟨suffixSource, _name, sourceDomain, _sourceBody, _bi, _bodyTarget,
      Hprefix, hsuffix, Hdomain, HdomainType, _Hbody⟩
  have Hbinder : Expr.ForallBinderAt
      (S.origin.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars ++
          H.bindings.flatMinors.fvars.take
            (recursorMinorOffset indTypes owner + i)))
      position sourceDomain := Hprefix.binderAt hsuffix
  have hselected :
      (fieldDomains ++ hypothesisDomains)[position] = hypothesisDomains[j]! := by
    dsimp only [position]
    rw [getElem!_pos hypothesisDomains j hjHypothesis]
    simpa [hfields] using
      List.getElem_append_right fieldDomains hypothesisDomains j hjHypothesis
  rw [hselected] at Hdomain HdomainType
  exact ⟨T, S, hypothesisOrigins, traversal, fieldDomains,
    hypothesisDomains, targetResidual, sourceDomain,
    hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos, htraversal,
    htraversalFields, htraversalRecursiveFields, htraversalStats,
    hparameterTail, hpositions,
    hlocal, hsourceFields, hsourceHypotheses, hsourceContext,
    HminorSemantic, hfields, hhypotheses, htarget, Hbinder, Hdomain,
    HdomainType⟩

/-- Identify the source side of the selected recursive-hypothesis translation
with the exact declaration type introduced by `mkRecInfos.loopU`.  Thus the
pointwise target-domain certificate is no longer mediated by an arbitrary
existential source expression. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorHypothesisDeclarationDomainAt
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let minorIdx := recursorMinorOffset indTypes owner + i
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecInfoMinorTypeShape,
        ∃ hypothesisOrigins : RecInfoMinorHypothesisTypeOrigins
            S.sourceFullContext S.recursiveFields S.hypotheses,
        ∃ traversal : RecInfoMinorTraversalShape,
        ∃ fieldDomains hypothesisDomains targetResidual,
          ∃ D : BoundFVarDeclarationAt
              S.sourceFullContext S.hypotheses j,
            S.hypothesis_type_origins = some hypothesisOrigins ∧
            hypothesisOrigins.stats = stats ∧
            hypothesisOrigins.recInfos.map (·.motive) =
              H.recInfos.map (·.motive) ∧
            S.traversal = some traversal ∧
            traversal.fields = S.fields ∧
            traversal.recursiveFields = S.recursiveFields ∧
            traversal.stats = stats ∧
            traversal.parameterTail = A.semantics.parameterTail ∧
            traversal.recursivePositions = A.semantics.recursivePositions ∧
            S.recursiveFields[j]! =
              S.fields[A.semantics.recursivePositions[j]!]! ∧
            A.rule.recursiveArgs[j]! =
              A.rule.allArgs[A.semantics.recursivePositions[j]!]! ∧
            S.localIndex = i ∧
            S.fields.size = A.rule.allArgs.size ∧
            S.hypotheses.size = A.rule.recursiveArgs.size ∧
            BindingContextLE S.sourceFullContext H.localContext ∧
            Nonempty (RecInfoMinorSemanticSourceAt H.recursorWF S
              H.parameterSuffix.parameterDecls) ∧
            fieldDomains.length = A.rule.allArgs.size ∧
            hypothesisDomains.length = A.rule.recursiveArgs.size ∧
            T.minors[minorIdx]! = VExpr.wrapForalls
              (fieldDomains ++ hypothesisDomains) targetResidual ∧
            let sourceBinders := H.params.fvars ++
              H.bindings.motives.fvars ++
                H.bindings.flatMinors.fvars.take minorIdx
            let position := A.rule.allArgs.size + j
            let declarationDomain :=
              ((D.type.abstractList
                  (S.hypotheses_bound.fvars.take j)).abstractList
                S.fields_bound.fvars j).abstractList
                  sourceBinders position
            Expr.ForallBinderAt
              (S.origin.abstractList sourceBinders) position
              declarationDomain ∧
            TrExprS H.outVEnv Us
              (abstractForallContext
                ((fieldDomains ++ hypothesisDomains).take position)
                (abstractForallContext
                  (T.params ++ T.motives ++ T.minors.take minorIdx) []))
              declarationDomain hypothesisDomains[j]! ∧
            H.outVEnv.IsType Us.length
              (abstractForallContext
                ((fieldDomains ++ hypothesisDomains).take position)
                (abstractForallContext
                  (T.params ++ T.motives ++ T.minors.take minorIdx) [])).toCtx
              hypothesisDomains[j]! ∧
            ∃ originRoot sourceType,
              Nonempty (RecInfoMinorHypothesisTypeOrigin
                hypothesisOrigins.stats hypothesisOrigins.recInfos
                originRoot S.recursiveFields[j]! sourceType) ∧
              D.type = sourceType.consumeTypeAnnotations ∧
              D.type = sourceType := by
  dsimp only
  rcases A.finalSelectedMinorHypothesisDomainAt j hj with
    ⟨T, S, hypothesisOrigins, traversal, fieldDomains, hypothesisDomains,
      targetResidual, sourceDomain, hhypothesisOrigins,
      hhypothesisStats, hhypothesisRecInfos, htraversal, htraversalFields,
      htraversalRecursiveFields, htraversalStats, hparameterTail, hpositions,
      hlocal, hsourceFields, hsourceHypotheses, hsourceContext,
      HminorSemantic,
      hfields, hhypotheses, htarget, Hbinder, Hdomain, HdomainType⟩
  have hjSource : j < S.hypotheses.size := by
    rw [hsourceHypotheses]
    exact hj
  rcases S.hypotheses_bound.declarationAt S.sourceFullWF j hjSource with
    ⟨D⟩
  rcases hypothesisOrigins.entry j hjSource with
    ⟨originRoot, sourceType, HtypeOrigin, Dorigin, htypeOrigin⟩
  have hdeclarationType : D.type = sourceType.consumeTypeAnnotations :=
    (D.type_unique Dorigin).trans htypeOrigin
  rcases HtypeOrigin with ⟨O⟩
  have hdeclarationTypeExact : D.type = sourceType :=
    hdeclarationType.trans O.consumeTypeAnnotations_eq_self
  have hjRecursiveFields : j < S.recursiveFields.size := by
    rw [← S.hypotheses_size, hsourceHypotheses]
    exact hj
  have hjTraversal : j < traversal.recursiveFields.size := by
    rw [htraversalRecursiveFields]
    exact hjRecursiveFields
  have hsourceSelected : S.recursiveFields[j]! =
      S.fields[A.semantics.recursivePositions[j]!]! := by
    have Hselected := traversal.decisions.selected_at j hjTraversal
    rw [htraversalRecursiveFields, htraversalFields, hpositions] at Hselected
    exact Hselected.2
  have hruleSelected : A.rule.recursiveArgs[j]! =
      A.rule.allArgs[A.semantics.recursivePositions[j]!]! :=
    (A.semantics.decisions.selected_at j hj).2
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take
      (recursorMinorOffset indTypes owner + i)
  let position := A.rule.allArgs.size + j
  let declarationDomain :=
    ((D.type.abstractList
        (S.hypotheses_bound.fvars.take j)).abstractList
      S.fields_bound.fvars j).abstractList sourceBinders position
  have HdeclarationBinder :=
    (S.hypothesisBinderAt D).abstractList sourceBinders
  simp only [Nat.zero_add] at HdeclarationBinder
  rw [hsourceFields] at HdeclarationBinder
  have HdeclarationBinder' : Expr.ForallBinderAt
      (S.origin.abstractList sourceBinders) position declarationDomain := by
    exact HdeclarationBinder
  have hsourceDomain : sourceDomain = declarationDomain :=
    Hbinder.unique HdeclarationBinder'
  rw [hsourceDomain] at Hdomain
  exact ⟨T, S, hypothesisOrigins, traversal, fieldDomains,
    hypothesisDomains, targetResidual, D,
    hhypothesisOrigins, hhypothesisStats, hhypothesisRecInfos, htraversal,
    htraversalFields, htraversalRecursiveFields, htraversalStats,
    hparameterTail, hpositions,
    hsourceSelected, hruleSelected,
    hlocal, hsourceFields, hsourceHypotheses, hsourceContext,
    HminorSemantic, hfields, hhypotheses,
    htarget, HdeclarationBinder', Hdomain, HdomainType,
    originRoot, sourceType, ⟨O⟩, hdeclarationType,
    hdeclarationTypeExact⟩

/-- Interpret the exact first-pass recursive-hypothesis declaration in the
completed verified recursor context.  The declaration is first transported
along its retained source-context extension and only then translated; this
keeps the original `loopUArgs` telescope available for comparison with the
second-pass semantic telescope. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorRawHypothesisTypeAt
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
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ S : RecInfoMinorTypeShape,
      ∃ hypothesisOrigins : RecInfoMinorHypothesisTypeOrigins
          S.sourceFullContext S.recursiveFields S.hypotheses,
      ∃ D : BoundFVarDeclarationAt S.sourceFullContext S.hypotheses j,
      ∃ originRoot sourceType,
      ∃ O : RecInfoMinorHypothesisTypeOrigin
          hypothesisOrigins.stats hypothesisOrigins.recInfos
          originRoot S.recursiveFields[j]! sourceType,
      ∃ HS : RecInfoMinorSemanticSourceAt H.recursorWF S
          H.parameterSuffix.parameterDecls,
      ∃ sourceTarget target,
        S.localIndex = i ∧
        S.fields.size = A.rule.allArgs.size ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        BindingContextLE S.sourceFullContext H.localContext ∧
        D.type = sourceType ∧
        TrExprS H.outVEnv Us HS.semantic.sourceWF.mlctx.vlctx
          D.type sourceTarget ∧
        target = sourceTarget.lift'
          (HS.semantic.extension.shift.consN 0) ∧
        TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx D.type target := by
  dsimp only
  rcases A.finalSelectedMinorHypothesisDeclarationDomainAt j hj with
    ⟨_T, S, hypothesisOrigins, _traversal, _fieldDomains,
      _hypothesisDomains, _targetResidual, D,
      _hhypothesisOrigins, _hhypothesisStats, _hhypothesisRecInfos,
      _htraversal, _htraversalFields, _htraversalRecursiveFields,
      _htraversalStats, _hparameterTail, _hpositions,
      _hsourceSelected, _hruleSelected, hlocal, hfields, hhypotheses,
      hsourceContext, HminorSemantic, _hfieldDomains, _hhypothesisDomains, _htarget,
      _Hbinder, _Hdomain, _HdomainType, originRoot, sourceType, ⟨O⟩,
      _hconsumed, htype⟩
  rcases HminorSemantic with ⟨HS⟩
  rcases HS.semantic.sourceWF.translatedDeclarationType D with
    ⟨sourceTarget, HsourceTarget⟩
  have henv : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv, R.declared.contextVEnv]
    exact H.installed.le
  have hsourceEnv : HS.semantic.sourceWF.venv ≤ H.outVEnv := by
    rw [← HS.semantic.extension.venv_eq]
    exact henv
  have HsourceTargetOut := HsourceTarget.mono hsourceEnv
  have Htarget := HS.semantic.extension.weakTrExprS HsourceTarget
  exact ⟨S, hypothesisOrigins, D, originRoot, sourceType, O, HS,
    sourceTarget,
    sourceTarget.lift' (HS.semantic.extension.shift.consN 0),
    hlocal, hfields, hhypotheses, hsourceContext, htype,
    HsourceTargetOut, rfl, Htarget.mono henv⟩

/-- Pointwise strengthening of mask alignment.  At every recursive-result
ordinal, both executable passes selected the field at the same constructor
ordinal.  The expressions themselves may use different fresh identifiers;
the common ordinal is the alpha-independent datum used by the subsequent
hypothesis-domain comparison. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorPositionAlignment
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
    ∃ S : RecInfoMinorTypeShape,
      ∃ traversal : RecInfoMinorTraversalShape,
        S.localIndex = i ∧
        S.traversal = some traversal ∧
        traversal.recursivePositions = A.semantics.recursivePositions ∧
        S.hypotheses.size = A.rule.recursiveArgs.size ∧
        BindingContextLE S.sourceFullContext H.localContext ∧
        ∀ j (hj : j < A.rule.recursiveArgs.size),
          traversal.recursiveFields[j]! =
              traversal.fields[A.semantics.recursivePositions[j]!]! ∧
            A.rule.recursiveArgs[j]! =
              A.rule.allArgs[A.semantics.recursivePositions[j]!]! := by
  rcases A.finalSelectedMinorMaskAlignment with
    ⟨S, traversal, hlocal, htraversal, hpositions, hhypotheses,
      hsourceContext⟩
  have hrecursive : traversal.recursiveFields.size =
      A.rule.recursiveArgs.size :=
    traversal.recursiveFields_size_eq_rule A.semantics hpositions
  refine ⟨S, traversal, hlocal, htraversal, hpositions, hhypotheses,
    hsourceContext, ?_⟩
  intro j hj
  have hjTraversal : j < traversal.recursiveFields.size := by
    rw [hrecursive]
    exact hj
  have Hminor := traversal.decisions.selected_at j hjTraversal
  have Hrule := A.semantics.decisions.selected_at j hj
  rw [hpositions] at Hminor
  exact ⟨Hminor.2, Hrule.2⟩


end VerifyInductive
end Lean4Lean
