import Lean4Lean.Verify.Inductive.CompletedEquationMinorAlignment

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Every first-pass induction hypothesis selected by the aligned mask has a
stable declaration in the completed recursor local context.  In particular,
subsequent proofs may recover its exact production domain rather than merely
the number of hypotheses introduced by `loopU`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorHypothesisDeclarations
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ S : RecInfoMinorTypeShape,
      S.localIndex = i ∧
      S.hypotheses.size = A.rule.recursiveArgs.size ∧
      ∀ j (hj : j < A.rule.recursiveArgs.size),
        Nonempty (BoundFVarDeclarationAt H.localContext S.hypotheses j) := by
  rcases A.finalSelectedMinorMaskAlignment with
    ⟨S, _traversal, hlocal, _htraversal, _hpositions, hhypotheses,
      hsourceContext⟩
  let Hhypotheses := S.hypotheses_bound.mono hsourceContext
  refine ⟨S, hlocal, hhypotheses, ?_⟩
  intro j hj
  have hj' : j < S.hypotheses.size := by
    rw [hhypotheses]
    exact hj
  exact Hhypotheses.declarationAt H.localWF j hj'

/-- The concrete owner-motive declaration mentions no interleaved executable
index or major locals.  Its only possible free variables are the common
parameters and strictly earlier motives, exactly the locals abstracted by the
generated recursor binder. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveSourceScope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let source := H.localContext.lctx.mkForall
      H.recInfos[owner]!.indices
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel))
    source.FVarsIn fun fv =>
      fv ∈ H.params.fvars ++ H.bindings.motives.fvars.take owner := by
  dsimp only
  rcases A.finalOwnerMotiveDomainTranslation with
    ⟨T, _S, _hparameters, Hgenerated, _HgeneratedType⟩
  let source := H.localContext.lctx.mkForall
    H.recInfos[owner]!.indices
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.sort H.elimLevel))
  let binders := H.params.fvars ++ H.bindings.motives.fvars.take owner
  have Habstraction : (source.abstractList binders).FVarsIn
      (fun _ => False) := by
    have Hscope := Hgenerated.fvarsIn
    exact Hscope.mono fun fv hfv => by simpa using hfv
  have Hsource := FVarsIn.of_abstractList Habstraction
  exact Hsource.mono fun fv hfv => by
    rcases hfv with hfv | hfalse
    · exact hfv
    · exact False.elim hfalse

/-- The generated owner-motive domain is itself an exactly sized typed
index/major telescope.  This follows from the retained production local
declarations, not by inspecting the translated target: the source closes the
owner indices and major, and abstraction over the preceding recursor binders
preserves that telescope. -/
theorem
    CompletedRecursorPhasesResult.finalOwnerMotiveTelescopeShapeAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.canonical.params.reverse ∧
        ∃ motiveDomains resultLevel,
          motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
          motiveDomains.length = (T.indices ++ T.major).length ∧
          T.motives[owner]! =
            VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
          resultLevel.WF Us.length := by
  dsimp only
  rcases H.finalOwnerMotiveFrameAt owner howner with
    ⟨T, S, hparameters, D, _hdeclarationOrigin, hdeclarationShape,
      suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      _Hsource, _hsource, hsourceDomain, Hdomain, HdomainType⟩
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner hrecInfo
  have hsortAbstract (fvars : List FVarId) (k : Nat) :
      (Expr.sort H.elimLevel).abstractList fvars k =
        .sort H.elimLevel := by
    exact Expr.abstractList_eq_self_of_abstract1 (.sort H.elimLevel)
      (by intro fv depth; rfl) fvars k
  have HmajorRaw : Expr.ForallTelescope
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel)) 1 (.sort H.elimLevel) := by
    simpa [hsortAbstract] using
      selections.major.forallTelescope (.sort H.elimLevel)
  have Hmajor : Expr.ForallTelescope
      ((H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel)).abstractList selections.indices.fvars)
      1 (.sort H.elimLevel) := by
    have HmajorClosed := HmajorRaw.abstractList selections.indices.fvars 0
    simpa only [hsortAbstract] using HmajorClosed
  have Hindices : Expr.ForallTelescope
      (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
          (.sort H.elimLevel)))
      (H.recInfos[owner]!.indices.size + 1) (.sort H.elimLevel) := by
    exact (selections.indices.forallTelescope
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel))).trans Hmajor
  have HsourceTelescope : Expr.ForallTelescope sourceDomain
      (H.recInfos[owner]!.indices.size + 1) (.sort H.elimLevel) := by
    rw [hsourceDomain, hdeclarationShape]
    have Habstract := Hindices.abstractList
      (H.params.fvars ++ H.bindings.motives.fvars.take owner) 0
    simpa only [hsortAbstract] using Habstract
  have Htyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    HsourceTelescope Hdomain HdomainType
  rcases Htyped.toWrapForalls with
    ⟨motiveDomains, sourceResidual, motiveResult, hlength,
      _HsourceResidual, htarget, Hresult, _HresultType⟩
  have hsourceResidual : sourceResidual = .sort H.elimLevel :=
    _HsourceResidual.residual_eq HsourceTelescope
  subst sourceResidual
  cases Hresult with
  | sort hlevel =>
    have hsuffixLength : motiveDomains.length =
        (T.indices ++ T.major).length := by
      simp only [List.length_append, T.indices_length, T.major_length,
        hlength]
    exact ⟨T, S, hparameters, motiveDomains, _, hlength, hsuffixLength,
      htarget, VLevel.WF.of_ofLevel hlevel⟩

/-- Arbitrary-witness form of `finalOwnerMotiveTelescopeShape`.  Structural
uniqueness transports the semantic shape to the exact `T` already selected
by an equation frame. -/
theorem
    CompletedRecursorPhasesResult.finalOwnerMotiveTelescopeShapeForAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
        H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse S.canonical.params.reverse ∧
      ∃ motiveDomains resultLevel,
        motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
        motiveDomains.length = (T.indices ++ T.major).length ∧
        T.motives[owner]! =
          VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
        resultLevel.WF Us.length := by
  dsimp only
  rcases H.finalOwnerMotiveTelescopeShapeAt owner howner with
    ⟨T₀, S, hparameters, motiveDomains, resultLevel,
      hdomainLength, hsuffixLength, hmotive, hresultLevel⟩
  rcases T₀.groupsResult_eq T with
    ⟨hparams, hmotives, _hminors, hindices, hmajor, _hresult⟩
  rw [hparams] at hparameters
  rw [hmotives] at hmotive
  rw [hindices, hmajor] at hsuffixLength
  exact ⟨S, hparameters, motiveDomains, resultLevel,
    hdomainLength, hsuffixLength, hmotive, hresultLevel⟩

/-- Single-witness frame for the final dependent-suffix comparison.  The
owner motive's forall shape, the literal canonical application residual, and
the residual's typehood all refer to the same retained generated telescope.
This is the complete premise needed to invert the application spine and
align the generated index/major context with the motive domains. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveApplicationFrame
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.canonical.params.reverse ∧
        ∃ motiveDomains resultLevel,
          motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
          motiveDomains.length = (T.indices ++ T.major).length ∧
          T.motives[owner]! =
            VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
          resultLevel.WF Us.length ∧
          (let domains :=
              T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major;
            OnCtx domains.reverse (H.outVEnv.IsType Us.length) ∧
              H.outVEnv.IsType Us.length domains.reverse T.result) ∧
          (let domains :=
              T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major;
            let offset :=
              1 + H.recInfos[owner]!.indices.size +
                (H.recInfos.flatMap (·.minors)).size +
                ((H.recInfos.map (·.motive)).size - 1 - owner);
            H.outVEnv.HasType Us.length domains.reverse (.bvar offset)
              (T.motives[owner]!.liftN (offset + 1) 0)) ∧
          T.result = VExpr.mkApps
            (.bvar
              (1 + H.recInfos[owner]!.indices.size +
                (H.recInfos.flatMap (·.minors)).size +
                ((H.recInfos.map (·.motive)).size - 1 - owner)))
            (((List.range H.recInfos[owner]!.indices.size).reverse.map
                fun index => .bvar (index + 1)) ++ [.bvar 0]) := by
  dsimp only
  rcases H.finalOwnerMotiveTelescopeShapeAt owner howner with
    ⟨T, S, hparameters, motiveDomains, resultLevel,
      hdomainLength, hsuffixLength, hmotive, hresultLevel⟩
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  exact ⟨T, S, hparameters, motiveDomains, resultLevel,
    hdomainLength, hsuffixLength, hmotive, hresultLevel,
    T.fullContextResultType H.outVEnvWF.ordered,
    T.ownerMotiveBvarTypingAtOffset hownerMotive,
    T.resultShape hownerMotive⟩

/-- End-to-end first-binder consequence of the owner-motive application
frame.  This is the induction base for aligning the complete dependent
index/major suffix: the first generated suffix declaration is convertible to
the first motive domain after weakening across later motives and minors. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveFirstDomainAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.canonical.params.reverse ∧
        ∃ motiveDomains resultLevel generatedFirst generatedRest
            motiveFirst motiveRest,
          motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
          T.motives[owner]! =
            VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
          T.indices ++ T.major = generatedFirst :: generatedRest ∧
          motiveDomains = motiveFirst :: motiveRest ∧
          H.outVEnv.IsDefEqU Us.length
            (T.params ++ T.motives ++ T.minors).reverse generatedFirst
            (motiveFirst.liftN
              ((T.motives.drop (owner + 1) ++ T.minors).length + 1) 0) := by
  dsimp only
  rcases H.finalOwnerMotiveTelescopeShapeAt owner howner with
    ⟨T, S, hparameters, motiveDomains, resultLevel,
      hdomainLength, _hsuffixLength, hmotive, _hresultLevel⟩
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  rcases T.ownerMotiveFirstDomainDefEq H.outVEnvWF hownerMotive
      motiveDomains resultLevel hmotive hdomainLength with
    ⟨generatedFirst, generatedRest, motiveFirst, motiveRest,
      hsuffix, hmotiveDomains, Hdomain⟩
  exact ⟨T, S, hparameters, motiveDomains, resultLevel,
    generatedFirst, generatedRest, motiveFirst, motiveRest,
    hdomainLength, hmotive, hsuffix, hmotiveDomains, Hdomain⟩

/-- Final all-binder owner-suffix alignment.  This is the completed bridge
from the five-group executable recursor telescope to the independently
shaped owner motive: every generated index and the retained major declaration
is related in one dependent context conversion. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveSuffixContextAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.canonical.params.reverse ∧
        ∃ motiveDomains resultLevel,
          motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
          T.motives[owner]! =
            VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
          let outer := T.params ++ T.motives ++ T.minors
          let suffix := T.indices ++ T.major
          let later := T.motives.drop (owner + 1) ++ T.minors
          let expected :=
            (liftContextPrefixAt (later.length + 1) 0
              motiveDomains.reverse).reverse
          VEnv.IsDefEqCtx H.outVEnv Us.length []
            (suffix.reverse ++ outer.reverse)
            (expected.reverse ++ outer.reverse) := by
  dsimp only
  rcases H.finalOwnerMotiveTelescopeShapeAt owner howner with
    ⟨T, S, hparameters, motiveDomains, resultLevel,
      hdomainLength, _hsuffixLength, hmotive, _hresultLevel⟩
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have Hsuffix := T.ownerMotiveSuffixContext H.outVEnvWF hownerMotive
    motiveDomains resultLevel hmotive hdomainLength
  exact ⟨T, S, hparameters, motiveDomains, resultLevel,
    hdomainLength, hmotive, Hsuffix⟩

/-- Arbitrary-witness specialization of the complete suffix alignment, for
direct use with the telescope retained by the canonical equation frame. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveSuffixContextAlignmentFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
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
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
        H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse S.canonical.params.reverse ∧
      ∃ motiveDomains resultLevel,
        motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
        T.motives[owner]! =
          VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
        let outer := T.params ++ T.motives ++ T.minors
        let suffix := T.indices ++ T.major
        let later := T.motives.drop (owner + 1) ++ T.minors
        let expected :=
          (liftContextPrefixAt (later.length + 1) 0
            motiveDomains.reverse).reverse
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (suffix.reverse ++ outer.reverse)
          (expected.reverse ++ outer.reverse) := by
  dsimp only
  rcases H.finalOwnerMotiveTelescopeShapeForAt owner howner T with
    ⟨S, hparameters, motiveDomains, resultLevel,
      hdomainLength, _hsuffixLength, hmotive, _hresultLevel⟩
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hownerRecInfo
  have Hsuffix := T.ownerMotiveSuffixContext H.outVEnvWF hownerMotive
    motiveDomains resultLevel hmotive hdomainLength
  exact ⟨S, hparameters, motiveDomains, resultLevel,
    hdomainLength, hmotive, Hsuffix⟩

/-- Insert an exact constructor-field telescope beneath both sides of the
owner index/major alignment.  This is the context conversion needed by the
equation LHS: the generated recursor suffix and the independent motive
domains are weakened through precisely the same locally bound fields. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveSuffixAlignmentUnderFields
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
        H.recInfos[owner]! H.elimLevel,
      VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse S.canonical.params.reverse ∧
      ∃ motiveDomains resultLevel,
        motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
        T.motives[owner]! =
          VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
        let outer := T.params ++ T.motives ++ T.minors
        let suffix := T.indices ++ T.major
        let later := T.motives.drop (owner + 1) ++ T.minors
        let expected :=
          (liftContextPrefixAt (later.length + 1) 0
            motiveDomains.reverse).reverse
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (liftContextPrefix fieldDomains.length suffix.reverse ++
            fieldDomains.reverse ++ outer.reverse)
          (liftContextPrefix fieldDomains.length expected.reverse ++
            fieldDomains.reverse ++ outer.reverse) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalOwnerMotiveSuffixContextAlignmentFor T with
    ⟨S, hparameters, motiveDomains, resultLevel,
      hdomainLength, hmotive, Hsuffix⟩
  let outer := T.params ++ T.motives ++ T.minors
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  have hsuffixLength : suffix.reverse.length = expected.reverse.length := by
    have htotal := Hsuffix.length_eq
    simp [outer, suffix, later, expected] at htotal ⊢
    omega
  have hfieldCtx : OnCtx (fieldDomains.reverse ++ outer.reverse)
      (H.outVEnv.IsType Us.length) := by
    simpa [outer, List.reverse_append, List.append_assoc] using hctx
  have Haligned := VEnv.IsDefEqCtx.insertSameMiddle
    H.outVEnvWF.ordered suffix.reverse expected.reverse
      fieldDomains.reverse outer.reverse Hsuffix hsuffixLength hfieldCtx
  have Haligned' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (liftContextPrefix fieldDomains.length suffix.reverse ++
        fieldDomains.reverse ++ outer.reverse)
      (liftContextPrefix fieldDomains.length expected.reverse ++
        fieldDomains.reverse ++ outer.reverse) := by
    simpa [List.length_reverse] using Haligned
  exact ⟨S, hparameters, motiveDomains, resultLevel,
    hdomainLength, hmotive, Haligned'⟩

/-- Consume the field-lifted suffix conversion in a typing derivation.  The
canonical recursor prefix is opened through all generated index/major
binders, then transported to the corresponding independently shaped motive
context.  The term and residual result type are unchanged by that context
transport. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveOpenedSuffixTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (prefixTarget : VExpr)
    (hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hprefix : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      prefixTarget
      ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
        fieldDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
      T.motives[owner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let outer := T.params ++ T.motives ++ T.minors
      let suffix := T.indices ++ T.major
      let later := T.motives.drop (owner + 1) ++ T.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      H.outVEnv.HasType Us.length
        (liftContextPrefix fieldDomains.length expected.reverse ++
          fieldDomains.reverse ++ outer.reverse)
        (VExpr.mkApps (prefixTarget.liftN suffix.length 0)
          (recursorCanonicalVars suffix.length))
        (T.result.liftN fieldDomains.length suffix.length) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalOwnerMotiveSuffixAlignmentUnderFields T fieldDomains hctx with
    ⟨_S, _hparameters, motiveDomains, resultLevel,
      hdomainLength, hmotive, Haligned⟩
  let outer := T.params ++ T.motives ++ T.minors
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  have Hprefix' := Hprefix
  rw [VExpr.liftN_wrapForalls] at Hprefix'
  have Hopened := VEnv.HasType.mkApps_wrapForalls_canonical
    H.outVEnvWF.ordered Hprefix'
  have Hopened' : H.outVEnv.HasType Us.length
      (liftContextPrefix fieldDomains.length suffix.reverse ++
        fieldDomains.reverse ++ outer.reverse)
      (VExpr.mkApps (prefixTarget.liftN suffix.length 0)
        (recursorCanonicalVars suffix.length))
      (T.result.liftN fieldDomains.length suffix.length) := by
    simpa [outer, suffix, liftContextPrefix, recursorCanonicalVars,
      List.reverse_append,
      List.append_assoc, Nat.add_comm] using Hopened
  have Htransported := Hopened'.defeqDFC H.outVEnvWF.ordered Haligned
  exact ⟨motiveDomains, resultLevel, hdomainLength, hmotive,
    Htransported⟩

/-- Re-close the field-lifted suffix conversion as equality of function
types in the canonical equation context.  The common residual is the
generated owner-motive application `T.result`; only the dependent domains
differ, and `closeWrapForalls` discharges exactly that distinction. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveSuffixTypeAlignment
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (prefixTarget : VExpr)
    (hctx : OnCtx
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (Hprefix : H.outVEnv.HasType
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (((T.params ++ T.motives ++ T.minors) ++ fieldDomains).reverse)
      prefixTarget
      ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
        fieldDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
      T.motives[owner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let outer := T.params ++ T.motives ++ T.minors
      let suffix := T.indices ++ T.major
      let later := T.motives.drop (owner + 1) ++ T.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      H.outVEnv.IsDefEqU Us.length
        (fieldDomains.reverse ++ outer.reverse)
        ((VExpr.wrapForalls suffix T.result).liftN
          fieldDomains.length 0)
        (VExpr.wrapForalls
          ((liftContextPrefix fieldDomains.length expected.reverse).reverse)
          (T.result.liftN fieldDomains.length suffix.length)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalOwnerMotiveSuffixAlignmentUnderFields T fieldDomains hctx with
    ⟨_S, _hparameters, motiveDomains, resultLevel,
      hdomainLength, hmotive, Haligned⟩
  let outer := T.params ++ T.motives ++ T.minors
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let actualRecent := liftContextPrefix fieldDomains.length suffix.reverse
  let expectedRecent :=
    liftContextPrefix fieldDomains.length expected.reverse
  let base := fieldDomains.reverse ++ outer.reverse
  have Haligned' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      (actualRecent ++ base) (expectedRecent ++ base) := by
    simpa [Us, actualRecent, expectedRecent, base, outer, suffix, later,
      expected] using Haligned
  have HprefixType := Hprefix.isType H.outVEnvWF hctx
  rw [VExpr.liftN_wrapForalls] at HprefixType
  have Hopened := VEnv.IsType.wrapForalls_inv H.outVEnvWF.ordered
    (ctx := base) (domains := actualRecent.reverse)
    (result := T.result.liftN fieldDomains.length suffix.length)
    (by simpa [base, outer] using hctx) (by
      simpa [actualRecent, suffix, base, outer, liftContextPrefix,
        Nat.add_comm] using
        HprefixType)
  rcases Hopened.2 with ⟨bodyLevel, Hbody⟩
  have Hbody' : H.outVEnv.HasType Us.length
      (liftContextPrefix fieldDomains.length suffix.reverse ++
        fieldDomains.reverse ++ outer.reverse)
      (T.result.liftN fieldDomains.length suffix.length)
      (.sort bodyLevel) := by
    simpa [actualRecent, base] using Hbody
  have Hbody'' : H.outVEnv.HasType Us.length (actualRecent ++ base)
      (T.result.liftN fieldDomains.length suffix.length)
      (.sort bodyLevel) := by
    simpa [actualRecent, base, outer, suffix] using Hbody'
  have hrecentLength : expectedRecent.length = actualRecent.length := by
    have hlength := Haligned'.length_eq
    simp only [List.length_append] at hlength
    omega
  have Hclosed := VEnv.IsDefEqCtx.closeHeads Haligned'
    actualRecent.length (by simp [actualRecent, suffix]) Hbody''
  rcases Hclosed with ⟨closedLevel, Hclosed⟩
  have Hclosed' : H.outVEnv.IsDefEq Us.length base
      (VExpr.wrapForalls actualRecent.reverse
        (T.result.liftN fieldDomains.length suffix.length))
      (VExpr.wrapForalls expectedRecent.reverse
        (T.result.liftN fieldDomains.length suffix.length))
      (.sort closedLevel) := by
    have hrightTake : (expectedRecent ++ base).take actualRecent.length =
        expectedRecent := by
      rw [← hrecentLength]
      simp
    rw [List.drop_left, List.take_left, hrightTake] at Hclosed
    exact Hclosed
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive, ?_⟩
  refine ⟨.sort closedLevel, ?_⟩
  change H.outVEnv.IsDefEq Us.length base
    ((VExpr.wrapForalls suffix T.result).liftN fieldDomains.length 0)
    (VExpr.wrapForalls expectedRecent.reverse
      (T.result.liftN fieldDomains.length suffix.length))
    (.sort closedLevel)
  rw [VExpr.liftN_wrapForalls]
  simpa [actualRecent, base, outer, suffix,
    liftContextPrefix, Nat.add_comm] using Hclosed'

/-- The owner-motive local itself is the comparison function for concrete
suffix application.  After weakening beneath constructor fields, its type
has exactly the independent domains appearing on the right side of
`finalOwnerMotiveSuffixTypeAlignment`, but ends in the elimination sort
rather than the generated recursor result. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveFieldWitnessTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
      T.motives[owner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let outer := T.params ++ T.motives ++ T.minors
      let later := T.motives.drop (owner + 1) ++ T.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      H.outVEnv.HasType Us.length
        (fieldDomains.reverse ++ outer.reverse)
        (.bvar (fieldDomains.length + later.length))
        (VExpr.wrapForalls
          ((liftContextPrefix fieldDomains.length expected.reverse).reverse)
          (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases H.finalOwnerMotiveTelescopeShapeForAt owner howner T with
    ⟨_S, _hparameters, motiveDomains, resultLevel,
      hdomainLength, _hsuffixLength, hmotive, _hresultLevel⟩
  have hownerRecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hownerMotive : owner < T.motives.length := by
    rw [T.motives_length]
    simpa using hownerRecInfo
  let outer := T.params ++ T.motives ++ T.minors
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  have Hmotive := T.ownerMotiveOuterBvarTyping hownerMotive
  have W : Ctx.LiftN fieldDomains.length 0 outer.reverse
      (fieldDomains.reverse ++ outer.reverse) := by
    exact .zero fieldDomains.reverse (by simp)
  have Hweak := Hmotive.weakN H.outVEnvWF.ordered W
  rw [show T.motives[owner]'hownerMotive = T.motives[owner]! by
    exact (getElem!_pos T.motives owner hownerMotive).symm,
    hmotive] at Hweak
  exact ⟨motiveDomains, resultLevel, hdomainLength, hmotive, by
    simpa [outer, later, expected, VExpr.liftN_wrapForalls,
      liftContextPrefix, VExpr.liftN_liftN, VExpr.liftN, liftVar_base,
      Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using Hweak⟩

/-- Transport the field-weakened owner-motive witness from the generated
parameter domains to the cached constructor-checking parameter context.  The
owner variable and its complete dependent function type are unchanged; only
the outer parameter domains are converted. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCachedOwnerMotiveWitnessTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr)
    (Hctx :
      let parameterDecls :=
        (R.materializedFinal.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      let canonicalDomains :=
        (T.params ++ T.motives ++ T.minors) ++ fieldDomains
      let cachedDomains :=
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        canonicalDomains.reverse cachedDomains.reverse) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    let cachedDomains :=
      (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
        fieldDomains
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
      T.motives[owner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let later := T.motives.drop (owner + 1) ++ T.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      H.outVEnv.HasType Us.length cachedDomains.reverse
        (.bvar (fieldDomains.length + later.length))
        (VExpr.wrapForalls
          ((liftContextPrefix fieldDomains.length expected.reverse).reverse)
          (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  let canonicalDomains :=
    (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  let cachedDomains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains
  rcases A.finalOwnerMotiveFieldWitnessTyping T fieldDomains with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive, Hmotive⟩
  have HmotiveCanonical : H.outVEnv.HasType Us.length
      canonicalDomains.reverse
      (.bvar
        (fieldDomains.length +
          (T.motives.drop (owner + 1) ++ T.minors).length))
      (VExpr.wrapForalls
        ((liftContextPrefix fieldDomains.length
          ((liftContextPrefixAt
            ((T.motives.drop (owner + 1) ++ T.minors).length + 1) 0
            motiveDomains.reverse).reverse).reverse).reverse)
        (.sort resultLevel)) := by
    simpa [canonicalDomains, List.reverse_append, List.append_assoc] using
      Hmotive
  have HmotiveCached :=
    HmotiveCanonical.defeqDFC H.outVEnvWF.ordered Hctx
  exact ⟨motiveDomains, resultLevel, hdomainLength, hmotive, by
    simpa [cachedDomains] using HmotiveCached⟩

/-- In the cached equation context, the recursor prefix and the owner motive
are typed by forall telescopes with literally the same dependent domains.
Their residuals deliberately differ: the prefix returns the generated
recursor result, while the motive application returns an elimination sort.
This is the exact interface consumed by `mkApps_sameTelescopeDomains`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCachedPrefixOwnerTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner)
    (fieldDomains : List VExpr) (prefixTarget : VExpr)
    (Hfull :
      let parameterDecls :=
        (R.materializedFinal.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      let canonicalDomains :=
        (T.params ++ T.motives ++ T.minors) ++ fieldDomains
      let cachedDomains :=
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains
      VEnv.IsDefEqCtx H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        canonicalDomains.reverse cachedDomains.reverse)
    (HcachedCtx :
      let parameterDecls :=
        (R.materializedFinal.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      let cachedDomains :=
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains
      OnCtx cachedDomains.reverse
        (H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length))
    (HprefixCached :
      let parameterDecls :=
        (R.materializedFinal.parameterSuffix.toRecursorContext
          H.elimLevelAdmissible).parameterDecls
      let cachedDomains :=
        (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
          fieldDomains
      H.outVEnv.HasType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        cachedDomains.reverse prefixTarget
        ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
          fieldDomains.length 0)) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    let parameterDecls :=
      (R.materializedFinal.parameterSuffix.toRecursorContext
        H.elimLevelAdmissible).parameterDecls
    let cachedDomains :=
      (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
        fieldDomains
    ∃ motiveDomains resultLevel,
      motiveDomains.length = H.recInfos[owner]!.indices.size + 1 ∧
      T.motives[owner]! =
        VExpr.wrapForalls motiveDomains (.sort resultLevel) ∧
      let suffix := T.indices ++ T.major
      let later := T.motives.drop (owner + 1) ++ T.minors
      let expected :=
        (liftContextPrefixAt (later.length + 1) 0
          motiveDomains.reverse).reverse
      let expectedDomains :=
        (liftContextPrefix fieldDomains.length expected.reverse).reverse
      H.outVEnv.HasType Us.length cachedDomains.reverse prefixTarget
          (VExpr.wrapForalls expectedDomains
            (T.result.liftN fieldDomains.length suffix.length)) ∧
        H.outVEnv.HasType Us.length cachedDomains.reverse
          (.bvar (fieldDomains.length + later.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) ∧
        SameTelescopeDomains expectedDomains.length
          (VExpr.wrapForalls expectedDomains
            (T.result.liftN fieldDomains.length suffix.length))
          (VExpr.wrapForalls expectedDomains (.sort resultLevel)) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let parameterDecls :=
    (R.materializedFinal.parameterSuffix.toRecursorContext
      H.elimLevelAdmissible).parameterDecls
  let canonicalDomains :=
    (T.params ++ T.motives ++ T.minors) ++ fieldDomains
  let cachedDomains :=
    (parameterDecls.toCtx.reverse ++ T.motives ++ T.minors) ++
      fieldDomains
  have HcanonicalCtx : OnCtx canonicalDomains.reverse
      (H.outVEnv.IsType Us.length) :=
    Hfull.isType
  have HprefixCanonical : H.outVEnv.HasType Us.length
      canonicalDomains.reverse prefixTarget
      ((VExpr.wrapForalls (T.indices ++ T.major) T.result).liftN
        fieldDomains.length 0) :=
    HprefixCached.defeqDFC H.outVEnvWF.ordered
      (Hfull.symm H.outVEnvWF.ordered)
  rcases A.finalOwnerMotiveSuffixTypeAlignment T fieldDomains prefixTarget
      (by simpa [canonicalDomains] using HcanonicalCtx)
      (by simpa [canonicalDomains] using HprefixCanonical) with
    ⟨alignedDomains, alignedLevel, halignedLength, halignedMotive,
      Haligned⟩
  rcases A.finalCachedOwnerMotiveWitnessTyping T fieldDomains Hfull with
    ⟨motiveDomains, resultLevel, hdomainLength, hmotive, Hmotive⟩
  have hdomains : motiveDomains = alignedDomains := by
    apply VExpr.wrapForalls_prefix_domains_eq hdomainLength halignedLength
      (suffix := [])
    simpa using hmotive.symm.trans halignedMotive
  subst alignedDomains
  have hresultLevel : resultLevel = alignedLevel := by
    have hsort : VExpr.sort resultLevel = VExpr.sort alignedLevel := by
      apply VExpr.wrapForalls_left_cancel motiveDomains
      exact hmotive.symm.trans halignedMotive
    exact VExpr.sort.inj hsort
  subst alignedLevel
  let suffix := T.indices ++ T.major
  let later := T.motives.drop (owner + 1) ++ T.minors
  let expected :=
    (liftContextPrefixAt (later.length + 1) 0
      motiveDomains.reverse).reverse
  let expectedDomains :=
    (liftContextPrefix fieldDomains.length expected.reverse).reverse
  have HalignedCanonical : H.outVEnv.IsDefEqU Us.length
      canonicalDomains.reverse
      ((VExpr.wrapForalls suffix T.result).liftN fieldDomains.length 0)
      (VExpr.wrapForalls expectedDomains
        (T.result.liftN fieldDomains.length suffix.length)) := by
    simpa [canonicalDomains, suffix, later, expected, expectedDomains,
      List.reverse_append] using Haligned
  have HalignedCached :=
    HalignedCanonical.defeqDFC H.outVEnvWF.ordered Hfull
  have HprefixExpected : H.outVEnv.HasType Us.length cachedDomains.reverse
      prefixTarget
      (VExpr.wrapForalls expectedDomains
        (T.result.liftN fieldDomains.length suffix.length)) := by
    exact HprefixCached.defeqU_r H.outVEnvWF HcachedCtx HalignedCached
  refine ⟨motiveDomains, resultLevel, hdomainLength, hmotive,
    HprefixExpected, ?_, ?_⟩
  · simpa [cachedDomains, suffix, later, expected, expectedDomains] using
      Hmotive
  · exact SameTelescopeDomains.wrapForalls expectedDomains _ _

/-- The generated owner-motive domain and the retained first-pass motive are
the same concrete declaration viewed at the two contexts that still have to
be related.  The retained closed scope is now decomposed explicitly into its
interleaved executable ambient prefix and the very parameter scope aligned
with the generated telescope.  No index, major, or current-motive weakening
remains hidden in this frame. -/
theorem
    CompletedRecursorPhasesResult.finalOwnerClosedMotiveFrameAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.motiveParameterScope.toCtx ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.motiveSourceScope.toCtx ∧
        VLCtx.FVLift' S.motiveSourceScope S.motiveSourceExpanded
            0 S.motiveSourceShift 0 ∧
        VLCtx.IsDefEq H.outVEnv Us.length S.motiveSourceExpanded
            S.motiveClosedScope ∧
        S.motiveClosedScope =
            S.motiveClosedAmbient ++ S.motiveParameterScope ∧
        TrExprS H.outVEnv Us S.motiveClosedScope
          (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
              (.sort H.elimLevel)))
          S.motiveClosedTarget ∧
        H.outVEnv.IsType Us.length S.motiveClosedScope.toCtx
          S.motiveClosedTarget ∧
        H.outVEnv.IsDefEqU Us.length S.motiveClosedScope.toCtx
          S.motiveClosedTarget S.motiveClosedCanonicalTarget ∧
        S.motiveType = S.motiveReopenedCanonicalTarget ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives.take owner) [])
          ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
              (.sort H.elimLevel))).abstractList
                (H.params.fvars ++ H.bindings.motives.fvars.take owner))
          T.motives[owner]! := by
  dsimp only
  rcases H.finalOwnerMotiveDomainTranslationAt owner howner with
    ⟨T, S, hparameters, Hgenerated, _HgeneratedType⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact VEnv.addProjections_le.trans H.installed.le
  have hparameterScope := S.motiveParameterAlignment.mono hbase
  have hparameters' :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
      hparameters hparameterScope
  have hsourceScope := S.motiveSourceAlignment.mono hbase
  have hsource :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
      hparameters hsourceScope
  exact ⟨T, S, hparameters', hsource, S.motiveSourceLift,
    S.motiveSourceContext.mono hbase, S.motiveClosedContext,
    S.motiveClosedTr.mono hbase, S.motiveClosedType.mono hbase,
    S.motiveClosedCanonicalDefEq.mono hbase, S.motiveTypeCanonicalEq,
    Hgenerated⟩

/-- Restrict the retained production motive translation all the way back to
the canonical parameter scope.  This is the first point where the ambient
frames from earlier mutual families are genuinely removed, rather than only
described by a context decomposition. -/
theorem
    CompletedRecursorPhasesResult.finalOwnerNarrowMotiveTranslationAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        ∃ narrowTarget,
          VEnv.IsDefEqCtx H.outVEnv Us.length []
              T.params.reverse S.motiveSourceScope.toCtx ∧
          TrExprS H.outVEnv Us S.motiveSourceScope
            (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
              (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
                (.sort H.elimLevel)))
            narrowTarget ∧
          H.outVEnv.IsDefEqU Us.length S.motiveSourceScope.toCtx
            narrowTarget S.canonical.motiveType ∧
          TrExprS H.outVEnv Us
            (abstractForallContext
              (T.params ++ T.motives.take owner) [])
            ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
              (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
                (.sort H.elimLevel))).abstractList
                  (H.params.fvars ++ H.bindings.motives.fvars.take owner))
            T.motives[owner]! := by
  dsimp only
  rcases H.finalOwnerClosedMotiveFrameAt owner howner with
    ⟨T, S, _hparameters, hsource, W, Hcontext, _hdecomposition,
      HclosedTr, _HclosedType, HclosedCanonical, _hmotiveType,
      Hgenerated⟩
  have hbvars : VLCtx.bvars S.motiveClosedScope = 0 := by
    calc
      VLCtx.bvars S.motiveClosedScope =
          VLCtx.bvars S.motiveSourceExpanded := Hcontext.bvars.symm
      _ = VLCtx.bvars S.motiveSourceScope := W.bvars_eq
      _ = 0 := S.motiveSourceNoBV
  have hclosed := HclosedTr.closed
  rw [hbvars] at hclosed
  rcases HclosedTr.weakFV'_inv H.outVEnvWF W
      (Hcontext.symm H.outVEnvWF.ordered) hclosed
      S.motiveSourceFVars with ⟨narrowTarget, Hnarrow⟩
  have HnarrowWeak : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      S.motiveSourceExpanded
      (H.localContext.lctx.mkForall H.recInfos[owner]!.indices
        (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
          (.sort H.elimLevel)))
      (narrowTarget.lift' S.motiveSourceShift) := by
    exact Hnarrow.weakFV' H.outVEnvWF.ordered W Hcontext.wf
  have HweakTarget := HnarrowWeak.uniq H.outVEnvWF Hcontext HclosedTr
  have HcanonicalExpanded := HclosedCanonical.defeqDFC
    H.outVEnvWF.ordered
    (Hcontext.defeqCtx.symm H.outVEnvWF.ordered)
  have HweakCanonical := HweakTarget.trans H.outVEnvWF
    Hcontext.wf.toCtx HcanonicalExpanded
  rw [← S.motiveClosedCanonicalEq] at HweakCanonical
  have Hcanonical :=
    (VEnv.IsDefEqU.weak'_iff H.outVEnvWF Hcontext.wf.toCtx W.toCtx).1
      HweakCanonical
  exact ⟨T, S, narrowTarget, hsource, Hnarrow, Hcanonical, Hgenerated⟩

/-- Abstract the exact cached parameter suffix of the narrowed production
motive, then transport it to the generated parameter telescope.  Earlier
mutual motives are absent from the concrete source, so adding their abstract
binders is precisely ordinary bound-variable weakening. -/
theorem
    CompletedRecursorPhasesResult.finalOwnerCanonicalMotiveDomainAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ S : RecursorMotiveTelescopeSeed H.recursorWF stats decl owner
          H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
            T.params.reverse S.motiveSourceScope.toCtx ∧
        H.outVEnv.IsDefEqU Us.length
          (abstractForallContext
            (T.params ++ T.motives.take owner) []).toCtx
          T.motives[owner]!
          (S.canonical.motiveType.liftN
            (T.motives.take owner).length 0) := by
  dsimp only
  rcases H.finalOwnerNarrowMotiveTranslationAt owner howner with
    ⟨T, S, narrowTarget, hparams, Hnarrow, Hcanonical, Hgenerated⟩
  let source := H.localContext.lctx.mkForall H.recInfos[owner]!.indices
    (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.sort H.elimLevel))
  have HnarrowParameters : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      S.motiveParameterScope source narrowTarget := by
    simpa [source, S.motiveSourceParameterScope] using Hnarrow
  rcases cachedParameterDecls_fvars S.motiveParameterDecls with
    ⟨parameterFVars, hparameterExprs, hparameterScopeFVars⟩
  have hstatsParams : stats.params.toList.reverse =
      H.params.fvars.reverse.map Expr.fvar := by
    have h := congrArg Array.toList H.params.expressions
    simpa [List.map_reverse] using congrArg List.reverse h
  have hparameterFVars : parameterFVars = H.params.fvars.reverse := by
    apply (List.map_inj_right (fun _ _ h => Expr.fvar.inj h)).mp
    exact hparameterExprs.symm.trans hstatsParams
  have Hdecls : List.Forall₂
      (fun fv entry => ∃ deps type,
        entry = (some (fv, deps), .vlam type))
      H.params.fvars.reverse S.motiveParameterScope := by
    have Hcached := S.motiveParameterDecls
    rw [hparameterExprs] at Hcached
    rw [List.forall₂_map_left_iff] at Hcached
    have Hdecls' : List.Forall₂
        (fun fv entry => ∃ deps type,
          entry = (some (fv, deps), .vlam type))
        parameterFVars S.motiveParameterScope :=
      Lean4Lean.List.Forall₂.imp
      (fun fv entry hentry => by
        rcases hentry with ⟨actual, deps, type, hparam, hentry⟩
        cases Expr.fvar.inj hparam
        exact ⟨deps, type, hentry⟩) Hcached
    simpa [hparameterFVars] using Hdecls'
  have houterNodup := H.bindings.outerNodup H.params H.noAlias
  have hparamsMotivesNodup :
      (H.params.fvars ++ H.bindings.motives.fvars).Nodup :=
    (List.nodup_append.mp houterNodup).1
  have hparamsNodup : H.params.fvars.reverse.Nodup :=
    List.nodup_reverse.mpr
      (List.nodup_append.mp hparamsMotivesNodup).1
  have HparameterAbstract :=
    Lean4Lean.VerifyInductive.TrExprS.abstractFVarLambdaSuffix
      (domains := []) Hdecls hparamsNodup (by
        simpa [abstractForallContext] using HnarrowParameters)
  simp only [List.reverse_reverse] at HparameterAbstract
  have HparameterAbstract' : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext S.motiveParameterScope.toCtx.reverse [])
      (source.abstractList H.params.fvars) narrowTarget := by
    simpa using HparameterAbstract
  have HparameterContext : VLCtx.IsDefEq H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext T.params [])
      (abstractForallContext
        S.motiveParameterScope.toCtx.reverse []) := by
    have hparams' := hparams
    rw [S.motiveSourceParameterScope] at hparams'
    exact abstractForallContext.isDefEq (by simpa using hparams')
  rcases HparameterAbstract'.defeqDFC H.outVEnvWF
      (HparameterContext.symm H.outVEnvWF.ordered) with
    ⟨parameterTarget, HparameterTarget⟩
  have HparameterTargets := HparameterAbstract'.uniq H.outVEnvWF
    (HparameterContext.symm H.outVEnvWF.ordered) HparameterTarget
  have HcanonicalParameters : H.outVEnv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        S.motiveParameterScope.toCtx.reverse []).toCtx
      narrowTarget S.canonical.motiveType := by
    have hctx :
        (abstractForallContext
          S.motiveParameterScope.toCtx.reverse []).toCtx =
          S.motiveParameterScope.toCtx := by
      simp [abstractForallContext]
    rw [hctx, ← S.motiveSourceParameterScope]
    exact Hcanonical
  have HparameterCanonicalAtSource : H.outVEnv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        S.motiveParameterScope.toCtx.reverse []).toCtx
      parameterTarget S.canonical.motiveType :=
    HparameterTargets.symm.trans H.outVEnvWF
      (HparameterContext.symm H.outVEnvWF.ordered).wf.toCtx
      HcanonicalParameters
  have HparameterCanonical := HparameterCanonicalAtSource.defeqDFC
    H.outVEnvWF.ordered
    (HparameterContext.symm H.outVEnvWF.ordered).defeqCtx
  let earlierFVars := H.bindings.motives.fvars.take owner
  have hsourceParameters : source.FVarsIn
      (· ∈ H.params.fvars) := by
    have Hfv := Hnarrow.fvarsIn
    rw [S.motiveSourceParameterScope, hparameterScopeFVars,
      hparameterFVars] at Hfv
    exact Hfv.mono fun fv hfv => by simpa using hfv
  have hsourceClosed : Closed source 0 := by
    have hclosed := Hnarrow.closed
    rw [S.motiveSourceNoBV] at hclosed
    exact hclosed
  have hsourceAvoidsEarlier : source.FVarsIn (· ∉ earlierFVars) := by
    exact hsourceParameters.mono fun fv hfv hearlier => by
      have hdisjoint := (List.nodup_append.mp hparamsMotivesNodup).2.2
      exact hdisjoint fv hfv fv (List.mem_of_mem_take hearlier) rfl
  have hearlierAbstract : source.abstractList earlierFVars = source :=
    hsourceAvoidsEarlier.abstractList_eq_self hsourceClosed
  have hearlierNodup : earlierFVars.Nodup := by
    exact (List.nodup_append.mp hparamsMotivesNodup).2.1.sublist
      (List.take_sublist owner H.bindings.motives.fvars)
  have hparamsNodup' : H.params.fvars.Nodup :=
    List.nodup_reverse.mp hparamsNodup
  have hparamsEarlierNodup :
      (H.params.fvars ++ earlierFVars).Nodup := by
    exact hparamsMotivesNodup.sublist
      ((List.Sublist.refl H.params.fvars).append
        (List.take_sublist owner H.bindings.motives.fvars))
  have habstractShape :
      (source.abstractList H.params.fvars).liftLooseBVars'
          0 earlierFVars.length =
        source.abstractList (H.params.fvars ++ earlierFVars) := by
    have hshift := Expr.abstractList_add_eq_liftLooseBVars
      (e := source) (fvars := H.params.fvars) (depth := 0)
      (extra := earlierFVars.length) hsourceClosed hparamsNodup'
    have happend := Expr.abstractList_after_inner
      (e := source) (outer := H.params.fvars)
      (inner := earlierFVars) (k := 0) hparamsEarlierNodup
    rw [hearlierAbstract] at happend
    exact hshift.symm.trans happend
  have W := abstractForallContext.bvLift (T.motives.take owner)
    (abstractForallContext T.params [])
  have HparameterWeak := HparameterTarget.weakBV
    H.outVEnvWF.ordered W
  have HparameterWeak' : TrExprS H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext
        (T.params ++ T.motives.take owner) [])
      (source.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars.take owner))
      (parameterTarget.liftN (T.motives.take owner).length 0) := by
    have hrecInfo : owner < H.recInfos.size := by
      simpa [H.generated.length] using howner
    have hownerMotive : owner < T.motives.length := by
      rw [T.motives_length]
      simpa using hrecInfo
    have hownerBinding : owner < H.bindings.motives.fvars.length := by
      have hlength : H.bindings.motives.fvars.length = H.recInfos.size := by
        have h := congrArg Array.size H.bindings.motives.expressions
        simpa using h.symm
      rw [hlength]
      exact hrecInfo
    have htakeT : (T.motives.take owner).length = owner := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hownerMotive)]
    have htakeSource : earlierFVars.length = owner := by
      simp [earlierFVars, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hownerBinding)]
    have hweakContext :
        abstractForallContext (T.motives.take owner)
            (abstractForallContext T.params []) =
          abstractForallContext
            (T.params ++ T.motives.take owner) [] := by
      simp [abstractForallContext, List.reverse_append, List.map_append,
        List.map_take, List.append_assoc]
    rw [htakeT] at HparameterWeak
    rw [← habstractShape, htakeT, htakeSource, ← hweakContext]
    exact HparameterWeak
  have htoCtx : ∀ types : List VExpr,
      VLCtx.toCtx (types.map fun type =>
        ((none, .vlam type) :
          Option (FVarId × List FVarId) × VLocalDecl)) = types := by
    intro types
    induction types with
    | nil => rfl
    | cons type types ih => simp [VLCtx.toCtx, ih]
  have anonymousWF : ∀ types : List VExpr,
      OnCtx types (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) →
      VLCtx.WF H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        (types.map fun type =>
          ((none, .vlam type) :
            Option (FVarId × List FVarId) × VLocalDecl)) := by
    intro types Htypes
    induction types with
    | nil => trivial
    | cons type types ih =>
      have Htype : H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          (VLCtx.toCtx (types.map fun type =>
            ((none, .vlam type) :
              Option (FVarId × List FVarId) × VLocalDecl))) type := by
        rw [htoCtx]
        exact Htypes.2
      exact ⟨ih Htypes.1, nofun, Htype⟩
  have HearlierCtx : OnCtx
      (abstractForallContext
        (T.params ++ T.motives.take owner) []).toCtx
      (H.outVEnv.IsType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length) := by
    have HprefixCtx := T.prefixContext H.outVEnvWF.ordered
    have hmotivesReverse : T.motives.reverse =
        (T.motives.drop owner).reverse ++
          (T.motives.take owner).reverse := by
      simpa [List.reverse_append] using
        congrArg List.reverse (List.take_append_drop owner T.motives).symm
    have hsplit : (T.params ++ T.motives ++ T.minors).reverse =
        (T.minors.reverse ++ (T.motives.drop owner).reverse) ++
          (T.params ++ T.motives.take owner).reverse := by
      rw [List.reverse_append, List.reverse_append, hmotivesReverse,
        List.reverse_append]
      simp [List.reverse_append, List.append_assoc]
    rw [hsplit] at HprefixCtx
    have Hsuffix := OnCtx.append_right HprefixCtx
    have hearlierToCtx :
        (abstractForallContext
          (T.params ++ T.motives.take owner) []).toCtx =
          (T.params ++ T.motives.take owner).reverse := by
      simpa [abstractForallContext] using
        htoCtx ((T.params ++ T.motives.take owner).reverse)
    rw [hearlierToCtx]
    exact Hsuffix
  have HearlierVLCtx : VLCtx.WF H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        (T.params ++ T.motives.take owner) []) := by
    have Hwf := anonymousWF
      ((T.params ++ T.motives.take owner).reverse)
      (by
        have hearlierToCtx :
            (abstractForallContext
              (T.params ++ T.motives.take owner) []).toCtx =
              (T.params ++ T.motives.take owner).reverse := by
          simpa [abstractForallContext] using
            htoCtx ((T.params ++ T.motives.take owner).reverse)
        rwa [hearlierToCtx] at HearlierCtx)
    simpa [abstractForallContext] using Hwf
  have Htargets := Hgenerated.uniq H.outVEnvWF
    (.refl H.outVEnvWF HearlierVLCtx)
    HparameterWeak'
  have HcanonicalWeak := HparameterCanonical.weakN
    H.outVEnvWF.ordered W.toCtx
  have HcanonicalWeak' : H.outVEnv.IsDefEqU
      (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
      (abstractForallContext
        (T.params ++ T.motives.take owner) []).toCtx
      (parameterTarget.liftN (T.motives.take owner).length 0)
      (S.canonical.motiveType.liftN
        (T.motives.take owner).length 0) := by
    simpa [abstractForallContext, List.reverse_append, List.map_append,
      List.map_take, List.append_assoc] using HcanonicalWeak
  have Hresult := Htargets.trans H.outVEnvWF
    HearlierCtx
    HcanonicalWeak'
  exact ⟨T, S, hparams, by simpa [source] using Hresult⟩

/-- For any retained translation of this recursor, the semantic motive
telescope consumes exactly as many arguments as its canonical index suffix,
and those semantic arguments translate the same concrete index spine later
abstracted into the equation context.  Thus the only remaining distinction
between the two spines is context transport, not source selection or arity. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.semanticMotiveIndexSpineFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (T : GeneratedRecursorTelescopeTranslation H.outVEnv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (H.generated.entry owner howner).info.type H.entries[owner].2.type
      stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size owner) :
    ∃ binding : RecursorMotiveBinding A.semantics.context
        H.recInfos[owner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence A.semantics.context
          stats H.recInfos[owner]! binding A.rule.target
          A.semantics.targetTarget,
        evidence.indices.length = T.indices.length ∧
        List.Forall₂
          (TrExprS A.semantics.context.venv
            (AddInductive.getRecLevelParams H.elimLevel c.lparams)
            A.semantics.context.mlctx.vlctx)
          (A.rule.target.getAppArgs[stats.params.size:]).toList
          evidence.indices := by
  rcases A.semanticMotiveTelescopeEvidence with
    ⟨binding, ⟨evidence⟩⟩
  have htranslated :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      evidence.indices_translation
  have hsourceArity := checkPositivityStep.getIIndices.index_arity
    A.semantics.target_valid
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hrecArity := H.arities owner hrecInfo
  have hlength : evidence.indices.length = T.indices.length := by
    rw [T.indices_length, hrecArity]
    rw [A.semantic_owner] at hsourceArity
    simpa [AddInductive.getIIndices] using htranslated.symm.trans hsourceArity
  exact ⟨binding, evidence, hlength, evidence.indices_translation⟩

/-- Exact semantic comparison application for a fixed generated recursor
telescope.  The independently checked target indices and constructor major
are retained separately, while the resulting target is exposed literally as
the motive local applied to that same spine. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.semanticConstructorMotiveExactFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
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
    ∃ binding : RecursorMotiveBinding A.semantics.context
        H.recInfos[owner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence A.semantics.context
          stats H.recInfos[owner]! binding A.rule.target
          A.semantics.targetTarget,
        evidence.indices.length = T.indices.length ∧
        List.Forall₂
          (TrExprS A.semantics.context.venv Us
            A.semantics.context.mlctx.vlctx)
          (A.rule.target.getAppArgs[stats.params.size:]).toList
          evidence.indices ∧
        let motiveTarget := VExpr.app
          (VExpr.mkApps binding.motiveTarget evidence.indices)
          A.semantics.constructorTarget
        TrExprS A.semantics.context.venv Us
          A.semantics.context.mlctx.vlctx
          (Expr.app
            (mkAppN H.recInfos[owner]!.motive
              A.rule.target.getAppArgs[stats.params.size:])
            A.rule.sourceConstructorMajor)
          motiveTarget ∧
        A.semantics.context.venv.HasType Us.length
          A.semantics.context.mlctx.vlctx.toCtx motiveTarget
          (.sort evidence.resultLevel) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.semanticMotiveIndexSpineFor T with
    ⟨binding, evidence, hlength, Hindices⟩
  have Hresult := evidence.applyMajorTypedExact
    A.semantics.constructor_translation A.semantics.constructor_typing
  exact ⟨binding, evidence, hlength, Hindices, Hresult⟩

/-- Applying the retained motive telescope to the checked constructor major
produces the exact semantic result sort of this generated equation. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.semanticConstructorMotiveTyped
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ motiveTarget resultLevel,
      TrExprS A.semantics.context.venv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        A.semantics.context.mlctx.vlctx
        (Expr.app
          (mkAppN H.recInfos[owner]!.motive
            A.rule.target.getAppArgs[stats.params.size:])
          A.rule.sourceConstructorMajor)
        motiveTarget ∧
      A.semantics.context.venv.HasType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        A.semantics.context.mlctx.vlctx.toCtx motiveTarget
        (.sort resultLevel) := by
  rcases A.semanticMotiveTelescopeEvidence with
    ⟨binding, ⟨Hevidence⟩⟩
  rcases Hevidence.applyMajorTyped A.semantics.constructor_translation
      A.semantics.constructor_typing with ⟨motiveTarget, Htr, Htyped⟩
  exact ⟨motiveTarget, Hevidence.resultLevel, Htr, Htyped⟩

/-- Final-environment form of `semanticConstructorMotiveTyped`.  Recursor
installation only extends the constant environment, so the exact result
sort and constructor-context translation are preserved. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalConstructorMotiveTyped
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    ∃ motiveTarget resultLevel,
      TrExprS H.outVEnv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        A.semantics.context.mlctx.vlctx
        (Expr.app
          (mkAppN H.recInfos[owner]!.motive
            A.rule.target.getAppArgs[stats.params.size:])
          A.rule.sourceConstructorMajor)
        motiveTarget ∧
      H.outVEnv.HasType
        (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
        A.semantics.context.mlctx.vlctx.toCtx motiveTarget
        (.sort resultLevel) := by
  rcases A.semanticConstructorMotiveTyped with
    ⟨motiveTarget, resultLevel, Htr, Htyped⟩
  have hsemantic : A.semantics.context.venv = R.context.venv :=
    A.semantics.context_venv.trans
      H.recursorEnv
  rw [hsemantic] at Htr Htyped
  exact ⟨motiveTarget, resultLevel,
    Htr.mono (VEnv.addProjections_le.trans H.installed.le),
    Htyped.mono (VEnv.addProjections_le.trans H.installed.le)⟩

/-- Close the independently typed constructor motive application over the
exact production field telescope.  This is the expected-side application
certificate used when transporting the equation LHS through the generated
owner-suffix context conversion. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalConstructorMotiveFieldTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ fieldDomains motiveTarget resultLevel,
      fieldDomains.length = A.rule.allArgs.size ∧
      TrExprS H.outVEnv Us
        A.semantics.fieldRootContext.mlctx.vlctx
        (A.rule.root.lctx.mkForall A.rule.allArgs
          (Expr.app
            (mkAppN H.recInfos[owner]!.motive
              A.rule.target.getAppArgs[stats.params.size:])
            A.rule.sourceConstructorMajor))
        (VExpr.wrapForalls fieldDomains motiveTarget) ∧
      H.outVEnv.IsType Us.length
        A.semantics.fieldRootContext.mlctx.vlctx.toCtx
        (VExpr.wrapForalls fieldDomains motiveTarget) ∧
      H.outVEnv.HasType Us.length
        (fieldDomains.reverse ++
          A.semantics.fieldRootContext.mlctx.vlctx.toCtx)
        motiveTarget (.sort resultLevel) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.semanticConstructorMotiveTyped with
    ⟨motiveTarget, resultLevel, Htr, Htyped⟩
  let fieldDomains := MLCtxForallDomains A.semantics.context.mlctx
    A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have Hclosed := A.semantics.fieldsRecent.mkForallExact Htr
    (⟨resultLevel, Htyped⟩ : A.semantics.context.venv.IsType Us.length
      A.semantics.context.mlctx.vlctx.toCtx motiveTarget)
  have hsemantic : A.semantics.fieldRootContext.venv =
      R.context.venv := by
    calc
      A.semantics.fieldRootContext.venv = A.semantics.context.venv :=
        A.semantics.fieldsRecent.venv_eq.symm
      _ = R.context.venv :=
        A.semantics.context_venv.trans
          H.recursorEnv
  rw [hsemantic] at Hclosed
  have HclosedFinal := And.intro
    (Hclosed.1.mono (VEnv.addProjections_le.trans H.installed.le))
    (Hclosed.2.mono (VEnv.addProjections_le.trans H.installed.le))
  have hlength : fieldDomains.length = A.rule.allArgs.size := by
    exact A.semantics.context.onlyLams.forallDomains_length
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hfieldDomains :=
    A.semantics.context.onlyLams.forallDomains_eq_take_reverse
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hvlctx := TypeChecker.MLCtx.vlctx_eq_take_append_dropN
    A.semantics.context.mlctx A.rule.allArgs.size
      A.semantics.fieldsRecent.size_le
  rw [A.semantics.fieldsRecent.drop_eq] at hvlctx
  have hctxEq : fieldDomains.reverse ++
      A.semantics.fieldRootContext.mlctx.vlctx.toCtx =
        A.semantics.context.mlctx.vlctx.toCtx := by
    rw [show fieldDomains =
        (A.semantics.context.mlctx.vlctx.toCtx.take
          A.rule.allArgs.size).reverse by
      exact hfieldDomains]
    have hvlctxToCtx := congrArg VLCtx.toCtx hvlctx.symm
    rw [VLCtx.toCtx_append] at hvlctxToCtx
    rw [A.semantics.context.onlyLams.toCtx_take] at hvlctxToCtx
    simpa [VLCtx.toCtx] using hvlctxToCtx
  have hcurrentSemantic : A.semantics.context.venv =
      R.context.venv :=
    A.semantics.context_venv.trans
      H.recursorEnv
  have HtypedFinal := Htyped
  rw [hcurrentSemantic] at HtypedFinal
  have HtypedOut := HtypedFinal.mono
    (VEnv.addProjections_le.trans H.installed.le)
  exact ⟨fieldDomains, motiveTarget, resultLevel, hlength,
    by simpa [fieldDomains] using HclosedFinal.1,
    by simpa [fieldDomains] using HclosedFinal.2,
    by rw [hctxEq]; exact HtypedOut⟩

/-- Exact-spine strengthening of `finalConstructorMotiveFieldTelescope` for
a fixed generated recursor telescope.  The field closure retains the literal
semantic motive local, index targets, and constructor target, so later
equation-context transport has no existential application target left to
identify. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalConstructorMotiveExactFieldTelescopeFor
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
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
    ∃ binding : RecursorMotiveBinding A.semantics.context
        H.recInfos[owner]! H.elimLevel,
      ∃ evidence : RecursorMotiveTelescopeEvidence A.semantics.context
          stats H.recInfos[owner]! binding A.rule.target
          A.semantics.targetTarget,
        ∃ fieldDomains : List VExpr,
          evidence.indices.length = T.indices.length ∧
          List.Forall₂
            (TrExprS H.outVEnv Us A.semantics.context.mlctx.vlctx)
            (A.rule.target.getAppArgs[stats.params.size:]).toList
            evidence.indices ∧
          fieldDomains.length = A.rule.allArgs.size ∧
          let motiveTarget := VExpr.app
            (VExpr.mkApps binding.motiveTarget evidence.indices)
            A.semantics.constructorTarget
          TrExprS H.outVEnv Us
            A.semantics.fieldRootContext.mlctx.vlctx
            (A.rule.root.lctx.mkForall A.rule.allArgs
              (Expr.app
                (mkAppN H.recInfos[owner]!.motive
                  A.rule.target.getAppArgs[stats.params.size:])
                A.rule.sourceConstructorMajor))
            (VExpr.wrapForalls fieldDomains motiveTarget) ∧
          H.outVEnv.IsType Us.length
            A.semantics.fieldRootContext.mlctx.vlctx.toCtx
            (VExpr.wrapForalls fieldDomains motiveTarget) ∧
          H.outVEnv.HasType Us.length
            (fieldDomains.reverse ++
              A.semantics.fieldRootContext.mlctx.vlctx.toCtx)
            motiveTarget (.sort evidence.resultLevel) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.semanticConstructorMotiveExactFor T with
    ⟨binding, evidence, hindexLength, Hindices, Htr, Htyped⟩
  let fieldDomains := MLCtxForallDomains A.semantics.context.mlctx
    A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have Hclosed := A.semantics.fieldsRecent.mkForallExact Htr
    (⟨evidence.resultLevel, Htyped⟩ :
      A.semantics.context.venv.IsType Us.length
        A.semantics.context.mlctx.vlctx.toCtx
        (VExpr.app
          (VExpr.mkApps binding.motiveTarget evidence.indices)
          A.semantics.constructorTarget))
  have hsemanticRoot : A.semantics.fieldRootContext.venv =
      R.context.venv := by
    calc
      A.semantics.fieldRootContext.venv = A.semantics.context.venv :=
        A.semantics.fieldsRecent.venv_eq.symm
      _ = R.context.venv :=
        A.semantics.context_venv.trans
          H.recursorEnv
  rw [hsemanticRoot] at Hclosed
  have HclosedFinal := And.intro
    (Hclosed.1.mono (VEnv.addProjections_le.trans H.installed.le))
    (Hclosed.2.mono (VEnv.addProjections_le.trans H.installed.le))
  have hfieldLength : fieldDomains.length = A.rule.allArgs.size := by
    exact A.semantics.context.onlyLams.forallDomains_length
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hfieldDomains :=
    A.semantics.context.onlyLams.forallDomains_eq_take_reverse
      A.rule.allArgs.size A.semantics.fieldsRecent.size_le
  have hvlctx := TypeChecker.MLCtx.vlctx_eq_take_append_dropN
    A.semantics.context.mlctx A.rule.allArgs.size
      A.semantics.fieldsRecent.size_le
  rw [A.semantics.fieldsRecent.drop_eq] at hvlctx
  have hctxEq : fieldDomains.reverse ++
      A.semantics.fieldRootContext.mlctx.vlctx.toCtx =
        A.semantics.context.mlctx.vlctx.toCtx := by
    rw [show fieldDomains =
        (A.semantics.context.mlctx.vlctx.toCtx.take
          A.rule.allArgs.size).reverse by
      exact hfieldDomains]
    have hvlctxToCtx := congrArg VLCtx.toCtx hvlctx.symm
    rw [VLCtx.toCtx_append] at hvlctxToCtx
    rw [A.semantics.context.onlyLams.toCtx_take] at hvlctxToCtx
    simpa [VLCtx.toCtx] using hvlctxToCtx
  have hsemanticCurrent : A.semantics.context.venv =
      R.context.venv :=
    A.semantics.context_venv.trans
      H.recursorEnv
  rw [hsemanticCurrent] at Hindices Htyped
  have HindicesFinal := Lean4Lean.List.Forall₂.imp
    (fun _ _ Hindex => Hindex.mono
      (VEnv.addProjections_le.trans H.installed.le)) Hindices
  have HtypedOut := Htyped.mono
    (VEnv.addProjections_le.trans H.installed.le)
  exact ⟨binding, evidence, fieldDomains, hindexLength, HindicesFinal,
    hfieldLength, by
      simpa [fieldDomains] using HclosedFinal.1,
    by simpa [fieldDomains] using HclosedFinal.2,
    by rw [hctxEq]; exact HtypedOut⟩

/-- The exact field telescope retained by rule generation remains available
after the generated recursors are installed.  This is the stage-correct form
used by equation typing: its source still refers to the production local
context, while every abstract translation and typing judgment lives in the
final environment. -/
theorem CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalFieldTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor) :
    let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
    ∃ domains : List VExpr,
      domains.length = A.rule.allArgs.size ∧
      TrExprS H.outVEnv Us
        A.semantics.fieldRootContext.mlctx.vlctx
        (A.rule.root.lctx.mkForall A.rule.allArgs A.rule.target)
        (VExpr.wrapForalls domains A.semantics.targetTarget) ∧
      H.outVEnv.IsType Us.length
        A.semantics.fieldRootContext.mlctx.vlctx.toCtx
        (VExpr.wrapForalls domains A.semantics.targetTarget) ∧
      TrExprS H.outVEnv Us
        A.semantics.fieldRootContext.mlctx.vlctx
        (A.rule.root.lctx.mkLambda A.rule.allArgs
          A.rule.sourceConstructorMajor)
        (VExpr.wrapLams domains A.semantics.constructorTarget) ∧
      H.outVEnv.HasType Us.length
        A.semantics.fieldRootContext.mlctx.vlctx.toCtx
        (VExpr.wrapLams domains A.semantics.constructorTarget)
        (VExpr.wrapForalls domains A.semantics.targetTarget) := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let F := A.semantics.fieldTelescope
  have hsemantic : A.semantics.fieldRootContext.venv =
      R.context.venv := by
    calc
      A.semantics.fieldRootContext.venv = A.semantics.context.venv :=
        A.semantics.fieldsRecent.venv_eq.symm
      _ = H.recursorWF.venv := A.semantics.context_venv
      _ = R.context.venv := H.recursorEnv
  have Htarget := F.target_translation
  have HtargetType := F.target_type
  have Hmajor := F.major_translation
  have HmajorType := F.major_typing
  rw [hsemantic] at Htarget HtargetType Hmajor HmajorType
  exact ⟨F.domains, F.domains_length,
    Htarget.mono (VEnv.addProjections_le.trans H.installed.le),
    HtargetType.mono (VEnv.addProjections_le.trans H.installed.le),
    Hmajor.mono (VEnv.addProjections_le.trans H.installed.le),
    HmajorType.mono (VEnv.addProjections_le.trans H.installed.le)⟩

/-- Every recursive result selected by an aligned generated rule retains the
typed higher-order field telescope from which its recursive call was built.
The pointwise semantic entry fixes the exact source array positions; this
theorem merely transports its already checked payload across recursor
installation. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalRecursiveAppliedFieldTelescope
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (A : H.GeneratedRuleAlignment owner howner i hctor)
    (j : Nat) (hj : j < A.rule.recursiveArgs.size) :
    ∃ originRoot,
    ∃ Rorigin : RecursorContextWF originRoot
        (AddInductive.getRecLevelParams H.elimLevel c.lparams),
    ∃ _ : RecursorContextExtension A.semantics.context Rorigin,
    ∃ callDepth,
    ∃ S : SemanticBoundGeneratedRecursiveCall indTypes stats
        (H.recInfos.map (·.motive)) (H.recInfos.flatMap (·.minors))
        (AddInductive.getRecLevels H.elimLevel stats.levels)
        Rorigin decl callDepth
        A.rule.recursiveArgs[j] A.rule.recursiveResults[j]!,
      ∃ domains : List VExpr,
        domains.length = S.generated.localArgs.size ∧
        TrExprS H.outVEnv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          Rorigin.mlctx.vlctx
          (S.generated.current.lctx.mkForall S.generated.localArgs
            S.generated.exposedType)
          (VExpr.wrapForalls domains S.exposedTarget) ∧
        H.outVEnv.IsType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          Rorigin.mlctx.vlctx.toCtx
          (VExpr.wrapForalls domains S.exposedTarget) ∧
        TrExprS H.outVEnv
          (AddInductive.getRecLevelParams H.elimLevel c.lparams)
          Rorigin.mlctx.vlctx
          (S.generated.current.lctx.mkLambda S.generated.localArgs
            (mkAppN A.rule.recursiveArgs[j] S.generated.localArgs))
          (VExpr.wrapLams domains S.appliedFieldTarget) ∧
        H.outVEnv.HasType
          (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
          Rorigin.mlctx.vlctx.toCtx
          (VExpr.wrapLams domains S.appliedFieldTarget)
          (VExpr.wrapForalls domains S.exposedTarget) := by
  rcases A.semantics.calls.entries j hj hj with
    ⟨originRoot, Rorigin, Hext, callDepth, S, _hscope⟩
  let F := S.appliedFieldTelescope
  have hsemantic : Rorigin.venv = R.context.venv :=
    Hext.venv_eq.trans <|
      A.semantics.context_venv.trans H.recursorEnv
  have Hexposed := F.exposed_translation
  have HexposedType := F.exposed_type
  have Happlied := F.applied_translation
  have HappliedType := F.applied_typing
  rw [hsemantic] at Hexposed HexposedType Happlied HappliedType
  exact ⟨originRoot, Rorigin, Hext, callDepth, S, F.domains, F.domains_length,
    Hexposed.mono (VEnv.addProjections_le.trans H.installed.le),
    HexposedType.mono (VEnv.addProjections_le.trans H.installed.le),
    Happlied.mono (VEnv.addProjections_le.trans H.installed.le),
    HappliedType.mono (VEnv.addProjections_le.trans H.installed.le)⟩

/-- The aligned recursor is present and well typed in the final environment
at its identity universe instantiation.  Rule typing can therefore consume
the independently recovered telescope without appealing to the equation
being constructed. -/
theorem CompletedRecursorPhasesResult.recursorTypingAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    (owner : Nat) (howner : owner < H.entries.length) :
    let recursor := H.entries[owner].2
    H.outVEnv.HasType recursor.uvars []
      (.const recursor.name (VLevel.params recursor.uvars)) recursor.type := by
  let recursor := H.entries[owner].2
  have hmem : recursor ∈ H.entries.map Prod.snd := by
    exact List.mem_map.mpr
      ⟨H.entries[owner], List.getElem_mem howner, rfl⟩
  have hlookup : H.outVEnv.constants recursor.name =
      some recursor.toVConstant := by
    apply VEnv.addConstVals_get H.installed.abstract
    exact hmem
  have hwfBase : recursor.toVConstant.WF
      (R.context.venv.addProjections decl.projectionEntries) :=
    H.generated.recursorsWF H.localWF H.bindings H.params recursor hmem
  have hwf : recursor.toVConstant.WF H.outVEnv :=
    hwfBase.mono H.installed.le
  exact VEnv.HasType.const0 hlookup hwf

theorem CompletedRecursorPhasesResult.GeneratedRuleAlignment.recursorTyping
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    {H : CompletedRecursorPhasesResult R outEnv}
    {owner : Nat} {howner : owner < H.entries.length}
    {i : Nat} {hctor : i < indTypes[owner]!.ctors.length}
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    let recursor := H.entries[owner].2
    H.outVEnv.HasType recursor.uvars []
      (.const recursor.name (VLevel.params recursor.uvars)) recursor.type := by
  exact H.recursorTypingAt owner howner


end VerifyInductive
end Lean4Lean
