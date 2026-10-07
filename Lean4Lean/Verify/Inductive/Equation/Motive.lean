import Lean4Lean.Verify.Inductive.Equation.MinorAlignment

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
    RecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorHypothesisDeclarations
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
    RecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveSourceScope
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
    RecursorPhasesResult.finalOwnerMotiveTelescopeShapeAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
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
  have hsortN (fvars : List FVarId) (k : Nat) :
      (Expr.sort H.elimLevel).abstractN fvars k = .sort H.elimLevel := rfl
  have HmajorRaw : Expr.ForallTelescope
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel)) 1 (.sort H.elimLevel) := by
    simpa [hsortN] using
      selections.major.forallTelescope (.sort H.elimLevel)
  have Hmajor : Expr.ForallTelescope
      ((H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel)).abstractN selections.indices.fvars)
      1 (.sort H.elimLevel) := by
    have HmajorClosed := HmajorRaw.abstractN selections.indices.fvars 0
    simpa only [hsortN] using HmajorClosed
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
    RecursorPhasesResult.finalOwnerMotiveTelescopeShapeForAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
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
    RecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveApplicationFrame
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


/-- The owner-motive local itself is the comparison function for concrete
suffix application.  After weakening beneath constructor fields, its type
has exactly the independent domains appearing on the right side of
`finalOwnerMotiveSuffixTypeAlignment`, but ends in the elimination sort
rather than the generated recursor result. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveFieldWitnessTyping
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
    RecursorPhasesResult.GeneratedRuleAlignment.finalCachedOwnerMotiveWitnessTyping
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
    (fieldDomains : List VExpr)
    (Hctx :
      let parameterDecls :=
        (R.materialized.parameterSuffix.toRecursorContext
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
      (R.materialized.parameterSuffix.toRecursorContext
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
    (R.materialized.parameterSuffix.toRecursorContext
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

/-- The generated owner-motive domain and the retained first-pass motive are
the same concrete declaration viewed at the two contexts that still have to
be related.  The retained closed scope is now decomposed explicitly into its
interleaved executable ambient prefix and the very parameter scope aligned
with the generated telescope.  No index, major, or current-motive weakening
remains hidden in this frame. -/
theorem
    RecursorPhasesResult.finalOwnerClosedMotiveFrameAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
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
    rw [H.recursorEnv_legacy, R.declared.contextVEnv]
    exact H.installed.le
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

/-- For any retained translation of this recursor, the semantic motive
telescope consumes exactly as many arguments as its canonical index suffix,
and those semantic arguments translate the same concrete index spine later
abstracted into the equation context.  Thus the only remaining distinction
between the two spines is context transport, not source selection or arity. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.semanticMotiveIndexSpineFor
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
    RecursorPhasesResult.GeneratedRuleAlignment.semanticConstructorMotiveExactFor
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
    RecursorPhasesResult.GeneratedRuleAlignment.semanticConstructorMotiveTyped
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
    RecursorPhasesResult.GeneratedRuleAlignment.finalConstructorMotiveTyped
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
  have hsemantic : A.semantics.context.venv = R.declared.context.venv :=
    A.semantics.context_venv.trans H.recursorEnv_legacy
  rw [hsemantic] at Htr Htyped
  rw [R.declared.contextVEnv] at Htr Htyped
  exact ⟨motiveTarget, resultLevel,
    Htr.mono H.installed.le,
    Htyped.mono H.installed.le⟩

/-- Close the independently typed constructor motive application over the
exact production field telescope.  This is the expected-side application
certificate used when transporting the equation LHS through the generated
owner-suffix context conversion. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalConstructorMotiveFieldTelescope
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
      R.declared.venvCtors.addProjections decl.projectionEntries := by
    calc
      A.semantics.fieldRootContext.venv = A.semantics.context.venv :=
        A.semantics.fieldsRecent.venv_eq.symm
      _ = R.declared.venvCtors.addProjections decl.projectionEntries :=
        A.semantics.context_venv.trans
          (H.recursorEnv_legacy.trans R.declared.contextVEnv)
  rw [hsemantic] at Hclosed
  have HclosedFinal := And.intro
    (Hclosed.1.mono H.installed.le)
    (Hclosed.2.mono H.installed.le)
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
      R.declared.venvCtors.addProjections decl.projectionEntries :=
    A.semantics.context_venv.trans
      (H.recursorEnv_legacy.trans R.declared.contextVEnv)
  have HtypedFinal := Htyped
  rw [hcurrentSemantic] at HtypedFinal
  have HtypedOut := HtypedFinal.mono H.installed.le
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
    RecursorPhasesResult.GeneratedRuleAlignment.finalConstructorMotiveExactFieldTelescopeFor
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
      R.declared.venvCtors.addProjections decl.projectionEntries := by
    calc
      A.semantics.fieldRootContext.venv = A.semantics.context.venv :=
        A.semantics.fieldsRecent.venv_eq.symm
      _ = R.declared.venvCtors.addProjections decl.projectionEntries :=
        A.semantics.context_venv.trans
          (H.recursorEnv_legacy.trans R.declared.contextVEnv)
  rw [hsemanticRoot] at Hclosed
  have HclosedFinal := And.intro
    (Hclosed.1.mono H.installed.le)
    (Hclosed.2.mono H.installed.le)
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
      R.declared.venvCtors.addProjections decl.projectionEntries :=
    A.semantics.context_venv.trans
      (H.recursorEnv_legacy.trans R.declared.contextVEnv)
  rw [hsemanticCurrent] at Hindices Htyped
  have HindicesFinal := Lean4Lean.List.Forall₂.imp
    (fun _ _ Hindex => Hindex.mono H.installed.le) Hindices
  have HtypedOut := Htyped.mono H.installed.le
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
theorem RecursorPhasesResult.GeneratedRuleAlignment.finalFieldTelescope
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
      R.declared.venvCtors.addProjections decl.projectionEntries := by
    calc
      A.semantics.fieldRootContext.venv = A.semantics.context.venv :=
        A.semantics.fieldsRecent.venv_eq.symm
      _ = H.recursorWF.venv := A.semantics.context_venv
      _ = R.declared.context.venv := H.recursorEnv_legacy
      _ = R.declared.venvCtors.addProjections decl.projectionEntries :=
        R.declared.contextVEnv
  have Htarget := F.target_translation
  have HtargetType := F.target_type
  have Hmajor := F.major_translation
  have HmajorType := F.major_typing
  rw [hsemantic] at Htarget HtargetType Hmajor HmajorType
  exact ⟨F.domains, F.domains_length,
    Htarget.mono H.installed.le,
    HtargetType.mono H.installed.le,
    Hmajor.mono H.installed.le,
    HmajorType.mono H.installed.le⟩

/-- Every recursive result selected by an aligned generated rule retains the
typed higher-order field telescope from which its recursive call was built.
The pointwise semantic entry fixes the exact source array positions; this
theorem merely transports its already checked payload across recursor
installation. -/
theorem
    RecursorPhasesResult.GeneratedRuleAlignment.finalRecursiveAppliedFieldTelescope
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
  have hsemantic : Rorigin.venv =
      R.declared.venvCtors.addProjections decl.projectionEntries :=
    Hext.venv_eq.trans <|
      A.semantics.context_venv.trans <|
        H.recursorEnv_legacy.trans R.declared.contextVEnv
  have Hexposed := F.exposed_translation
  have HexposedType := F.exposed_type
  have Happlied := F.applied_translation
  have HappliedType := F.applied_typing
  rw [hsemantic] at Hexposed HexposedType Happlied HappliedType
  exact ⟨originRoot, Rorigin, Hext, callDepth, S, F.domains, F.domains_length,
    Hexposed.mono H.installed.le,
    HexposedType.mono H.installed.le,
    Happlied.mono H.installed.le,
    HappliedType.mono H.installed.le⟩

/-- The aligned recursor is present and well typed in the final environment
at its identity universe instantiation.  Rule typing can therefore consume
the independently recovered telescope without appealing to the equation
being constructed. -/
theorem RecursorPhasesResult.recursorTypingAt
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {headerEnv ctorEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats decl nparams isUnsafe depth
      sourceEnv indTypes headerEnv}
    {R : ConstructorPhasesResult Hheaders ctorEnv}
    (H : RecursorPhasesResult R outEnv)
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
      (R.declared.venvCtors.addProjections decl.projectionEntries) :=
    H.generated.recursorsWF H.localWF H.bindings H.params recursor hmem
  have hwf : recursor.toVConstant.WF H.outVEnv :=
    hwfBase.mono H.installed.le
  exact VEnv.HasType.const0 hlookup hwf

theorem RecursorPhasesResult.GeneratedRuleAlignment.recursorTyping
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
    (_A : H.GeneratedRuleAlignment owner howner i hctor) :
    let recursor := H.entries[owner].2
    H.outVEnv.HasType recursor.uvars []
      (.const recursor.name (VLevel.params recursor.uvars)) recursor.type := by
  exact H.recursorTypingAt owner howner


end VerifyInductive
end Lean4Lean
