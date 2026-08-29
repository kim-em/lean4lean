import Lean4Lean.Verify.Inductive.CompletedEquationSetup

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

open checkInductiveTypes.loopType

/-- The generated recursor and the independently replayed canonical motive
share the same parameter context.  This is the first direct bridge from the
five-group executable telescope to the permutation-free semantic telescope;
subsequent index alignment can therefore work under either parameter list
without reusing an executable `isDefEq` success as an assumption. -/
theorem CompletedRecursorPhasesResult.finalPairedParameterAlignmentAt
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
          T.params.reverse S.canonical.params.reverse := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases H.finalRecursorParameterContextAt owner howner with
    ⟨T, hgenerated⟩
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  rcases H.motiveTelescopes.seed owner hrecInfo with ⟨S, hcanonical⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  refine ⟨T, S, ?_⟩
  exact Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    hgenerated ((hcanonical.mono hbase).symm H.outVEnvWF.ordered)

theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalPairedParameterAlignment
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
          T.params.reverse S.canonical.params.reverse := by
  exact H.finalPairedParameterAlignmentAt owner howner

theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalCanonicalParameterAlignment
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
      ∃ C : RecursorCanonicalMotiveTelescope H.outVEnv Us stats decl
          owner H.recInfos[owner]! H.elimLevel,
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          T.params.reverse C.params.reverse := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  rcases A.finalPairedParameterAlignment with ⟨T, S, hparameters⟩
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  exact ⟨T, S.canonical.mono hbase, by
    simpa [RecursorCanonicalMotiveTelescope.mono] using hparameters⟩

/-- Final executable/canonical owner-motive comparison frame.  This packages
the independently replayed canonical motive with the exact source domain and
abstract target selected from the installed generated recursor.  The target
domain is checked under parameters and strictly earlier motives only; hence
the remaining comparison with `C.motiveType` is a context-transport problem,
not another inversion of the production telescope. -/
theorem
    CompletedRecursorPhasesResult.finalOwnerMotiveFrameAt
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
        ∃ D : BoundFVarDeclarationAt H.localContext
            (H.recInfos.map (·.motive)) owner,
          D.type = H.origins.motiveTypes[owner]! ∧
          D.type = H.localContext.lctx.mkForall
            H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
              (.sort H.elimLevel)) ∧
          ∃ (suffixSource : Expr) (name : Name)
            (sourceDomain sourceBody : Expr) (bi : BinderInfo)
            (bodyTarget : VExpr),
            Expr.ForallTelescope
              (H.generated.entry owner howner).info.type
              (T.params.length + owner) suffixSource ∧
            suffixSource = .forallE name sourceDomain sourceBody bi ∧
            sourceDomain = D.type.abstractList
              (H.params.fvars ++ H.bindings.motives.fvars.take owner) ∧
            TrExprS H.outVEnv Us
              (abstractForallContext
                (T.params ++ T.motives.take owner) [])
              sourceDomain T.motives[owner]! ∧
            H.outVEnv.IsType Us.length
              (abstractForallContext
                (T.params ++ T.motives.take owner) []).toCtx
              T.motives[owner]! := by
  dsimp only
  rcases H.finalPairedParameterAlignmentAt owner howner with
    ⟨T, S, hparameters⟩
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  have hmotive : owner < T.motives.length := by
    rw [T.motives_length]
    simpa using hrecInfo
  have hmotiveArray : owner < (H.recInfos.map (·.motive)).size := by
    simpa using hrecInfo
  rcases H.origins.motives.declaration owner hmotiveArray with
    ⟨D, hdeclarationOrigin⟩
  have hdeclarationShape : D.type = H.localContext.lctx.mkForall
      H.recInfos[owner]!.indices
      (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.sort H.elimLevel)) :=
    hdeclarationOrigin.trans (H.motiveShapes.shape owner hrecInfo)
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  have HoriginBinder :=
    selections.ownerMotiveBinderAt hselectionNoAlias D
  have HoriginBinderStats : Expr.ForallBinderAt
      (H.generated.entry owner howner).info.type
      (stats.params.size + owner)
      (D.type.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars.take owner)) := by
    rw [(H.generated.entry owner howner).type]
    simpa [selections, RecInfoBindings.toRecursorLocalSelections,
      BoundFVarArray.toLocalForallSelection] using HoriginBinder
  have HoriginBinder' : Expr.ForallBinderAt
      (H.generated.entry owner howner).info.type
      (T.params.length + owner)
      (D.type.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars.take owner)) := by
    simpa [T.params_length] using HoriginBinderStats
  rcases T.ownerMotiveBinder hmotive with
    ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      Hsource, hsource, Hdomain, HdomainType⟩
  have HsourceBinder := Hsource.binderAt hsource
  have hsourceDomain : sourceDomain = D.type.abstractList
      (H.params.fvars ++ H.bindings.motives.fvars.take owner) := by
    have heq := HsourceBinder.unique HoriginBinder'
    simpa [selections, RecInfoBindings.toRecursorLocalSelections] using heq
  exact ⟨T, S, hparameters, D, hdeclarationOrigin, hdeclarationShape,
    suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
    Hsource, hsource, hsourceDomain,
    by simpa [getElem!_pos T.motives owner hmotive] using Hdomain,
    by simpa [getElem!_pos T.motives owner hmotive] using HdomainType⟩

/-- Rule-local specialization of `finalOwnerMotiveFrameAt`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveFrame
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
        ∃ D : BoundFVarDeclarationAt H.localContext
            (H.recInfos.map (·.motive)) owner,
          D.type = H.origins.motiveTypes[owner]! ∧
          D.type = H.localContext.lctx.mkForall
            H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
              (.sort H.elimLevel)) ∧
          ∃ (suffixSource : Expr) (name : Name)
            (sourceDomain sourceBody : Expr) (bi : BinderInfo)
            (bodyTarget : VExpr),
            Expr.ForallTelescope
              (H.generated.entry owner howner).info.type
              (T.params.length + owner) suffixSource ∧
            suffixSource = .forallE name sourceDomain sourceBody bi ∧
            sourceDomain = D.type.abstractList
              (H.params.fvars ++ H.bindings.motives.fvars.take owner) ∧
            TrExprS H.outVEnv Us
              (abstractForallContext
                (T.params ++ T.motives.take owner) [])
              sourceDomain T.motives[owner]! ∧
            H.outVEnv.IsType Us.length
              (abstractForallContext
                (T.params ++ T.motives.take owner) []).toCtx
              T.motives[owner]! := by
  exact H.finalOwnerMotiveFrameAt owner howner

/-- Reduced owner-motive bridge with all positional witnesses rewritten
away.  The left side is now the exact production declaration shape closed
over the source binders corresponding to the target context on the right.
This is the form needed for the final comparison with `C.motiveType`. -/
theorem
    CompletedRecursorPhasesResult.finalOwnerMotiveDomainTranslationAt
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
        TrExprS H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives.take owner) [])
          ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
              (.sort H.elimLevel))).abstractList
                (H.params.fvars ++ H.bindings.motives.fvars.take owner))
          T.motives[owner]! ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext
            (T.params ++ T.motives.take owner) []).toCtx
          T.motives[owner]! := by
  dsimp only
  rcases H.finalOwnerMotiveFrameAt owner howner with
    ⟨T, S, hparameters, D, _hdeclarationOrigin, hdeclarationShape,
      suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      _Hsource, _hsource, hsourceDomain, Hdomain, HdomainType⟩
  rw [hsourceDomain, hdeclarationShape] at Hdomain
  exact ⟨T, S, hparameters, Hdomain, HdomainType⟩

/-- Rule-local specialization of `finalOwnerMotiveDomainTranslationAt`. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOwnerMotiveDomainTranslation
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
        TrExprS H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives.take owner) [])
          ((H.localContext.lctx.mkForall H.recInfos[owner]!.indices
            (H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
              (.sort H.elimLevel))).abstractList
                (H.params.fvars ++ H.bindings.motives.fvars.take owner))
          T.motives[owner]! ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext
            (T.params ++ T.motives.take owner) []).toCtx
          T.motives[owner]! := by
  exact H.finalOwnerMotiveDomainTranslationAt owner howner

/-- Final-environment identification of the generated recursor domain at
this rule's flattened minor slot.  The source selected structurally from the
translated recursor is exactly the declaration type recorded by the second
`mkRecInfos` pass, closed over parameters, motives, and earlier minors. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorDomain
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
          let sourceBinders := H.params.fvars ++
            H.bindings.motives.fvars ++
              H.bindings.flatMinors.fvars.take minorIdx
          TrExprS H.outVEnv Us
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) [])
              (D.type.abstractList sourceBinders) T.minors[minorIdx]! ∧
            H.outVEnv.IsType Us.length
              (abstractForallContext
                (T.params ++ T.motives ++ T.minors.take minorIdx) []).toCtx
              T.minors[minorIdx]! := by
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  rcases A.finalRecursorTelescopeTranslation with ⟨T⟩
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hminorArray :
      minorIdx < (H.recInfos.flatMap (·.minors)).size :=
    A.rule.minor_valid
  rcases H.bindings.flatMinors.declarationAt H.localWF minorIdx
      hminorArray with ⟨D⟩
  rcases H.origins.flatMinorOrigin D with ⟨O⟩
  have hshapeBound : O.localIndex <
      H.origins.minorTypes[O.owner]!.size := by
    rw [(H.origins.minors O.owner O.owner_lt).size_eq]
    simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt
  let S := H.origins.minorShapes O.owner O.owner_lt O.localIndex hshapeBound
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  have HoriginBinder := selections.minorBinderAt hselectionNoAlias D
  have HoriginBinderStats : Expr.ForallBinderAt
      (H.generated.entry owner howner).info.type
      (stats.params.size + (H.recInfos.map (·.motive)).size + minorIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars ++
          H.bindings.flatMinors.fvars.take minorIdx)) := by
    rw [(H.generated.entry owner howner).type]
    simpa [selections,
      RecInfoBindings.toRecursorLocalSelections,
      BoundFVarArray.toLocalForallSelection, List.append_assoc] using
      HoriginBinder
  have HoriginBinder' : Expr.ForallBinderAt
      (H.generated.entry owner howner).info.type
      (T.params.length + T.motives.length + minorIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.bindings.motives.fvars ++
          H.bindings.flatMinors.fvars.take minorIdx)) := by
    simpa [T.params_length, T.motives_length, Nat.add_assoc] using
      HoriginBinderStats
  rcases T.minorBinder minorIdx hminor with
    ⟨suffixSource, name, sourceDomain, sourceBody, bi, bodyTarget,
      Hsource, hsource, Hdomain, HdomainType⟩
  have HsourceBinder := Hsource.binderAt hsource
  have hsourceDomain : sourceDomain = D.type.abstractList
      (H.params.fvars ++ H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars.take minorIdx) := by
    exact HsourceBinder.unique HoriginBinder'
  rw [hsourceDomain] at Hdomain
  exact ⟨T, D, O, S, by
    simpa [minorIdx, getElem!_pos T.minors minorIdx hminor] using Hdomain,
    by simpa [minorIdx, getElem!_pos T.minors minorIdx hminor] using HdomainType⟩

/-- The parameters, motives, and an arbitrary initial minor segment form a
dependency-closed subset of the interleaved recursor context.  The proof
reads each declaration's domain from the fully closed generated recursor
telescope, so skipped indices and majors cannot enter the retained set. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalMinorPrefixUp
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
    (minorLimit : Nat)
    (hminorLimit : minorLimit ≤ H.bindings.flatMinors.fvars.length) :
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorLimit
    IsFVarUpSet (fun fv => fv ∈ sourceBinders)
      H.recursorWF.mlctx.vlctx := by
  dsimp only
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorLimit
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner hrecInfo
  have hselectionParams : selections.params.fvars = H.params.fvars := rfl
  have hselectionMotives :
      selections.motives.fvars = H.bindings.motives.fvars := rfl
  have hselectionMinors :
      selections.minors.fvars = H.bindings.flatMinors.fvars := rfl
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  rcases A.finalRecursorTelescopeTranslation with ⟨T⟩
  have HsourceClosed :
      (H.generated.entry owner howner).info.type.FVarsIn
        (fun _ => False) := by
    have Hscope := T.typed.translation.fvarsIn
    exact Hscope.mono fun fv hfv => by simpa using hfv
  have Hcontext := H.recursorWF.mlctx_wf.tr
  rw [H.recursorWF.lctx_eq] at Hcontext
  apply checkInductiveTypes.loopType.TrLCtx'.isFVarUpSet Hcontext.2
  intro d hd hselected dep hdep
  change d.fvarId ∈ sourceBinders at hselected
  rcases List.mem_append.mp hselected with hprefix | hminor
  · rcases List.mem_append.mp hprefix with hparam | hmotive
    · rcases List.mem_iff_getElem.mp hparam with ⟨idx, hidx, hget⟩
      have hi : idx < stats.params.size := by
        rw [← H.params.length_fvars]
        exact hidx
      rcases H.params.declarationAt H.localWF idx hi with ⟨D⟩
      rcases H.params.getElem_eq_fvar idx hi with ⟨_hidxFVars, hexpr⟩
      have hDfv : D.fvar = d.fvarId := by
        apply Expr.fvar.inj
        calc
          .fvar D.fvar = stats.params[idx] := D.expression.symm
          _ = .fvar H.params.fvars[idx] := hexpr
          _ = .fvar d.fvarId := congrArg Expr.fvar hget
      have hdEq := D.declaration_eq_of_mem H.localWF d hd hDfv.symm
      have Hbinder := selections.parameterBinderAt hselectionNoAlias D
      dsimp only at Hbinder
      rw [← (H.generated.entry owner howner).type] at Hbinder
      have Hclosed := Hbinder.domainFVarsIn HsourceClosed
      have Htype := FVarsIn.of_abstractList Hclosed
      have HtypeScope : D.type.FVarsIn (fun fv => fv ∈ sourceBinders) :=
        Htype.mono fun fv hfv => by
          rcases hfv with hfv | hfalse
          · exact List.mem_append_left _
              (List.mem_append_left _ (List.mem_of_mem_take hfv))
          · exact False.elim hfalse
      rw [hdEq] at hdep
      exact (fvarsIn_iff.mp HtypeScope).1 dep hdep
    · rcases List.mem_iff_getElem.mp hmotive with ⟨idx, hidx, hget⟩
      have hi : idx < (H.recInfos.map (·.motive)).size := by
        rw [← H.bindings.motives.length_fvars]
        exact hidx
      rcases H.bindings.motives.declarationAt H.localWF idx hi with ⟨D⟩
      rcases H.bindings.motives.getElem_eq_fvar idx hi with
        ⟨_hidxFVars, hexpr⟩
      have hDfv : D.fvar = d.fvarId := by
        apply Expr.fvar.inj
        calc
          .fvar D.fvar = (H.recInfos.map (·.motive))[idx] :=
            D.expression.symm
          _ = .fvar H.bindings.motives.fvars[idx] := hexpr
          _ = .fvar d.fvarId := congrArg Expr.fvar hget
      have hdEq := D.declaration_eq_of_mem H.localWF d hd hDfv.symm
      have Hbinder := selections.motiveBinderAt hselectionNoAlias D
      dsimp only at Hbinder
      rw [← (H.generated.entry owner howner).type] at Hbinder
      have Hclosed := Hbinder.domainFVarsIn HsourceClosed
      have Htype := FVarsIn.of_abstractList Hclosed
      have HtypeScope : D.type.FVarsIn
          (fun fv => fv ∈ sourceBinders) :=
        Htype.mono fun fv hfv => by
          rcases hfv with hfv | hfalse
          · rcases List.mem_append.mp hfv with hparam | hmotive
            · exact List.mem_append_left _ (List.mem_append_left _ hparam)
            · exact List.mem_append_left _
                (List.mem_append_right _ (List.mem_of_mem_take hmotive))
          · exact False.elim hfalse
      rw [hdEq] at hdep
      exact (fvarsIn_iff.mp HtypeScope).1 dep hdep
  · rcases List.mem_iff_getElem.mp hminor with ⟨idx, hidxTake, hgetTake⟩
    have htakeLength :
        (H.bindings.flatMinors.fvars.take minorLimit).length = minorLimit := by
      simp [Nat.min_eq_left hminorLimit]
    have hidxMinor : idx < minorLimit := by
      rw [htakeLength] at hidxTake
      exact hidxTake
    have hidx : idx < H.bindings.flatMinors.fvars.length :=
      Nat.lt_of_lt_of_le hidxMinor hminorLimit
    have hget : H.bindings.flatMinors.fvars[idx] = d.fvarId := by
      simpa using hgetTake
    have hi : idx < (H.recInfos.flatMap (·.minors)).size := by
      rw [← H.bindings.flatMinors.length_fvars]
      exact hidx
    rcases H.bindings.flatMinors.declarationAt H.localWF idx hi with ⟨D⟩
    rcases H.bindings.flatMinors.getElem_eq_fvar idx hi with
      ⟨_hidxFVars, hexpr⟩
    have hDfv : D.fvar = d.fvarId := by
      apply Expr.fvar.inj
      calc
        .fvar D.fvar = (H.recInfos.flatMap (·.minors))[idx] :=
          D.expression.symm
        _ = .fvar H.bindings.flatMinors.fvars[idx] := hexpr
        _ = .fvar d.fvarId := congrArg Expr.fvar hget
    have hdEq := D.declaration_eq_of_mem H.localWF d hd hDfv.symm
    have Hbinder := selections.minorBinderAt hselectionNoAlias D
    dsimp only at Hbinder
    rw [← (H.generated.entry owner howner).type] at Hbinder
    have Hclosed := Hbinder.domainFVarsIn HsourceClosed
    have Htype := FVarsIn.of_abstractList Hclosed
    have HtypeScope : D.type.FVarsIn
        (fun fv => fv ∈ sourceBinders) :=
      Htype.mono fun fv hfv => by
        rcases hfv with hfv | hfalse
        · rw [hselectionParams, hselectionMotives,
              hselectionMinors] at hfv
          rcases List.mem_append.mp hfv with hprefix | hprior
          · rcases List.mem_append.mp hprefix with hparam | hmotive
            · exact List.mem_append_left _ (List.mem_append_left _ hparam)
            · exact List.mem_append_left _
                (List.mem_append_right _ hmotive)
          · exact List.mem_append_right _
              ((List.take_sublist_take_left
                (Nat.le_of_lt hidxMinor)).subset hprior)
        · exact False.elim hfalse
    rw [hdEq] at hdep
    exact (fvarsIn_iff.mp HtypeScope).1 dep hdep

/-- The parameters, motives, and strictly earlier minors selected by one
generated minor form a dependency-closed subset of the interleaved recursor
context. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorPrefixUp
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    IsFVarUpSet (fun fv => fv ∈ sourceBinders)
      H.recursorWF.mlctx.vlctx := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  apply A.finalMinorPrefixUp minorIdx
  rw [H.bindings.flatMinors.length_fvars]
  exact Nat.le_of_lt A.rule.minor_valid

/-- Every generated parameter, motive, and minor local is dependency-closed
as a group inside the interleaved executable recursor context.  Indices and
majors may occur between these declarations operationally, but no retained
outer declaration depends on them. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOuterPrefixUp
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
    let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars
    IsFVarUpSet (fun fv => fv ∈ outerBinders)
      H.recursorWF.mlctx.vlctx := by
  dsimp only
  simpa using A.finalMinorPrefixUp
    H.bindings.flatMinors.fvars.length (Nat.le_refl _)

/-- Filtering the interleaved executable context by all generated outer
locals recovers exactly their canonical newest-first order. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOuterFilteredFVars
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
    let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars
    H.recursorWF.mlctx.vlctx.fvars.filter (· ∈ outerBinders) =
      outerBinders.reverse := by
  dsimp only
  let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars
  have hfiltered :=
    checkInductiveTypes.loopType.List.filter_mem_eq_of_sublist_nodup
      H.outerOrder H.recursorWF.mlctx_wf.fvars_nodup
  calc
    H.recursorWF.mlctx.vlctx.fvars.filter (· ∈ outerBinders) =
        H.recursorWF.mlctx.vlctx.fvars.filter
          (· ∈ outerBinders.reverse) := by
      apply List.filter_congr
      intro fv _
      simp
    _ = outerBinders.reverse := hfiltered

/-- Narrow the interleaved executable context to the complete generated
parameter/motive/minor scope, retaining both its exact operational lift and
its concrete source closure.  This is the semantic counterpart of the full
anonymous recursor prefix used by equation checking. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOuterNarrowScope
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
    let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
        scope.fvars = outerBinders.reverse ∧
        Hscope.shift = fvarSelectionLift
          H.recursorWF.mlctx.vlctx.fvars (· ∈ outerBinders) ∧
        ∀ body,
          Hscope.sources.closeSource body =
            H.localContext.lctx.mkForall
              (outerBinders.map Expr.fvar).toArray body := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars
  rcases MLCtxOnlyLams.narrowFVarsSource
      H.recursorWF.onlyLams
      H.recursorWF.checking.tr.wf H.recursorWF.mlctx_wf
      (fun fv => fv ∈ outerBinders) A.finalOuterPrefixUp with
    ⟨scope, Hscope, hscopeFiltered, hscopeShift,
      _hscopeDecls, hscopeSource⟩
  have hscope : scope.fvars = outerBinders.reverse :=
    hscopeFiltered.trans A.finalOuterFilteredFVars
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  let HscopeOut := Hscope.mono hbase
  have hscopeSourceOut : ∀ body,
      HscopeOut.sources.closeSource body =
        H.localContext.lctx.mkForall
          (outerBinders.map Expr.fvar).toArray body := by
    intro body
    have hsource := hscopeSource body
    rw [hscope, List.reverse_reverse] at hsource
    change (Hscope.sources.mono hbase).closeSource body = _
    rw [checkInductiveTypes.loopType.FVarNarrowSources.closeSource_mono]
    simpa [H.recursorWF.lctx_eq] using hsource
  exact ⟨scope, HscopeOut, hscope, hscopeShift, hscopeSourceOut⟩

/-- Chronological strengthening of `finalSelectedMinorPrefixUp`: the exact
selected prefix occurs, newest first, inside the executable recursor
context. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorPrefixOrder
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    sourceBinders.reverse <+ H.recursorWF.mlctx.vlctx.fvars := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  have hforward : sourceBinders <+
      H.params.fvars ++ H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars := by
    dsimp only [sourceBinders]
    exact (List.Sublist.refl
      (H.params.fvars ++ H.bindings.motives.fvars)).append
        (List.take_sublist minorIdx H.bindings.flatMinors.fvars)
  exact hforward.reverse.trans H.outerOrder

/-- Filtering the executable context by the selected-prefix predicate has
no hidden reordering or extra binders. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorFilteredFVars
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    H.recursorWF.mlctx.vlctx.fvars.filter (· ∈ sourceBinders) =
      sourceBinders.reverse := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  have horder : sourceBinders.reverse <+
      H.recursorWF.mlctx.vlctx.fvars :=
    A.finalSelectedMinorPrefixOrder
  have hfiltered :=
    checkInductiveTypes.loopType.List.filter_mem_eq_of_sublist_nodup horder
    H.recursorWF.mlctx_wf.fvars_nodup
  calc
    H.recursorWF.mlctx.vlctx.fvars.filter (· ∈ sourceBinders) =
        H.recursorWF.mlctx.vlctx.fvars.filter
          (· ∈ sourceBinders.reverse) := by
      apply List.filter_congr
      intro fv _
      simp
    _ = sourceBinders.reverse := hfiltered

/-- The dependency and ordering certificates together construct the exact
non-contiguous semantic scope used to close the selected minor type. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorNarrowScope
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.recursorWF.venv Us scope H.recursorWF.mlctx.vlctx,
        scope.fvars = sourceBinders.reverse := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases checkInductiveTypes.loopType.narrowFVars
      H.recursorWF.onlyLams
      H.recursorWF.checking.tr.wf H.recursorWF.mlctx_wf
      (fun fv => fv ∈ sourceBinders) A.finalSelectedMinorPrefixUp with
    ⟨scope, Hscope, hscope⟩
  exact ⟨scope, Hscope, hscope.trans A.finalSelectedMinorFilteredFVars⟩

/-- Close the exact selected-minor declaration through the independently
narrowed free-variable scope.  This exposes two translations of the same
closed source domain: one over the scope's semantic domains and one over the
generated recursor telescope.  Their context comparison is the remaining
bridge needed by the canonical RHS application. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorExactClosedDomain
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ D : BoundFVarDeclarationAt H.localContext
          (H.recInfos.flatMap (·.minors)) minorIdx,
      ∃ O : H.origins.FlatMinorOrigin D,
      ∃ S : RecInfoMinorTypeShape,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
      ∃ narrowTarget,
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        (∀ body,
          Hscope.sources.closeSource body =
            H.localContext.lctx.mkForall
              (sourceBinders.map Expr.fvar).toArray body) ∧
        TrExprS H.outVEnv Us scope D.type narrowTarget ∧
        TrExprS H.outVEnv Us
          (abstractForallContext scope.toCtx.reverse [])
          (D.type.abstractList sourceBinders) narrowTarget ∧
        OnCtx (abstractForallContext scope.toCtx.reverse []).toCtx
          (H.outVEnv.IsType Us.length) ∧
        TrExprS H.outVEnv Us
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors.take minorIdx) [])
          (D.type.abstractList sourceBinders) T.minors[minorIdx]! ∧
        H.outVEnv.IsType Us.length
          (abstractForallContext
            (T.params ++ T.motives ++ T.minors.take minorIdx) []).toCtx
          T.minors[minorIdx]! := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.finalSelectedMinorDomain with
    ⟨T, D, O, S, Hdomain, HdomainType⟩
  rcases MLCtxOnlyLams.narrowFVarsSource
      H.recursorWF.onlyLams
      H.recursorWF.checking.tr.wf H.recursorWF.mlctx_wf
      (fun fv => fv ∈ sourceBinders) A.finalSelectedMinorPrefixUp with
    ⟨scope, Hscope, hscopeFiltered, hscopeShift,
      _hscopeDecls, hscopeSource⟩
  have hscope : scope.fvars = sourceBinders.reverse :=
    hscopeFiltered.trans A.finalSelectedMinorFilteredFVars
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  let HscopeOut := Hscope.mono hbase
  have hscopeSourceOut : ∀ body,
      HscopeOut.sources.closeSource body =
        H.localContext.lctx.mkForall
          (sourceBinders.map Expr.fvar).toArray body := by
    intro body
    have hsource := hscopeSource body
    rw [hscope, List.reverse_reverse] at hsource
    change (Hscope.sources.mono hbase).closeSource body = _
    rw [checkInductiveTypes.loopType.FVarNarrowSources.closeSource_mono]
    simpa [H.recursorWF.lctx_eq] using hsource
  rcases H.recursorWF.translatedDeclarationType D with
    ⟨runtimeTarget, Hruntime⟩
  have HruntimeOut := Hruntime.mono hbase
  have hclosed : Closed D.type 0 := by
    have h := Hruntime.closed
    rw [H.recursorWF.mlctx.noBV] at h
    exact h
  have HabstractClosed :
      (D.type.abstractList sourceBinders).FVarsIn (fun _ => False) := by
    apply Hdomain.fvarsIn.mono
    intro fv hfv
    simpa using hfv
  have HtypeScope : D.type.FVarsIn (· ∈ scope.fvars) := by
    have Hraw := FVarsIn.of_abstractList HabstractClosed
    apply Hraw.mono
    intro fv hfv
    rcases hfv with hfv | hfalse
    · rw [hscope]
      exact List.mem_reverse.mpr hfv
    · exact False.elim hfalse
  rcases HscopeOut.restrict H.outVEnvWF HruntimeOut hclosed HtypeScope with
    ⟨narrowTarget, Hnarrow⟩
  have Hclosed := HscopeOut.abstractAll H.outVEnvWF Hnarrow
  rw [hscope, List.reverse_reverse] at Hclosed
  exact ⟨T, D, O, S, scope, HscopeOut, narrowTarget, hscope,
    hscopeShift, hscopeSourceOut, Hnarrow, Hclosed,
    HscopeOut.abstractAllWF H.outVEnvWF, Hdomain, HdomainType⟩

/-- Reconstruct the complete source telescope of the exact selected prefix.
Its abstract domains are precisely the non-contiguous narrowed context and
its arity is precisely the generated parameter/motive/earlier-minor prefix.
This is the binder-by-binder comparison input missing from the earlier
whole-domain closing theorem. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorExactPrefixSource
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
      ∃ prefixSource,
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        (∀ body,
          Hscope.sources.closeSource body =
            H.localContext.lctx.mkForall
              (sourceBinders.map Expr.fvar).toArray body) ∧
        prefixSource = Hscope.sources.closeSource
          (.sort (.zero : Level)) ∧
        prefixSource = H.localContext.lctx.mkForall
          (sourceBinders.map Expr.fvar).toArray
          (.sort (.zero : Level)) ∧
        TrExprS H.outVEnv Us [] prefixSource
          (VExpr.wrapForalls scope.toCtx.reverse
            (.sort (.zero : VLevel))) ∧
        H.outVEnv.IsType Us.length []
          (VExpr.wrapForalls scope.toCtx.reverse
            (.sort (.zero : VLevel))) ∧
        Expr.ForallTelescopeTypeTranslation H.outVEnv Us [] prefixSource
          scope.length
          (VExpr.wrapForalls scope.toCtx.reverse
            (.sort (.zero : VLevel))) ∧
        scope.toCtx.reverse.length =
          (T.params ++ T.motives ++ T.minors.take minorIdx).length := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.finalSelectedMinorExactClosedDomain with
    ⟨T, _D, _O, _S, scope, Hscope, _narrowTarget, hscope,
      hscopeShift, hscopeSource, _Hnarrow, _Hclosed, _HscopeWF,
      _Hdomain, _HdomainType⟩
  rcases Hscope.closedSortTranslation H.outVEnvWF with
    ⟨Hprefix, HprefixType⟩
  have HprefixTelescope := Hscope.closedSortTelescope H.outVEnvWF
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hprefixLength : scope.toCtx.reverse.length =
      (T.params ++ T.motives ++ T.minors.take minorIdx).length := by
    calc
      scope.toCtx.reverse.length = scope.length := by
        simpa using Hscope.toCtx_length
      _ = scope.fvars.length := Hscope.fvars_length.symm
      _ = sourceBinders.reverse.length := congrArg List.length hscope
      _ = sourceBinders.length := by simp
      _ = (T.params ++ T.motives ++ T.minors.take minorIdx).length := by
        simp only [sourceBinders, List.length_append, List.length_take]
        rw [H.params.length_fvars, H.bindings.motives.length_fvars,
          H.bindings.flatMinors.length_fvars,
          T.params_length, T.motives_length, T.minors_length]
  exact ⟨T, scope, Hscope,
    Hscope.sources.closeSource (.sort (.zero : Level)), hscope,
    hscopeShift, hscopeSource, rfl,
    hscopeSource (.sort (.zero : Level)),
    Hprefix, HprefixType, HprefixTelescope, hprefixLength⟩

/-- A concrete parameter/motive/minor prefix and the production recursor have
the same source domain at every retained slot.  The proof selects the exact
local declaration on both sides, rather than appealing to whole-expression
equality. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalMinorPrefixBinderEq
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
    (minorLimit : Nat)
    (hminorLimit : minorLimit ≤ H.bindings.flatMinors.fvars.length) :
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorLimit
    ∀ position (hposition : position < sourceBinders.length)
      {prefixDomain recursorDomain : Expr},
      Expr.ForallBinderAt
        (H.localContext.lctx.mkForall
          (sourceBinders.map Expr.fvar).toArray
          (.sort (.zero : Level))) position prefixDomain →
      Expr.ForallBinderAt
        (H.generated.entry owner howner).info.type position recursorDomain →
      prefixDomain = recursorDomain := by
  dsimp only
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorLimit
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner hrecInfo
  have hselectionNoAlias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  have hsourceNodup : sourceBinders.Nodup := by
    have houter := H.bindings.outerNodup H.params H.noAlias
    have hsub :
        (H.params.fvars ++ H.bindings.motives.fvars) ++
            H.bindings.flatMinors.fvars.take minorLimit <+
          (H.params.fvars ++ H.bindings.motives.fvars) ++
            H.bindings.flatMinors.fvars :=
      (List.Sublist.refl
        (H.params.fvars ++ H.bindings.motives.fvars)).append
          (List.take_sublist _ H.bindings.flatMinors.fvars)
    simpa [sourceBinders, List.append_assoc] using houter.sublist hsub
  have hsourceMembers : ∀ fv ∈ sourceBinders,
      fv ∈ H.localContext.lctx.fvars := by
    intro fv hfv
    rcases List.mem_append.mp hfv with hprefix | hminor
    · rcases List.mem_append.mp hprefix with hparam | hmotive
      · exact H.params.members fv hparam
      · exact H.bindings.motives.members fv hmotive
    · exact H.bindings.flatMinors.members fv
        (List.mem_of_mem_take hminor)
  have hsourceDecls : ∀ fv ∈ sourceBinders,
      ∃ index name type bi kind,
        H.localContext.lctx.find? fv =
          some (.cdecl index fv name type bi kind) := by
    intro fv hfv
    exact H.localWF.findCDecl fv (hsourceMembers fv hfv)
  intro position hposition prefixDomain recursorDomain Hprefix Hrecursor
  by_cases hparam : position < H.params.fvars.length
  · have hparamArray : position < stats.params.size := by
      rw [← H.params.length_fvars]
      exact hparam
    rcases H.params.declarationAt H.localWF position hparamArray with ⟨D⟩
    rcases H.params.getElem_eq_fvar position hparamArray with
      ⟨_hparamFVars, hparamExpr⟩
    have hparamFVar : H.params.fvars[position] = D.fvar :=
      Expr.fvar.inj (hparamExpr.symm.trans D.expression)
    have hsourceAt : sourceBinders[position] = D.fvar := by
      rw [List.getElem_append_left]
      · rw [List.getElem_append_left hparam]
        exact hparamFVar
      · simp only [List.length_append]
        omega
    have htake : sourceBinders.take position =
        H.params.fvars.take position := by
      dsimp only [sourceBinders]
      rw [List.take_append, List.take_append]
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hparam)]
      rw [Nat.sub_eq_zero_of_le (by simp; omega :
        position ≤ (H.params.fvars ++ H.bindings.motives.fvars).length)]
      simp
    have HprefixCanonical :=
      LocalContext.mkForall_fvars_forallBinderAt hsourceDecls hsourceNodup
        position hposition D.index D.userName D.type D.binderInfo D.kind (by
          rw [hsourceAt]
          exact D.declaration)
        (body := (.sort (.zero : Level)))
    have HrecursorCanonical :=
      selections.parameterBinderAt hselectionNoAlias D
    dsimp only at HrecursorCanonical
    rw [← (H.generated.entry owner howner).type] at HrecursorCanonical
    have hprefixDomain : prefixDomain =
        D.type.abstractList (H.params.fvars.take position) := by
      rw [← htake]
      exact Hprefix.unique HprefixCanonical
    exact hprefixDomain.trans
      (Hrecursor.unique HrecursorCanonical).symm
  · by_cases hmotive : position <
        H.params.fvars.length + H.bindings.motives.fvars.length
    · let motivePos := position - H.params.fvars.length
      have hmotivePos : motivePos < H.bindings.motives.fvars.length := by
        dsimp only [motivePos]
        omega
      have hmotiveArray : motivePos <
          (H.recInfos.map (·.motive)).size := by
        rw [← H.bindings.motives.length_fvars]
        exact hmotivePos
      rcases H.bindings.motives.declarationAt H.localWF motivePos
          hmotiveArray with ⟨D⟩
      rcases H.bindings.motives.getElem_eq_fvar motivePos hmotiveArray with
        ⟨_hmotiveFVars, hmotiveExpr⟩
      have hmotiveFVar : H.bindings.motives.fvars[motivePos] = D.fvar :=
        Expr.fvar.inj (hmotiveExpr.symm.trans D.expression)
      have hpositionEq : H.params.fvars.length + motivePos = position := by
        dsimp only [motivePos]
        omega
      have hsourceAt : sourceBinders[position] = D.fvar := by
        rw [List.getElem_append_left]
        · rw [List.getElem_append_right (Nat.le_of_not_gt hparam)]
          simpa [motivePos] using hmotiveFVar
        · simp only [List.length_append]
          omega
      have htake : sourceBinders.take position =
          H.params.fvars ++
            H.bindings.motives.fvars.take motivePos := by
        rw [← hpositionEq]
        dsimp only [sourceBinders]
        rw [List.take_append, List.take_append]
        rw [List.take_of_length_le (by omega :
          H.params.fvars.length ≤ H.params.fvars.length + motivePos)]
        rw [Nat.sub_eq_zero_of_le (by simp; omega :
          H.params.fvars.length + motivePos ≤
            (H.params.fvars ++ H.bindings.motives.fvars).length)]
        simp
      have HprefixCanonical :=
        LocalContext.mkForall_fvars_forallBinderAt hsourceDecls hsourceNodup
          position hposition D.index D.userName D.type D.binderInfo D.kind (by
            rw [hsourceAt]
            exact D.declaration)
          (body := (.sort (.zero : Level)))
      have HrecursorCanonical :=
        selections.motiveBinderAt hselectionNoAlias D
      dsimp only at HrecursorCanonical
      rw [← (H.generated.entry owner howner).type] at HrecursorCanonical
      have hstatsPosition : stats.params.size + motivePos = position := by
        rw [← H.params.length_fvars]
        exact hpositionEq
      rw [hstatsPosition] at HrecursorCanonical
      have hprefixDomain : prefixDomain = D.type.abstractList
          (H.params.fvars ++
            H.bindings.motives.fvars.take motivePos) := by
        rw [← htake]
        exact Hprefix.unique HprefixCanonical
      exact hprefixDomain.trans
        (Hrecursor.unique HrecursorCanonical).symm
    · let priorPos := position -
        (H.params.fvars.length + H.bindings.motives.fvars.length)
      have hpriorPos : priorPos < minorLimit := by
        dsimp only [priorPos, sourceBinders] at hposition ⊢
        simp only [List.length_append, List.length_take,
          Nat.min_eq_left hminorLimit] at hposition
        omega
      have hpriorArray : priorPos <
          (H.recInfos.flatMap (·.minors)).size := by
        rw [← H.bindings.flatMinors.length_fvars]
        exact Nat.lt_of_lt_of_le hpriorPos hminorLimit
      rcases H.bindings.flatMinors.declarationAt H.localWF priorPos
          hpriorArray with ⟨D⟩
      rcases H.bindings.flatMinors.getElem_eq_fvar priorPos hpriorArray with
        ⟨_hpriorFVars, hpriorExpr⟩
      have hpriorFVar : H.bindings.flatMinors.fvars[priorPos] = D.fvar :=
        Expr.fvar.inj (hpriorExpr.symm.trans D.expression)
      have hpositionEq : H.params.fvars.length +
          H.bindings.motives.fvars.length + priorPos = position := by
        dsimp only [priorPos]
        omega
      have hsourceAt : sourceBinders[position] = D.fvar := by
        rw [List.getElem_append_right (by
          simp only [List.length_append]
          omega : (H.params.fvars ++ H.bindings.motives.fvars).length ≤
            position)]
        rw [List.getElem_take]
        simpa only [List.length_append, priorPos] using hpriorFVar
      have htake : sourceBinders.take position =
          H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take priorPos := by
        rw [← hpositionEq]
        dsimp only [sourceBinders]
        rw [List.take_append, List.take_append]
        rw [List.take_of_length_le (by omega :
          H.params.fvars.length ≤ H.params.fvars.length +
            H.bindings.motives.fvars.length + priorPos)]
        have hmotivesCount :
            H.params.fvars.length + H.bindings.motives.fvars.length +
                priorPos - H.params.fvars.length =
              H.bindings.motives.fvars.length + priorPos := by omega
        rw [hmotivesCount, List.take_of_length_le (by omega)]
        have hminorCount :
            H.params.fvars.length + H.bindings.motives.fvars.length +
                priorPos -
                  (H.params.fvars ++ H.bindings.motives.fvars).length =
              priorPos := by
          simp only [List.length_append]
          omega
        rw [hminorCount, List.take_take,
          Nat.min_eq_left (Nat.le_of_lt hpriorPos)]
      have HprefixCanonical :=
        LocalContext.mkForall_fvars_forallBinderAt hsourceDecls hsourceNodup
          position hposition D.index D.userName D.type D.binderInfo D.kind (by
            rw [hsourceAt]
            exact D.declaration)
          (body := (.sort (.zero : Level)))
      have HrecursorCanonical :=
        selections.minorBinderAt hselectionNoAlias D
      dsimp only at HrecursorCanonical
      rw [← (H.generated.entry owner howner).type] at HrecursorCanonical
      have hstatsPosition : stats.params.size +
          (H.recInfos.map (·.motive)).size + priorPos = position := by
        rw [← H.params.length_fvars,
          ← H.bindings.motives.length_fvars]
        exact hpositionEq
      rw [hstatsPosition] at HrecursorCanonical
      have hprefixDomain : prefixDomain = D.type.abstractList
          (H.params.fvars ++ H.bindings.motives.fvars ++
            H.bindings.flatMinors.fvars.take priorPos) := by
        rw [← htake]
        exact Hprefix.unique HprefixCanonical
      exact hprefixDomain.trans
        (Hrecursor.unique HrecursorCanonical).symm

/-- The independently narrowed selected-minor source prefix and the
production recursor have the same domain at every retained parameter,
motive, and earlier-minor slot. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorPrefixBinderEq
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∀ position (hposition : position < sourceBinders.length)
      {prefixDomain recursorDomain : Expr},
      Expr.ForallBinderAt
        (H.localContext.lctx.mkForall
          (sourceBinders.map Expr.fvar).toArray
          (.sort (.zero : Level))) position prefixDomain →
      Expr.ForallBinderAt
        (H.generated.entry owner howner).info.type position recursorDomain →
      prefixDomain = recursorDomain := by
  dsimp only
  let minorIdx := recursorMinorOffset indTypes owner + i
  apply A.finalMinorPrefixBinderEq minorIdx
  rw [H.bindings.flatMinors.length_fvars]
  exact Nat.le_of_lt A.rule.minor_valid

/-- The exact semantic context retained by non-contiguous narrowing is
definitionally equal to the generated recursor's parameter/motive/earlier-
minor prefix.  This closes the dependent outer-context conversion needed to
type the canonical rule right-hand side. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedMinorPrefixDefEqCtx
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
        scope.fvars = sourceBinders.reverse ∧
        Hscope.shift = fvarSelectionLift H.recursorWF.mlctx.vlctx.fvars
          (· ∈ sourceBinders) ∧
        (∀ body,
          Hscope.sources.closeSource body =
            H.localContext.lctx.mkForall
              (sourceBinders.map Expr.fvar).toArray body) ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
          (T.params ++ T.motives ++ T.minors.take minorIdx).reverse := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let sourceBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  rcases A.finalSelectedMinorExactPrefixSource with
    ⟨T, scope, Hscope, prefixSource, hscope, hscopeShift, hscopeSource,
      hprefixSource, hprefixLocal, _HprefixTr, _HprefixType, HprefixTelescope,
      hselectedLength⟩
  let fullDomains := T.params ++ T.motives ++ T.minors ++
    T.indices ++ T.major
  let selectedDomains := T.params ++ T.motives ++ T.minors.take minorIdx
  have hminor : minorIdx < T.minors.length := by
    rw [T.minors_length]
    exact A.rule.minor_valid
  have hscopeDomainsLength : scope.toCtx.reverse.length = scope.length := by
    simpa using Hscope.toCtx_length
  have hfullLength : fullDomains.length =
      stats.params.size + (H.recInfos.map (·.motive)).size +
        (H.recInfos.flatMap (·.minors)).size +
          H.recInfos[owner]!.indices.size + 1 := by
    simp only [fullDomains, List.length_append, T.params_length,
      T.motives_length, T.minors_length, T.indices_length, T.major_length]
  have hselectedArity : selectedDomains.length = sourceBinders.length := by
    simp only [selectedDomains, sourceBinders, List.length_append,
      List.length_take]
    rw [H.params.length_fvars, H.bindings.motives.length_fvars,
      H.bindings.flatMinors.length_fvars,
      T.params_length, T.motives_length, T.minors_length]
  have hscopeArity : sourceBinders.length = scope.length := by
    calc
      sourceBinders.length = sourceBinders.reverse.length := by simp
      _ = scope.fvars.length := congrArg List.length hscope.symm
      _ = scope.length := Hscope.fvars_length
  have Hctx := HprefixTelescope.commonPrefixDefEqCtx H.outVEnvWF T.typed
    scope.toCtx.reverse fullDomains (.sort (.zero : VLevel)) T.result
    rfl
    (by simpa [fullDomains, List.append_assoc] using T.target_eq)
    hscopeDomainsLength hfullLength sourceBinders.length
    (Nat.le_of_eq hscopeArity) (by
      have hselectedLeFull : selectedDomains.length ≤ fullDomains.length := by
        have htakeLe := List.length_take_le minorIdx T.minors
        simp only [selectedDomains, fullDomains, List.length_append] at ⊢
        omega
      calc
        sourceBinders.length = selectedDomains.length := hselectedArity.symm
        _ ≤ fullDomains.length := hselectedLeFull
        _ = stats.params.size + (H.recInfos.map (·.motive)).size +
            (H.recInfos.flatMap (·.minors)).size +
              H.recInfos[owner]!.indices.size + 1 := hfullLength) (by
        intro position hposition _hiPrefix _hiRecursor
          prefixDomain recursorDomain HprefixBinder HrecursorBinder
        apply A.finalSelectedMinorPrefixBinderEq position hposition
        · rw [← hprefixLocal]
          exact HprefixBinder
        · exact HrecursorBinder)
  have htakeScope : (scope.toCtx.reverse).take sourceBinders.length =
      scope.toCtx.reverse := by
    rw [hscopeArity, ← hscopeDomainsLength]
    exact List.take_length
  have htakeFull : fullDomains.take sourceBinders.length =
      selectedDomains := by
    rw [← hselectedArity]
    rw [show fullDomains =
        selectedDomains ++
          (T.minors.drop minorIdx ++ T.indices ++ T.major) by
      have hsplit := (List.take_append_drop minorIdx T.minors).symm
      simpa only [fullDomains, selectedDomains, List.append_assoc] using
        congrArg (fun minors =>
          T.params ++ T.motives ++ minors ++ T.indices ++ T.major) hsplit]
    exact List.take_append_length
  rw [htakeScope, htakeFull] at Hctx
  exact ⟨T, scope, Hscope, hscope, hscopeShift, hscopeSource, by
    simpa [selectedDomains, List.reverse_append, List.append_assoc] using
      Hctx⟩

/-- The complete dependency-selected outer semantic scope is definitionally
equal to the generated recursor's full parameter/motive/minor prefix.  This
is the all-minors analogue of `finalSelectedMinorPrefixDefEqCtx`; indices and
majors are excluded even when their executable declarations are interleaved
with the retained outer locals. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOuterPrefixDefEqCtx
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
    let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ scope,
      ∃ Hscope : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us scope H.recursorWF.mlctx.vlctx,
        scope.fvars = outerBinders.reverse ∧
        Hscope.shift = fvarSelectionLift
          H.recursorWF.mlctx.vlctx.fvars (· ∈ outerBinders) ∧
        (∀ body,
          Hscope.sources.closeSource body =
            H.localContext.lctx.mkForall
              (outerBinders.map Expr.fvar).toArray body) ∧
        VEnv.IsDefEqCtx H.outVEnv Us.length [] scope.toCtx
          (T.params ++ T.motives ++ T.minors).reverse := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars
  rcases A.finalRecursorTelescopeTranslation with ⟨T⟩
  rcases A.finalOuterNarrowScope with
    ⟨scope, Hscope, hscope, hscopeShift, hscopeSource⟩
  rcases Hscope.closedSortTranslation H.outVEnvWF with
    ⟨Hprefix, _HprefixType⟩
  have HprefixTelescope := Hscope.closedSortTelescope H.outVEnvWF
  let fullDomains := T.params ++ T.motives ++ T.minors ++
    T.indices ++ T.major
  let outerDomains := T.params ++ T.motives ++ T.minors
  have hscopeDomainsLength : scope.toCtx.reverse.length = scope.length := by
    simpa using Hscope.toCtx_length
  have houterArity : outerBinders.length = scope.length := by
    calc
      outerBinders.length = outerBinders.reverse.length := by simp
      _ = scope.fvars.length := congrArg List.length hscope.symm
      _ = scope.length := Hscope.fvars_length
  have houterDomains : outerDomains.length = outerBinders.length := by
    simp only [outerDomains, outerBinders, List.length_append]
    rw [H.params.length_fvars, H.bindings.motives.length_fvars,
      H.bindings.flatMinors.length_fvars,
      T.params_length, T.motives_length, T.minors_length]
  have hfullLength : fullDomains.length =
      stats.params.size + (H.recInfos.map (·.motive)).size +
        (H.recInfos.flatMap (·.minors)).size +
          H.recInfos[owner]!.indices.size + 1 := by
    simp only [fullDomains, List.length_append, T.params_length,
      T.motives_length, T.minors_length, T.indices_length, T.major_length]
  have Hctx := HprefixTelescope.commonPrefixDefEqCtx H.outVEnvWF T.typed
    scope.toCtx.reverse fullDomains (.sort (.zero : VLevel)) T.result
    rfl
    (by simpa [fullDomains, List.append_assoc] using T.target_eq)
    hscopeDomainsLength hfullLength outerBinders.length
    (Nat.le_of_eq houterArity) (by
      calc
        outerBinders.length = outerDomains.length := houterDomains.symm
        _ ≤ fullDomains.length := by
          simp [outerDomains, fullDomains]
        _ = stats.params.size + (H.recInfos.map (·.motive)).size +
            (H.recInfos.flatMap (·.minors)).size +
              H.recInfos[owner]!.indices.size + 1 := hfullLength) (by
        have HbinderEq := A.finalMinorPrefixBinderEq
          H.bindings.flatMinors.fvars.length (Nat.le_refl _)
        simp only [List.take_length] at HbinderEq
        intro position hposition _hiPrefix _hiRecursor
          prefixDomain recursorDomain HprefixBinder HrecursorBinder
        apply HbinderEq position hposition
        · rw [← hscopeSource (.sort (.zero : Level))]
          exact HprefixBinder
        · exact HrecursorBinder)
  have htakeScope : (scope.toCtx.reverse).take outerBinders.length =
      scope.toCtx.reverse := by
    rw [houterArity, ← hscopeDomainsLength]
    exact List.take_length
  have htakeFull : fullDomains.take outerBinders.length = outerDomains := by
    rw [← houterDomains]
    change (outerDomains ++ T.indices ++ T.major).take outerDomains.length = _
    simp
  rw [htakeScope, htakeFull] at Hctx
  exact ⟨T, scope, Hscope, hscope, hscopeShift, hscopeSource, by
    simpa [outerDomains, List.reverse_append, List.append_assoc] using Hctx⟩

/-- Translate the original constructor tail directly in the complete outer
scope.  This gives a source-stable field telescope over the same generated
parameter/motive/minor prefix used by the installed selected minor. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalOuterConstructorFieldTelescopeFor
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
        (T.params ++ T.motives ++ T.minors).reverse := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars
  rcases A.finalOuterPrefixDefEqCtx with
    ⟨T₁, outerScope, Houter, houterFVars, houterShift,
      _houterSource, HouterPrefix⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams, hmotives, hminors] at HouterPrefix
  have hbase : H.recursorWF.venv ≤ H.outVEnv := by
    rw [H.recursorEnv]
    exact H.installed.le
  let E := A.semantics.fieldRootExtension
  have Hruntime : TrExprS H.outVEnv Us H.recursorWF.mlctx.vlctx
      A.semantics.parameterTail
        (A.semantics.parameterTarget.lift' (E.shift.consN 0)) :=
    (E.weakTrExprS A.semantics.parameterTranslation).mono hbase
  have HruntimeType : H.outVEnv.IsType Us.length
      H.recursorWF.mlctx.vlctx.toCtx
        (A.semantics.parameterTarget.lift' (E.shift.consN 0)) :=
    (E.weakIsType A.semantics.parameterType).mono hbase
  have hclosed : Closed A.semantics.parameterTail 0 := by
    have h := Hruntime.closed
    rw [H.recursorWF.mlctx.noBV] at h
    exact h
  have HtailFVars : A.semantics.parameterTail.FVarsIn
      (· ∈ outerScope.fvars) := by
    apply A.semantics.parameterTail_fvars.mono
    intro fv hfv
    rw [houterFVars]
    simp only [List.mem_reverse]
    exact List.mem_append_left _ (List.mem_append_left _ (by
      rw [← H.params.exprArrayFVarIds]
      exact hfv))
  rcases Houter.restrict H.outVEnvWF Hruntime hclosed HtailFVars with
    ⟨outerTarget, HouterTail⟩
  rcases HruntimeType with ⟨u, HruntimeType⟩
  have HouterType : H.outVEnv.HasType Us.length outerScope.toCtx
      outerTarget (.sort u) :=
    Houter.hasTypeOfFull H.outVEnvWF HouterTail Hruntime HruntimeType
  have Htyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS
    A.semantics.fieldOpening.telescope HouterTail
      (⟨u, HouterType⟩ : H.outVEnv.IsType Us.length
        outerScope.toCtx outerTarget)
  rcases Htyped.toWrapForalls with
    ⟨outerFields, _sourceResidual, outerResidual, houterFields,
      _Hsource, houterTarget, _Hresidual, _HresidualType⟩
  rw [houterTarget] at HouterTail HouterType
  exact ⟨outerScope, Houter, outerFields, outerResidual,
    houterFVars, houterShift, houterFields, HouterTail,
    ⟨u, HouterType⟩, HouterPrefix⟩

/-- The selected outer scope becomes the complete outer scope after the
selected minor and every later minor are restored as an anonymous dependent
prefix.  This is the base-context conversion underlying the natural
full-prefix field application. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.finalSelectedToOuterPrefixDefEqCtx
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
    let minorIdx := recursorMinorOffset indTypes owner + i
    let selectedBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars
    ∃ T : GeneratedRecursorTelescopeTranslation H.outVEnv Us
        (H.generated.entry owner howner).info.type H.entries[owner].2.type
        stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size
        H.recInfos[owner]!.indices.size owner,
      ∃ selectedScope,
      ∃ Hselected : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us selectedScope H.recursorWF.mlctx.vlctx,
      ∃ outerScope,
      ∃ Houter : checkInductiveTypes.loopType.FVarNarrowScope
          H.outVEnv Us outerScope H.recursorWF.mlctx.vlctx,
        selectedScope.fvars = selectedBinders.reverse ∧
        Hselected.shift = fvarSelectionLift
          H.recursorWF.mlctx.vlctx.fvars (· ∈ selectedBinders) ∧
        outerScope.fvars = outerBinders.reverse ∧
        Houter.shift = fvarSelectionLift
          H.recursorWF.mlctx.vlctx.fvars (· ∈ outerBinders) ∧
        let remaining := (T.minors.drop minorIdx).reverse
        VEnv.IsDefEqCtx H.outVEnv Us.length []
          (remaining ++ selectedScope.toCtx) outerScope.toCtx := by
  dsimp only
  let Us := AddInductive.getRecLevelParams H.elimLevel c.lparams
  let minorIdx := recursorMinorOffset indTypes owner + i
  let selectedBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars.take minorIdx
  let outerBinders := H.params.fvars ++ H.bindings.motives.fvars ++
    H.bindings.flatMinors.fvars
  rcases A.finalSelectedMinorPrefixDefEqCtx with
    ⟨T, selectedScope, Hselected, hselectedFVars, hselectedShift,
      _hselectedSource, HselectedPrefix⟩
  rcases A.finalOuterPrefixDefEqCtx with
    ⟨T₁, outerScope, Houter, houterFVars, houterShift,
      _houterSource, HouterPrefix⟩
  rcases T₁.groupsResult_eq T with
    ⟨hparams, hmotives, hminors, _hindices, _hmajor, _hresult⟩
  rw [hparams, hmotives, hminors] at HouterPrefix
  let selectedBase := T.params ++ T.motives ++ T.minors.take minorIdx
  let remaining := (T.minors.drop minorIdx).reverse
  have hfullContext : remaining ++ selectedBase.reverse =
      (T.params ++ T.motives ++ T.minors).reverse := by
    have hsplit := List.take_append_drop minorIdx T.minors
    have hminors : T.minors.reverse = remaining ++
        (T.minors.take minorIdx).reverse := by
      simpa only [remaining, List.reverse_append] using
        congrArg List.reverse hsplit.symm
    simp only [selectedBase, List.reverse_append]
    rw [← List.append_assoc, hminors]
  have HouterPrefix' : VEnv.IsDefEqCtx H.outVEnv Us.length []
      outerScope.toCtx (remaining ++ selectedBase.reverse) := by
    rw [hfullContext]
    exact HouterPrefix
  have Hremaining : OnCtx (remaining ++ selectedBase.reverse)
      (H.outVEnv.IsType Us.length) := by
    have Hprefix := T.prefixContext H.outVEnvWF.ordered
    have hsplit := List.take_append_drop minorIdx T.minors
    have hminors : T.minors.reverse = remaining ++
        (T.minors.take minorIdx).reverse := by
      simpa only [remaining, List.reverse_append] using
        congrArg List.reverse hsplit.symm
    simp only [List.reverse_append] at Hprefix
    rw [hminors] at Hprefix
    simpa [selectedBase, remaining, List.reverse_append,
      List.append_assoc] using Hprefix
  have HselectedExtended :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.extendSamePrefix
      (HselectedPrefix.symm H.outVEnvWF.ordered) Hremaining
  have HselectedExtended' := HselectedExtended.symm H.outVEnvWF.ordered
  have Hbridge := VEnv.IsDefEqCtx.transEmpty H.outVEnvWF
    HselectedExtended' (HouterPrefix'.symm H.outVEnvWF.ordered)
  exact ⟨T, selectedScope, Hselected, outerScope, Houter,
    hselectedFVars, hselectedShift, houterFVars, houterShift, by
      simpa [selectedBase, remaining, List.append_assoc] using Hbridge⟩

/-- Invert the flattened minor lookup at this rule's canonical offset.  The
row owner and row-local slot recovered from the retained declaration are the
same owner/constructor coordinates used by the rule traversal. -/
theorem
    CompletedRecursorPhasesResult.GeneratedRuleAlignment.selectedMinorOriginPosition
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
    {D : BoundFVarDeclarationAt H.localContext
      (H.recInfos.flatMap (·.minors))
      (recursorMinorOffset indTypes owner + i)}
    (O : H.origins.FlatMinorOrigin D) :
    O.owner = owner ∧ O.localIndex = i := by
  let minorIdx := recursorMinorOffset indTypes owner + i
  let originIdx := recursorMinorOffset indTypes O.owner + O.localIndex
  have hsizes : H.recInfos.size = indTypes.size := by
    calc
      H.recInfos.size = decl.types.length := H.cardinality.records
      _ = indTypes.toList.length :=
        (Lean4Lean.VerifyInductive.TrInductDeclCore.types_length R.core).symm
      _ = indTypes.size := by simp
  have horiginOwner : O.owner < indTypes.size := by
    rw [← hsizes]
    exact O.owner_lt
  have horiginLocal : O.localIndex < indTypes[O.owner]!.ctors.length := by
    rw [← H.minorCounts O.owner O.owner_lt]
    simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt
  have horiginRoom := recursorMinorOffset_room indTypes O.owner horiginOwner
  have hflatSize : (H.recInfos.flatMap (·.minors)).size =
      (indTypes.flatMap fun type => type.ctors.toArray).size :=
    mkRecInfos.flatMinors_size hsizes H.minorCounts
  have horiginIdx : originIdx <
      (H.recInfos.flatMap (·.minors)).size := by
    have hconcrete : originIdx <
        (indTypes.toList.flatMap (fun type => type.ctors)).length := by
      dsimp only [originIdx]
      omega
    rw [hflatSize, ← ownedConstructors_length_eq_flattened_size]
    simpa [ownedConstructors, List.length_flatMap] using hconcrete
  have hrecInfo : owner < H.recInfos.size := by
    simpa [H.generated.length] using howner
  let selections := H.bindings.toRecursorLocalSelections H.localWF H.params
    owner hrecInfo
  have hnoalias : selections.NoAlias :=
    H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner hrecInfo
  have hflatNodup :
      (H.recInfos.flatMap (·.minors)).toList.Nodup := by
    rw [H.bindings.flatMinors.expressions]
    have mapFVarNodup : ∀ xs : List FVarId, xs.Nodup →
        (xs.map Expr.fvar).Nodup := by
      intro xs hxs
      induction hxs with
      | nil => exact .nil
      | @cons fv xs hnotmem _ ih =>
          exact .cons (by simpa using hnotmem) ih
    have hminorNodup : H.bindings.flatMinors.fvars.Nodup := by
      simpa [selections, RecInfoBindings.toRecursorLocalSelections,
        BoundFVarArray.toLocalForallSelection] using hnoalias.parts.minors
    exact mapFVarNodup _ hminorNodup
  have htoListFlatMap :
      (H.recInfos.flatMap (·.minors)).toList =
        H.recInfos.toList.flatMap (fun info => info.minors.toList) := by
    exact Array.toList_flatMap
  have horiginIdxRows : originIdx <
      (H.recInfos.toList.flatMap
        (fun info => info.minors.toList)).length := by
    rw [← htoListFlatMap, Array.length_toList]
    exact horiginIdx
  have horiginIdxList : originIdx <
      (H.recInfos.flatMap (·.minors)).toList.length := by
    rw [Array.length_toList]
    exact horiginIdx
  have hminorIdxList : minorIdx <
      (H.recInfos.flatMap (·.minors)).toList.length := by
    rw [Array.length_toList]
    simpa [minorIdx] using D.inBounds
  have horiginLocalList : O.localIndex <
      H.recInfos[O.owner].minors.toList.length := by
    simpa using O.local_lt
  have HoriginGet := List.flatMap_getElem_prefix H.recInfos.toList
    (fun info => info.minors.toList) O.owner O.localIndex
    (by simpa using O.owner_lt)
    (by simpa [getElem!_pos H.recInfos O.owner O.owner_lt] using O.local_lt)
    (by
      rw [H.minorPrefixLength_eq O.owner (Nat.le_of_lt O.owner_lt)]
      simpa [originIdx] using horiginIdxRows)
  have HoriginGet' :
      (H.recInfos.flatMap (·.minors)).toList[originIdx]'horiginIdxList =
        H.recInfos[O.owner].minors.toList[O.localIndex]'horiginLocalList := by
    simpa [Array.toList_flatMap, originIdx,
      H.minorPrefixLength_eq O.owner (Nat.le_of_lt O.owner_lt)] using
      HoriginGet
  have hvalue :
      (H.recInfos.flatMap (·.minors)).toList[originIdx]'horiginIdxList =
        (H.recInfos.flatMap (·.minors)).toList[minorIdx]'hminorIdxList := by
    calc
      _ = H.recInfos[O.owner].minors.toList[O.localIndex]'horiginLocalList :=
        HoriginGet'
      _ = (H.recInfos.flatMap (·.minors)).toList[minorIdx]'hminorIdxList := by
        simpa only [Array.getElem_toList] using O.expression_eq
  have hposition : originIdx = minorIdx :=
    (List.getElem_inj (h₀ := horiginIdxList)
      (h₁ := hminorIdxList) hflatNodup).mp hvalue
  have hownerEq : O.owner = owner := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hmono := recursorMinorOffset_mono indTypes (O.owner + 1)
          owner (by omega) (by omega)
      have hstep := recursorMinorOffset_step indTypes O.owner horiginOwner
      dsimp only [originIdx, minorIdx] at hposition
      rw [hstep] at hmono
      omega
    · have hownerSource : owner < indTypes.size := by omega
      have hmono := recursorMinorOffset_mono indTypes (owner + 1)
          O.owner (by omega) (by omega)
      have hstep := recursorMinorOffset_step indTypes owner hownerSource
      dsimp only [originIdx, minorIdx] at hposition
      rw [hstep] at hmono
      omega
  refine ⟨hownerEq, ?_⟩
  dsimp only [originIdx, minorIdx] at hposition
  rw [hownerEq] at hposition
  omega


end VerifyInductive
end Lean4Lean
