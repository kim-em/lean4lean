import Lean4Lean.Verify.Inductive.Recursor.CanonicalFieldReplay
import Lean4Lean.Verify.Inductive.Recursor.CanonicalSourceBounds
namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The field domains of each source-owned constructor are selected once
before installation, in the original universe and parameter scope. -/
noncomputable def CompletedRecursorConstruction.sourceFields
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) : List VExpr :=
  Classical.choose (H.sourceFieldDomains owner howner (by rwa [← H.sourceFamilyCount])
    localIndex hlocal (H.sourceMinorOffsetBound owner howner localIndex hlocal))

theorem CompletedRecursorConstruction.sourceFields_length
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    (H.sourceFields owner howner localIndex hlocal).length =
      (H.origins.minorShapes owner howner localIndex hlocal).fields.size :=
  (Classical.choose_spec (H.sourceFieldDomains owner howner (by rwa [← H.sourceFamilyCount])
    localIndex hlocal (H.sourceMinorOffsetBound owner howner localIndex hlocal))).1

theorem CompletedRecursorConstruction.sourceFields_headerReplay
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let source := (H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList H.params.fvars
    TrExprS R.headerVEnv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        source (VExpr.wrapForalls (H.sourceFields owner howner localIndex hlocal) (.sort .zero)) ∧
      R.headerVEnv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls (H.sourceFields owner howner localIndex hlocal) (.sort .zero)) ∧
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source
        (VExpr.wrapForalls
          ((H.sourceFields owner howner localIndex hlocal).map
            (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
          (.sort .zero)) :=
  (Classical.choose_spec (H.sourceFieldDomains owner howner (by rwa [← H.sourceFamilyCount])
    localIndex hlocal (H.sourceMinorOffsetBound owner howner localIndex hlocal))).2

theorem CompletedRecursorConstruction.sourceFields_replay
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[owner]!.size) :
    let S := H.origins.minorShapes owner howner localIndex hlocal
    let source := (H.localContext.lctx.mkForall S.fields (.sort .zero)).abstractList H.params.fvars
    TrExprS R.context.venv c.lparams (abstractForallContext R.parameterScope.toCtx.reverse [])
        source (VExpr.wrapForalls (H.sourceFields owner howner localIndex hlocal) (.sort .zero)) ∧
      R.context.venv.IsType c.lparams.length R.parameterScope.toCtx
        (VExpr.wrapForalls (H.sourceFields owner howner localIndex hlocal) (.sort .zero)) ∧
      TrExprS H.recursorWF.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext H.parameterSuffix.parameterDecls.toCtx.reverse []) source
        (VExpr.wrapForalls
          ((H.sourceFields owner howner localIndex hlocal).map
            (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
          (.sort .zero)) := by
  obtain ⟨Hsource, Htype, Hrec⟩ := H.sourceFields_headerReplay owner howner localIndex hlocal
  have Hle := R.installation.constructorLE.trans R.ctorLE
  exact ⟨Hsource.mono Hle, Htype.mono Hle, Hrec⟩

end Lean4Lean.VerifyInductive
