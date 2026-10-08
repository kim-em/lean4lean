import Lean4Lean.Verify.Inductive.CompletedConstructorReplay
import Lean4Lean.Verify.Inductive.Nested.Compilation
import Lean4Lean.Verify.Inductive.Recursor.ReplayCompat
import Lean4Lean.Verify.Inductive.TypeAnnotations

import Lean4Lean.Verify.Inductive.CompletedSourceSignature

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace VerifyInductive

/-- Retained executable recursor construction before abstract targets are
selected and installed. Every canonical translation is derived at this
boundary from the shared source signature and these construction traces. -/
structure CompletedRecursorConstruction
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv : Environment}
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    where
  sourceSafety : isUnsafe = (c.safety != .safe)
  elimLevel : Level
  elimLevelAdmissible : AddInductive.AdmissibleElimLevel c.lparams elimLevel
  /-- Retain the actual elimination decision in the constructor-stage context.
  Freshness of a universe parameter alone does not justify large elimination. -/
  elimLevelChecked : AddInductive.getElimLevel stats indTypes
    { c with env := ctorEnv } = .ok elimLevel
  lparamsNodup : c.lparams.Nodup
  kTarget : Bool
  kTargetChecked : KTargetCheck stats indTypes kTarget
  recInfos : Array AddInductive.RecInfo
  localContext : AddInductive.Context
  localWF : BindingContextWF localContext
  localExtends : BindingContextLE { c with
    env := ctorEnv
    typeCheckerLParams := some <|
      AddInductive.getRecLevelParams elimLevel c.lparams } localContext
  recursorDepth : Nat
  recursorWF : RecursorContextWF localContext
    (AddInductive.getRecLevelParams elimLevel c.lparams)
  recursorEnv : recursorWF.venv = R.context.venv
  /-- The executable type-checks every generated recursor type before any
  recursor is installed.  These translations are the only derivations of the
  closed recursor telescopes available before installation: the minor
  premises mention motives, so their translations cannot be rebuilt from the
  free-variable contexts of the first pass without strengthening. -/
  recursorTypes : RecursorTypeTranslations R.context.venv localContext.lparams elimLevel
    localContext stats indTypes recInfos
  parameterSuffix : RecursorParameterContextSuffix recursorWF stats
    recursorDepth
  parameterDecls : parameterSuffix.parameterDecls =
    (R.materializedFinal.parameterSuffix.toRecursorContext
      elimLevelAdmissible).parameterDecls
  validStats : RecursorValidAppStatsWF recursorWF.venv
    (AddInductive.getRecLevelParams elimLevel c.lparams)
    recursorWF.mlctx.vlctx stats decl recursorDepth
  noIndConsts : VLCtx.NoIndConsts (decl.types.map (·.name))
    recursorWF.mlctx.vlctx
  bindings : RecInfoBindings localContext recInfos
  origins : RecInfoTypeOrigins localContext recInfos
  blueprints : RecInfoRuleBlueprintOrigins stats recInfos origins
  blueprintSemantics : RecInfoRuleBlueprintSemanticOrigins recursorWF decl
    stats recInfos elimLevel parameterSuffix.parameterDecls origins
  minorSources : RecInfoMinorSourceAlignment stats indTypes origins
  minorSemantics : RecInfoMinorSemanticAlignment recursorWF origins
    parameterSuffix.parameterDecls
  majorTypes : RecursorTranslatedOriginTypes recursorWF origins.majorTypes
  majorShapes : RecInfoMajorTypeShapes stats recInfos origins.majorTypes
  motiveTypes : RecursorTranslatedOriginTypes recursorWF origins.motiveTypes
  motiveShapes : RecInfoMotiveTypeShapes localContext recInfos
    origins.motiveTypes elimLevel
  motiveTelescopes : RecInfoMotiveTelescopes recursorWF stats decl
    (R.materializedFinal.parameterSuffix.toRecursorContext
      elimLevelAdmissible).parameterDecls.toCtx recInfos elimLevel
  indexRows : RecursorTranslatedOriginTypeRows recursorWF origins.indexTypes
  params : BoundFVarArray localContext stats.params
  noAlias : bindings.NoAlias params
  outerOrder : RecInfoOuterOrder recursorWF params bindings
  arities : RecInfoArities stats recInfos
  minorCounts : forall i, i < recInfos.size ->
    recInfos[i]!.minors.size = indTypes[i]!.ctors.length
  cardinality : RecursorCardinalityCertificate stats recInfos decl

/-- Fix the source signature's universe instance before selecting any
abstract recursor entry. -/
noncomputable def CompletedConstructorPhases.sourceGeneration
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (elimLevel : Level) (helim : AddInductive.AdmissibleElimLevel c.lparams elimLevel) :
    InductiveSignature.Instance R.sourceSignature where
  uvars := (AddInductive.getRecLevelParams elimLevel c.lparams).length
  levels := recursorDeclarationAbstractLevels c.lparams helim
  targetLevel := Classical.choose helim.ofLevel
  recursorName owner := R.sourceSignature.families[owner].name.str "rec"

theorem CompletedConstructorPhases.sourceSignature_familyCount
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv) : R.sourceSignature.families.size = indTypes.size := by
  have h := Lean4Lean.List.Forall₂.length_eq R.core.types
  simpa [ConstructorBoundary.sourceSignature,
    ConstructorBoundary.sourceSignatureHeader,
    checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureHeader] using h.symm

end VerifyInductive
end Lean4Lean
