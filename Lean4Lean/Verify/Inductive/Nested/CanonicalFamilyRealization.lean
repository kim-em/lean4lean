import Lean4Lean.Verify.Inductive.Nested.GeneratedFamilySemantics

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Turn the canonical family telescope retained by the completed first
recursor pass into a concrete source-facing realization.  The concrete head
and parameter spine are fixed by the declaration and the executable level
and parameter arrays; only the independently installed family lookup is
needed to replay that syntax in the target environment.

This is the original-family counterpart of
`ClosedNestedAuxiliaryTranslation.toRestoredFamilyRealizationZero`: callers
do not supply an opaque translation of the family application. -/
def RecursorCanonicalMotiveTelescope.toRestoredFamilyRealization
    (C : RecursorCanonicalMotiveTelescope env levelParams stats decl target info
      elimLevel)
    (henv : env.WF)
    (parameterDomains : List VExpr)
    (Hparams : VEnv.IsDefEqCtx env levelParams.length [] C.params.reverse
      parameterDomains.reverse)
    (hparameterCtx : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length))
    (hlookup : env.constants (decl.types[target]'C.target_lt).name =
      some (decl.types[target]'C.target_lt).toVConstant) :
    RestoredFamilyRealization env levelParams parameterDomains
      info.indices.size
      (Expr.mkAppList
        (.const (decl.types[target]'C.target_lt).name stats.levels)
        (sourceCanonicalVars parameterDomains.length)) := by
  let semantics := C.toRestoredFamilySemantics henv.ordered
    parameterDomains Hparams
  have hparameterLength : parameterDomains.length = C.params.length := by
    simpa using Hparams.length_eq.symm
  have Hhead : TrExprS env levelParams
      (abstractForallContext parameterDomains [])
      (.const (decl.types[target]'C.target_lt).name stats.levels)
      (.const (decl.types[target]'C.target_lt).name C.levels) := by
    apply TrExprS.const hlookup C.levels_translation
    exact (checkPositivityStep.List.mapM_some_length
      C.levels_translation).trans C.levels_length
  have Hargs : List.Forall₂
      (TrExprS env levelParams
        (abstractForallContext parameterDomains []))
      (sourceCanonicalVars parameterDomains.length)
      (recursorCanonicalVars parameterDomains.length) := by
    rw [recursorCanonicalVars_eq_ofFn]
    exact TrExprS.canonicalBvars_of_abstractForallContext
      parameterDomains [] parameterDomains.length (by omega)
  have HfamilyTyping : env.HasType levelParams.length
      parameterDomains.reverse C.family
      (VExpr.wrapForalls C.indices C.familyResult) :=
    C.family_typing.defeqDFC henv.ordered Hparams
  have HfamilyWF : VExpr.WF env levelParams.length
      (abstractForallContext parameterDomains []).toCtx C.family := by
    refine ⟨VExpr.wrapForalls C.indices C.familyResult, ?_⟩
    change env.IsDefEq levelParams.length parameterDomains.reverse
      C.family C.family (VExpr.wrapForalls C.indices C.familyResult) at HfamilyTyping
    simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HfamilyTyping
  have Hsource : TrExprS env levelParams
      (abstractForallContext parameterDomains [])
      (Expr.mkAppList
        (.const (decl.types[target]'C.target_lt).name stats.levels)
        (sourceCanonicalVars parameterDomains.length))
      C.family := by
    have Happ := checkPositivityStep.TrExprS.mkAppList henv.ordered
      (by simpa [abstractForallContext_toCtx, VLCtx.toCtx] using hparameterCtx)
      Hhead Hargs
      (show VExpr.WF env levelParams.length
        (abstractForallContext parameterDomains []).toCtx
        (VExpr.mkApps
          (.const (decl.types[target]'C.target_lt).name C.levels)
          (recursorCanonicalVars parameterDomains.length)) from by
        simpa [C.family_eq, hparameterLength, VExpr.liftN] using HfamilyWF)
    simpa [C.family_eq, hparameterLength, VExpr.liftN] using Happ
  exact {
    semantics := semantics
    sourceTranslation := Hsource
  }

/-- Package an exact source index-prefix translation with the canonical
family realization.  This is the final constructor needed by the nested
suffix lemmas: its residual deliberately remains existential and may mention
the independently restored family. -/
def RecursorCanonicalMotiveTelescope.toRestoredIndexedFamilyRealization
    (C : RecursorCanonicalMotiveTelescope env levelParams stats decl target info
      elimLevel)
    (F : RestoredFamilyRealization env levelParams parameterDomains
      info.indices.size sourceFamily)
    (hindexDomains : F.semantics.indexDomains = C.indices)
    (Hindices : Expr.ForallTelescopeTypeTranslation env levelParams
      (abstractForallContext parameterDomains []) sourceIndexType
      info.indices.size
      (VExpr.wrapForalls C.indices indexResidual)) :
    RestoredIndexedFamilyRealization env levelParams parameterDomains
      info.indices.size sourceFamily sourceIndexType where
  family := F
  indexResidual := indexResidual
  indexTypeTranslation := by
    rw [hindexDomains]
    exact Hindices

/-- Construct the complete indexed realization in one step.  The family
head, universe instantiation, and common-parameter application are all
derived by `toRestoredFamilyRealization`; callers supply only the literal
source index telescope translated to the canonical index domains. -/
def RecursorCanonicalMotiveTelescope.toRestoredIndexedFamilyRealizationFromPrefix
    (C : RecursorCanonicalMotiveTelescope env levelParams stats decl target info
      elimLevel)
    (henv : env.WF)
    (parameterDomains : List VExpr)
    (Hparams : VEnv.IsDefEqCtx env levelParams.length [] C.params.reverse
      parameterDomains.reverse)
    (hparameterCtx : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length))
    (hlookup : env.constants (decl.types[target]'C.target_lt).name =
      some (decl.types[target]'C.target_lt).toVConstant)
    (Hindices : Expr.ForallTelescopeTypeTranslation env levelParams
      (abstractForallContext parameterDomains []) sourceIndexType
      info.indices.size (VExpr.wrapForalls C.indices indexResidual)) :
    RestoredIndexedFamilyRealization env levelParams parameterDomains
      info.indices.size
      (Expr.mkAppList
        (.const (decl.types[target]'C.target_lt).name stats.levels)
        (sourceCanonicalVars parameterDomains.length))
      sourceIndexType := by
  let F := C.toRestoredFamilyRealization henv parameterDomains Hparams
    hparameterCtx hlookup
  exact C.toRestoredIndexedFamilyRealization F (by rfl) Hindices

end VerifyInductive
end Lean4Lean
