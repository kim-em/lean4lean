import Lean4Lean.Verify.Inductive.Nested.Restoration

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Source-facing realization of a restored family telescope.  Unlike
`RestoredFamilySemantics`, this companion package retains the concrete source
family expression and its exact translation to the semantic family head.
This is the connection later motive, major, and index-domain proofs need. -/
structure RestoredFamilyRealization
    (env : VEnv) (levelParams : List Name)
    (parameterDomains : List VExpr) (numIndices : Nat)
    (sourceFamily : Expr) where
  semantics : RestoredFamilySemantics env levelParams parameterDomains
    numIndices
  sourceTranslation : TrExprS env levelParams
    (abstractForallContext parameterDomains []) sourceFamily semantics.family

/-- Source-facing realization of a family with genuine indices.  Besides the
family head retained by `RestoredFamilyRealization`, this package keeps one
literal concrete source index telescope and its binder-by-binder translation
to the independently reconstructed semantic index domains.  The residual
after those domains is retained but deliberately left opaque: rebuilding a
motive or index slot uses the exact domains, not the first pass's residual.
The motive translation itself is deliberately not stored. -/
structure RestoredIndexedFamilyRealization
    (env : VEnv) (levelParams : List Name)
    (parameterDomains : List VExpr) (numIndices : Nat)
    (sourceFamily sourceIndexType : Expr) where
  family : RestoredFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily
  indexResidual : VExpr
  indexTypeTranslation : Expr.ForallTelescopeTypeTranslation env levelParams
    (abstractForallContext parameterDomains []) sourceIndexType numIndices
    (VExpr.wrapForalls family.semantics.indexDomains
      indexResidual)

/-- The concrete canonical variables used after closing an index telescope,
in source binder order. -/
def sourceCanonicalVars (n : Nat) : List Expr :=
  List.ofFn fun i : Fin n => .bvar (n - 1 - i)

@[simp] theorem sourceCanonicalVars_length (n : Nat) :
    (sourceCanonicalVars n).length = n := by
  simp [sourceCanonicalVars]

/-- Apply a retained concrete family head to the canonical variables of its
semantic index telescope.  This is the source-facing major-premise
translation shared by motive reconstruction and the final major slot. -/
theorem RestoredFamilyRealization.familyApplicationTranslation
    (H : RestoredFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily)
    (henv : env.WF)
    (hparams : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length)) :
    TrExprS env levelParams
      (abstractForallContext
        (parameterDomains ++ H.semantics.indexDomains) [])
      (Expr.mkAppList
        (sourceFamily.liftLooseBVars' 0 H.semantics.indexDomains.length)
        (sourceCanonicalVars H.semantics.indexDomains.length))
      (VExpr.mkApps
        (H.semantics.family.liftN H.semantics.indexDomains.length 0)
        (recursorCanonicalVars H.semantics.indexDomains.length)) := by
  let indexDomains := H.semantics.indexDomains
  have HfamilyWeak := H.sourceTranslation.weakBV henv.ordered
    (abstractForallContext.bvLift indexDomains
      (abstractForallContext parameterDomains []))
  have Hargs : List.Forall₂
      (TrExprS env levelParams
        (abstractForallContext (parameterDomains ++ indexDomains) []))
      (sourceCanonicalVars indexDomains.length)
      (recursorCanonicalVars indexDomains.length) := by
    rw [recursorCanonicalVars_eq_ofFn]
    apply TrExprS.canonicalBvars_of_abstractForallContext
    simp
  have Hctx : OnCtx
      (abstractForallContext (parameterDomains ++ indexDomains) []).toCtx
      (env.IsType levelParams.length) := by
    have HfamilyType := H.semantics.familyTyping.isType henv.ordered hparams
    have Hindices :=
      VEnv.IsType.wrapForalls_inv henv.ordered hparams HfamilyType
    simpa [abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append] using Hindices.1
  have Hwf : VExpr.WF env levelParams.length
      (abstractForallContext (parameterDomains ++ indexDomains) []).toCtx
      (VExpr.mkApps
        (H.semantics.family.liftN indexDomains.length 0)
        (recursorCanonicalVars indexDomains.length)) := by
    rcases H.semantics.familyApplicationType with ⟨familyLevel, Htyped⟩
    refine ⟨.sort familyLevel, ?_⟩
    change env.IsDefEq _ _ _ _ _
    change env.IsDefEq _ _ _ _ _ at Htyped
    simpa [indexDomains, abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append] using Htyped
  have Happlication := checkPositivityStep.TrExprS.mkAppList
    henv.ordered Hctx
    (by simpa [abstractForallContext_append] using HfamilyWeak)
    Hargs Hwf
  simpa [indexDomains] using Happlication

/-- An indexed family realization reconstructs its full concrete motive
domain from syntax-only telescope alignment.  The template supplies the
literal index domains and their independent translation; the retained family
head supplies the major-domain translation after applying the canonical
index variables.  No translation of the completed motive is assumed. -/
theorem RestoredIndexedFamilyRealization.motiveDomainTranslation
    (H : RestoredIndexedFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily sourceIndexType)
    (henv : env.WF)
    (hparams : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length))
    (sourceMotive : Expr) (sourceLevel : Level) (resultLevel : VLevel)
    (hlevel : VLevel.ofLevel levelParams sourceLevel = some resultLevel)
    (name : Name) (bi : BinderInfo)
    (Hsame : Expr.SameForallDomains numIndices sourceIndexType sourceMotive)
    (Hmotive : Expr.ForallTelescope sourceMotive numIndices
      (.forallE name
        (Expr.mkAppList
          (sourceFamily.liftLooseBVars' 0 numIndices)
          (sourceCanonicalVars numIndices))
        (.sort sourceLevel) bi)) :
    TrExprS env levelParams (abstractForallContext parameterDomains [])
      sourceMotive (H.family.semantics.motiveType resultLevel) := by
  let indexDomains := H.family.semantics.indexDomains
  have hindices : indexDomains.length = numIndices :=
    H.family.semantics.indexCount
  have Hsame' : Expr.SameForallDomains indexDomains.length
      sourceIndexType sourceMotive := by
    simpa [hindices] using Hsame
  have Hmotive' : Expr.ForallTelescope sourceMotive indexDomains.length
      (.forallE name
        (Expr.mkAppList
          (sourceFamily.liftLooseBVars' 0 indexDomains.length)
          (sourceCanonicalVars indexDomains.length))
        (.sort sourceLevel) bi) := by
    simpa [hindices] using Hmotive
  have HfamilyWeak := H.family.sourceTranslation.weakBV henv.ordered
    (abstractForallContext.bvLift indexDomains
      (abstractForallContext parameterDomains []))
  have Hargs : List.Forall₂
      (TrExprS env levelParams
        (abstractForallContext (parameterDomains ++ indexDomains) []))
      (sourceCanonicalVars indexDomains.length)
      (recursorCanonicalVars indexDomains.length) := by
    rw [recursorCanonicalVars_eq_ofFn]
    apply TrExprS.canonicalBvars_of_abstractForallContext
    simp
  have HfamilyApplication : TrExprS env levelParams
      (abstractForallContext (parameterDomains ++ indexDomains) [])
      (Expr.mkAppList
        (sourceFamily.liftLooseBVars' 0 indexDomains.length)
        (sourceCanonicalVars indexDomains.length))
      (VExpr.mkApps
        (H.family.semantics.family.liftN indexDomains.length 0)
        (recursorCanonicalVars indexDomains.length)) := by
    have Hctx : OnCtx
        (abstractForallContext (parameterDomains ++ indexDomains) []).toCtx
        (env.IsType levelParams.length) := by
      have HfamilyType := H.family.semantics.familyTyping.isType
        henv.ordered hparams
      have Hindices :=
        VEnv.IsType.wrapForalls_inv henv.ordered hparams HfamilyType
      simpa [abstractForallContext_toCtx, VLCtx.toCtx,
        List.reverse_append] using Hindices.1
    have Hwf : VExpr.WF env levelParams.length
        (abstractForallContext (parameterDomains ++ indexDomains) []).toCtx
        (VExpr.mkApps
          (H.family.semantics.family.liftN indexDomains.length 0)
          (recursorCanonicalVars indexDomains.length)) := by
      rcases H.family.semantics.familyApplicationType with
        ⟨familyLevel, Htyped⟩
      refine ⟨.sort familyLevel, ?_⟩
      change env.IsDefEq _ _ _ _ _
      change env.IsDefEq _ _ _ _ _ at Htyped
      simpa [indexDomains, abstractForallContext_toCtx, VLCtx.toCtx,
        List.reverse_append] using Htyped
    have Happlication := checkPositivityStep.TrExprS.mkAppList
      henv.ordered Hctx
      (by simpa [abstractForallContext_append] using HfamilyWeak)
      Hargs Hwf
    simpa using Happlication
  have HmajorType : env.IsType levelParams.length
      (abstractForallContext (parameterDomains ++ indexDomains) []).toCtx
      (VExpr.mkApps
        (H.family.semantics.family.liftN indexDomains.length 0)
        (recursorCanonicalVars indexDomains.length)) := by
    simpa [abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append] using
      H.family.semantics.familyApplicationType
  have HsortType : env.IsType levelParams.length
      ((VExpr.mkApps
          (H.family.semantics.family.liftN indexDomains.length 0)
          (recursorCanonicalVars indexDomains.length)) ::
        (abstractForallContext
          (parameterDomains ++ indexDomains) []).toCtx)
      (.sort resultLevel) :=
    ⟨.succ resultLevel, VEnv.HasType.sort (.of_ofLevel hlevel)⟩
  have Hresidual : TrExprS env levelParams
      (abstractForallContext (parameterDomains ++ indexDomains) [])
      (.forallE name
        (Expr.mkAppList
          (sourceFamily.liftLooseBVars' 0 indexDomains.length)
          (sourceCanonicalVars indexDomains.length))
        (.sort sourceLevel) bi)
      (.forallE
        (VExpr.mkApps
          (H.family.semantics.family.liftN indexDomains.length 0)
          (recursorCanonicalVars indexDomains.length))
        (.sort resultLevel)) :=
    .forallE HmajorType HsortType HfamilyApplication (.sort hlevel)
  have HresidualType : env.IsType levelParams.length
      (abstractForallContext (parameterDomains ++ indexDomains) []).toCtx
      (.forallE
        (VExpr.mkApps
          (H.family.semantics.family.liftN indexDomains.length 0)
          (recursorCanonicalVars indexDomains.length))
        (.sort resultLevel)) :=
    .forallE HmajorType HsortType
  rcases H.indexTypeTranslation.telescope with
    ⟨sourceResidual, Htemplate⟩
  have Htemplate' : Expr.ForallTelescope sourceIndexType
      indexDomains.length sourceResidual := by
    simpa [hindices] using Htemplate
  have Hresidual' : TrExprS env levelParams
      (abstractForallContext indexDomains
        (abstractForallContext parameterDomains []))
      (.forallE name
        (Expr.mkAppList
          (sourceFamily.liftLooseBVars' 0 indexDomains.length)
          (sourceCanonicalVars indexDomains.length))
        (.sort sourceLevel) bi)
      (.forallE
        (VExpr.mkApps
          (H.family.semantics.family.liftN indexDomains.length 0)
          (recursorCanonicalVars indexDomains.length))
        (.sort resultLevel)) := by
    simpa only [abstractForallContext_append] using Hresidual
  have HresidualType' : env.IsType levelParams.length
      (abstractForallContext indexDomains
        (abstractForallContext parameterDomains [])).toCtx
      (.forallE
        (VExpr.mkApps
          (H.family.semantics.family.liftN indexDomains.length 0)
          (recursorCanonicalVars indexDomains.length))
        (.sort resultLevel)) := by
    simpa only [abstractForallContext_append] using HresidualType
  have Htranslated := Hsame'.replaceTranslatedResidual Htemplate' Hmotive'
    henv.ordered (by
      simpa [abstractForallContext_toCtx, VLCtx.toCtx] using hparams)
    rfl H.indexTypeTranslation.translation Hresidual' HresidualType'
  simpa [RestoredFamilySemantics.motiveType] using Htranslated

/-- Weakening the reconstructed indexed motive domain beneath an already
restored suffix preserves its literal source and canonical semantic target. -/
theorem RestoredIndexedFamilyRealization.motiveDomainTranslationAfter
    (H : RestoredIndexedFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily sourceIndexType)
    (henv : env.WF)
    (hparams : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length))
    (added : List VExpr)
    (sourceMotive : Expr) (sourceLevel : Level) (resultLevel : VLevel)
    (hlevel : VLevel.ofLevel levelParams sourceLevel = some resultLevel)
    (name : Name) (bi : BinderInfo)
    (Hsame : Expr.SameForallDomains numIndices sourceIndexType sourceMotive)
    (Hmotive : Expr.ForallTelescope sourceMotive numIndices
      (.forallE name
        (Expr.mkAppList
          (sourceFamily.liftLooseBVars' 0 numIndices)
          (sourceCanonicalVars numIndices))
        (.sort sourceLevel) bi)) :
    TrExprS env levelParams
      (abstractForallContext (parameterDomains ++ added) [])
      (sourceMotive.liftLooseBVars' 0 added.length)
      ((H.family.semantics.motiveType resultLevel).liftN added.length 0) := by
  have Hbase := H.motiveDomainTranslation henv hparams sourceMotive
    sourceLevel resultLevel hlevel name bi Hsame Hmotive
  have Hweak := Hbase.weakBV henv.ordered
    (abstractForallContext.bvLift added
      (abstractForallContext parameterDomains []))
  simpa only [abstractForallContext_append] using Hweak

/-- An indexless realization has no hidden semantic index domains. -/
theorem RestoredFamilyRealization.indexDomains_eq_nil
    (H : RestoredFamilyRealization env levelParams parameterDomains 0
      sourceFamily) :
    H.semantics.indexDomains = [] :=
  List.eq_nil_of_length_eq_zero H.semantics.indexCount

/-- For an indexless family, the concrete restored motive domain is exactly
the family source followed by its major binder and the motive result sort.
The retained source translation supplies the major domain; no postulated
family-syntax translation is needed. -/
theorem RestoredFamilyRealization.motiveDomainTranslationZero
    (H : RestoredFamilyRealization env levelParams parameterDomains 0
      sourceFamily)
    (sourceLevel : Level) (resultLevel : VLevel)
    (hlevel : VLevel.ofLevel levelParams sourceLevel = some resultLevel)
    (name : Name) (bi : BinderInfo) :
    TrExprS env levelParams (abstractForallContext parameterDomains [])
      (.forallE name sourceFamily (.sort sourceLevel) bi)
      (H.semantics.motiveType resultLevel) := by
  have hindices := H.indexDomains_eq_nil
  have HfamilyType : env.IsType levelParams.length
      (abstractForallContext parameterDomains []).toCtx H.semantics.family := by
    simpa [hindices, abstractForallContext_toCtx, VLCtx.toCtx,
      VExpr.mkApps] using H.semantics.familyApplicationType
  have HresultType : env.IsType levelParams.length
      (H.semantics.family ::
        (abstractForallContext parameterDomains []).toCtx)
      (.sort resultLevel) :=
    ⟨.succ resultLevel, VEnv.HasType.sort (.of_ofLevel hlevel)⟩
  have Hresult : TrExprS env levelParams
      ((none, .vlam H.semantics.family) ::
        abstractForallContext parameterDomains [])
      (.sort sourceLevel) (.sort resultLevel) :=
    .sort hlevel
  have Hdomain := TrExprS.forallE (name := name) (bi := bi)
    HfamilyType HresultType H.sourceTranslation Hresult
  simpa [RestoredFamilySemantics.motiveType, hindices,
    VExpr.wrapForalls, VExpr.mkApps] using Hdomain

/-- Weakening the zero-index motive-domain translation below an already
restored suffix preserves both the literal lifted source and the canonical
semantic motive type at the same depth. -/
theorem RestoredFamilyRealization.motiveDomainTranslationZeroAfter
    (H : RestoredFamilyRealization env levelParams parameterDomains 0
      sourceFamily)
    (henv : env.Ordered) (added : List VExpr)
    (sourceLevel : Level) (resultLevel : VLevel)
    (hlevel : VLevel.ofLevel levelParams sourceLevel = some resultLevel)
    (name : Name) (bi : BinderInfo) :
    TrExprS env levelParams
      (abstractForallContext (parameterDomains ++ added) [])
      ((Expr.forallE name sourceFamily (.sort sourceLevel) bi).liftLooseBVars'
        0 added.length)
      ((H.semantics.motiveType resultLevel).liftN added.length 0) := by
  have Hbase := H.motiveDomainTranslationZero sourceLevel resultLevel hlevel
    name bi
  have Hweak := Hbase.weakBV henv
    (abstractForallContext.bvLift added
      (abstractForallContext parameterDomains []))
  simpa only [abstractForallContext_append] using Hweak

end VerifyInductive
end Lean4Lean
