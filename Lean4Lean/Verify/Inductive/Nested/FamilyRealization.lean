import Lean4Lean.Verify.Inductive.Nested.Restoration
import Lean4Lean.Verify.Inductive.Specification.Formation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Re-invert a typed concrete telescope after replacing its ambient local
context by a definitionally equal one.  The translated domains are allowed
to be reselected: dependent translation is unique only up to definitional
equality, and requiring literal preservation here would recreate the broad
alpha/preservation premise that nested restoration is meant to avoid. -/
theorem Expr.ForallTelescopeTypeTranslation.rebaseContext
    (H : Expr.ForallTelescopeTypeTranslation env levelParams sourceCtx
      source arity target)
    (henv : env.WF)
    (Hctx : VLCtx.IsDefEq env levelParams.length sourceCtx targetCtx) :
    ∃ target', Expr.ForallTelescopeTypeTranslation env levelParams
      targetCtx source arity target' := by
  rcases H.translation.defeqDFC henv Hctx with ⟨target', Htranslation⟩
  have HtargetType : env.IsType levelParams.length targetCtx.toCtx target :=
    H.isType.defeqDFC henv.ordered Hctx.defeqCtx
  have HtargetEq : env.IsDefEqU levelParams.length targetCtx.toCtx
      target' target :=
    Htranslation.uniq henv (Hctx.symm henv.ordered) H.translation
  have HtargetType' : env.IsType levelParams.length targetCtx.toCtx target' :=
    VEnv.IsType.defeqU_l henv (Hctx.symm henv.ordered).wf.toCtx HtargetEq.symm
      HtargetType
  rcases H.telescope with ⟨residual, Htelescope⟩
  exact ⟨target',
    Expr.ForallTelescopeTypeTranslation.ofTrExprS Htelescope Htranslation
      HtargetType'⟩

/-- Target-aware form of `rebaseContext`.  Besides rebuilding the
binder-by-binder certificate, retain the definitional equality relating its
newly selected target to the original target.  This lets a family typing
judgment travel with the exact producer telescope rather than being
reconstructed by a caller. -/
theorem Expr.ForallTelescopeTypeTranslation.rebaseContextWithTargetEq
    (H : Expr.ForallTelescopeTypeTranslation env levelParams sourceCtx
      source arity target)
    (henv : env.WF)
    (Hctx : VLCtx.IsDefEq env levelParams.length sourceCtx targetCtx) :
    ∃ target',
      Expr.ForallTelescopeTypeTranslation env levelParams
        targetCtx source arity target' ∧
      env.IsDefEqU levelParams.length targetCtx.toCtx target' target := by
  rcases H.translation.defeqDFC henv Hctx with ⟨target', Htranslation⟩
  have HtargetType : env.IsType levelParams.length targetCtx.toCtx target :=
    H.isType.defeqDFC henv.ordered Hctx.defeqCtx
  have HtargetEq : env.IsDefEqU levelParams.length targetCtx.toCtx
      target' target :=
    Htranslation.uniq henv (Hctx.symm henv.ordered) H.translation
  have HtargetType' : env.IsType levelParams.length targetCtx.toCtx target' :=
    VEnv.IsType.defeqU_l henv (Hctx.symm henv.ordered).wf.toCtx HtargetEq.symm
      HtargetType
  rcases H.telescope with ⟨residual, Htelescope⟩
  exact ⟨target',
    Expr.ForallTelescopeTypeTranslation.ofTrExprS Htelescope Htranslation
      HtargetType', HtargetEq⟩

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

/-- An abstract forall context is well formed whenever its underlying target
context is well formed.  Keeping this elementary reconstruction local avoids
making family restoration depend on a caller-provided `VLCtx.WF` witness. -/
theorem abstractForallContext_wf_of_onCtx
    {env : VEnv} {levelParams : List Name}
    {parameterDomains : List VExpr}
    (H : OnCtx parameterDomains.reverse (env.IsType levelParams.length)) :
    (abstractForallContext parameterDomains []).WF env levelParams.length := by
  have go : ∀ domains : List VExpr,
      OnCtx domains (env.IsType levelParams.length) →
      VLCtx.WF env levelParams.length
        (domains.map fun type =>
          ((none, .vlam type) :
            Option (FVarId × List FVarId) × VLocalDecl)) := by
    intro domains Hdomains
    induction domains with
    | nil => trivial
    | cons domain domains ih =>
      have Hdomain : env.IsType levelParams.length
          (VLCtx.toCtx (domains.map fun type =>
            ((none, .vlam type) :
              Option (FVarId × List FVarId) × VLocalDecl))) domain := by
        rw [VLCtx.toCtx_map_anonymousLams]
        exact Hdomains.2
      exact ⟨ih Hdomains.1, nofun, Hdomain⟩
  simpa [abstractForallContext] using go parameterDomains.reverse H

/-- Upgrade a source-facing family realization with the exact translated
source index telescope produced by the same header application.  The index
domains are selected from that translation itself; they need not be
syntactically equal to an independently normalized first-pass telescope.
Consequently this constructor requires only the two judgments obtained by
typing that exact family application against the translated telescope. -/
def RestoredFamilyRealization.toIndexedOfTranslatedType
    (F : RestoredFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily)
    (Hindices : Expr.ForallTelescopeTypeTranslation env levelParams
      (abstractForallContext parameterDomains []) sourceIndexType numIndices
      indexTarget)
    (indexDomains : List VExpr) (indexResidual : VExpr)
    (hindexDomains : indexDomains.length = numIndices)
    (hindexTarget : indexTarget =
      VExpr.wrapForalls indexDomains indexResidual)
    (Hfamily : env.HasType levelParams.length parameterDomains.reverse
      F.semantics.family
      (VExpr.wrapForalls indexDomains indexResidual))
    (Happlication : env.IsType levelParams.length
      (indexDomains.reverse ++ parameterDomains.reverse)
      (VExpr.mkApps (F.semantics.family.liftN indexDomains.length 0)
        (recursorCanonicalVars indexDomains.length))) :
    RestoredIndexedFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily sourceIndexType where
  family := {
    semantics := {
      family := F.semantics.family
      indexDomains := indexDomains
      familyResult := indexResidual
      indexCount := hindexDomains
      familyTyping := Hfamily
      familyApplicationType := Happlication }
    sourceTranslation := F.sourceTranslation }
  indexResidual := indexResidual
  indexTypeTranslation := by
    subst indexTarget
    simpa only using Hindices

/-- Upgrade a restored family when an exact source-index replay selects a
definitionally equal dependent domain context rather than the literal domain
list retained by the family realization.  The replay residual is deliberately
independent of the family's result universe: it is only a syntax template for
the index binders.

`Hdomains` is producer-derived by comparing the two concrete telescope
replays.  It transports the actual family typing and canonical application to
the replay-selected domains, while the retained index translation keeps its
own harmless residual. -/
def RestoredFamilyRealization.toIndexedOfDomainContext
    (F : RestoredFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily)
    (henv : env.WF)
    (hparams : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length))
    (Hindices : Expr.ForallTelescopeTypeTranslation env levelParams
      (abstractForallContext parameterDomains []) sourceIndexType numIndices
      (VExpr.wrapForalls indexDomains indexResidual))
    (hindexDomains : indexDomains.length = numIndices)
    (Hdomains : VEnv.IsDefEqCtx env levelParams.length []
      (F.semantics.indexDomains.reverse ++ parameterDomains.reverse)
      (indexDomains.reverse ++ parameterDomains.reverse)) :
    RestoredIndexedFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily sourceIndexType := by
  have holdLength : F.semantics.indexDomains.length = numIndices :=
    F.semantics.indexCount
  have hnewLength : indexDomains.length =
      F.semantics.indexDomains.length := by omega
  have HfamilyType : env.IsType levelParams.length parameterDomains.reverse
      (VExpr.wrapForalls F.semantics.indexDomains
        F.semantics.familyResult) :=
    F.semantics.familyTyping.isType henv.ordered hparams
  have Hclosed' : env.IsDefEqU levelParams.length parameterDomains.reverse
      (VExpr.wrapForalls F.semantics.indexDomains
        F.semantics.familyResult)
      (VExpr.wrapForalls indexDomains F.semantics.familyResult) := by
    have Hopened :=
      VEnv.IsType.wrapForalls_inv henv.ordered hparams HfamilyType
    rcases Hopened.2 with ⟨_resultLevel, Hresult⟩
    have Hclosed := VEnv.IsDefEqCtx.closeHeads Hdomains
      F.semantics.indexDomains.length (by simp [hnewLength]) Hresult
    rcases Hclosed with ⟨closedLevel, Hclosed⟩
    refine ⟨.sort closedLevel, ?_⟩
    have holdDrop :
        (F.semantics.indexDomains.reverse ++
            parameterDomains.reverse).drop
              F.semantics.indexDomains.length =
          parameterDomains.reverse := by simp
    have hnewDrop :
        (indexDomains.reverse ++ parameterDomains.reverse).drop
              F.semantics.indexDomains.length =
          parameterDomains.reverse := by
      rw [← hnewLength]
      simp
    have holdTake :
        (F.semantics.indexDomains.reverse ++
            parameterDomains.reverse).take
              F.semantics.indexDomains.length =
          F.semantics.indexDomains.reverse := by simp
    have hnewTake :
        (indexDomains.reverse ++ parameterDomains.reverse).take
              F.semantics.indexDomains.length =
          indexDomains.reverse := by
      rw [← hnewLength]
      simp
    rw [holdDrop, holdTake, hnewTake] at Hclosed
    simpa using Hclosed
  have Hfamily : env.HasType levelParams.length parameterDomains.reverse
      F.semantics.family
      (VExpr.wrapForalls indexDomains F.semantics.familyResult) :=
    F.semantics.familyTyping.defeqU_r henv hparams Hclosed'
  have Happlication : env.IsType levelParams.length
      (indexDomains.reverse ++ parameterDomains.reverse)
      (VExpr.mkApps (F.semantics.family.liftN indexDomains.length 0)
        (recursorCanonicalVars indexDomains.length)) := by
    have Hold := F.semantics.familyApplicationType.defeqDFC
      henv.ordered Hdomains
    simpa [hnewLength] using Hold
  exact {
    family := {
      semantics := {
        family := F.semantics.family
        indexDomains := indexDomains
        familyResult := F.semantics.familyResult
        indexCount := hindexDomains
        familyTyping := Hfamily
        familyApplicationType := Happlication }
      sourceTranslation := F.sourceTranslation }
    indexResidual := indexResidual
    indexTypeTranslation := Hindices }

/-- Turn the canonical index replay retained by header production into an
indexed restored family in the cached recursor-parameter context.  The two
context conversions are both producer facts: `HsourceReplay` identifies the
normalized semantic header with the replay-selected telescope, and
`HsourceParameters` identifies that header's own parameters with the cached
parameter suffix.

The replay is rebased binder-by-binder into the cached context.  Translation
uniqueness then compares the two translations of the same concrete index
telescope, so neither literal target preservation nor a caller-selected
domain equality is required. -/
theorem RestoredFamilyRealization.toIndexedOfCanonicalReplay
    {sourceParameterDomains replayParameterDomains replayIndexDomains :
      List VExpr}
    {sourceIndexType : Expr} {replayResidual : VExpr}
    (F : RestoredFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily)
    (henv : env.WF)
    (hparams : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length))
    (Hindices : Expr.ForallTelescopeTypeTranslation env levelParams
      (abstractForallContext replayParameterDomains []) sourceIndexType
      numIndices
      (VExpr.wrapForalls replayIndexDomains replayResidual))
    (hreplayIndexCount : replayIndexDomains.length = numIndices)
    (HsourceReplay : VEnv.IsDefEqCtx env levelParams.length []
      (F.semantics.indexDomains.reverse ++ sourceParameterDomains.reverse)
      (replayIndexDomains.reverse ++ replayParameterDomains.reverse))
    (HsourceParameters : VEnv.IsDefEqCtx env levelParams.length []
      sourceParameterDomains.reverse parameterDomains.reverse) :
    Nonempty (RestoredIndexedFamilyRealization env levelParams
      parameterDomains numIndices sourceFamily sourceIndexType) := by
  have holdIndexCount : F.semantics.indexDomains.length = numIndices :=
    F.semantics.indexCount
  have HsourceReplayParameters : VEnv.IsDefEqCtx env levelParams.length []
      sourceParameterDomains.reverse replayParameterDomains.reverse := by
    apply VEnv.IsDefEqCtx.dropPrefixes HsourceReplay
    simp [holdIndexCount, hreplayIndexCount]
  have HreplayParameters : VEnv.IsDefEqCtx env levelParams.length []
      replayParameterDomains.reverse parameterDomains.reverse :=
    VEnv.IsDefEqCtx.transEmpty henv
      (HsourceReplayParameters.symm henv.ordered) HsourceParameters
  have HreplayVLCtx : VLCtx.IsDefEq env levelParams.length
      (abstractForallContext replayParameterDomains [])
      (abstractForallContext parameterDomains []) := by
    simpa [abstractForallContext] using
      VLCtx.IsDefEq.ofDefEqCtxAnonymous HreplayParameters
  rcases Hindices.rebaseContext henv HreplayVLCtx with
    ⟨rebasedTarget, Hrebased⟩
  rcases Hrebased.toWrapForalls with
    ⟨rebasedIndexDomains, sourceResidual, rebasedResidual,
      hrebasedIndexCount, _HsourceShape, hrebasedTarget,
      _HresidualTranslation, _HresidualType⟩
  have HreplayRebased :=
    Expr.ForallTelescopeTypeTranslation.commonPrefixDefEqCtxOver
      henv HreplayParameters Hindices Hrebased
      replayIndexDomains rebasedIndexDomains replayResidual rebasedResidual
      rfl hrebasedTarget hreplayIndexCount hrebasedIndexCount
      numIndices (by simp) (by simp) (by
        intro _position _hposition _hiReplay _hiRebased
          _domainReplay _domainRebased HbinderReplay HbinderRebased
        exact HbinderReplay.unique HbinderRebased)
  have hreplayTake : replayIndexDomains.take numIndices =
      replayIndexDomains := by
    rw [← hreplayIndexCount]
    exact List.take_length
  have hrebasedTake : rebasedIndexDomains.take numIndices =
      rebasedIndexDomains := by
    rw [← hrebasedIndexCount]
    exact List.take_length
  rw [hreplayTake, hrebasedTake] at HreplayRebased
  have HfamilyType : env.IsType levelParams.length parameterDomains.reverse
      (VExpr.wrapForalls F.semantics.indexDomains
        F.semantics.familyResult) :=
    F.semantics.familyTyping.isType henv.ordered hparams
  have HfullParameters : OnCtx
      (F.semantics.indexDomains.reverse ++ parameterDomains.reverse)
      (env.IsType levelParams.length) :=
    (VEnv.IsType.wrapForalls_inv henv.ordered hparams HfamilyType).1
  have HparameterToSource := VEnv.IsDefEqCtx.extendSamePrefix
    (HsourceParameters.symm henv.ordered) HfullParameters
  have HoldReplay := VEnv.IsDefEqCtx.transEmpty henv
    HparameterToSource HsourceReplay
  have Hdomains := VEnv.IsDefEqCtx.transEmpty henv
    HoldReplay HreplayRebased
  rw [hrebasedTarget] at Hrebased
  exact ⟨F.toIndexedOfDomainContext henv hparams Hrebased
    hrebasedIndexCount Hdomains⟩

/-- Upgrade a restored family using two independently retained translations
of the *same* concrete index telescope.  Translation uniqueness relates the
old semantic telescope to the exact producer-selected telescope; the family
typing and its canonical application are then derived internally.  The
selected universe may differ from the first translation, while all
downstream motive, index, and major proofs depend only on the retained
domains. -/
def RestoredFamilyRealization.toIndexedOfSharedTranslation
    (F : RestoredFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily)
    (henv : env.WF)
    (hparams : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length))
    (Hsemantic : Expr.ForallTelescopeTypeTranslation env levelParams
      (abstractForallContext parameterDomains []) sourceIndexType numIndices
      (VExpr.wrapForalls F.semantics.indexDomains
        F.semantics.familyResult))
    (Hcanonical : Expr.ForallTelescopeTypeTranslation env levelParams
      (abstractForallContext parameterDomains []) sourceIndexType numIndices
      (VExpr.wrapForalls indexDomains (.sort indexLevel)))
    (hindexDomains : indexDomains.length = numIndices) :
    RestoredIndexedFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily sourceIndexType := by
  have hctx :
      (abstractForallContext parameterDomains []).WF env levelParams.length :=
    abstractForallContext_wf_of_onCtx hparams
  have Htargets : env.IsDefEqU levelParams.length
      (abstractForallContext parameterDomains []).toCtx
      (VExpr.wrapForalls indexDomains (.sort indexLevel))
      (VExpr.wrapForalls F.semantics.indexDomains
        F.semantics.familyResult) :=
    Hcanonical.translation.uniq henv (.refl henv hctx) Hsemantic.translation
  have Hfamily : env.HasType levelParams.length parameterDomains.reverse
      F.semantics.family
      (VExpr.wrapForalls indexDomains (.sort indexLevel)) := by
    have Htargets' : env.IsDefEqU levelParams.length parameterDomains.reverse
        (VExpr.wrapForalls indexDomains (.sort indexLevel))
        (VExpr.wrapForalls F.semantics.indexDomains
          F.semantics.familyResult) := by
      simpa [abstractForallContext_toCtx, VLCtx.toCtx] using Htargets
    exact F.semantics.familyTyping.defeqU_r henv hparams Htargets'.symm
  have Happlication : env.IsType levelParams.length
      (indexDomains.reverse ++ parameterDomains.reverse)
      (VExpr.mkApps (F.semantics.family.liftN indexDomains.length 0)
        (recursorCanonicalVars indexDomains.length)) := by
    exact ⟨indexLevel,
      VEnv.HasType.mkApps_wrapForalls_canonical henv.ordered Hfamily⟩
  exact F.toIndexedOfTranslatedType Hcanonical indexDomains (.sort indexLevel)
    hindexDomains rfl Hfamily Happlication

/-- Upgrade a restored family from the exact family application and index
telescope emitted by one source-header replay.  The independently retained
`F.sourceTranslation` may choose a different abstract family term, but
translation uniqueness identifies the two terms and transports the replay's
typing judgment.  Thus no equality between independently selected index
domain lists is requested from a caller. -/
def RestoredFamilyRealization.toIndexedOfTranslatedFamily
    (F : RestoredFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily)
    (henv : env.WF)
    (hparams : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length))
    (Hindices : Expr.ForallTelescopeTypeTranslation env levelParams
      (abstractForallContext parameterDomains []) sourceIndexType numIndices
      (VExpr.wrapForalls indexDomains (.sort indexLevel)))
    (hindexDomains : indexDomains.length = numIndices)
    (selectedFamily : VExpr)
    (HselectedFamily : TrExpr env levelParams
      (abstractForallContext parameterDomains []) sourceFamily selectedFamily)
    (HselectedTyping : env.HasType levelParams.length parameterDomains.reverse
      selectedFamily (VExpr.wrapForalls indexDomains (.sort indexLevel))) :
    RestoredIndexedFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily sourceIndexType := by
  have hctx :
      (abstractForallContext parameterDomains []).WF env levelParams.length :=
    abstractForallContext_wf_of_onCtx hparams
  have Hfamilies : env.IsDefEqU levelParams.length parameterDomains.reverse
      selectedFamily F.semantics.family := by
    rcases HselectedFamily with
      ⟨actualFamily, HactualFamily, HactualSelected⟩
    have HactualRestored := HactualFamily.uniq henv (.refl henv hctx)
      F.sourceTranslation
    have HactualSelected' : env.IsDefEqU levelParams.length
        parameterDomains.reverse actualFamily selectedFamily := by
      simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HactualSelected
    have HactualRestored' : env.IsDefEqU levelParams.length
        parameterDomains.reverse actualFamily F.semantics.family := by
      simpa [abstractForallContext_toCtx, VLCtx.toCtx] using HactualRestored
    exact HactualSelected'.symm.trans henv hparams HactualRestored'
  have Hfamily : env.HasType levelParams.length parameterDomains.reverse
      F.semantics.family
      (VExpr.wrapForalls indexDomains (.sort indexLevel)) :=
    HselectedTyping.defeqU_l henv hparams Hfamilies
  have Happlication : env.IsType levelParams.length
      (indexDomains.reverse ++ parameterDomains.reverse)
      (VExpr.mkApps (F.semantics.family.liftN indexDomains.length 0)
        (recursorCanonicalVars indexDomains.length)) :=
    ⟨indexLevel,
      VEnv.HasType.mkApps_wrapForalls_canonical henv.ordered Hfamily⟩
  exact F.toIndexedOfTranslatedType Hindices indexDomains (.sort indexLevel)
    hindexDomains rfl Hfamily Happlication

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

/-- Regard an indexless restored family as an indexed realization with the
family expression itself as the empty source telescope.  This is the
canonical zero-index bridge used for generated auxiliary families: no
source-side telescope or semantic evidence is selected by a caller. -/
def RestoredFamilyRealization.toIndexedZero
    (H : RestoredFamilyRealization env levelParams parameterDomains 0
      sourceFamily) :
    RestoredIndexedFamilyRealization env levelParams parameterDomains 0
      sourceFamily sourceFamily where
  family := H
  indexResidual := H.semantics.family
  indexTypeTranslation := .nil (by
    simpa [H.indexDomains_eq_nil, VExpr.wrapForalls] using
      H.sourceTranslation) (by
    have Happ := H.semantics.familyApplicationType
    simpa [H.indexDomains_eq_nil, VExpr.wrapForalls, VExpr.mkApps,
      abstractForallContext_toCtx, VLCtx.toCtx] using Happ)

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
