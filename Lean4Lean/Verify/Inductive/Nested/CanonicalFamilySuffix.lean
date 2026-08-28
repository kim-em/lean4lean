import Lean4Lean.Verify.Inductive.Nested.CanonicalFamilyRealization
import Lean4Lean.Verify.Inductive.Nested.CanonicalSuffixTargets

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- A realized indexless family discharges one canonical motive slot once
the operational restoration equation identifies the restored concrete
domain.  The target and its typehood are derived from the family realization;
callers only supply the source universe conversion and the exact positional
restoration equation. -/
theorem GeneratedRecursorCanonicalDomainTranslation.ofZeroIndexFamilyMotive
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    {H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry}
    {newEnv : VEnv} {newBase : VLCtx}
    {parameterDomains targets : List VExpr} {position binderDepth : Nat}
    (F : RestoredFamilyRealization newEnv Hentry.info.levelParams
      parameterDomains 0 sourceFamily)
    (henv : newEnv.WF)
    (hbase : newBase = [])
    (hctx : OnCtx
      ((targets.take position).reverse ++ parameterDomains.reverse)
      (newEnv.IsType Hentry.info.levelParams.length))
    (sourceLevel : Level) (resultLevel : VLevel)
    (hlevel : VLevel.ofLevel Hentry.info.levelParams sourceLevel =
      some resultLevel)
    (name : Name) (bi : BinderInfo)
    (htarget : targets[position]! =
      (F.semantics.motiveType resultLevel).liftN
        (targets.take position).length 0)
    (Hrestored : forall {oldDomain newDomain},
      Expr.ForallBinderAt
        (H.trace.opening.body.abstractList H.trace.opening.selection.fvars)
        position
        (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth) ->
      ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain ->
      newDomain.abstractList H.trace.opening.selection.fvars binderDepth =
        ((Expr.forallE name sourceFamily (.sort sourceLevel) bi).liftLooseBVars'
          0 (targets.take position).length)) :
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      parameterDomains targets position binderDepth := by
  subst newBase
  apply GeneratedRecursorCanonicalDomainTranslation.ofRestoredAbstractEq
    ((Expr.forallE name sourceFamily (.sort sourceLevel) bi).liftLooseBVars'
      0 (targets.take position).length) Hrestored
  · rw [htarget]
    simpa only [abstractForallContext_append] using
      F.motiveDomainTranslationZeroAfter henv.ordered
        (targets.take position) sourceLevel resultLevel hlevel name bi
  · rw [htarget]
    simpa [abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append] using
      F.semantics.motiveTypeIsTypeAfter henv.ordered
        (targets.take position) hctx resultLevel (.of_ofLevel hlevel)

/-- Indexed counterpart of `ofZeroIndexFamilyMotive`.  The source motive is
not accepted through an opaque translation premise: it must share the exact
concrete index telescope retained by the family realization, and its
residual must be the canonical family application followed by the selected
elimination sort. -/
theorem GeneratedRecursorCanonicalDomainTranslation.ofIndexedFamilyMotive
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    {H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry}
    {newEnv : VEnv} {newBase : VLCtx}
    {parameterDomains targets : List VExpr} {position binderDepth : Nat}
    (F : RestoredIndexedFamilyRealization newEnv Hentry.info.levelParams
      parameterDomains numIndices sourceFamily sourceIndexType)
    (henv : newEnv.WF)
    (hbase : newBase = [])
    (hctx : OnCtx
      ((targets.take position).reverse ++ parameterDomains.reverse)
      (newEnv.IsType Hentry.info.levelParams.length))
    (sourceMotive : Expr) (sourceLevel : Level) (resultLevel : VLevel)
    (hlevel : VLevel.ofLevel Hentry.info.levelParams sourceLevel =
      some resultLevel)
    (name : Name) (bi : BinderInfo)
    (Hsame : Expr.SameForallDomains numIndices sourceIndexType sourceMotive)
    (Hmotive : Expr.ForallTelescope sourceMotive numIndices
      (.forallE name
        (Expr.mkAppList
          (sourceFamily.liftLooseBVars' 0 numIndices)
          (sourceCanonicalVars numIndices))
        (.sort sourceLevel) bi))
    (htarget : targets[position]! =
      (F.family.semantics.motiveType resultLevel).liftN
        (targets.take position).length 0)
    (Hrestored : forall {oldDomain newDomain},
      Expr.ForallBinderAt
        (H.trace.opening.body.abstractList H.trace.opening.selection.fvars)
        position
        (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth) ->
      ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain ->
      newDomain.abstractList H.trace.opening.selection.fvars binderDepth =
        sourceMotive.liftLooseBVars' 0 (targets.take position).length) :
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      parameterDomains targets position binderDepth := by
  subst newBase
  apply GeneratedRecursorCanonicalDomainTranslation.ofRestoredAbstractEq
    (sourceMotive.liftLooseBVars' 0 (targets.take position).length) Hrestored
  · rw [htarget]
    exact F.motiveDomainTranslationAfter henv
      (OnCtx.append_right hctx) (targets.take position) sourceMotive
      sourceLevel resultLevel hlevel name bi Hsame Hmotive
  · rw [htarget]
    simpa [abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append] using
      F.family.semantics.motiveTypeIsTypeAfter henv.ordered
        (targets.take position) hctx resultLevel (.of_ofLevel hlevel)

/-- Select one concrete source index domain from the retained family
telescope and insert an already generated motive/minor block immediately
beneath the common parameters. -/
theorem RestoredIndexedFamilyRealization.indexDomainTranslationAfter
    (H : RestoredIndexedFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily sourceIndexType)
    (henv : env.Ordered) (added : List VExpr)
    (i : Nat) (hi : i < numIndices) (sourceDomain : Expr)
    (Hsource : Expr.ForallBinderAt sourceIndexType i sourceDomain) :
    TrExprS env levelParams
      (abstractForallContext
        (parameterDomains ++ added ++
          (H.family.semantics.indexDomainsAfter added).take i) [])
      (sourceDomain.liftLooseBVars' i added.length)
      (H.family.semantics.indexDomainsAfter added)[i]! := by
  let domains := H.family.semantics.indexDomains
  have hdomains : domains.length = numIndices :=
    H.family.semantics.indexCount
  have hi' : i < domains.length := by omega
  rcases H.indexTypeTranslation.binderAt_target domains
      H.indexResidual rfl hdomains i (by omega) with
    ⟨suffixSource, name, selectedDomain, sourceBody, bi, bodyTarget,
      Hprefix, hsuffix, Hdomain, _HdomainType, _Hbody⟩
  have Hselected : Expr.ForallBinderAt sourceIndexType i selectedDomain :=
    Hprefix.binderAt hsuffix
  have hselected : selectedDomain = sourceDomain :=
    Hselected.unique Hsource
  subst selectedDomain
  have Hdomain' : TrExprS env levelParams
      (abstractForallContext
        (parameterDomains ++ domains.take i) [])
      sourceDomain domains[i] := by
    simpa only [abstractForallContext_append] using Hdomain
  have Hinserted := TrExprS.insertBeforeInner henv Hdomain' added
  have hprefix :
      (H.family.semantics.indexDomainsAfter added).take i =
        (liftContextPrefix added.length (domains.take i).reverse).reverse := by
    have hsplit : domains = domains.take i ++ domains.drop i :=
      (List.take_append_drop i domains).symm
    have W := liftContextPrefixAt_reverse_append_take_left
      added.length 0 (domains.take i) (domains.drop i)
    have W' :
        ((liftContextPrefix added.length
          (domains.take i ++ domains.drop i).reverse).reverse).take i =
          (liftContextPrefix added.length (domains.take i).reverse).reverse := by
      simpa [liftContextPrefix, List.length_take,
        Nat.min_eq_left (Nat.le_of_lt hi')] using W
    rw [← hsplit] at W'
    simpa [RestoredFamilySemantics.indexDomainsAfter, domains] using W'
  have htarget : (H.family.semantics.indexDomainsAfter added)[i]! =
      domains[i]!.liftN added.length i := by
    rw [RestoredFamilySemantics.indexDomainsAfter, show
      H.family.semantics.indexDomains = domains from rfl]
    simpa [liftContextPrefix] using
      liftContextPrefixAt_reverse_getElem added.length 0 domains i hi'
  rw [hprefix, htarget]
  simpa [List.append_assoc, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hi'), getElem!_pos, hi'] using Hinserted

/-- Insert an already restored motive/minor block below all indices in the
retained family application. -/
theorem RestoredIndexedFamilyRealization.majorDomainTranslationAfter
    (H : RestoredIndexedFamilyRealization env levelParams parameterDomains
      numIndices sourceFamily sourceIndexType)
    (henv : env.WF)
    (hparams : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length))
    (added : List VExpr) :
    TrExprS env levelParams
      (abstractForallContext
        (parameterDomains ++ added ++
          H.family.semantics.indexDomainsAfter added) [])
      ((Expr.mkAppList
        (sourceFamily.liftLooseBVars' 0 numIndices)
        (sourceCanonicalVars numIndices)).liftLooseBVars'
          numIndices added.length)
      (H.family.semantics.majorTypeAfter added) := by
  let domains := H.family.semantics.indexDomains
  have hdomains : domains.length = numIndices :=
    H.family.semantics.indexCount
  have Hbase := H.family.familyApplicationTranslation henv hparams
  have Hinserted := TrExprS.insertBeforeInner henv.ordered Hbase added
  simpa [domains, hdomains, RestoredFamilySemantics.indexDomainsAfter,
    RestoredFamilySemantics.majorTypeAfter] using Hinserted

/-- A retained indexed-family telescope discharges one canonical index slot.
The positional prefix equation is deliberately exact: `added` is the
completed motive/minor block, while the selected semantic row contributes
precisely its preceding index domains. -/
theorem GeneratedRecursorCanonicalDomainTranslation.ofIndexedFamilyIndex
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    {H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry}
    {newEnv : VEnv} {newBase : VLCtx}
    {parameterDomains targets added : List VExpr}
    {position binderDepth numIndices : Nat}
    (F : RestoredIndexedFamilyRealization newEnv Hentry.info.levelParams
      parameterDomains numIndices sourceFamily sourceIndexType)
    (henv : newEnv.WF)
    (hbase : newBase = [])
    (hctx : OnCtx (added.reverse ++ parameterDomains.reverse)
      (newEnv.IsType Hentry.info.levelParams.length))
    (i : Nat) (hi : i < numIndices) (sourceDomain : Expr)
    (Hsource : Expr.ForallBinderAt sourceIndexType i sourceDomain)
    (hprefix : targets.take position =
      added ++ (F.family.semantics.indexDomainsAfter added).take i)
    (htarget : targets[position]! =
      (F.family.semantics.indexDomainsAfter added)[i]!)
    (Hrestored : forall {oldDomain newDomain},
      Expr.ForallBinderAt
        (H.trace.opening.body.abstractList H.trace.opening.selection.fvars)
        position
        (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth) ->
      ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain ->
      newDomain.abstractList H.trace.opening.selection.fvars binderDepth =
        sourceDomain.liftLooseBVars' i added.length) :
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      parameterDomains targets position binderDepth := by
  subst newBase
  apply GeneratedRecursorCanonicalDomainTranslation.ofRestoredAbstractEq
    (sourceDomain.liftLooseBVars' i added.length) Hrestored
  · rw [htarget, hprefix]
    simpa only [List.append_assoc] using
      F.indexDomainTranslationAfter henv.ordered added i hi sourceDomain Hsource
  · rw [htarget, hprefix]
    have hi' : i < (F.family.semantics.indexDomainsAfter added).length := by
      simpa using hi
    have htarget' : (F.family.semantics.indexDomainsAfter added)[i]! =
        (F.family.semantics.indexDomainsAfter added)[i] := by
      exact getElem!_pos (F.family.semantics.indexDomainsAfter added) i hi'
    rw [htarget']
    simpa [abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append, List.append_assoc] using
      F.family.semantics.indexDomainAfterIsType henv.ordered added hctx i hi'

/-- A retained family realization discharges the canonical major slot after
all motives, minors, and owner indices have been restored. -/
theorem GeneratedRecursorCanonicalDomainTranslation.ofIndexedFamilyMajor
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    {H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry}
    {newEnv : VEnv} {newBase : VLCtx}
    {parameterDomains targets added : List VExpr}
    {position binderDepth numIndices : Nat}
    (F : RestoredIndexedFamilyRealization newEnv Hentry.info.levelParams
      parameterDomains numIndices sourceFamily sourceIndexType)
    (henv : newEnv.WF)
    (hbase : newBase = [])
    (hctx : OnCtx (added.reverse ++ parameterDomains.reverse)
      (newEnv.IsType Hentry.info.levelParams.length))
    (hprefix : targets.take position =
      added ++ F.family.semantics.indexDomainsAfter added)
    (htarget : targets[position]! =
      F.family.semantics.majorTypeAfter added)
    (Hrestored : forall {oldDomain newDomain},
      Expr.ForallBinderAt
        (H.trace.opening.body.abstractList H.trace.opening.selection.fvars)
        position
        (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth) ->
      ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain ->
      newDomain.abstractList H.trace.opening.selection.fvars binderDepth =
        ((Expr.mkAppList
          (sourceFamily.liftLooseBVars' 0 numIndices)
          (sourceCanonicalVars numIndices)).liftLooseBVars'
            numIndices added.length)) :
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      parameterDomains targets position binderDepth := by
  subst newBase
  apply GeneratedRecursorCanonicalDomainTranslation.ofRestoredAbstractEq
    ((Expr.mkAppList
      (sourceFamily.liftLooseBVars' 0 numIndices)
      (sourceCanonicalVars numIndices)).liftLooseBVars'
        numIndices added.length) Hrestored
  · rw [htarget, hprefix]
    simpa only [List.append_assoc] using
      F.majorDomainTranslationAfter henv (OnCtx.append_right hctx) added
  · rw [htarget, hprefix]
    simpa [abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append, List.append_assoc] using
      F.family.semantics.majorTypeAfterIsType henv.ordered added

/-- Canonical-target specialization of `ofIndexedFamilyIndex`.  Once the
motive/minor prefix is fixed, the index position, preceding target prefix,
and selected semantic target are consequences of the literal canonical
target list rather than caller-supplied equations. -/
theorem GeneratedRecursorCanonicalDomainTranslation.ofIndexedFamilyIndexAtCanonicalTargets
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    {H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry}
    {newEnv : VEnv} {newBase : VLCtx}
    {parameterDomains motiveMinorTargets : List VExpr}
    {binderDepth numIndices : Nat}
    (F : RestoredIndexedFamilyRealization newEnv Hentry.info.levelParams
      parameterDomains numIndices sourceFamily sourceIndexType)
    (henv : newEnv.WF)
    (hbase : newBase = [])
    (hctx : OnCtx (motiveMinorTargets.reverse ++ parameterDomains.reverse)
      (newEnv.IsType Hentry.info.levelParams.length))
    (i : Nat) (hi : i < numIndices) (sourceDomain : Expr)
    (Hsource : Expr.ForallBinderAt sourceIndexType i sourceDomain)
    (Hrestored : forall {oldDomain newDomain},
      Expr.ForallBinderAt
        (H.trace.opening.body.abstractList H.trace.opening.selection.fvars)
        (motiveMinorTargets.length + i)
        (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth) ->
      ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain ->
      newDomain.abstractList H.trace.opening.selection.fvars binderDepth =
        sourceDomain.liftLooseBVars' i motiveMinorTargets.length) :
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      parameterDomains
      (F.family.semantics.canonicalRecursorTargets motiveMinorTargets)
      (motiveMinorTargets.length + i) binderDepth := by
  apply GeneratedRecursorCanonicalDomainTranslation.ofIndexedFamilyIndex
    F henv hbase hctx i hi sourceDomain Hsource
  · exact F.family.semantics.canonicalRecursorTargets_take_index
      motiveMinorTargets i hi
  · have hposition : motiveMinorTargets.length + i <
        (F.family.semantics.canonicalRecursorTargets
          motiveMinorTargets).length := by
      simp
      omega
    rw [getElem!_pos
      (F.family.semantics.canonicalRecursorTargets motiveMinorTargets)
      (motiveMinorTargets.length + i) hposition]
    have hselected :=
      F.family.semantics.canonicalRecursorTargets_getElem_index
        motiveMinorTargets i hi
    dsimp only at hselected
    have hi' : i <
        (F.family.semantics.indexDomainsAfter motiveMinorTargets).length := by
      simpa using hi
    rw [List.getElem?_eq_getElem hposition,
      List.getElem?_eq_getElem hi'] at hselected
    rw [getElem!_pos
      (F.family.semantics.indexDomainsAfter motiveMinorTargets) i hi']
    exact Option.some.inj hselected
  · exact Hrestored

/-- Canonical-target specialization of `ofIndexedFamilyMajor`.  It derives
both the completed index prefix and terminal major target from the restored
family semantics. -/
theorem GeneratedRecursorCanonicalDomainTranslation.ofIndexedFamilyMajorAtCanonicalTargets
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    {H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry}
    {newEnv : VEnv} {newBase : VLCtx}
    {parameterDomains motiveMinorTargets : List VExpr}
    {binderDepth numIndices : Nat}
    (F : RestoredIndexedFamilyRealization newEnv Hentry.info.levelParams
      parameterDomains numIndices sourceFamily sourceIndexType)
    (henv : newEnv.WF)
    (hbase : newBase = [])
    (hctx : OnCtx (motiveMinorTargets.reverse ++ parameterDomains.reverse)
      (newEnv.IsType Hentry.info.levelParams.length))
    (Hrestored : forall {oldDomain newDomain},
      Expr.ForallBinderAt
        (H.trace.opening.body.abstractList H.trace.opening.selection.fvars)
        (motiveMinorTargets.length + numIndices)
        (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth) ->
      ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain ->
      newDomain.abstractList H.trace.opening.selection.fvars binderDepth =
        ((Expr.mkAppList
          (sourceFamily.liftLooseBVars' 0 numIndices)
          (sourceCanonicalVars numIndices)).liftLooseBVars'
            numIndices motiveMinorTargets.length)) :
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      parameterDomains
      (F.family.semantics.canonicalRecursorTargets motiveMinorTargets)
      (motiveMinorTargets.length + numIndices) binderDepth := by
  apply GeneratedRecursorCanonicalDomainTranslation.ofIndexedFamilyMajor
    F henv hbase hctx
  · exact F.family.semantics.canonicalRecursorTargets_take_major
      motiveMinorTargets
  · have hposition : motiveMinorTargets.length + numIndices <
        (F.family.semantics.canonicalRecursorTargets
          motiveMinorTargets).length := by
      simp
    rw [getElem!_pos
      (F.family.semantics.canonicalRecursorTargets motiveMinorTargets)
      (motiveMinorTargets.length + numIndices) hposition]
    have hselected :=
      F.family.semantics.canonicalRecursorTargets_getElem_major
        motiveMinorTargets
    dsimp only at hselected
    rw [List.getElem?_eq_getElem hposition] at hselected
    exact Option.some.inj hselected
  · exact Hrestored

/-- Forward, typed counterpart of
`TrExprS.concreteRecursorResult_eq`: in a canonical binder context the
concrete de Bruijn recursor result translates to the identical abstract
application spine. -/
theorem TrExprS.concreteRecursorResult
    (henv : env.WF)
    (howner : ownerIdx < numMotives)
    (htotal : numMotives + numMinors + numIndices + 1 <= domains.length)
    (hctx : OnCtx (abstractForallContext domains base).toCtx
      (env.IsType Us.length))
    (Htype : env.IsType Us.length
      (abstractForallContext domains base).toCtx
      (VExpr.mkApps
        (.bvar (1 + numIndices + numMinors +
          (numMotives - 1 - ownerIdx)))
        ((List.ofFn fun i : Fin numIndices =>
          VExpr.bvar (1 + (numIndices - 1 - i))) ++ [.bvar 0]))) :
    TrExprS env Us (abstractForallContext domains base)
      (concreteRecursorResult numMotives numMinors numIndices ownerIdx)
      (VExpr.mkApps
        (.bvar (1 + numIndices + numMinors +
          (numMotives - 1 - ownerIdx)))
        ((List.ofFn fun i : Fin numIndices =>
          VExpr.bvar (1 + (numIndices - 1 - i))) ++ [.bvar 0])) := by
  let motiveOffset := 1 + numIndices + numMinors +
    (numMotives - 1 - ownerIdx)
  let offsets :=
    (List.ofFn fun i : Fin numIndices =>
      1 + (numIndices - 1 - i)) ++ [0]
  have hmotive : motiveOffset < domains.length := by
    dsimp [motiveOffset]
    omega
  have hoffsets : forall i, i ∈ offsets -> i < domains.length := by
    intro i hi
    simp only [offsets, List.mem_append, List.mem_ofFn,
      List.mem_singleton] at hi
    rcases hi with ⟨j, rfl⟩ | rfl <;> omega
  have Hfn : TrExprS env Us (abstractForallContext domains base)
      (.bvar motiveOffset) (.bvar motiveOffset) :=
    TrExprS.bvar_of_abstractForallContext domains base motiveOffset hmotive
  have Hargs : List.Forall₂
      (TrExprS env Us (abstractForallContext domains base))
      (offsets.map Expr.bvar) (offsets.map VExpr.bvar) :=
    TrExprS.bvars_of_abstractForallContext domains base offsets hoffsets
  have htargetArgs : offsets.map VExpr.bvar =
      (List.ofFn fun i : Fin numIndices =>
        VExpr.bvar (1 + (numIndices - 1 - i))) ++ [.bvar 0] := by
    simp [offsets, Function.comp_def]
  have Hwf : VExpr.WF env Us.length
      (abstractForallContext domains base).toCtx
      (VExpr.mkApps (.bvar motiveOffset) (offsets.map VExpr.bvar)) := by
    rcases Htype with ⟨resultLevel, Htyped⟩
    rw [htargetArgs]
    exact ⟨.sort resultLevel, by
      change env.HasType Us.length
        (abstractForallContext domains base).toCtx
        (VExpr.mkApps (.bvar motiveOffset)
          ((List.ofFn fun i : Fin numIndices =>
            VExpr.bvar (1 + (numIndices - 1 - i))) ++ [.bvar 0]))
        (.sort resultLevel)
      simpa [motiveOffset] using Htyped⟩
  have Happlication := checkPositivityStep.TrExprS.mkAppList
    henv.ordered hctx Hfn Hargs Hwf
  have hsource :
      VerifyInductive.concreteRecursorResult numMotives numMinors numIndices
          ownerIdx =
        Expr.mkAppList (.bvar motiveOffset) (offsets.map Expr.bvar) := by
    unfold VerifyInductive.concreteRecursorResult
    dsimp [motiveOffset, offsets]
    rw [Expr.mkAppN_eq_mkAppList]
    simp [Expr.mkAppList, Function.comp_def]
  rw [hsource, ← htargetArgs]
  exact Happlication

/-- The residual slot of a restored recursor is forced by the retained
family semantics.  Its concrete translation is reconstructed from the
canonical de Bruijn context, and its type is the ordinary application of the
selected motive to the selected major premise. -/
theorem RestoredFamilySemantics.concreteRecursorResultAbstractTypeTranslationAfter
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (henv : env.WF) (added : List VExpr)
    (hctx : OnCtx (added.reverse ++ parameterDomains.reverse)
      (env.IsType levelParams.length))
    (hadded : added.length = numMotives + numMinors + numIndices + 1)
    (howner : ownerIdx < numMotives)
    (resultLevel : VLevel)
    (Hmotive : env.HasType levelParams.length
      (added.reverse ++ parameterDomains.reverse)
      (.bvar (1 + numIndices + numMinors +
        (numMotives - 1 - ownerIdx)))
      ((S.motiveType resultLevel).liftN added.length 0))
    (Hmajor : env.HasType levelParams.length
      (added.reverse ++ parameterDomains.reverse) (.bvar 0)
      (VExpr.mkApps (S.family.liftN added.length 0)
        (List.ofFn fun i : Fin numIndices =>
          VExpr.bvar (1 + (numIndices - 1 - i))))) :
    Expr.AbstractTypeTranslation env levelParams
      (abstractForallContext (parameterDomains ++ added) [])
      (VerifyInductive.concreteRecursorResult
        numMotives numMinors numIndices ownerIdx) := by
  let indexTargets := List.ofFn fun i : Fin numIndices =>
    VExpr.bvar (1 + (numIndices - 1 - i))
  let motive := VExpr.bvar (1 + numIndices + numMinors +
    (numMotives - 1 - ownerIdx))
  have hindices : indexTargets.length = S.indexDomains.length := by
    simp [indexTargets, S.indexCount]
  have Hresult := S.applyMajorTypedAfter henv added hctx indexTargets hindices
    resultLevel motive (.bvar 0) (by simpa [motive] using Hmotive)
      (by simpa [indexTargets] using Hmajor)
  have HresultType : env.IsType levelParams.length
      (abstractForallContext (parameterDomains ++ added) []).toCtx
      (.app (VExpr.mkApps motive indexTargets) (.bvar 0)) := by
    refine ⟨resultLevel, ?_⟩
    simpa [abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append] using Hresult
  have htotal : numMotives + numMinors + numIndices + 1 ≤
      (parameterDomains ++ added).length := by
    simp [hadded]
  have Htranslation := TrExprS.concreteRecursorResult
    (domains := parameterDomains ++ added) (base := [])
    (Us := levelParams) henv howner htotal
    (by simpa [abstractForallContext_toCtx, VLCtx.toCtx,
      List.reverse_append] using hctx) (by
      simpa [motive, indexTargets, VExpr.mkApps,
        List.foldl_append] using HresultType)
  exact S.residualAbstractTypeTranslationAfter henv added indexTargets hctx
    hindices resultLevel motive (.bvar 0)
      (VerifyInductive.concreteRecursorResult
        numMotives numMinors numIndices ownerIdx)
      (by simpa [motive, indexTargets, VExpr.mkApps,
        List.foldl_append] using Htranslation)
      (by simpa [motive] using Hmotive)
      (by simpa [indexTargets] using Hmajor)

end VerifyInductive
end Lean4Lean
