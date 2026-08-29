import Lean4Lean.Verify.Inductive.Nested.RecursorSemantics

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

namespace VerifyInductive

/-- Select a domain in source telescope order from a well-formed context,
recovering exactly the context of the preceding source domains. -/
theorem _root_.Lean4Lean.OnCtx.sourceOrder_getElem
    {domains outer : List VExpr} {P : List VExpr -> VExpr -> Prop}
    (H : OnCtx (domains.reverse ++ outer) P)
    (i : Nat) (hi : i < domains.length) :
    P ((domains.take i).reverse ++ outer) domains[i] := by
  induction domains generalizing outer i with
  | nil => simp at hi
  | cons head tail ih =>
    cases i with
    | zero =>
        have Hdrop := H.drop tail.length
        have Hhead : OnCtx (head :: outer) P := by
          simpa [List.reverse_cons, List.append_assoc] using Hdrop
        exact Hhead.2
    | succ i =>
        have Htail : OnCtx (tail.reverse ++ head :: outer) P := by
          simpa [List.reverse_cons, List.append_assoc] using H
        have Hselected := ih Htail i (by simpa using hi)
        simpa [List.take, List.reverse_cons, List.append_assoc] using Hselected

/-- The restored index telescope after inserting already generated motive and
minor domains between its indices and the common parameter context.  The
dependent prefix is lifted at its exact per-domain cutoff. -/
def RestoredFamilySemantics.indexDomainsAfter
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (added : List VExpr) : List VExpr :=
  (liftContextPrefix added.length S.indexDomains.reverse).reverse

@[simp] theorem RestoredFamilySemantics.indexDomainsAfter_length
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (added : List VExpr) :
    (S.indexDomainsAfter added).length = numIndices := by
  simp [RestoredFamilySemantics.indexDomainsAfter, S.indexCount]

/-- The major-premise target obtained by inserting motives and minors below
the restored indices. -/
def RestoredFamilySemantics.majorTypeAfter
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (added : List VExpr) : VExpr :=
  (VExpr.mkApps (S.family.liftN S.indexDomains.length 0)
    (recursorCanonicalVars S.indexDomains.length)).liftN
      added.length S.indexDomains.length

/-- Formation of the restored family telescope supplies all owner-index
domains in the canonical context after motives and minors have been inserted.
This is the index-group context invariant used by the suffix fold. -/
theorem RestoredFamilySemantics.indexDomainsAfterCtx
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (henv : env.Ordered) (added : List VExpr)
    (hctx : OnCtx (added.reverse ++ parameterDomains.reverse)
      (env.IsType levelParams.length)) :
    OnCtx
      ((S.indexDomainsAfter added).reverse ++ added.reverse ++
        parameterDomains.reverse)
      (env.IsType levelParams.length) := by
  have hparams : OnCtx parameterDomains.reverse
      (env.IsType levelParams.length) := OnCtx.append_right hctx
  have hfamilyType := S.familyTyping.isType henv hparams
  have hindices := VEnv.IsType.wrapForalls_inv henv hparams hfamilyType
  have hinserted := OnCtx.insertAfterPrefix henv hindices.1 hctx
  simpa [RestoredFamilySemantics.indexDomainsAfter, List.append_assoc]
    using hinserted

/-- One restored owner-index domain is well formed in precisely the prefix
present when the suffix fold reaches it. -/
theorem RestoredFamilySemantics.indexDomainAfterIsType
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (henv : env.Ordered) (added : List VExpr)
    (hctx : OnCtx (added.reverse ++ parameterDomains.reverse)
      (env.IsType levelParams.length))
    (i : Nat) (hi : i < (S.indexDomainsAfter added).length) :
    env.IsType levelParams.length
      (((S.indexDomainsAfter added).take i).reverse ++ added.reverse ++
        parameterDomains.reverse)
      (S.indexDomainsAfter added)[i] := by
  have Hfull : OnCtx
      ((S.indexDomainsAfter added).reverse ++
        (added.reverse ++ parameterDomains.reverse))
      (env.IsType levelParams.length) := by
    simpa [List.append_assoc] using S.indexDomainsAfterCtx henv added hctx
  simpa [List.append_assoc] using Hfull.sourceOrder_getElem i hi

/-- The canonical restored major domain is a type in the completed index
context.  No additional family-specific premise is needed beyond
`RestoredFamilySemantics`. -/
theorem RestoredFamilySemantics.majorTypeAfterIsType
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (henv : env.Ordered) (added : List VExpr) :
    env.IsType levelParams.length
      ((S.indexDomainsAfter added).reverse ++ added.reverse ++
        parameterDomains.reverse)
      (S.majorTypeAfter added) := by
  have W := Ctx.LiftN.insertAfterPrefix S.indexDomains.reverse added.reverse
    parameterDomains.reverse
  have Htype := S.familyApplicationType.weakN henv W
  simpa [RestoredFamilySemantics.indexDomainsAfter,
    RestoredFamilySemantics.majorTypeAfter, List.append_assoc] using Htype

/-- Once the concrete restored result has translated to the canonical motive
application, its typehood is forced by the restored family semantics.  Thus
the residual callback need retain only its concrete translation and the
ordinary motive/major variable typings, not an independent result-formation
postulate. -/
theorem RestoredFamilySemantics.residualAbstractTypeTranslationAfter
    (S : RestoredFamilySemantics env levelParams parameterDomains numIndices)
    (henv : env.WF) (added indexTargets : List VExpr)
    (hctx : OnCtx (added.reverse ++ parameterDomains.reverse)
      (env.IsType levelParams.length))
    (hindices : indexTargets.length = S.indexDomains.length)
    (resultLevel : VLevel) (motive major : VExpr) (source : Expr)
    (Htranslation : TrExprS env levelParams
      (abstractForallContext (parameterDomains ++ added) []) source
      (.app (VExpr.mkApps motive indexTargets) major))
    (Hmotive : env.HasType levelParams.length
      (added.reverse ++ parameterDomains.reverse) motive
      ((S.motiveType resultLevel).liftN added.length 0))
    (Hmajor : env.HasType levelParams.length
      (added.reverse ++ parameterDomains.reverse) major
      (VExpr.mkApps (S.family.liftN added.length 0) indexTargets)) :
    Expr.AbstractTypeTranslation env levelParams
      (abstractForallContext (parameterDomains ++ added) []) source := by
  refine ⟨.app (VExpr.mkApps motive indexTargets) major, Htranslation, ?_⟩
  have Htype := S.applyMajorTypedAfter henv added hctx indexTargets hindices
    resultLevel motive major Hmotive Hmajor
  have hcontext :
      (abstractForallContext (parameterDomains ++ added) []).toCtx =
        added.reverse ++ parameterDomains.reverse := by
    simp [List.reverse_append, VLCtx.toCtx]
  refine ⟨resultLevel, ?_⟩
  rw [hcontext]
  exact Htype

/-- The exact semantic obligation for one member of a fixed canonical target
suffix.  Unlike the accumulator-facing restoration callback, the context and
target are determined solely by `targets` and `position`. -/
def GeneratedRecursorCanonicalDomainTranslation
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (newEnv : VEnv) (newBase : VLCtx) (initialPrefix targets : List VExpr)
    (position binderDepth : Nat) : Prop :=
  forall {oldDelta oldDomain newDomain oldDomainTarget},
    Expr.ForallBinderAt
        (H.trace.opening.body.abstractList
          H.trace.opening.selection.fvars)
        position
        (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth) ->
    ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain ->
    TrExprS venv Hentry.info.levelParams oldDelta
      (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth)
      oldDomainTarget ->
    venv.IsType Hentry.info.levelParams.length oldDelta.toCtx
      oldDomainTarget ->
    TrExprS newEnv Hentry.info.levelParams
        (abstractForallContext
          (initialPrefix ++ targets.take position) newBase)
        (newDomain.abstractList H.trace.opening.selection.fvars binderDepth)
        targets[position]! /\
      newEnv.IsType Hentry.info.levelParams.length
        (abstractForallContext
          (initialPrefix ++ targets.take position) newBase).toCtx
        targets[position]!

/-- Reduce one canonical slot to a syntax-only restoration equation plus an
independently derived translation of that restored source.  The old
checker-side translation is deliberately unused: it cannot justify a type in
the independently rebuilt source environment. -/
theorem GeneratedRecursorCanonicalDomainTranslation.ofRestoredAbstractEq
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    {H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry}
    {newEnv : VEnv} {newBase : VLCtx} {initialPrefix targets : List VExpr}
    {position binderDepth : Nat} (restoredSource : Expr)
    (Hrestored : forall {oldDomain newDomain},
      Expr.ForallBinderAt
        (H.trace.opening.body.abstractList H.trace.opening.selection.fvars)
        position
        (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth) ->
      ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain ->
      newDomain.abstractList H.trace.opening.selection.fvars binderDepth =
        restoredSource)
    (Htranslation : TrExprS newEnv Hentry.info.levelParams
      (abstractForallContext (initialPrefix ++ targets.take position) newBase)
      restoredSource targets[position]!)
    (Htype : newEnv.IsType Hentry.info.levelParams.length
      (abstractForallContext
        (initialPrefix ++ targets.take position) newBase).toCtx
      targets[position]!) :
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      initialPrefix targets position binderDepth := by
  intro oldDelta oldDomain newDomain oldDomainTarget Hdomain Hreplacement
    _Hold _HoldType
  rw [Hrestored Hdomain Hreplacement]
  exact ⟨Htranslation, Htype⟩

/-- Equivalence-based form of `ofRestoredAbstractEq`.  Operational
restoration and alpha-reopening are specified by Lean's expression
equivalence relation, which is exactly the congruence respected by `TrExprS`;
requiring propositional syntax equality here would discard valid producer
evidence. -/
theorem GeneratedRecursorCanonicalDomainTranslation.ofRestoredAbstractEqv
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    {H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry}
    {newEnv : VEnv} {newBase : VLCtx} {initialPrefix targets : List VExpr}
    {position binderDepth : Nat} (restoredSource : Expr)
    (Hrestored : forall {oldDomain newDomain},
      Expr.ForallBinderAt
        (H.trace.opening.body.abstractList H.trace.opening.selection.fvars)
        position
        (oldDomain.abstractList H.trace.opening.selection.fvars binderDepth) ->
      ExprReplacement
        (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
        oldDomain newDomain ->
      (newDomain.abstractList H.trace.opening.selection.fvars binderDepth ==
        restoredSource) = true)
    (Htranslation : TrExprS newEnv Hentry.info.levelParams
      (abstractForallContext (initialPrefix ++ targets.take position) newBase)
      restoredSource targets[position]!)
    (Htype : newEnv.IsType Hentry.info.levelParams.length
      (abstractForallContext
        (initialPrefix ++ targets.take position) newBase).toCtx
      targets[position]!) :
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      initialPrefix targets position binderDepth := by
  intro oldDelta oldDomain newDomain oldDomainTarget Hdomain Hreplacement
    _Hold _HoldType
  exact ⟨Htranslation.eqv
    (BEq.symm (Hrestored Hdomain Hreplacement)), Htype⟩

/-- A canonical target list plus source-facing translations for the four
generated recursor domain groups and its final residual.  This interface
removes all dependent-fold state bookkeeping from later semantic proofs:
each field is checked only in the uniquely determined canonical prefix. -/
structure GeneratedRecursorCanonicalSuffixTranslations
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    (H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry)
    (Horigins : RecInfoTypeOrigins c recInfos)
    (newEnv : VEnv) (newBase : VLCtx) (initialPrefix targets : List VExpr) :
    Prop where
  targets_length : targets.length =
    (recInfos.map (·.motive)).size +
      (recInfos.flatMap (·.minors)).size +
      recInfos[ownerIdx]!.indices.size + 1
  motive : forall i (hi : i < (recInfos.map (·.motive)).size)
      (declaration : BoundFVarDeclarationAt c
        (recInfos.map (·.motive)) i)
      (originType_eq : declaration.type = Horigins.motiveTypes[i]!)
      (binderDepth : Nat),
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      initialPrefix targets i binderDepth
  minor : forall i (hi : i < (recInfos.flatMap (·.minors)).size)
      (declaration : BoundFVarDeclarationAt c
        (recInfos.flatMap (·.minors)) i)
      (origin : Horigins.FlatMinorOrigin declaration)
      (binderDepth : Nat),
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      initialPrefix targets ((recInfos.map (·.motive)).size + i) binderDepth
  index : forall i (hi : i < recInfos[ownerIdx]!.indices.size)
      (declaration : BoundFVarDeclarationAt c
        recInfos[ownerIdx]!.indices i)
      (originType_eq : declaration.type =
        Horigins.indexTypes[ownerIdx]![i]!)
      (binderDepth : Nat),
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      initialPrefix targets
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size + i) binderDepth
  major : forall (declaration : BoundFVarDeclarationAt c
      #[recInfos[ownerIdx]!.major] 0)
      (originType_eq : declaration.type = Horigins.majorTypes[ownerIdx]!)
      (binderDepth : Nat),
    GeneratedRecursorCanonicalDomainTranslation H newEnv newBase
      initialPrefix targets
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size) binderDepth
  residual : forall {oldDelta oldResidualTarget},
    ExprReplacement
      (result.restoreNestedNode prodEnv H.trace.opening.params auxRec)
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx)
      (concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx) ->
    TrExprS venv Hentry.info.levelParams oldDelta
      ((concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
        H.trace.opening.selection.fvars
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1)) oldResidualTarget ->
    venv.IsType Hentry.info.levelParams.length oldDelta.toCtx
      oldResidualTarget ->
    Expr.AbstractTypeTranslation newEnv Hentry.info.levelParams
      (abstractForallContext (initialPrefix ++ targets) newBase)
      ((concreteRecursorResult (recInfos.map (·.motive)).size
        (recInfos.flatMap (·.minors)).size
        recInfos[ownerIdx]!.indices.size ownerIdx).abstractList
        H.trace.opening.selection.fvars
        ((recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size + 1))

/-- The canonical target list is itself the dependent-fold invariant.  Thus
semantic work may establish exact targets locally; this theorem supplies all
prefix extension equations and the completed residual state. -/
def GeneratedRecursorCanonicalSuffixTranslations.toInvariant
    {recInfos : Array AddInductive.RecInfo} {ownerIdx : Nat}
    {Hentry : GeneratedRecursorEntry safety venv lparams elimLevel c stats
      indTypes recInfos ownerIdx entry}
    {H : GeneratedRecursorRestorationTelescopeAlignment result prodEnv auxRec
      newInfo Hentry}
    {Horigins : RecInfoTypeOrigins c recInfos}
    {newEnv : VEnv} {newBase : VLCtx} {initialPrefix : List VExpr}
    {targets : List VExpr}
    (S : GeneratedRecursorCanonicalSuffixTranslations H Horigins newEnv
      newBase initialPrefix targets) :
    GeneratedRecursorRestoredSuffixTranslationsInvariant H Horigins newEnv
      newBase initialPrefix := by
  let State : Nat -> List VExpr -> Prop := fun position accumulated =>
    accumulated = initialPrefix ++ targets.take position
  refine {
    State := State
    initial := by simp [State]
    domains := ?_
    residual := ?_
  }
  · refine {
      motive := ?_
      minor := ?_
      index := ?_
      major := ?_
    }
    · intro i hi declaration horigin binderDepth accumulated Hstate _
        oldDelta oldDomain newDomain oldDomainTarget Hdomain Hreplacement Htr
        Htype
      subst accumulated
      rcases S.motive i hi declaration horigin binderDepth Hdomain
          Hreplacement Htr Htype with ⟨Hnew, HnewType⟩
      refine ⟨targets[i]!, Hnew, HnewType, ?_⟩
      simp only [State]
      have hposition : i < targets.length := by
        rw [S.targets_length]
        omega
      rw [getElem!_pos targets i hposition,
        List.take_succ_eq_append_getElem hposition]
      simp [List.append_assoc]
    · intro i hi declaration horigin binderDepth accumulated Hstate _
        oldDelta oldDomain newDomain oldDomainTarget Hdomain Hreplacement Htr
        Htype
      subst accumulated
      rcases S.minor i hi declaration horigin binderDepth Hdomain
          Hreplacement Htr Htype with ⟨Hnew, HnewType⟩
      refine ⟨targets[(recInfos.map (·.motive)).size + i]!, Hnew,
        HnewType, ?_⟩
      simp only [State]
      have hposition : (recInfos.map (·.motive)).size + i <
          targets.length := by
        rw [S.targets_length]
        omega
      rw [getElem!_pos targets _ hposition,
        List.take_succ_eq_append_getElem hposition]
      simp [List.append_assoc]
    · intro i hi declaration horigin binderDepth accumulated Hstate _
        oldDelta oldDomain newDomain oldDomainTarget Hdomain Hreplacement Htr
        Htype
      subst accumulated
      rcases S.index i hi declaration horigin binderDepth Hdomain
          Hreplacement Htr Htype with ⟨Hnew, HnewType⟩
      refine ⟨targets[(recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size + i]!, Hnew, HnewType, ?_⟩
      simp only [State]
      have hposition : (recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size + i < targets.length := by
        rw [S.targets_length]
        omega
      rw [getElem!_pos targets _ hposition,
        List.take_succ_eq_append_getElem hposition]
      simp [List.append_assoc]
    · intro declaration horigin binderDepth accumulated Hstate _ oldDelta
        oldDomain newDomain oldDomainTarget Hdomain Hreplacement Htr Htype
      subst accumulated
      rcases S.major declaration horigin binderDepth Hdomain Hreplacement Htr
          Htype with ⟨Hnew, HnewType⟩
      refine ⟨targets[(recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size]!, Hnew, HnewType, ?_⟩
      simp only [State]
      have hposition : (recInfos.map (·.motive)).size +
          (recInfos.flatMap (·.minors)).size +
          recInfos[ownerIdx]!.indices.size < targets.length := by
        rw [S.targets_length]
        omega
      rw [getElem!_pos targets _ hposition,
        List.take_succ_eq_append_getElem hposition]
      simp [List.append_assoc]
  · intro oldDelta oldResidualTarget accumulated Hstate _ Hreplacement Htr
      Htype
    have Hstate' : accumulated = initialPrefix ++ targets := by
      rw [Hstate, ← S.targets_length]
      simp
    rw [Hstate']
    exact S.residual Hreplacement Htr Htype

end VerifyInductive
end Lean4Lean
