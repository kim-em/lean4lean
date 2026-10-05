import Lean4Lean.Verify.Inductive.Recursor.CanonicalMinorFields
import Lean4Lean.Verify.Inductive.Nested.Replacement
import Lean4Lean.Verify.Inductive.Recursor.CanonicalConstructorIndices

/-! Inversion of the executable's pre-installation recursor type check.

`CompletedRecursorConstruction.recursorTypes` retains the translation of every
closed generated recursor type produced by `checkRecursorTypes`.  Decomposing
that translation along the five executable binder groups gives translations of
each parameter, motive, minor, index and major domain in the abstract contexts
used by the independent generator.  Translations are syntactically unique
(`TrExprS.uniqueS`), so the parameter and motive groups coincide with the
canonical choices already made before this stage. -/

namespace Lean4Lean.VerifyInductive
open Lean hiding Environment Exception
open Kernel

/-- The retained type check, with the universe parameters named through the
outer context. -/
theorem CompletedRecursorConstruction.recursorTypeTranslation
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < indTypes.size) :
    ∃ type : VExpr,
      TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
        (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
        type ∧
      R.context.venv.IsType (AddInductive.getRecLevelParams H.elimLevel c.lparams).length []
        type := by
  have h := H.recursorTypes.typeAt owner howner
  rwa [H.localExtends.lparams_eq] at h

/-- Five-group decomposition of the checked recursor type, obtained solely by
inverting the retained translation along the exact binder selections of
`declareRecursors`. -/
theorem CompletedRecursorConstruction.recursorTelescope
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) (owner : Nat) (howner : owner < H.recInfos.size) :
    ∃ target : VExpr,
      TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams) []
        (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
        target ∧
      Nonempty (GeneratedRecursorTelescopeTranslation R.context.venv
        (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
        target stats.params.size (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner) := by
  have hsourceOwner : owner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨target, Htr, Htype⟩ := H.recursorTypeTranslation owner hsourceOwner
  let Hsel := H.bindings.toRecursorLocalSelections H.localWF H.params owner howner
  have hnoalias := H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner
  have Htel := Hsel.forallTelescope
    (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices) H.recInfos[owner]!.major)
  rw [Hsel.residual_eq_concreteRecursorResult howner hnoalias] at Htel
  have Htel' : Expr.ForallTelescope
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      (stats.params.size + (H.recInfos.map (·.motive)).size +
        (H.recInfos.flatMap (·.minors)).size + H.recInfos[owner]!.indices.size + 1)
      (concreteRecursorResult (H.recInfos.map (·.motive)).size
        (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner) := Htel
  have Htyped := Expr.ForallTelescopeTypeTranslation.ofTrExprS Htel' Htr Htype
  rcases TrExprS.forallTelescope_shape_with_context Htel' Htr with
    ⟨domains, result, hlen, htarget, Hresult⟩
  rcases List.exists_append_five_of_length_eq domains stats.params.size
      (H.recInfos.map (·.motive)).size (H.recInfos.flatMap (·.minors)).size
      H.recInfos[owner]!.indices.size 1 hlen with
    ⟨params, motives, minors, indices, major, hdomains, hp, hm, hmi, hi, hma⟩
  refine ⟨target, Htr, ⟨⟨params, motives, minors, indices, major, result, ?_, hp, hm, hmi, hi,
    hma, Htyped, ?_⟩⟩⟩
  · simpa [hdomains] using htarget
  · simpa [hdomains] using Hresult

/-- The parameter group of the checked recursor type is the cached parameter
telescope: both translate the same closed parameter prefix. -/
theorem CompletedRecursorConstruction.recursorTelescope_params
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) {owner : Nat} {target : VExpr}
    (T : GeneratedRecursorTelescopeTranslation R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner) :
    T.params = H.parameterSuffix.parameterDecls.toCtx.reverse := by
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams : H.params.fvars.Nodup := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  have Htr := T.typed.translation
  rw [T.target_eq, VExpr.wrapForalls_append, VExpr.wrapForalls_append, VExpr.wrapForalls_append,
    VExpr.wrapForalls_append] at Htr
  have Htel := H.params.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) <|
      H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
      H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
      H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
        (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
          H.recInfos[owner]!.major))
  have Hdomains := (TrExprS.forallDomainsOnly Htel T.params_length Htr).1
  rw [H.params.forallDomainsOnly H.localWF hparams] at Hdomains
  have Hcached := H.sourceParameterTranslation
  rw [← H.parameterDomains] at Hcached
  have heq := Hdomains.uniqueS Hcached
  exact VExpr.wrapForalls_prefix_domains_eq (suffix := []) T.params_length
    (by simp [H.parameterDomains, H.sourceParameterCount])
    (by simpa using heq)

/-- The motive group of the checked recursor type is the generator's motive
list: both translate the same parameter-closed motive telescope. -/
theorem CompletedRecursorConstruction.recursorTelescope_motives
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) {owner : Nat} {target : VExpr}
    (T : GeneratedRecursorTelescopeTranslation R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (g : InductiveSignature.Instance s)
    (hp : s.params = R.parameterScope.toCtx.reverse)
    (hf : s.families = H.consumedFamilies)
    (hl : g.levels = recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)
    (hu : VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some g.targetLevel) :
    T.motives = g.motives := by
  have houter := H.bindings.outerNodup H.params H.noAlias
  have hparams : H.params.fvars.Nodup := (List.nodup_append.mp (List.nodup_append.mp houter).1).1
  have hmotives : H.bindings.motives.fvars.Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp houter).1).2.1
  have Htr := T.typed.translation
  rw [T.target_eq, VExpr.wrapForalls_append, VExpr.wrapForalls_append, VExpr.wrapForalls_append,
    VExpr.wrapForalls_append] at Htr
  let inner := H.localContext.lctx.mkForall (H.recInfos.flatMap (·.minors)) <|
    H.localContext.lctx.mkForall H.recInfos[owner]!.indices <|
    H.localContext.lctx.mkForall #[H.recInfos[owner]!.major]
      (.app (mkAppN H.recInfos[owner]!.motive H.recInfos[owner]!.indices)
        H.recInfos[owner]!.major)
  have Htel := H.params.mkForall_forallTelescope H.localWF
    (H.localContext.lctx.mkForall (H.recInfos.map (·.motive)) inner)
  have Hres := TrExprS.forallTelescope_residual Htel T.params_length Htr
  have HtelM := (H.bindings.motives.mkForall_forallTelescope H.localWF inner).abstractN
    H.params.fvars
  have Hdom := (TrExprS.forallDomainsOnly HtelM (by simpa using T.motives_length) Hres).1
  rw [Expr.forallDomainsOnly_abstractN, H.bindings.motives.forallDomainsOnly H.localWF hmotives]
    at Hdom
  have hmotivesClosed : Closed (H.localContext.lctx.mkForall (H.recInfos.map (·.motive))
      (.sort .zero)) :=
    H.bindings.motives.mkForall_closed H.localWF hmotives H.recursorWF.lctxClosed trivial
  rw [Expr.abstractN_eq_abstractList_of_closed hparams hmotivesClosed] at Hdom
  have Hgen := (H.generatedMotivesTranslation g hp hf hl hu).1
  have hp' : g.params = H.parameterSuffix.parameterDecls.toCtx.reverse := by
    rw [InductiveSignature.Instance.params, hp, hl, H.parameterDomains]
  rw [H.recursorEnv, hp', ← H.recursorTelescope_params T] at Hgen
  have heq := Hdom.uniqueS Hgen
  exact VExpr.wrapForalls_prefix_domains_eq (suffix := []) T.motives_length
    (by simp [InductiveSignature.Instance.motives, hf]) (by simpa using heq)

/-- `RecursorLocalSelections.minorBinderAt` before `inferImplicit`: the flat
minor slot of the raw recursor type is the retained minor declaration type
closed over parameters, motives and the strictly earlier minors. -/
theorem RecursorLocalSelections.minorBinderAtRaw
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias)
    (D : BoundFVarDeclarationAt c (recInfos.flatMap (·.minors)) minorIdx) :
    Expr.ForallBinderAt
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive recInfos[ownerIdx]!.indices)
           recInfos[ownerIdx]!.major))
      (stats.params.size + (recInfos.map (·.motive)).size + minorIdx)
      (D.type.abstractN
        (H.params.fvars ++ H.motives.fvars ++ H.minors.fvars.take minorIdx)) := by
  let minorBody :=
    c.lctx.mkForall recInfos[ownerIdx]!.indices <|
    c.lctx.mkForall #[recInfos[ownerIdx]!.major]
      (.app (mkAppN recInfos[ownerIdx]!.motive
        recInfos[ownerIdx]!.indices) recInfos[ownerIdx]!.major)
  let minorSource :=
    c.lctx.mkForall (recInfos.flatMap (·.minors)) minorBody
  let motiveSource :=
    c.lctx.mkForall (recInfos.map (·.motive)) minorSource
  let parts := hnoalias.parts
  have hminorFVars : minorIdx < H.minors.fvars.length := by
    rw [← H.minors.size]
    exact D.inBounds
  have Hminor : Expr.ForallBinderAt minorSource minorIdx
      (D.type.abstractN (H.minors.fvars.take minorIdx)) := by
    exact H.minors.forallBinderAt parts.minors D (body := minorBody)
  have HminorMotives := Hminor.abstractN H.motives.fvars 0
  have hdomainMotives :
      (D.type.abstractN (H.minors.fvars.take minorIdx)).abstractN
          H.motives.fvars minorIdx =
        D.type.abstractN
          (H.motives.fvars ++ H.minors.fvars.take minorIdx) := by
    have Hclose := Expr.abstractN_after_inner
      (e := D.type) (outer := H.motives.fvars)
      (inner := H.minors.fvars.take minorIdx) (k := 0)
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hminorFVars)] using Hclose
  have Hmotives := H.motives.forallTelescope minorSource
  have HthroughMotives := Hmotives.prependBinderAt (by
    simpa [Nat.zero_add, hdomainMotives] using HminorMotives)
  have HthroughParams := HthroughMotives.abstractN H.params.fvars 0
  have hdomainParams :
      (D.type.abstractN
          (H.motives.fvars ++ H.minors.fvars.take minorIdx)).abstractN
          H.params.fvars (H.motives.fvars.length + minorIdx) =
        D.type.abstractN
          (H.params.fvars ++ (H.motives.fvars ++
            H.minors.fvars.take minorIdx)) := by
    have Hclose := Expr.abstractN_after_inner
      (e := D.type) (outer := H.params.fvars)
      (inner := H.motives.fvars ++ H.minors.fvars.take minorIdx)
      (k := 0)
    simpa [List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hminorFVars), List.append_assoc]
      using Hclose
  have Hparams := H.params.forallTelescope motiveSource
  have hparamsLength : H.params.fvars.length = stats.params.size := by
    rw [← H.params.size]
  have hmotivesLength : H.motives.fvars.length =
      (recInfos.map (·.motive)).size := by
    rw [← H.motives.size]
  have hmotivesLength' : H.motives.fvars.length = recInfos.size := by
    simpa using hmotivesLength
  have HrawBase := Hparams.prependBinderAt (by
    simpa [Nat.zero_add, Nat.add_assoc] using HthroughParams)
  have hdomainParamsStats :
      (D.type.abstractN
          (H.motives.fvars ++ H.minors.fvars.take minorIdx)).abstractN
          H.params.fvars (recInfos.size + minorIdx) =
        D.type.abstractN
          (H.params.fvars ++ (H.motives.fvars ++
            H.minors.fvars.take minorIdx)) := by
    rw [← hmotivesLength']
    exact hdomainParams
  rw [hdomainParamsStats] at HrawBase
  have Hraw : Expr.ForallBinderAt
      (c.lctx.mkForall stats.params motiveSource)
      (H.params.fvars.length + (H.motives.fvars.length + minorIdx))
      (D.type.abstractN
        (H.params.fvars ++ (H.motives.fvars ++
          H.minors.fvars.take minorIdx))) := by
    simpa [hparamsLength, hmotivesLength, Nat.add_assoc] using
      HrawBase
  simpa [motiveSource, minorSource, minorBody, hparamsLength,
    hmotivesLength, Nat.add_assoc] using Hraw

/-- Sequential-model form of `minorBinderAtRaw` for a locally closed context. -/
theorem RecursorLocalSelections.minorBinderAtRawList
    (H : RecursorLocalSelections c stats recInfos ownerIdx)
    (hnoalias : H.NoAlias) (hl : LocalContext.LctxClosed c.lctx)
    (D : BoundFVarDeclarationAt c (recInfos.flatMap (·.minors)) minorIdx) :
    Expr.ForallBinderAt
      (c.lctx.mkForall stats.params <|
       c.lctx.mkForall (recInfos.map (·.motive)) <|
       c.lctx.mkForall (recInfos.flatMap (·.minors)) <|
       c.lctx.mkForall recInfos[ownerIdx]!.indices <|
       c.lctx.mkForall #[recInfos[ownerIdx]!.major]
         (.app (mkAppN recInfos[ownerIdx]!.motive recInfos[ownerIdx]!.indices)
           recInfos[ownerIdx]!.major))
      (stats.params.size + (recInfos.map (·.motive)).size + minorIdx)
      (D.type.abstractList
        (H.params.fvars ++ H.motives.fvars ++ H.minors.fvars.take minorIdx)) := by
  have h := H.minorBinderAtRaw hnoalias D
  have hall : (H.params.fvars ++ (H.motives.fvars ++
      (H.minors.fvars ++ (H.indices.fvars ++ H.major.fvars)))).Nodup := hnoalias
  have hnodup : (H.params.fvars ++ H.motives.fvars ++
      H.minors.fvars.take minorIdx).Nodup := by
    rw [List.append_assoc]
    exact List.Nodup.sublist (List.Sublist.append (List.Sublist.refl _)
      (List.Sublist.append (List.Sublist.refl _)
        ((List.take_sublist _ _).trans (List.sublist_append_left _ _)))) hall
  rwa [Expr.abstractN_eq_abstractList_of_closed hnodup (D.closed hl)] at h

theorem GeneratedRecursorTelescopeTranslation.take_minorPrefix
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (minorIdx : Nat) (h : minorIdx ≤ T.minors.length) :
    (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major).take
        (numParams + numMotives + minorIdx) =
      T.params ++ T.motives ++ T.minors.take minorIdx := by
  have hp := T.params_length
  have hm := T.motives_length
  simp only [List.append_assoc]
  rw [List.take_append, List.take_of_length_le (by omega),
    List.take_append, List.take_of_length_le (by omega),
    List.take_append_of_le_length (by omega),
    show numParams + numMotives + minorIdx - T.params.length - T.motives.length = minorIdx by omega]

theorem GeneratedRecursorTelescopeTranslation.getElem_minor
    (T : GeneratedRecursorTelescopeTranslation env Us source target
      numParams numMotives numMinors numIndices ownerIdx)
    (minorIdx : Nat) (h : minorIdx < T.minors.length)
    (hi : numParams + numMotives + minorIdx <
      (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major).length) :
    (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major)[numParams + numMotives + minorIdx] =
      T.minors[minorIdx] := by
  have hp := T.params_length
  have hm := T.motives_length
  simp only [List.append_assoc]
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
    List.getElem_append_left (by omega)]
  congr 1
  omega

/-- The flat minor slot of the checked recursor type translates the retained
minor declaration type, closed over parameters, motives and earlier minors,
in the generator's abstract context for that slot. -/
theorem CompletedRecursorConstruction.recursorTelescope_minor
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : GeneratedRecursorTelescopeTranslation R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D : BoundFVarDeclarationAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx) :
    TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (abstractForallContext (T.params ++ T.motives ++ T.minors.take minorIdx) [])
      (D.type.abstractList (H.params.fvars ++ H.bindings.motives.fvars ++
        H.bindings.flatMinors.fvars.take minorIdx))
      (T.minors[minorIdx]'(by rw [T.minors_length]; exact D.inBounds)) := by
  let Hsel := H.bindings.toRecursorLocalSelections H.localWF H.params owner howner
  have hnoalias := H.bindings.selectionNoAlias H.localWF H.params H.noAlias owner howner
  have Hb := Hsel.minorBinderAtRawList hnoalias H.recursorWF.lctxClosed D
  have Htr := T.typed.translation
  rw [T.target_eq] at Htr
  have hminor : minorIdx < T.minors.length := by rw [T.minors_length]; exact D.inBounds
  have hi : stats.params.size + (H.recInfos.map (·.motive)).size + minorIdx <
      (T.params ++ T.motives ++ T.minors ++ T.indices ++ T.major).length := by
    have hmin := T.minors_length
    simp only [List.length_append, T.params_length, T.motives_length, T.minors_length,
      T.indices_length, T.major_length]
    omega
  have Ht := Hb.translation Htr hi
  rw [T.take_minorPrefix minorIdx (Nat.le_of_lt hminor), T.getElem_minor minorIdx hminor hi] at Ht
  exact Ht

end Lean4Lean.VerifyInductive
