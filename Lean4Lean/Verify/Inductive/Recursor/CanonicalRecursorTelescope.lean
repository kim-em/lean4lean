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

/-- The field domains of a flat minor slot of the checked recursor type are
the `insertBinders` lift of the selected source field domains; the residual
is the translation of the hypothesis telescope and motive application closed
over the fields. -/
theorem CompletedRecursorConstruction.recursorTelescope_minorFields
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) {owner : Nat} (howner : owner < H.recInfos.size)
    {target : VExpr}
    (T : GeneratedRecursorTelescopeTranslation R.context.venv
      (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      (AddInductive.declareRecursors.recursorType stats H.recInfos H.localContext.lctx owner)
      target stats.params.size (H.recInfos.map (·.motive)).size
      (H.recInfos.flatMap (·.minors)).size H.recInfos[owner]!.indices.size owner)
    (minorIdx : Nat)
    (D : BoundFVarDeclarationAt H.localContext (H.recInfos.flatMap (·.minors)) minorIdx)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size)
    (hD : D.type = H.origins.minorTypes[mowner]![localIndex]!) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let fields := InductiveSignature.insertBinders
      ((H.sourceFields mowner hmowner localIndex hlocal).map
        (VExpr.instL (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible)))
      ((H.recInfos.map (·.motive)).size + minorIdx)
    let ys := H.params.fvars ++ H.bindings.motives.fvars ++
      H.bindings.flatMinors.fvars.take minorIdx
    ∃ residual : VExpr,
      T.minors[minorIdx]'(by rw [T.minors_length]; exact D.inBounds) =
        VExpr.wrapForalls fields residual ∧
      TrExprS R.context.venv (AddInductive.getRecLevelParams H.elimLevel c.lparams)
        (abstractForallContext (T.params ++ T.motives ++ T.minors.take minorIdx ++ fields) [])
        (((S.sourceContext.mkForall S.hypotheses S.motiveApp).abstractN
          S.fields_bound.fvars).abstractList ys S.fields.size)
        residual := by
  intro S fields ys
  have Hminor := H.recursorTelescope_minor howner T minorIdx D
  have hsourceOwner : mowner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨horigin, _, _, _, _, _, _, _, _, _, _, _, _, _, hsourceLE⟩ :=
    H.minorSources mowner hmowner hsourceOwner localIndex hlocal
  let HS := H.sourceMinorSemantics mowner hmowner localIndex hlocal
  have hsource : D.type = S.sourceType := by
    rw [hD, ← horigin, ← S.consumed_eq, HS.semantic.sourceType_consumeTypeAnnotations_eq_self]
  rw [hsource] at Hminor
  have hminor : minorIdx < (H.recInfos.flatMap (·.minors)).size := D.inBounds
  have Htel := (S.fieldTelescope (S.sourceContext.mkForall S.hypotheses S.motiveApp)).abstractList ys
  rw [← S.sourceType_eq, Nat.zero_add] at Htel
  obtain ⟨F, residual, hF, heq, Hres⟩ := TrExprS.forallTelescope_shape_with_context Htel Hminor
  have Hdom := (TrExprS.forallDomainsOnly Htel hF (heq ▸ Hminor)).1
  have hsort : S.sourceContext.mkForall S.fields (.sort .zero) =
      H.localContext.lctx.mkForall S.fields (.sort .zero) := by
    rw [← S.sourceContext_eq]
    exact (S.fields_bound.mkForall_mono hsourceLE (.sort .zero)).symm
  rw [Expr.forallDomainsOnly_abstractList, S.sourceType_eq, ← S.sourceContext_eq,
    S.fields_bound.forallDomainsOnly S.sourceFullWF S.fields_nodup, S.sourceContext_eq, hsort]
    at Hdom
  have hmotivesLen : H.bindings.motives.fvars.length = T.motives.length := by
    rw [H.bindings.motives.length_fvars, T.motives_length]
  have hminorsLen : (H.bindings.flatMinors.fvars.take minorIdx).length =
      (T.minors.take minorIdx).length := by
    rw [List.length_take, List.length_take, H.bindings.flatMinors.length_fvars, T.minors_length]
  have Htemplate := H.minorFieldsTemplate mowner hmowner localIndex hlocal
    (T.motives ++ T.minors.take minorIdx)
    (H.bindings.motives.fvars ++ H.bindings.flatMinors.fvars.take minorIdx)
    (by simp only [List.length_append, hmotivesLen, hminorsLen])
  have hinserted : (T.motives ++ T.minors.take minorIdx).length =
      (H.recInfos.map (·.motive)).size + minorIdx := by
    simp only [List.length_append, T.motives_length, List.length_take, T.minors_length]
    omega
  rw [H.recursorEnv, ← H.recursorTelescope_params T, hinserted, ← List.append_assoc,
    ← List.append_assoc] at Htemplate
  have hF' : F = fields :=
    VExpr.wrapForalls_prefix_domains_eq (suffix := []) hF (by
      simp only [fields, InductiveSignature.insertBinders, List.length_map, List.length_zipIdx,
        H.sourceFields_length]
      exact hF.symm ▸ rfl) (by simpa [ys, fields, List.append_assoc] using Hdom.uniqueS Htemplate)
  refine ⟨residual, by rw [heq, hF'], ?_⟩
  rw [← hF']
  simpa [abstractForallContext, List.reverse_append, List.map_append, List.append_assoc] using Hres

/-- The executable's universe arguments translate to the recursor's abstract
level list, for any materialized header over the same parameter names. -/
theorem checkInductiveTypes.loopInd.MaterializedHeaderResult.recursorLevelTranslation'
    {env : VEnv} {Us : List Name} {Δ : VLCtx} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {depth : Nat}
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult env Us Δ stats decl depth)
    (hlparams : Us.Nodup) {elimLevel : Level}
    (Helim : AddInductive.AdmissibleElimLevel Us elimLevel) :
    stats.levels.mapM (VLevel.ofLevel (AddInductive.getRecLevelParams elimLevel Us)) =
      some (recursorDeclarationAbstractLevels Us Helim) := by
  cases elimLevel with
  | zero =>
    simpa [AddInductive.getRecLevelParams, recursorDeclarationAbstractLevels,
      List.map_param_idxOf_eq_params hlparams] using H.levelTranslation
  | param fresh =>
    have hshifted := VLevel.mapM_ofLevel_fresh_cons Helim H.levelTranslation
    simpa [AddInductive.getRecLevelParams, recursorDeclarationAbstractLevels,
      List.map_param_idxOf_eq_params hlparams] using hshifted
  | succ level | max level₁ level₂ | imax level₁ level₂ | mvar id =>
    simp [AddInductive.AdmissibleElimLevel] at Helim

theorem CompletedRecursorConstruction.statsLevelsTranslation
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R) :
    stats.levels.mapM (VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)) =
      some (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible) :=
  R.materialized.recursorLevelTranslation' H.lparamsNodup H.elimLevelAdmissible

/-- The source motive application of a minor, with the owner of its motive
resolved through the validated terminal application. -/
theorem CompletedRecursorConstruction.minorMotiveAppForm
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorConstruction R)
    (mowner : Nat) (hmowner : mowner < H.recInfos.size)
    (localIndex : Nat) (hlocal : localIndex < H.origins.minorTypes[mowner]!.size) :
    let S := H.origins.minorShapes mowner hmowner localIndex hlocal
    let HS := H.sourceMinorSemantics mowner hmowner localIndex hlocal
    S.motiveApp = Expr.app
      (mkAppN H.recInfos[mowner]!.motive
        (AddInductive.getIIndices stats HS.semantic.traversal.terminal).2)
      (mkAppN (mkAppN (.const S.constructor.name stats.levels) stats.params) S.fields) := by
  intro S HS
  have hsourceOwner : mowner < indTypes.size := by rwa [← H.sourceFamilyCount]
  obtain ⟨_, _, _, _, traversal, htraversal, _, _, _, _, _, hmotiveApp, _, _, _⟩ :=
    H.minorSources mowner hmowner hsourceOwner localIndex hlocal
  have heq : traversal = HS.semantic.traversal :=
    Option.some.inj (htraversal.symm.trans HS.semantic.traversal_eq)
  subst heq
  have hfst := checkPositivityStep.getIIndices.fst_eq_of_valid (H.constructorTerminalOwner mowner hmowner localIndex hlocal HS)
  rw [hmotiveApp]
  rcases hindices : AddInductive.getIIndices stats HS.semantic.traversal.terminal with
    ⟨motiveOwner, indices⟩
  have : motiveOwner = mowner := by simpa [hindices] using hfst
  subst this
  rfl

/-- Closing a list of distinct free variables over itself yields the
canonical descending de Bruijn spine above the abstraction depth. -/
theorem Expr.abstractList_fvar_spine (fvs : List FVarId) (hnd : fvs.Nodup) (k : Nat) :
    (fvs.map Expr.fvar).map (fun e => e.abstractList fvs k) =
      List.ofFn fun j : Fin fvs.length => Expr.bvar (k + (fvs.length - 1 - j)) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < fvs.length := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractList_fvar_getElem hnd i hi

/-- Closing a prefix of distinct free variables over a longer distinct list
places each at its descending position above the trailing variables. -/
theorem Expr.abstractList_fvar_prefix_spine (fvs rest : List FVarId)
    (hnd : (fvs ++ rest).Nodup) (k : Nat) :
    (fvs.map Expr.fvar).map (fun e => e.abstractList (fvs ++ rest) k) =
      List.ofFn fun j : Fin fvs.length => Expr.bvar ((k + rest.length) + (fvs.length - 1 - j)) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < fvs.length := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn]
    have h := Expr.abstractList_fvar_getElem hnd (fvs := fvs ++ rest) i (by simp; omega) (k := k)
    rw [List.getElem_append_left hi] at h
    rw [h]
    congr 1
    simp only [List.length_append]
    omega

/-- Bound variables below the abstraction depth are untouched. -/
theorem Expr.abstractList_bvar_spine (n below : Nat) (fvs : List FVarId) (k : Nat)
    (h : below + n ≤ k) :
    (List.ofFn fun j : Fin n => Expr.bvar (below + (n - 1 - j))).map
        (fun e => e.abstractList fvs k) =
      List.ofFn fun j : Fin n => Expr.bvar (below + (n - 1 - j)) := by
  apply List.ext_getElem
  · simp
  · intro i hleft hright
    have hi : i < n := by simpa using hright
    simp only [List.getElem_map, List.getElem_ofFn]
    exact Expr.abstractList_bvar_lt fvs (by omega)

end Lean4Lean.VerifyInductive
