import Lean4Lean.Verify.Inductive.CompletedRecursorPhases
import Lean4Lean.Verify.Inductive.CompletedSourceSignature
import Lean4Lean.Verify.Inductive.Header.SingletonElimination
import Lean4Lean.Verify.Inductive.Nested.ConstructorParameterRawShape
import Lean4Lean.Theory.Inductive.SignatureLemmas

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The universe and naming policy is fixed by the successful executable
run, independently of the supplied source signature. -/
noncomputable def CompletedRecursorPhasesResult.generationInstance
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) (s : InductiveSignature) :
    InductiveSignature.Instance s where
  uvars := (AddInductive.getRecLevelParams H.elimLevel c.lparams).length
  levels := recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible
  targetLevel := Classical.choose H.elimLevelAdmissible.ofLevel
  recursorName owner := s.families[owner].name.str "rec"

/-- The completed run fixes both the source signature and its universe
instance. Generation and concrete metadata must use this same choice. -/
noncomputable def CompletedRecursorPhasesResult.canonicalGeneration
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    InductiveSignature.Instance H.toCompletedRecursorConstruction.generationSignature :=
  H.toCompletedRecursorConstruction.generationInstance

/-- The final phase result installs precisely its one canonical generator's
recursor table. -/
theorem CompletedRecursorPhasesResult.canonicalGeneration_recursors
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    H.entries.map Prod.snd = H.canonicalGeneration.recursors :=
  H.canonicalRecursors

theorem CompletedRecursorPhasesResult.generationInstance_target
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) (s : InductiveSignature) :
    VLevel.ofLevel (AddInductive.getRecLevelParams H.elimLevel c.lparams)
      H.elimLevel = some (H.generationInstance s).targetLevel :=
  Classical.choose_spec H.elimLevelAdmissible.ofLevel

/-- The completed producer retains the reason for its elimination universe.
The nonzero branch is already interpreted in the independent source model;
the singleton branch retains every actual field check for interpretation
against the normalized constructor telescope. -/
theorem CompletedRecursorPhasesResult.eliminationDecision
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {decl : VInductDecl} {nparams depth : Nat} {isUnsafe : Bool}
    {sourceEnv : VEnv} {indTypes : Array InductiveType}
    {ctorEnv outEnv : Environment}
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    (∀ family ∈ decl.types, family.resultLevel.IsNeverZero) ∨
    H.elimLevel = .zero ∨
    ∃ ind, indTypes = #[ind] ∧
      (ind.ctors = [] ∨ ∃ ctor, ind.ctors = [ctor] ∧
        LargeEliminationTrace stats
          { c with env := ctorEnv, checkLCtx := {} } ctor.type 0 #[]) := by
  by_cases hzero : H.elimLevel = .zero
  · exact .inr (.inl hzero)
  rcases AddInductive.isLargeEliminator.shape_of_checked
      (AddInductive.getElimLevel.large_of_checked H.elimLevelChecked hzero) with
    hnotzero | ⟨ind, hind, hctors⟩
  · exact .inl fun _ hfamily =>
      R.sourceMaterialized.familyNeverZero hnotzero hfamily
  · refine .inr (.inr ⟨ind, hind, ?_⟩)
    rcases hctors with hnil | ⟨ctor, hctor, hchecked⟩
    · exact .inl hnil
    · exact .inr ⟨ctor, hctor,
        AddInductive.isLargeEliminator.loop.trace hchecked⟩

/-- Source modeling transports the nonzero decision to every specialized
family in the selected signature. -/
theorem CompletedRecursorPhasesResult.generationInstance_nonzero
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {s : InductiveSignature} (Hmodel : s.Models sourceEnv decl)
    (Hnonzero : ∀ family ∈ decl.types, family.resultLevel.IsNeverZero) :
    ∀ family ∈ s.families.toList,
      (family.resultLevel.inst (H.generationInstance s).levels).IsNeverZero := by
  intro family hfamily
  rcases List.mem_iff_getElem.mp hfamily with ⟨i, hi, rfl⟩
  let owner : Fin s.families.size := ⟨i, by simpa using hi⟩
  rcases Hmodel.family owner with ⟨source, hsource, _, _, _, hlevel, _⟩
  exact ((Hnonzero source hsource).of_equiv hlevel.symm).inst

/-- Once the remaining singleton-field alternative is interpreted, the
universe policy satisfies the independent generator's full admissibility
judgment. Neither universe arity nor naming is a caller choice. -/
theorem CompletedRecursorPhasesResult.generationInstance_admissible
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv)
    {s : InductiveSignature} (Hmodel : s.Models sourceEnv decl)
    (Helim :
      (∀ family ∈ decl.types, family.resultLevel.IsNeverZero) ∨
      H.elimLevel = .zero ∨
      s.SingletonElimination R.headerVEnv (H.generationInstance s).uvars
        (H.generationInstance s).levels) :
    (H.generationInstance s).Admissible R.headerVEnv := by
  refine {
    levels_length := ?_
    levels_wf := recursorDeclarationAbstractLevels_wf H.elimLevelAdmissible
    target_wf := .of_ofLevel (H.generationInstance_target s)
    elimination := ?_ }
  · change (recursorDeclarationAbstractLevels c.lparams H.elimLevelAdmissible).length = s.uvars
    rw [recursorDeclarationAbstractLevels_length, Hmodel.uvars, R.core.uvars]
  · rcases Helim with hnonzero | hsmall | hsingleton
    · exact .inl (H.generationInstance_nonzero Hmodel hnonzero)
    · apply Or.inr; apply Or.inl
      have ht := H.generationInstance_target s
      rw [hsmall] at ht
      have : (H.generationInstance s).targetLevel = .zero := Option.some.inj ht.symm
      rw [this]
      rfl
    · exact .inr (.inr hsingleton)

open _root_.Lean4Lean.InductiveSignature in
/-- The executable singleton decision interpreted against the literal tail
retained with the source constructor selection. -/
theorem SourceConstructorReplay.singletonFields
    (H : SourceConstructorReplay env Us scope stats decl family source sourceCtor s ctor)
    (Hc : ContextWF c) (hus : Us = c.lparams)
    (hle : env ≤ Hc.venv) (henv : env.WF)
    (hscope : scope.WF env Us.length)
    (hparams : env.IsDefEqCtx Us.length [] s.params.reverse scope.toCtx)
    (hu : decl.uvars = Us.length)
    (Htrace : LargeEliminationTrace stats c source.type 0 #[])
    (Hspine : Expr.ForallSpine source.type arity) :
    ∀ i (hi : i < ctor.fields.length),
      env.HasType Us.length (((s.fieldTypes ctor).take i).reverse ++ s.params.reverse)
        (s.fieldType i ctor.fields[i]) (.sort .zero) ∨
      .bvar (ctor.fields.length - 1 - i) ∈ ctor.indices := by
  subst Us
  obtain ⟨tail, tailTarget, sourceDomains, hraw, hprefix, hchecked,
    htail, hcert, hsynthesis, hgenerator⟩ := H
  obtain ⟨rawScope, domains, residual, hrawType, hlength, hrawCtx,
    hcontexts, hshapeCtx, hresidual⟩ := hchecked.rawTranslation henv hscope hraw.type
  have Hclosed := Htrace.singletonClosed Hc Hspine (hraw.type.mono hle)
  rw [hrawType] at Hclosed
  have HrawTail := Hclosed.dropParams
  simp only [List.append_nil, Nat.zero_add, hlength, ← hrawCtx] at HrawTail
  have HrawTail' := HrawTail.of_defeq Hc.checking.tr.wf
    ((hcontexts.wf.toCtx).mono (VEnv.IsType.mono hle))
    ((hresidual.uniq henv hcontexts htail).mono hle)
    (TrExprS.rawShape hshapeCtx.rawShape hresidual htail)
  have Htail' := HrawTail'.defeqCtx Hc.checking.tr.wf.ordered
    (hcontexts.defeqCtx.mono hle)
  have HtailSmall := Htail'.of_mono hle henv Hc.checking.tr.wf hscope.toCtx
    (by simpa [hu] using hcert.isType)
  have Hcanonical := HtailSmall.defeqCtx henv.ordered (hparams.symm henv.ordered)
  rw [sourceConstructor_tail_eq hgenerator] at Hcanonical
  intro i hi
  have hlengthFields : (s.fieldTypes ctor).length = ctor.fields.length := by
    simp [fieldTypes]
  have hresult : (s.familyApp ctor.owner (VLevel.params s.uvars)
      (vars s.params.length ctor.fields.length) ctor.indices).forallArity = 0 :=
    VExpr.forallArity_eq_zero_of_getAppFnArgs (VExpr.getAppFnArgs_mkApps_const _ _ _)
  have Hfield := Hcanonical.fieldAt (Nat.le_refl _) hresult i (by simpa [hlengthFields] using hi)
  have hfield : (s.fieldTypes ctor)[i]'(by simpa [hlengthFields] using hi) = s.fieldType i ctor.fields[i] := by
    simp [fieldTypes]
  rw [hfield] at Hfield
  rcases Hfield with hp | hx
  · exact .inl hp
  · apply Or.inr
    simp only [familyApp, VExpr.getAppFnArgs_mkApps_const, hlengthFields] at hx
    rcases List.mem_append.mp hx with hparam | hindex
    · simp only [vars, List.mem_map] at hparam
      obtain ⟨j, hj, heq⟩ := hparam
      have heq := VExpr.bvar.inj heq
      omega
    · exact hindex

/-- A singleton source block accepted by the concrete large-elimination
check satisfies the generator's field condition at every universe instance. -/
theorem CompletedConstructorPhases.singletonElimination
    (R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv)
    (hls : ∀ level ∈ levels, level.WF U)
    (Hsingleton : ∃ ind, indTypes = #[ind] ∧
      (ind.ctors = [] ∨ ∃ ctor, ind.ctors = [ctor] ∧
        LargeEliminationTrace stats { c with env := ctorEnv, checkLCtx := {} }
          ctor.type 0 #[])) :
    R.sourceSignature.SingletonElimination R.headerVEnv U levels := by
  obtain ⟨ind, hind, hctors⟩ := Hsingleton
  have hfcount : R.sourceSignature.families.size = decl.types.length := by
    simp [CompletedConstructorPhases.sourceSignature,
      CompletedConstructorPhases.sourceSignatureHeader,
      checkInductiveTypes.loopInd.MaterializedHeaderResult.signatureHeader]
  have hsourceCount := Lean4Lean.List.Forall₂.length_eq R.core.types
  have hccount : R.sourceSignature.constructors.size = decl.ownedConstructors.length := by
    simp [CompletedConstructorPhases.sourceSignature]
  have hsourceCtorCount := Lean4Lean.VerifyInductive.TrInductDeclCore.ownedConstructors_length R.core
  have hctorCount : decl.ownedConstructors.length = ind.ctors.length := by
    simpa [hind, ownedConstructors] using hsourceCtorCount.symm
  refine ⟨?_, ?_, ?_⟩
  · simpa [hind, hfcount] using hsourceCount.symm
  · rw [hccount, hctorCount]
    rcases hctors with hnil | ⟨ctor, hctor, _⟩ <;> simp_all
  · intro ctor hctor i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hctor
    have hj' : j < decl.ownedConstructors.length := by simpa [hccount] using hj
    obtain ⟨production, hproduction, hreplay⟩ := R.sourceSignature_replay ⟨j, hj'⟩
    simp [hind] at hproduction
    rcases hctors with hnil | ⟨source, hsource, htrace⟩
    · simp [hnil] at hproduction
    · have hprod : production = source := by simpa [hsource] using hproduction
      subst production
      have henv : sourceEnv.WF := by
        simpa only [R.sourceContextVEnv] using R.sourceContext.checking.tr.wf
      have hheader := Lean4Lean.VerifyInductive.TrInductDeclCore.envTypesWF R.core henv
      have hscope : R.parameterScope.WF R.headerVEnv c.lparams.length := by
        rw [← R.materializedParameterScope]
        exact R.materialized.runtimeScope.scopeWF hheader
      have hparams : R.headerVEnv.IsDefEqCtx c.lparams.length []
          R.sourceSignature.params.reverse R.parameterScope.toCtx := by
        simpa only [CompletedConstructorPhases.sourceSignature, R.materializedParams,
          R.materializedParameterScope, R.sourceSignatureHeader_params] using R.materialized.paramsContext
      have hspine := R.parameterPrefixes.spines 0 (by simp [hind]) 0 (by simp [hind, hsource])
      simp only [hind, Array.getElem_singleton, hsource, List.getElem_cons_zero] at hspine
      obtain ⟨arity, hspine⟩ := hspine
      have hfields := hreplay.singletonFields
        (R.context.withCheckLCtx {} LocalContext.empty_mapWF .empty) rfl
        (R.installation.constructorLE.trans R.ctorLE) hheader hscope hparams
        R.core.uvars htrace hspine i hi
      rcases hfields with hproof | hindex
      · exact .inl (by simpa only [List.map_append, List.map_reverse, VExpr.instL, VLevel.inst, Array.getElem_toList] using hproof.instL hls)
      · exact .inr hindex

/-- The actual completed universe check discharges all elimination cases
for the one fixed source signature and generation instance. -/
theorem CompletedRecursorPhasesResult.rawGeneration_admissible
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    (H.generationInstance R.sourceSignature).Admissible R.headerVEnv := by
  apply H.generationInstance_admissible R.sourceSignature_models
  rcases H.eliminationDecision with hnonzero | hzero | hsingleton
  · exact .inl hnonzero
  · exact .inr (.inl hzero)
  · exact .inr (.inr (R.singletonElimination
      (recursorDeclarationAbstractLevels_wf H.elimLevelAdmissible) hsingleton))


/-- Admissibility belongs to the same consumed signature selected before
installation, including the actual singleton decision and universe policy. -/
theorem CompletedRecursorPhasesResult.canonicalGeneration_admissible
    {R : CompletedConstructorPhases c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : CompletedRecursorPhasesResult R outEnv) :
    H.canonicalGeneration.Admissible R.headerVEnv :=
  H.toCompletedRecursorConstruction.consumedGeneration.admissible

end VerifyInductive
end Lean4Lean
