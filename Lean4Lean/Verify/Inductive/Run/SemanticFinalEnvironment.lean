import Lean4Lean.Verify.Inductive.Run.SemanticAddInduct
import Lean4Lean.Verify.Inductive.Run.EqCanonical

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

private theorem property_of_mem_zipWith
    (f : α → β → γ) (P : γ → Prop)
    (hproperty : ∀ a b, P (f a b)) :
    ∀ {as : List α} {bs : List β} {value : γ},
      value ∈ List.zipWith f as bs → P value := by
  intro as
  induction as with
  | nil => simp
  | cons a as ih =>
    intro bs value hmem
    cases bs with
    | nil => simp at hmem
    | cons b bs =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact hproperty a b
      · exact ih htail

private theorem inductiveTypeInfo_isUnsafe
    (hinfo : info ∈ (AddInductive.inductiveTypeInfos stats nparams
      indTypes numNested isUnsafe lparams).toList) :
    info.isUnsafe = isUnsafe := by
  simp only [AddInductive.inductiveTypeInfos, Array.toList_zipWith,
    Array.toList_map] at hinfo
  apply property_of_mem_zipWith
    (f := fun (indType : InductiveType) (numIndices : Nat) =>
      show InductiveVal from {
        name := indType.name
        levelParams := lparams
        type := indType.type
        numParams := nparams
        numIndices := numIndices
        all := indTypes.toList.map (fun x => x.name)
        ctors := indType.ctors.map (fun x => x.name)
        numNested := numNested
        isRec := AddInductive.isRec indTypes stats.indConsts
        isUnsafe := isUnsafe
        isReflexive := AddInductive.isReflexive indTypes stats.indConsts })
    (P := fun candidate => candidate.isUnsafe = isUnsafe)
    (by intros; rfl) hinfo

private theorem InductiveHeaderEntries.entrySafety_eq_unsafe
    (H : InductiveHeaderEntries
      (AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe lparams).toList entries)
    (hunsafe : isUnsafe = true) (hentry : entry ∈ entries) :
    entry.1.safety = .unsafe := by
  rcases H.originInfo hentry with ⟨info, hinfo, hentryInfo⟩
  rw [hentryInfo]
  have hinfoUnsafe := inductiveTypeInfo_isUnsafe hinfo
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, hinfoUnsafe, hunsafe]

private theorem ConstructorListEntries.entrySafety_eq_unsafe
    (H : ConstructorListEntries
      (AddInductive.constructorInfo stats lparams isUnsafe owner)
      start ctors entries)
    (hunsafe : isUnsafe = true) (hentry : entry ∈ entries) :
    entry.1.safety = .unsafe := by
  induction H with
  | nil => simp at hentry
  | cons Htail ih =>
    simp only [List.mem_cons] at hentry
    rcases hentry with rfl | htail
    · simp [AddInductive.constructorInfo, ConstantInfo.safety,
        ConstantInfo.isUnsafe, hunsafe]
    · exact ih htail

private theorem ConstructorTypeEntries.entrySafety_eq_unsafe
    (H : ConstructorTypeEntries
      (AddInductive.constructorInfo stats lparams isUnsafe) types entries)
    (hunsafe : isUnsafe = true) (hentry : entry ∈ entries) :
    entry.1.safety = .unsafe := by
  induction H with
  | nil => simp at hentry
  | cons Hhead Htail ih =>
    rcases List.mem_append.mp hentry with hhead | htail
    · exact Hhead.entrySafety_eq_unsafe hunsafe hhead
    · exact ih htail

private theorem GeneratedRecursors.entrySafety_eq_unsafe
    (H : GeneratedRecursors safety env lparams elimLevel c stats indTypes
      recInfos entries)
    (hsafety : c.safety = .unsafe)
    {entry : ConstantInfo × VConstVal} (hentry : entry ∈ entries) :
    entry.1.safety = .unsafe := by
  rcases List.mem_iff_getElem.mp hentry with ⟨i, hi, heq⟩
  have hi' : i < entries.length := by simpa using hi
  let E := H.entry i hi'
  have hsource : entries[i].1 = .recInfo E.info := E.source_eq
  have hinfoUnsafe : E.info.isUnsafe = true := by
    exact E.isUnsafe.trans (by rw [hsafety]; decide)
  rw [← heq, hsource]
  simp [ConstantInfo.safety, ConstantInfo.isUnsafe, hinfoUnsafe]

/-- A completed safe ordinary run extends the complete safety-indexed model.
The result depends only on the successful run and the source environment
model; equality bootstrap state is irrelevant to inductive soundness. -/
theorem SemanticRunWithStatsResult.extendSafeExact
    {ves : VEnvs}
    (Hrun : SemanticRunWithStatsResult c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env)
    (hsafety : c.safety = .safe)
    (hsource : sourceEnv = ves.venv .safe)
    (hnonempty : indTypes.toList ≠ []) :
    ∃ ves' : VEnvs, ∃ decl : VInductDecl, ∃ envTypes envCtors : VEnv,
      ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      TrInductDeclCore (ves.venv .safe) c.lparams nparams indTypes.toList
        isUnsafe decl envTypes envCtors ∧
      VEnv.AddInduct (ves.venv .safe) decl (ves'.venv .safe) := by
  subst sourceEnv
  rcases Hrun with
    ⟨decl, headerEnv, ctorEnv, Hheaders, R, ⟨Hrecursors⟩⟩
  rcases Hrecursors.canonicalOrdinaryRuleTranslation with ⟨T⟩
  let B0 := Hrecursors.blockCertificate T.rules T.rulesWF
  let B := B0.sf_mono (safety := .safe) (by
    rw [hsafety]
    exact DefinitionSafety.le_rfl)
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  have hdecl : decl.WF (ves.venv .safe) :=
    R.formation.declWF Htranslated.sourceWF
  have hcompile : decl.CompilesTo (ves.venv .safe) B.block :=
    by simpa [B, B0, BlockCertificate.sf_mono, BlockCertificate.block] using
      T.compilation.compilesTo
  have hconstructors :
      InductiveConstructorsSemanticallyCoherent .safe outEnv
        (Hrecursors.outVEnv.addDefEqRules T.rules) := by
    exact Hrecursors.completedConstructorSemantics
      (wf.constructorSemantics (safety := .safe)) T.rules
  have horigins :
      ProductionInductiveOrigins c.env.constants outEnv.constants decl :=
    Hrecursors.productionInductiveOrigins
  have howners : ConstructorOwnersPresent outEnv :=
    Hrecursors.constructorOwnersPresent wf.constructorOwners
  rcases B.extendSafeExact wf hdecl hcompile horigins
      Hrecursors.closed howners hconstructors with
    ⟨ves', wf', hle, hadd, _hsafe⟩
  exact ⟨ves', decl, Hheaders.context.venv, R.declared.venvCtors,
    wf', hle, R.core, hadd⟩

/-- Environment-preservation projection of `extendSafeExact`. -/
theorem SemanticRunWithStatsResult.extendSafe
    {ves : VEnvs}
    (Hrun : SemanticRunWithStatsResult c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env)
    (hsafety : c.safety = .safe)
    (hsource : sourceEnv = ves.venv .safe)
    (hnonempty : indTypes.toList ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rcases Hrun.extendSafeExact wf hsafety hsource hnonempty with
    ⟨ves', _decl, _envTypes, _envCtors, wf', hle, _source, _hadd⟩
  exact ⟨ves', wf', hle⟩

/-- Canonical equality, when already available, is preserved by monotonicity
of the generic safe extension. -/
theorem SemanticRunWithStatsResult.extendSafeOfQuotReady
    (Hrun : SemanticRunWithStatsResult c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env)
    (hEq : CanonicalEqEnvs ves)
    (hsafety : c.safety = .safe)
    (hsource : sourceEnv = ves.venv .safe)
    (hnonempty : indTypes.toList ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rcases Hrun.extendSafe wf hsafety hsource hnonempty with
    ⟨ves', wf', hle⟩
  exact ⟨ves', wf', hEq.mono hle, hle⟩

/-- A completed unsafe ordinary run extends the unsafe model and is hidden
from the partial and safe observers. Uniform entry safety is obtained from
the actual staged installation rather than assumed separately. -/
theorem SemanticRunWithStatsResult.extendUnsafeExact
    {ves : VEnvs}
    (Hrun : SemanticRunWithStatsResult c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env)
    (hsafety : c.safety = .unsafe)
    (hsource : sourceEnv = ves.venv .unsafe)
    (hproduction : isUnsafe = (c.safety != .safe))
    (hnonempty : indTypes.toList ≠ []) :
    ∃ ves' : VEnvs, ∃ decl : VInductDecl, ∃ envTypes envCtors : VEnv,
      ves'.WF outEnv ∧
      (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
      TrInductDeclCore (ves.venv .unsafe) c.lparams nparams indTypes.toList
        isUnsafe decl envTypes envCtors ∧
      VEnv.AddInduct (ves.venv .unsafe) decl (ves'.venv .unsafe) := by
  subst sourceEnv
  rcases Hrun with
    ⟨decl, headerEnv, ctorEnv, Hheaders, R, ⟨Hrecursors⟩⟩
  rcases Hrecursors.canonicalOrdinaryRuleTranslation with ⟨T⟩
  let B0 := Hrecursors.blockCertificate T.rules T.rulesWF
  let B := B0.sf_mono (safety := .unsafe) (by
    rw [hsafety]
    exact DefinitionSafety.le_rfl)
  have Htranslated :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.toTrInductDeclOfNonempty
      R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  have hdecl : decl.WF (ves.venv .unsafe) :=
    R.formation.declWF Htranslated.sourceWF
  have hcompile : decl.CompilesTo (ves.venv .unsafe) B.block :=
    by simpa [B, B0, BlockCertificate.sf_mono, BlockCertificate.block] using
      T.compilation.compilesTo
  have hisUnsafe : isUnsafe = true := by
    exact hproduction.trans (by rw [hsafety]; decide)
  have hconstructors :
      InductiveConstructorsSemanticallyCoherent .unsafe outEnv
        (Hrecursors.outVEnv.addDefEqRules T.rules) := by
    exact Hrecursors.completedConstructorSemantics
      (wf.constructorSemantics (safety := .unsafe)) T.rules
  have horigins :
      ProductionInductiveOrigins c.env.constants outEnv.constants decl :=
    Hrecursors.productionInductiveOrigins
  have howners : ConstructorOwnersPresent outEnv :=
    Hrecursors.constructorOwnersPresent wf.constructorOwners
  have hentries : ∀ entry ∈
      Hheaders.entries ++ R.declared.entries ++ Hrecursors.entries,
      entry.1.safety = .unsafe := by
    have hlocalSafety : Hrecursors.localContext.safety = .unsafe :=
      Hrecursors.localExtends.safety_eq.trans hsafety
    intro entry hentry
    rcases List.mem_append.mp hentry with hprefix | hrecursors
    · rcases List.mem_append.mp hprefix with hheaders | hconstructors
      · rcases Hheaders.sourceAligned with ⟨numNested, Haligned⟩
        exact Haligned.entrySafety_eq_unsafe hisUnsafe hheaders
      · exact R.declared.sourceAligned.entrySafety_eq_unsafe
          hisUnsafe hconstructors
    · exact Hrecursors.generated.entrySafety_eq_unsafe
        hlocalSafety hrecursors
  rcases B.extendUnsafeOfHiddenExact wf hdecl hcompile
      horigins hentries Hrecursors.closed howners hconstructors with
    ⟨ves', wf', hle, hadd⟩
  exact ⟨ves', decl, Hheaders.context.venv, R.declared.venvCtors,
    wf', hle, R.core, hadd⟩

/-- Environment-preservation projection of `extendUnsafeExact`. -/
theorem SemanticRunWithStatsResult.extendUnsafe
    {ves : VEnvs}
    (Hrun : SemanticRunWithStatsResult c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env)
    (hsafety : c.safety = .unsafe)
    (hsource : sourceEnv = ves.venv .unsafe)
    (hproduction : isUnsafe = (c.safety != .safe))
    (hnonempty : indTypes.toList ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rcases Hrun.extendUnsafeExact wf hsafety hsource hproduction hnonempty with
    ⟨ves', _decl, _envTypes, _envCtors, wf', hle, _source, _hadd⟩
  exact ⟨ves', wf', hle⟩

/-- Canonical equality, when already available, is preserved by monotonicity
of the generic unsafe extension. -/
theorem SemanticRunWithStatsResult.extendUnsafeOfQuotReady
    (Hrun : SemanticRunWithStatsResult c stats nparams depth indTypes
      isUnsafe sourceEnv outEnv)
    (wf : ves.WF c.env)
    (hEq : CanonicalEqEnvs ves)
    (hsafety : c.safety = .unsafe)
    (hsource : sourceEnv = ves.venv .unsafe)
    (hproduction : isUnsafe = (c.safety != .safe))
    (hnonempty : indTypes.toList ≠ []) :
    ∃ ves' : VEnvs, ves'.WF outEnv ∧ CanonicalEqEnvs ves' ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  rcases Hrun.extendUnsafe wf hsafety hsource hproduction hnonempty with
    ⟨ves', wf', hle⟩
  exact ⟨ves', wf', hEq.mono hle, hle⟩

end VerifyInductive
end Lean4Lean
