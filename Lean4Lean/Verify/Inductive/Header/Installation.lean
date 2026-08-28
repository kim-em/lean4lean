import Lean4Lean.Verify.Inductive.Header.SemanticFold
import Lean4Lean.Verify.Inductive.Recursor.Installation

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Existential form of the atomic mutual-header installer.  Freshness is
recovered from each successful production `checkName`, so the abstract
`addConstVals` equation is an output rather than a premise. -/
theorem AddConstants.ofDeclareInductiveTypeInfosExists
    (Hvalid : CheckingEnv.Valid safety env venv)
    (Hentries : List.Forall₂
      (fun info ci' =>
        TrConstVal safety sourceEnv (.inductInfo info) ci' ∧
          ci'.toVConstant.WF sourceEnv)
      infos values)
    (hle : sourceEnv ≤ venv)
    (hnprim : allowPrimitive = true → ∀ info ∈ infos,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypeInfos allowPrimitive infos env).WF
      fun outEnv => ∃ outVEnv,
        AddConstants safety env venv
          (List.zip (infos.map (fun info => .inductInfo info)) values)
          outEnv outVEnv := by
  induction Hentries generalizing env venv with
  | nil =>
    exact Except.WF.pure ⟨venv, .nil⟩
  | @cons info ci' infos values Hentry _ ih =>
    rw [AddInductive.declareInductiveTypeInfos]
    exact (checkName.WF Hvalid.tr.map_wf info.name allowPrimitive).bind
      fun _ hchecked => by
        have hnprimHead :
            ¬ Kernel.Environment.primitives.contains info.name := by
          cases hallow : allowPrimitive with
          | false => simpa using hchecked.2 hallow
          | true => exact hnprim hallow info (by simp)
        have hnprimTail : allowPrimitive = true → ∀ info ∈ infos,
            ¬ Kernel.Environment.primitives.contains info.name := by
          intro hallow info hinfo
          exact hnprim hallow info (by simp [hinfo])
        have hn : env.find? info.name = none := hchecked.1
        rcases CheckingEnv.exists_addConst Hvalid.tr hn
            ci'.toVConstant with ⟨nextVEnv, haddRaw⟩
        have htr : TrConstVal safety venv (.inductInfo info) ci' :=
          Hentry.1.mono hle
        have hwf : ci'.toVConstant.WF venv := Hentry.2.mono hle
        have hname : info.name = ci'.name := Hentry.1.2
        have hadd : venv.addConst info.name ci'.toVConstant =
            some nextVEnv := by
          simpa [hname] using haddRaw
        have HnextValid : CheckingEnv.Valid safety
            (env.add (.inductInfo info)) nextVEnv :=
          Hvalid.add hn hnprimHead htr.1 hwf hadd rfl
        have hnextLe : sourceEnv ≤ nextVEnv :=
          hle.trans (VEnv.addConst_le hadd)
        exact (ih HnextValid hnextLe hnprimTail).mono
          fun outEnv Hrest => by
            rcases Hrest with ⟨outVEnv, Htail⟩
            exact ⟨outVEnv, by
              simpa using AddConstants.cons (ci := .inductInfo info)
                (ci' := ci') hn hnprimHead htr hwf hadd rfl Htail⟩

/-- Production mutual-header metadata translates directly to the exact
constants recovered by the skeleton-free header traversal. -/
theorem AddInductive.inductiveTypeInfos.translatedMaterializedHeaders
    (Hheaders : MaterializedSourceHeaderAccumulator env lparams
      indTypes.toList)
    (hindices : stats.nindices.size = indTypes.size)
    (hvisible : safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    List.Forall₂
      (fun info ci' =>
        TrConstVal safety env (.inductInfo info) ci' ∧
          ci'.toVConstant.WF env)
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams).toList
      Hheaders.targets := by
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe lparams
  have hsourceLength : indTypes.toList.length = Hheaders.targets.length :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      Hheaders.translations
  have hinfosLength : infos.toList.length = Hheaders.targets.length := by
    calc
      infos.toList.length = indTypes.size := by
        simp [infos, AddInductive.inductiveTypeInfos, hindices]
      _ = indTypes.toList.length := by simp
      _ = Hheaders.targets.length := hsourceLength
  apply List.forall₂_of_getElem hinfosLength
  intro i hiInfo hiTarget
  have hiSource : i < indTypes.toList.length := by
    simpa [hsourceLength] using hiTarget
  have Htarget := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    Hheaders.translations i hiSource hiTarget
  constructor
  · apply TrSourceConst.inductInfo Htarget
    · simp [infos, AddInductive.inductiveTypeInfos]
    · simp [infos, AddInductive.inductiveTypeInfos]
    · simp [infos, AddInductive.inductiveTypeInfos]
    · simpa [infos, AddInductive.inductiveTypeInfos, hindices] using
        hvisible
  · exact Htarget.wf

/-- The production header declaration installs the skeleton-free abstract
header constants in exact source order.  In particular the abstract
`addConstVals` equation is obtained from execution and is not supplied by a
caller skeleton. -/
theorem AddInductive.declareInductiveTypes.installsMaterializedHeadersWF
    (Hc : ContextWF c)
    (Hheaders : MaterializedSourceHeaderAccumulator Hc.venv c.lparams
      indTypes.toList)
    (hindices : stats.nindices.size = indTypes.size)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv => ∃ outVEnv,
        Hc.venv.addConstVals Hheaders.targets = some outVEnv ∧
        AddConstants c.safety c.env Hc.venv
          (List.zip
            ((AddInductive.inductiveTypeInfos stats numParams indTypes
              numNested isUnsafe c.lparams).toList.map
                (fun info => .inductInfo info))
            Hheaders.targets)
          outEnv outVEnv := by
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe c.lparams
  have Hentries := AddInductive.inductiveTypeInfos.translatedMaterializedHeaders
    (stats := stats) (numParams := numParams) (numNested := numNested)
    Hheaders hindices hvisible
  have Hinstall := AddConstants.ofDeclareInductiveTypeInfosExists
    (allowPrimitive := c.allowPrimitive) Hc.checking Hentries VEnv.LE.rfl
      (by simpa [infos] using hnprim)
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _
  exact Hinstall.mono fun outEnv Hinstalled => by
    rcases Hinstalled with ⟨outVEnv, Hinstalled⟩
    refine ⟨outVEnv, ?_, ?_⟩
    · have habstract := Hinstalled.abstract
      have hvalues :
          (List.zip
            (infos.toList.map (fun info => ConstantInfo.inductInfo info))
            Hheaders.targets).map Prod.snd = Hheaders.targets := by
        apply List.map_snd_zip
        have hlength :=
          Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hentries
        rw [List.length_map]
        exact Nat.le_of_eq hlength.symm
      rw [hvalues] at habstract
      exact habstract
    · simpa [infos] using Hinstalled

/-- Skeleton-free production boundary after all mutual family constants have
been installed and before any constructor is checked. -/
structure InstalledSemanticHeaders
    (c : AddInductive.Context) (Hc : ContextWF c)
    (stats : AddInductive.InductiveStats)
    (nparams : Nat) (indTypes : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    (commonParams : List VExpr) (commonLevel : VLevel)
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams nparams commonParams commonLevel indTypes.toList)
    (outEnv : Environment) where
  envTypes : VEnv
  context : ContextWF { c with env := outEnv }
  contextVEnv : context.venv = envTypes
  contextMLCtx : context.mlctx = Hc.mlctx
  installed : AddConstants c.safety c.env Hc.venv
    (List.zip
      ((AddInductive.inductiveTypeInfos stats nparams indTypes numNested
        isUnsafe c.lparams).toList.map (fun info => .inductInfo info))
      Hsemantic.headers.targets)
    outEnv envTypes
  values : (List.zip
    ((AddInductive.inductiveTypeInfos stats nparams indTypes numNested
      isUnsafe c.lparams).toList.map (fun info => ConstantInfo.inductInfo info))
    Hsemantic.headers.targets).map Prod.snd = Hsemantic.headers.targets
  typesAdded : Hc.venv.addConstVals
    (Hsemantic.headerDecl isUnsafe).typeConstants = some envTypes
  headers : HeaderCertificate Hc.venv (Hsemantic.headerDecl isUnsafe)

/-- Package exact abstract installation, the valid installed checking
context, and the header certificate while retaining every semantic payload
and normalized source telescope. -/
theorem AddInductive.declareInductiveTypes.semanticHeadersWF
    (Hc : ContextWF c)
    (Hsemantic :
      checkInductiveTypes.loopType.MaterializedSourceHeaderSemanticAccumulator
        Hc.venv c.lparams numParams commonParams commonLevel indTypes.toList)
    (hindices : stats.nindices.size = indTypes.size)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : c.allowPrimitive = true → ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        Nonempty (InstalledSemanticHeaders c Hc stats numParams indTypes
          numNested isUnsafe commonParams commonLevel Hsemantic outEnv) := by
  have Hinstall :=
    AddInductive.declareInductiveTypes.installsMaterializedHeadersWF
      Hc Hsemantic.headers hindices hvisible hnprim
  exact Hinstall.mono fun outEnv Hresult => by
    rcases Hresult with ⟨envTypes, htypes, Hinstalled⟩
    exact ⟨{
      envTypes := envTypes
      context := Hc.withEnv (Hinstalled.valid Hc.checking) Hinstalled.le
      contextVEnv := rfl
      contextMLCtx := rfl
      installed := Hinstalled
      values := by
        apply List.map_snd_zip
        have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
          Hsemantic.headers.translations
        have hinfos :
            (AddInductive.inductiveTypeInfos stats numParams indTypes
              numNested isUnsafe c.lparams).toList.length = indTypes.size := by
          simp [AddInductive.inductiveTypeInfos, hindices]
        simpa [hinfos] using Nat.le_of_eq hlength.symm
      typesAdded := by
        rw [Hsemantic.headerDecl_typeConstants]
        exact htypes
      headers := Hsemantic.headerCertificate isUnsafe }⟩

end VerifyInductive
end Lean4Lean
