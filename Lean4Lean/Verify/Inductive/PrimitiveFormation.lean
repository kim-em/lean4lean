import Lean4Lean.Verify.Inductive.CompletedRunWithStats

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Primitive header installation follows the executable header fold exactly,
but returns only a staged context.  No `HasPrimitives` claim is made before
the Bool/Nat constructors have also been installed. -/
theorem AddInductive.declareInductiveTypes.primitiveHeadersWF
    {envTypes : VEnv}
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclHeaders Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl envTypes)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ _ : PrimitiveDeclaredHeadersResult c stats decl numParams isUnsafe
          depth Hc.venv indTypes outEnv, True := by
  rcases Hdecl with
    ⟨huvars, hnparams, hunsafe, htypesAdded, Htypes⟩
  let infos := AddInductive.inductiveTypeInfos stats numParams indTypes
    numNested isUnsafe c.lparams
  have Htranslated := AddInductive.inductiveTypeInfos.translated
    (numParams := numParams) (numNested := numNested)
    Htypes Hmaterialized.indices hvisible
  have Hentries : List.Forall₂
      (fun info ci' =>
        TrConstVal c.safety Hc.venv (.inductInfo info) ci' ∧
          ci'.toVConstant.WF Hc.venv)
      infos.toList decl.typeConstants := by
    simpa [infos, VInductDecl.typeConstants] using Htranslated
  have Hinstall := AtomicAddConstants.ofDeclareInductiveTypeInfos
    (allowPrimitive := c.allowPrimitive)
    Hc.checking.tr Hentries VEnv.LE.rfl htypesAdded
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _
  exact Hinstall.mono fun outEnv Hinstalled => by
    have hvalues :
        (List.zip
          (infos.toList.map (fun info => ConstantInfo.inductInfo info))
          decl.typeConstants).map Prod.snd = decl.typeConstants := by
      have hlength : infos.toList.length = decl.typeConstants.length :=
        Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hentries
      apply List.map_snd_zip
      simpa [hlength]
    let Hstaged := Hc.toStaged.withEnv
      (Hinstalled.checking Hc.checking.tr) Hinstalled.le
    refine ⟨{
      entries := List.zip
        (infos.toList.map (fun info => .inductInfo info)) decl.typeConstants
      production := by
        refine ⟨numNested, ?_⟩
        have hfst : (List.zip
            (infos.toList.map (fun info => ConstantInfo.inductInfo info))
            decl.typeConstants).map Prod.fst =
            infos.toList.map (fun info => ConstantInfo.inductInfo info) := by
          apply List.map_fst_zip
          have hlength :=
            Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hentries
          simpa using Nat.le_of_eq hlength
        simpa [infos] using hfst
      sourceAligned := ⟨numNested, by
        apply InductiveHeaderEntries.ofZip
        simpa using
          Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hentries⟩
      values := hvalues
      context := Hstaged
      headers := Hmaterialized.headers
      translation := {
        uvars := huvars
        nparams := hnparams
        isUnsafe := hunsafe
        typesAdded := htypesAdded
        types := Htypes }
      installed := Hinstalled
      sourceContext := Hc
      sourceContextVEnv := rfl
      sourceMaterialized := Hmaterialized
      materialized := Hmaterialized.mono Hinstalled.le
      headerParams := rfl }, trivial⟩

end VerifyInductive
end Lean4Lean
