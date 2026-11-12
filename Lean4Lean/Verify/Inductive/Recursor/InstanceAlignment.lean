import Lean4Lean.Verify.Inductive.Recursor.Metadata
import Lean4Lean.Theory.Inductive.SignatureLemmas
import Lean4Lean.Verify.Inductive.Recursor.Entries.TrRecursorVal
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Inductive.RecursiveShapeCorrespondence

/-! Alignment of the installed block with a signature that models the source declaration,
for a recursor check: field counts, index arities, constructor types, family metadata, the
major premise and K-like recursors (`RecursorInstallation.alignmentOfTr`,
`RecursorInstallation.kOfMetadata`).

Source formation supplies raw constructor shapes. The normalized signature supplies exact
family and constructor correspondences, while typing of the generated equations fixes
constructor field counts. All typing arguments take place in the recursor environment
`H.outVEnv`, before the iota rules are added; the resulting shapes and K equalities then
extend to the installed environment `H.outVEnv.addDefEqRules g.equations`.
-/

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
namespace InductiveSignature

end InductiveSignature

namespace VerifyInductive

/-- The recursor-stage environment is a checking environment of the output. -/
theorem RecursorInstallation.validCore
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) :
    CheckingEnv.ValidCore c.safety outEnv H.outVEnv := by
  have hv : CheckingEnv.ValidCore H.localContext.safety H.localContext.env R.context.venv := by
    rw [H.localExtends.safety_eq, H.localExtends.env_eq]
    exact R.context.checking.toValidCore
  have := H.installed.validCore hv
  rwa [H.localExtends.safety_eq] at this

theorem RecursorInstallation.outVEnvWF
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) : H.outVEnv.WF :=
  H.validCore.tr.wf

theorem RecursorInstallation.headerLE
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) : R.headerVEnv ≤ H.outVEnv :=
  R.headerLE.trans (R.ctorLE.trans H.installed.le)

theorem RecursorInstallation.sourceLE
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv) : sourceEnv ≤ H.outVEnv :=
  R.sourceLE.trans H.headerLE

theorem RecursorInstallation.familyConstant
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    H.outVEnv.constants family.name = some family.toVConstant :=
  H.headerLE.constants (VEnv.addConstVals_get R.core.typesAdded
    (List.mem_map.mpr ⟨family, hf, rfl⟩))

theorem RecursorInstallation.constructorConstant
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (ctor : VConstVal) (hc : ctor ∈ decl.constructorConstants) :
    H.outVEnv.constants ctor.name = some ctor.toVConstant :=
  (R.ctorLE.trans H.installed.le).constants
    (VEnv.addConstVals_get R.core.ctorsAdded hc)

/-- The installed header is an `inductInfo` whose constructor-name list is exactly that of
the source family. -/
theorem RecursorInstallation.familyInfo
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    (family : VInductiveType) (hf : family ∈ decl.types) :
    ∃ info : InductiveVal,
      outEnv.constants.find? family.name = some (.inductInfo info) ∧
      info.ctors = family.ctors.map VConstVal.name := by
  obtain ⟨info, hinfo, htr⟩ := List.Forall₂.forall_exists_r R.headers.trHeaders family hf
  have hname : info.name = family.name := htr.1.2
  have hctorWF : H.localContext.env.constants.WF := by
    rw [H.localExtends.env_eq]; exact R.context.checking.tr.map_wf
  have hfind : H.localContext.env.find? info.name = some (.inductInfo info) := by
    rw [H.localExtends.env_eq]; exact R.headerInfo_find hinfo
  have hout := H.installed.preservesSourceFind hctorWF hfind
  have houtWF := H.installed.targetMapWF hctorWF
  rw [Lean.Kernel.Environment.find?, houtWF.find?'_eq_find?, hname] at hout
  exact ⟨info, hout, htr.2⟩

/-- The K flag of a generated recursor, read off the recursor metadata alone, in the
recursor stage. -/
theorem RecursorInstallation.kOfMetadata
    {R : ConstructorCheck c stats decl nparams isUnsafe depth
      sourceEnv indTypes ctorEnv}
    (H : RecursorInstallation R outEnv)
    {s : InductiveSignature} (hm : s.Models sourceEnv decl) (g : s.Instance)
    {owner : Fin s.families.size} {rec : RecursorVal}
    (hr : InductiveSignature.RecursorMetadata g H.outVEnv owner rec) :
    KLikeRecursor outEnv.constants H.outVEnv rec := by
  intro hk
  rcases hr.k hk with ⟨hfamilies, hctors, hzero, _⟩
  let index : Fin s.constructors.size := ⟨0, by omega⟩
  have howner : s.constructors[index].owner = owner := by
    apply Fin.eq_of_val_eq
    have h1 := s.constructors[index].owner.isLt
    have h2 := owner.isLt
    omega
  have hctorList : s.constructors.toList = [s.constructors[index]] := by
    apply List.ext_getElem
    · simpa only [Array.length_toList, List.length_singleton] using hctors
    · intro i hi hi'
      have heq : i = 0 := by simpa using hi'
      subst i
      rfl
  rcases hm.family owner with
    ⟨family, hfamily, hfname, hfuvars, hfindex, hflevel, hfctors⟩
  have hsingle : (s.declarationFamily owner).ctors.map VConstVal.name =
      [s.constructors[index].name] := by
    have hownerVal : s.constructors[index].owner.val = owner.val := congrArg Fin.val howner
    simp only [InductiveSignature.declarationFamily, hctorList, List.filterMap_cons,
      List.filterMap_nil, if_pos hownerVal, List.map_cons, List.map_nil]
  have hnames := Lean4Lean.VerifyInductive.TrInductDeclCore.sourceNames_nodup R.core
  rcases hm.constructorInFamily hnames index R.core.typesAdded hfamily
      (by simpa only [howner] using hfctors) with
    ⟨ctor, hctor, hcname, hcuvars, hctype⟩
  rcases H.familyInfo family hfamily with ⟨info, hlookupInfo, hinfoCtors⟩
  refine ⟨info, s.constructors[index].name, ?_, ?_, ?_⟩
  · simpa only [hr.major, hfname] using hlookupInfo
  · exact hinfoCtors.trans (hfctors.symm.trans hsingle)
  · have henv := H.outVEnvWF
    have hlookupF := H.familyConstant family hfamily
    have hlookupC := H.constructorConstant ctor (List.mem_flatMap.mpr ⟨family, hfamily, hctor⟩)
    have hfamilyWF : H.outVEnv.IsType decl.uvars [] family.type := by
      simpa only [VConstant.WF, ← hfuvars, hm.uvars] using henv.ordered.constWF hlookupF
    have hctorWF : H.outVEnv.IsType decl.uvars [] ctor.type := by
      simpa only [VConstant.WF, ← hcuvars, hm.uvars] using henv.ordered.constWF hlookupC
    -- The header and constructor shapes come from source formation.
    obtain ⟨params, envTypes', htypes', Htypes, Hctors, _⟩ :=
      R.formation.formationWF.sourceParameterWF
    have hEnvTypes : envTypes' = R.headerVEnv :=
      Option.some.inj (htypes'.symm.trans R.core.typesAdded)
    subst hEnvTypes
    obtain ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnorm, htakeP, htakeI, hPD, hres⟩ := Htypes family hfamily
    obtain ⟨ownParamsC, tail, htakeC, hPDC⟩ := Hctors family hfamily ctor hctor
    obtain ⟨hnormEq, hPlen⟩ := VExpr.takeForalls_rebuild htakeP
    obtain ⟨hafterEq, hIlen⟩ := VExpr.takeForalls_rebuild htakeI
    obtain ⟨hctorShape, hClen⟩ := VExpr.takeForalls_rebuild htakeC
    have hnorm' : H.outVEnv.IsDefEq decl.uvars [] family.type
        (VExpr.wrapForalls (ownParams ++ indices) result) exprType := by
      rw [VExpr.wrapForalls_append, ← hafterEq, ← hnormEq]
      exact hnorm.mono H.sourceLE
    have hnormalizedWF : H.outVEnv.IsType decl.uvars []
        (VExpr.wrapForalls (ownParams ++ indices) result) :=
      hfamilyWF.defeqU_l henv (by trivial) ⟨_, hnorm'⟩
    rcases VEnv.IsType.wrapForalls_inv henv (by trivial) hnormalizedWF with ⟨hctx, _⟩
    have hres' : H.outVEnv.IsDefEq decl.uvars ((ownParams ++ indices).reverse ++ [])
        result (.sort family.resultLevel) (.sort (.succ family.resultLevel)) := by
      simpa [List.reverse_append] using hres.mono H.sourceLE
    have hsortWF : H.outVEnv.IsType decl.uvars ((ownParams ++ indices).reverse ++ [])
        (.sort family.resultLevel) := ⟨_, hres'.hasType.2⟩
    have hsort : H.outVEnv.IsDefEq decl.uvars ((ownParams ++ indices).reverse ++ [])
        (.sort family.resultLevel) (.sort .zero) (.sort (.succ family.resultLevel)) :=
      .sortDF (hsortWF.sort_inv henv.ordered) trivial (hflevel.symm.trans hzero)
    rcases VExpr.wrapForalls_defeq hctx (hres'.trans hsort) with ⟨sortLevel, hwrapped⟩
    have hprop : H.outVEnv.IsDefEqU decl.uvars [] family.type
        (VExpr.wrapForalls (ownParams ++ indices) (.sort .zero)) :=
      VEnv.IsDefEqU.trans henv (by trivial) ⟨_, hnorm'⟩ ⟨_, hwrapped⟩
    have hctorEq : H.outVEnv.IsDefEqU decl.uvars [] ctor.type
        (VExpr.wrapForalls ownParamsC tail) := by
      rw [← hctorShape]
      obtain ⟨_, h⟩ := hctorWF
      exact ⟨_, h⟩
    have hPDo : VEnv.IsDefEqCtx H.outVEnv decl.uvars [] params.reverse ownParams.reverse :=
      VEnv.IsDefEqCtx.mono H.sourceLE hPD
    have hPDCo : VEnv.IsDefEqCtx H.outVEnv decl.uvars [] params.reverse ownParamsC.reverse :=
      VEnv.IsDefEqCtx.mono H.headerLE hPDC
    have hOC : decl.ParamsDefEq H.outVEnv ownParams ownParamsC :=
      VEnv.IsDefEqCtx.trans_empty henv (hPDo.symm henv.ordered) hPDCo
    refine ⟨decl.uvars, family.type, ctor.type, ownParams ++ indices,
      ownParamsC, tail, ?_, hprop, ?_, ?_, hctorEq, ?_, ?_⟩
    · have hu : family.uvars = decl.uvars := hfuvars.symm.trans hm.uvars
      rw [hr.major, hfname, hlookupF]
      rw [← hu]
    · rw [hr.numParams, hr.numIndices, List.length_append, hPlen, hIlen, hm.nparams, hfindex]
    · have hu : ctor.uvars = decl.uvars := hcuvars.symm.trans hm.uvars
      rw [hcname, hlookupC]
      rw [← hu]
    · rw [hr.numParams, hClen, hm.nparams]
    · intro k hk hk'
      have hkP : k < ownParams.length := by omega
      obtain ⟨u, h⟩ := VInductDecl.ParamsDefEq.getElem (i := k) hOC hkP
      rw [List.take_append_of_le_length (by omega), List.getElem_append_left hkP]
      exact ⟨_, h⟩

end VerifyInductive
end Lean4Lean
