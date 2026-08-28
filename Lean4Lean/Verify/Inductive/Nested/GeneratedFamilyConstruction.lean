import Lean4Lean.Verify.Inductive.Nested.FormationEvidence

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-! # Exact construction provenance for generated nested families -/

/-- Rebase source common-parameter formation to the exact header environment
produced by adding the same mutual type constants to a larger base. -/
theorem VInductDecl.SourceParameterWF.rebaseToTypes
    {decl : VInductDecl} {base largerBase largerTypes : VEnv}
    (H : decl.SourceParameterWF base)
    (hbase : base ≤ largerBase)
    (htypes : largerBase.addConstVals decl.typeConstants =
      some largerTypes) :
    ∃ params,
      (∀ type ∈ decl.types, decl.TypeShape largerBase params type) ∧
      ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
        decl.CtorParameterShape largerTypes params ctor := by
  rcases H with
    ⟨params, sourceTypes, hsourceTypes, Htypes, Hconstructors⟩
  have htypesLE : sourceTypes ≤ largerTypes :=
    VEnv.addConstVals_mono hbase hsourceTypes htypes
  exact ⟨params,
    fun type htype => (Htypes type htype).mono hbase,
    fun type htype ctor hctor =>
      (Hconstructors type htype ctor hctor).mono htypesLE⟩

/-- A finite installed declaration retains source-facing raw parameter
formation in the ambient observer.  Ordinary formation supplies it directly;
the nested branch carries the native source certificate and rebases it through
the exact type-header installation used by this block. -/
theorem VEnv.InstalledInductCertificate.sourceParameterWF
    (H : VEnv.InstalledInductCertificate env decl) :
    ∃ params,
      (∀ type ∈ decl.types, decl.TypeShape env params type) ∧
      ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
        decl.CtorParameterShape env params ctor := by
  cases H with
  | @intro _ _ base block installed Hsource Hformation Hcompile Hblock
      Hinstall hle =>
    rcases Hblock with
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecursors,
        _htypesWF, _hctorsWF, _hrecursorsWF, _hrulesWF⟩
    have hdeclTypes : base.addConstVals decl.typeConstants = some envTypes := by
      simpa [Hcompile.types] using htypes
    have HsourceParameters : ∃ params,
        (∀ type ∈ decl.types, decl.TypeShape base params type) ∧
        ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
          decl.CtorParameterShape envTypes params ctor := by
      cases Hformation with
      | ordinary Hordinary =>
        exact VInductDecl.SourceParameterWF.rebaseToTypes
          Hordinary.sourceParameterWF VEnv.LE.rfl hdeclTypes
      | nested Hnested hformationBase =>
        cases Hnested with
        | @intro _ _ _ _ _ _ Hparameters _ _ _ _ =>
          exact VInductDecl.SourceParameterWF.rebaseToTypes Hparameters
            hformationBase hdeclTypes
    have hcanonical : VInductBlock.install base block =
        some (envRecursors.addDefEqRules block.rules) := by
      simp [VInductBlock.install, htypes, hctors, hrecursors]
    have hinstalled : installed = envRecursors.addDefEqRules block.rules :=
      Option.some.inj (Hinstall.symm.trans hcanonical)
    subst installed
    have htypesEnv : envTypes ≤ env :=
      (VEnv.addConstVals_le hctors).trans
        ((VEnv.addConstVals_le hrecursors).trans
          (VEnv.addDefEqRules_le.trans hle))
    have hbaseEnv : base ≤ env :=
      (VEnv.addConstVals_le hdeclTypes).trans htypesEnv
    rcases HsourceParameters with ⟨params, Htypes, Hconstructors⟩
    exact ⟨params,
      fun type htype => (Htypes type htype).mono hbaseEnv,
      fun type htype ctor hctor =>
        (Hconstructors type htype ctor hctor).mono htypesEnv⟩

/-- Finite installation provenance exposes the exact abstract constructor at
each family/constructor position, just as it exposes the family header. -/
theorem installedInductCertificate_constructorLookup
    (H : VEnv.InstalledInductCertificate env decl)
    (familyIdx ctorIdx : Nat) (hfamily : familyIdx < decl.types.length)
    (hctor : ctorIdx < decl.types[familyIdx].ctors.length) :
    env.constants decl.types[familyIdx].ctors[ctorIdx].name =
      some decl.types[familyIdx].ctors[ctorIdx].toVConstant := by
  cases H with
  | @intro _ _ base block installed Hsource Hformation Hcompile Hblock
      Hinstall hle =>
    rcases Hblock with
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecursors,
        _htypesWF, _hctorsWF, _hrecursorsWF, _hrulesWF⟩
    have hmember : decl.types[familyIdx].ctors[ctorIdx] ∈ block.ctors := by
      rw [Hcompile.ctors]
      simp only [VInductDecl.constructorConstants, List.mem_flatMap]
      exact ⟨decl.types[familyIdx], List.getElem_mem hfamily,
        List.getElem_mem hctor⟩
    have hlookupCtors := VEnv.addConstVals_get hctors hmember
    have hcanonical : VInductBlock.install base block =
        some (envRecursors.addDefEqRules block.rules) := by
      simp [VInductBlock.install, htypes, hctors, hrecursors]
    have hinstalled : installed = envRecursors.addDefEqRules block.rules :=
      Option.some.inj (Hinstall.symm.trans hcanonical)
    subst installed
    exact hle.constants <| VEnv.addDefEqRules_le.constants <|
      (VEnv.addConstVals_le hrecursors).constants hlookupCtors

/-- Canonical abstract constructor obtained by specializing one constructor
of a previously installed family.  Keeping this definition independent of
the concrete auxiliary builder makes the remaining translation obligation
pointwise and exact. -/
def VConstVal.directAuxiliary
    (sourceParams baseArgs : List VExpr) (levels : List VLevel)
    (containerFamily : VInductiveType) (auxName : Name) (auxUvars : Nat)
    (source : VConstVal) : VConstVal where
  uvars := auxUvars
  name := source.name.replacePrefix containerFamily.name auxName
  type := VExpr.wrapForalls sourceParams
    (VExpr.instantiateForallPrefix (source.type.instL levels) baseArgs)

/-- Canonical pre-lowering family generated by one direct nested
specialization.  Its semantic metadata is deliberately supplied by the exact
final header position; the executable auxiliary builder itself fixes only the
name, type, and ordered constructors. -/
def VInductiveType.directAuxiliary
    (sourceParams baseArgs : List VExpr) (levels : List VLevel)
    (containerFamily : VInductiveType) (auxName : Name) (auxUvars : Nat)
    (numIndices : Nat) (resultLevel : VLevel) : VInductiveType where
  uvars := auxUvars
  name := auxName
  type := VExpr.wrapForalls sourceParams
    (VExpr.instantiateForallPrefix (containerFamily.type.instL levels)
      baseArgs)
  numIndices := numIndices
  resultLevel := resultLevel
  ctors := containerFamily.ctors.map
    (VConstVal.directAuxiliary sourceParams baseArgs levels containerFamily
      auxName auxUvars)

/-- The direct-constructor portion of `NestedAuxiliarySource` is true by
construction for the canonical pre-lowering family.  No expression
translation or final-lowering fact is hidden in this lemma. -/
theorem VInductiveType.directAuxiliary_constructors
    (containerFamily : VInductiveType)
    (Htypes : ∀ source ∈ containerFamily.ctors,
      (VConstVal.directAuxiliary sourceParams baseArgs levels
        containerFamily auxName auxUvars source).type.WF env auxUvars []) :
    List.Forall₂
      (VInductDecl.DirectAuxConstructor env auxUvars sourceParams baseArgs
        levels containerFamily
        (VInductiveType.directAuxiliary sourceParams baseArgs levels
          containerFamily auxName auxUvars numIndices resultLevel))
      containerFamily.ctors
      (VInductiveType.directAuxiliary sourceParams baseArgs levels
        containerFamily auxName auxUvars numIndices resultLevel).ctors := by
  let auxiliaryFamily := VInductiveType.directAuxiliary sourceParams
    baseArgs levels containerFamily auxName auxUvars numIndices resultLevel
  have go : ∀ sources,
      (∀ source ∈ sources,
        (VConstVal.directAuxiliary sourceParams baseArgs levels
          containerFamily auxName auxUvars source).type.WF env auxUvars []) →
      List.Forall₂
        (VInductDecl.DirectAuxConstructor env auxUvars sourceParams baseArgs
          levels containerFamily auxiliaryFamily)
        sources
        (sources.map (VConstVal.directAuxiliary sourceParams baseArgs levels
          containerFamily auxName auxUvars)) := by
    intro sources Htypes'
    induction sources with
    | nil => exact .nil
    | cons source sources ih =>
      exact .cons {
        name := by rfl
        uvars := by rfl
        type := VEnv.IsDefEqU.refl (Htypes' source (by simp)) } (ih (by
          intro source hsource
          exact Htypes' source (by simp [hsource])))
  simpa only [auxiliaryFamily, VInductiveType.directAuxiliary] using
    go containerFamily.ctors Htypes

/-- The installed-container witness selects the exact canonical family from
which the concrete `BuiltAuxiliary` was generated.  This is the declaration
and constructor-order half of the pre-lowering abstract source; only its
translation from the concrete built syntax remains to be joined. -/
theorem GeneratedFamilyInstalledContainer.directAuxiliaryEvidence
    (C : GeneratedFamilyInstalledContainer prodEnv venv params nestedAux
      concrete H)
    (sourceParams baseArgs : List VExpr) (levels : List VLevel)
    (auxUvars numIndices : Nat) (resultLevel : VLevel) :
    (∀ source ∈
      (C.container.types[C.familyIdx]'C.familyIdx_lt).ctors,
      (VConstVal.directAuxiliary sourceParams baseArgs levels
        (C.container.types[C.familyIdx]'C.familyIdx_lt) H.auxName auxUvars
          source).type.WF venv auxUvars []) →
    let containerFamily := C.container.types[C.familyIdx]'C.familyIdx_lt
    let auxiliaryFamily := VInductiveType.directAuxiliary sourceParams
      baseArgs levels containerFamily H.auxName auxUvars numIndices resultLevel
    VEnv.InstalledInductCertificate venv C.container ∧
      containerFamily ∈ C.container.types ∧
      List.Forall₂
        (VInductDecl.DirectAuxConstructor venv auxUvars sourceParams baseArgs
          levels containerFamily auxiliaryFamily)
        containerFamily.ctors auxiliaryFamily.ctors := by
  intro Htypes
  dsimp only
  exact ⟨C.installed, List.getElem_mem C.familyIdx_lt,
    VInductiveType.directAuxiliary_constructors _ Htypes⟩

/-- Exact concrete/abstract source-constructor pair selected by one
`BuiltAuxiliary` position.  This retains the source telescope used by the
builder and derives its semantic translation from persistent environment
alignment and finite installation, rather than asking for it separately. -/
structure GeneratedFamilyInstalledContainer.BuiltConstructorTranslation
    {ves : VEnvs}
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv .unsafe)
      params nestedAux concrete H)
    (i : Nat) (hi : i < H.sourceInfo.ctors.length) where
  targetIdx_lt : i < H.data.type.ctors.length
  sourceInfo : ConstantInfo
  sourceTail : Expr
  sourceLookup : prodEnv.find? H.sourceInfo.ctors[i] = some sourceInfo
  sourceTelescope : Expr.ForallTelescope
    (sourceInfo.type.instantiateLevelParams sourceInfo.levelParams H.levels)
    H.nestedNParams sourceTail
  targetName : H.data.type.ctors[i].name =
    H.sourceInfo.ctors[i].replacePrefix H.sourceName H.auxName
  targetType : H.data.type.ctors[i].type = H.lctx.mkForall H.As
    (sourceTail.instantiateRevRange 0 H.nestedNParams H.args)
  abstractIdx_lt : i <
    (C.container.types[C.familyIdx]'C.familyIdx_lt).ctors.length
  sourceTranslation : TrConstant .unsafe (ves.venv .unsafe) sourceInfo
    (((C.container.types[C.familyIdx]'C.familyIdx_lt).ctors[i]'abstractIdx_lt).toVConstant)

/-- The executable builder, production alignment, and installed-container
certificate determine the exact translated source constructor at every
position. -/
theorem GeneratedFamilyInstalledContainer.builtConstructorTranslation
    {ves : VEnvs}
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv .unsafe)
      params nestedAux concrete H)
    (wf : ves.WF prodEnv)
    (i : Nat) (hi : i < H.sourceInfo.ctors.length) :
    Nonempty (C.BuiltConstructorTranslation i hi) := by
  rcases H.built.constructorAt i hi with ⟨htarget, Hbuilt⟩
  rcases Hbuilt.source with
    ⟨sourceInfo, sourceTail, hlookup, Htelescope, hname, htype⟩
  have habstractIdx : i <
      (C.container.types[C.familyIdx]'C.familyIdx_lt).ctors.length := by
    simpa [← C.constructors] using hi
  have habstractLookup : (ves.venv .unsafe).constants
      (((C.container.types[C.familyIdx]'C.familyIdx_lt).ctors[i]'habstractIdx).name) =
      some (((C.container.types[C.familyIdx]'C.familyIdx_lt).ctors[i]'habstractIdx).toVConstant) :=
    installedInductCertificate_constructorLookup C.installed C.familyIdx i
      C.familyIdx_lt habstractIdx
  have hsourceName : H.sourceInfo.ctors[i] =
      ((C.container.types[C.familyIdx]'C.familyIdx_lt).ctors[i]'habstractIdx).name :=
    C.constructorName i hi
  have hlookup' : prodEnv.find?
      ((C.container.types[C.familyIdx]'C.familyIdx_lt).ctors[i]'habstractIdx).name =
        some sourceInfo := by
    rw [← hsourceName]
    exact hlookup
  have Htranslation := (wf.tr (safety := .unsafe)).find?_uniq hlookup'
    habstractLookup |>.2
  exact ⟨{
    targetIdx_lt := htarget
    sourceInfo := sourceInfo
    sourceTail := sourceTail
    sourceLookup := hlookup
    sourceTelescope := Htelescope
    targetName := hname
    targetType := htype
    abstractIdx_lt := habstractIdx
    sourceTranslation := Htranslation }⟩



end VerifyInductive
end Lean4Lean
