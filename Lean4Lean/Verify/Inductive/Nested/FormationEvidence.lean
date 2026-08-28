import Lean4Lean.Verify.Inductive.Nested.ExpansionProjection
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- A finite installed-declaration derivation exposes the exact abstract
family constant at every source position. -/
theorem installedInductCertificate_familyLookup
    (H : VEnv.InstalledInductCertificate env decl)
    (i : Nat) (hi : i < decl.types.length) :
    env.constants decl.types[i].name = some decl.types[i].toVConstant := by
  cases H with
  | @intro _ _ base block installed Hsource Hformation Hcompile Hblock
      Hinstall hle =>
    rcases Hblock with
      ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecursors,
        _htypesWF, _hctorsWF, _hrecursorsWF, _hrulesWF⟩
    have hmember : decl.types[i].toVConstVal ∈ block.types := by
      rw [Hcompile.types]
      exact List.mem_map.mpr ⟨decl.types[i], List.getElem_mem hi, rfl⟩
    have hlookupTypes := VEnv.addConstVals_get htypes hmember
    have hlookupInstalled : installed.constants decl.types[i].name =
        some decl.types[i].toVConstant := by
      have hcanonical : VInductBlock.install base block =
          some (envRecursors.addDefEqRules block.rules) := by
        simp [VInductBlock.install, htypes, hctors, hrecursors]
      have hinstalled : installed = envRecursors.addDefEqRules block.rules :=
        Option.some.inj (Hinstall.symm.trans hcanonical)
      subst installed
      exact VEnv.addDefEqRules_le.constants
        ((VEnv.addConstVals_le hrecursors).constants
          ((VEnv.addConstVals_le hctors).constants hlookupTypes))
    exact hle.constants hlookupInstalled

/-- The declaration-level portion of a legal nested auxiliary source, obtained
from the production family lookup retained by lowering and the persistent
environment invariant.  In particular, `container` is not an arbitrary
declaration with a matching family name: it has a finite prior
well-formedness/compilation/installation derivation in the current abstract
environment. -/
structure GeneratedFamilyInstalledContainer
    (prodEnv : Environment) (venv : VEnv)
    (params : Array Expr) (nestedAux : Array (Expr × Name))
    (family : InductiveType)
    (H : GeneratedFamilyWitness prodEnv params nestedAux family) where
  container : VInductDecl
  familyIdx : Nat
  familyIdx_lt : familyIdx < container.types.length
  installed : VEnv.InstalledInductCertificate venv container
  lookupName : H.sourceName = H.sourceInfo.name
  familyName : H.sourceInfo.name = container.types[familyIdx].name
  numParams : H.sourceInfo.numParams = container.nparams
  levelParams : H.sourceInfo.levelParams.length = container.uvars
  constructors : H.sourceInfo.ctors.length =
    container.types[familyIdx].ctors.length
  constructorName : ∀ i (hi : i < H.sourceInfo.ctors.length),
    H.sourceInfo.ctors[i] = container.types[familyIdx].ctors[i].name
  familyLookup : venv.constants H.sourceName =
    some container.types[familyIdx].toVConstant
  familyTranslation : TrConstant .unsafe venv
    (.inductInfo H.sourceInfo) container.types[familyIdx].toVConstant

/-- Persistent installed-inductive provenance turns every generated-family
lookup made by nested lowering into an exact prior-container certificate.
This discharges the soundness-critical first premise of
`NestedAuxiliarySource`; the remaining premises describe the concrete
parameter specialization and its translation to the generated abstract
family. -/
theorem GeneratedFamilyWitness.installedContainer
    {ves : VEnvs}
    (H : GeneratedFamilyWitness prodEnv params nestedAux family)
    (wf : ves.WF prodEnv) :
    Nonempty (GeneratedFamilyInstalledContainer prodEnv (ves.venv .unsafe)
      params nestedAux family H) := by
  have hfind : prodEnv.constants.find? H.sourceName =
      some (.inductInfo H.sourceInfo) := by
    have hlookup := H.built.lookup
    rw [Lean.Kernel.Environment.find?,
      (wf.tr (safety := .unsafe)).map_wf.find?'_eq_find?] at hlookup
    exact hlookup
  rcases wf.inductiveProvenance H.sourceName H.sourceInfo hfind
      DefinitionSafety.unsafe_le with ⟨P⟩
  have hfamily := P.alignment.familyIdx_lt
  have habstractLookup : (ves.venv .unsafe).constants H.sourceName =
      some (P.decl.types[P.familyIdx]'hfamily).toVConstant := by
    calc
      (ves.venv .unsafe).constants H.sourceName =
          (ves.venv .unsafe).constants H.sourceInfo.name :=
        congrArg (ves.venv .unsafe).constants P.name
      _ = (ves.venv .unsafe).constants
          (P.decl.types[P.familyIdx]'hfamily).name :=
        congrArg (ves.venv .unsafe).constants P.alignment.name
      _ = some (P.decl.types[P.familyIdx]'hfamily).toVConstant :=
        installedInductCertificate_familyLookup P.installed P.familyIdx
          hfamily
  refine ⟨{
    container := P.decl
    familyIdx := P.familyIdx
    familyIdx_lt := P.alignment.familyIdx_lt
    installed := P.installed
    lookupName := P.name
    familyName := ?_
    numParams := P.alignment.numParams
    levelParams := P.alignment.levelParams
    constructors := P.alignment.constructors
    constructorName := ?_
    familyLookup := ?_
    familyTranslation := ?_ }⟩
  exact P.alignment.name
  intro i hi
  have hfamily := P.alignment.familyIdx_lt
  have htarget : i < (P.decl.types[P.familyIdx]'hfamily).ctors.length := by
    simpa [P.alignment.constructors] using hi
  rcases P.alignment.constructor i htarget with ⟨C⟩
  exact C.name
  · exact habstractLookup
  · exact (wf.tr (safety := .unsafe)).find?_uniq H.built.lookup
      habstractLookup |>.2


/-- Recover the installed container in the exact abstract observer that
translated the recognized family.  Visibility is derived from the concrete
lookup and the supplied abstract lookup through environment alignment; it is
not an additional safety premise. -/
theorem GeneratedFamilyWitness.installedContainerOfAbstractLookup
    {ves : VEnvs}
    (H : GeneratedFamilyWitness prodEnv params nestedAux family)
    (wf : ves.WF prodEnv) (safety : DefinitionSafety)
    (abstractFamily : VConstant)
    (habstract : (ves.venv safety).constants H.sourceName =
      some abstractFamily) :
    Nonempty (GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
      params nestedAux family H) := by
  have hfind : prodEnv.constants.find? H.sourceName =
      some (.inductInfo H.sourceInfo) := by
    have hlookup := H.built.lookup
    rw [Lean.Kernel.Environment.find?,
      (wf.tr (safety := safety)).map_wf.find?'_eq_find?] at hlookup
    exact hlookup
  have Haligned := (wf.tr (safety := safety)).find?_uniq
    H.built.lookup habstract
  rcases wf.inductiveProvenance H.sourceName H.sourceInfo hfind Haligned.2.1
      with ⟨P⟩
  have hfamily := P.alignment.familyIdx_lt
  have habstractLookup : (ves.venv safety).constants H.sourceName =
      some (P.decl.types[P.familyIdx]'hfamily).toVConstant := by
    calc
      (ves.venv safety).constants H.sourceName =
          (ves.venv safety).constants H.sourceInfo.name :=
        congrArg (ves.venv safety).constants P.name
      _ = (ves.venv safety).constants
          (P.decl.types[P.familyIdx]'hfamily).name :=
        congrArg (ves.venv safety).constants P.alignment.name
      _ = some (P.decl.types[P.familyIdx]'hfamily).toVConstant :=
        installedInductCertificate_familyLookup P.installed P.familyIdx
          hfamily
  refine ⟨{
    container := P.decl
    familyIdx := P.familyIdx
    familyIdx_lt := P.alignment.familyIdx_lt
    installed := P.installed
    lookupName := P.name
    familyName := P.alignment.name
    numParams := P.alignment.numParams
    levelParams := P.alignment.levelParams
    constructors := P.alignment.constructors
    constructorName := ?_
    familyLookup := habstractLookup
    familyTranslation := ?_ }⟩
  · intro i hi
    have htarget : i <
        (P.decl.types[P.familyIdx]'P.alignment.familyIdx_lt).ctors.length := by
      simpa [P.alignment.constructors] using hi
    rcases P.alignment.constructor i htarget with ⟨C⟩
    exact C.name
  · exact ((wf.tr (safety := safety)).find?_uniq H.built.lookup
      habstractLookup).2.sf_mono DefinitionSafety.unsafe_le

/-- Repackage the reusable structural expression carrier into the specialized
strictly-positive carrier used by the finite formation derivation. -/
theorem nestedExprExpansion_toNestedExprWFExpansion
    (H : VExpr.NestedExprExpansion
      (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
      depth input output) :
    VInductDecl.NestedExprWFExpansion env source generated depth input
      output := by
  induction H with
  | hit Hleaf =>
    rcases Hleaf with ⟨relativeDepth, hdepth, Hrelative⟩
    exact .hit hdepth Hrelative
  | bvar => exact .bvar
  | sort => exact .sort
  | const => exact .const
  | app _ _ ihFn ihArg => exact .app ihFn ihArg
  | lam _ _ ihDomain ihBody => exact .lam ihDomain ihBody
  | forallE _ _ ihDomain ihBody => exact .forallE ihDomain ihBody

/-- Repackage the retained common-parameter prefix into the mutually
strictly-positive formation carrier. -/
theorem nestedForallPrefixExpansion_toNestedForallPrefixWFExpansion
    (H : VExpr.NestedForallPrefixExpansion
      (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
      depth arity input output) :
    VInductDecl.NestedForallPrefixWFExpansion env source generated depth
      arity input output := by
  induction H with
  | nil Hbody =>
    exact .nil (nestedExprExpansion_toNestedExprWFExpansion Hbody)
  | cons Hdomain _ ih =>
    exact .cons (nestedExprExpansion_toNestedExprWFExpansion Hdomain) ih

/-- Convert ordered generic constructor expansion into the mutual
strict-positivity encoding required by `NestedFormationWF`. -/
theorem nestedConstructorWFExpansions_ofForall₂
    (H : List.Forall₂
      (VInductDecl.NestedConstructorExpansion
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated)
        source.nparams)
      sourceCtors targetCtors) :
    VInductDecl.NestedConstructorWFExpansions env source generated
      sourceCtors targetCtors := by
  induction H with
  | nil => exact .nil
  | cons Hhead _ ih =>
    exact .cons Hhead.name Hhead.uvars
      (nestedForallPrefixExpansion_toNestedForallPrefixWFExpansion
        Hhead.parameters)
      (nestedExprExpansion_toNestedExprWFExpansion Hhead.type) ih

/-- Convert ordered generic family expansion into the mutual
strict-positivity encoding required by `NestedFormationWF`. -/
theorem nestedTypeWFExpansions_ofForall₂
    (H : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated))
      sourceTypes targetTypes) :
    VInductDecl.NestedTypeWFExpansions env source generated sourceTypes
      targetTypes := by
  induction H with
  | nil => exact .nil
  | cons Hhead _ ih =>
    exact .cons Hhead.name Hhead.uvars Hhead.type Hhead.numIndices
      Hhead.resultLevel
      (nestedConstructorWFExpansions_ofForall₂ Hhead.constructors) ih

/-- Final assembly point for a nested formation derivation once the lowering
projection has supplied ordered family expansion for the original prefix and
every generated queue family.  The expanded declaration alone supplies the
ordinary formation judgment; no executable callback enters the abstract
specification. -/
theorem VInductDecl.NestedFormationWF.ofForall₂
    {env : VEnv} {source expanded : VInductDecl}
    {generated : List VInductiveType}
    (Hsource : expanded.SourceWF env)
    (Hformation : expanded.FormationWF env)
    (HsourceParameters : source.SourceParameterWF env)
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hunsafe : expanded.isUnsafe = source.isUnsafe)
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated))
      (source.types ++ generated) expanded.types) :
    source.NestedFormationWF env :=
  .intro Hsource Hformation HsourceParameters huvars hnparams hunsafe
    (nestedTypeWFExpansions_ofForall₂ Htypes)

/-- Reviewable inputs to the nested-formation judgment.  The expanded
declaration is explicit, as is the exact ordered expansion of the original
families followed by the generated queue. -/
structure NestedFormationAssembly (env : VEnv) (source : VInductDecl) where
  expanded : VInductDecl
  generated : List VInductiveType
  expandedSource : expanded.SourceWF env
  expandedFormation : expanded.FormationWF env
  sourceParameters : source.SourceParameterWF env
  uvars : expanded.uvars = source.uvars
  nparams : expanded.nparams = source.nparams
  isUnsafe : expanded.isUnsafe = source.isUnsafe
  types : List.Forall₂
    (VInductDecl.NestedTypeExpansion env source
      (VInductDecl.NestedAuxiliarySourceAbsolute env source generated))
    (source.types ++ generated) expanded.types

theorem NestedFormationAssembly.formation
    (H : NestedFormationAssembly env source) :
    source.NestedFormationWF env :=
  Lean4Lean.VerifyInductive.VInductDecl.NestedFormationWF.ofForall₂
    H.expandedSource H.expandedFormation H.sourceParameters H.uvars H.nparams
      H.isUnsafe H.types

/-- A successful ordinary header/constructor run supplies both independent
well-formedness judgments for the expanded block.  Thus the only genuinely
nested input left at this boundary is the ordered lowering expansion itself
(plus the declaration metadata equalities fixed by lowering). -/
def NestedFormationAssembly.ofConstructorPhases
    {c : AddInductive.Context} {stats : AddInductive.InductiveStats}
    {expanded source : VInductDecl} {nparams depth : Nat}
    {isUnsafe : Bool} {env : VEnv} {indTypes : Array InductiveType}
    {headerEnv outEnv : Environment}
    {Hheaders : DeclaredHeadersResult c stats expanded nparams isUnsafe depth
      env indTypes headerEnv}
    (R : ConstructorPhasesResult Hheaders outEnv)
    (generated : List VInductiveType)
    (hnonempty : indTypes.toList ≠ [])
    (HsourceParameters : source.SourceParameterWF env)
    (huvars : expanded.uvars = source.uvars)
    (hnparams : expanded.nparams = source.nparams)
    (hunsafe : expanded.isUnsafe = source.isUnsafe)
    (Htypes : List.Forall₂
      (VInductDecl.NestedTypeExpansion env source
        (VInductDecl.NestedAuxiliarySourceAbsolute env source generated))
      (source.types ++ generated) expanded.types) :
    NestedFormationAssembly env source where
  expanded := expanded
  generated := generated
  expandedSource :=
    Lean4Lean.VerifyInductive.TrInductDeclCore.sourceWF_ofNonempty R.core
      (Lean4Lean.VerifyInductive.TrInductDeclCore.nonempty R.core hnonempty)
  expandedFormation := R.formation.formationWF
  sourceParameters := HsourceParameters
  uvars := huvars
  nparams := hnparams
  isUnsafe := hunsafe
  types := Htypes

end VerifyInductive
end Lean4Lean
