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

/-- Universe arity of the selected family, projected from the finite source
derivation carried by its installation certificate. -/
theorem GeneratedFamilyInstalledContainer.familyUvars
    (C : GeneratedFamilyInstalledContainer prodEnv venv params nestedAux
      concrete H) :
    (C.container.types[C.familyIdx]'C.familyIdx_lt).uvars =
      C.container.uvars := by
  cases C.installed with
  | intro Hsource _ _ _ _ _ =>
    exact Hsource.2.2.1 _ (List.getElem_mem C.familyIdx_lt)

/-- The executable lowering arity agrees with the installed container's
common-parameter arity.  The first equality is retained when the generated
family is produced from its environment lookup; the second comes from the
finite installation certificate for that exact container. -/
theorem GeneratedFamilyInstalledContainer.nestedNParams
    (C : GeneratedFamilyInstalledContainer prodEnv venv params nestedAux
      concrete H) :
    H.nestedNParams = C.container.nparams :=
  H.sourceNumParams.trans C.numParams

/-- Installed-container provenance is persistent under an abstract
environment extension. -/
def GeneratedFamilyInstalledContainer.mono
    (C : GeneratedFamilyInstalledContainer prodEnv venv params nestedAux
      concrete H)
    (hle : venv ≤ larger) :
    GeneratedFamilyInstalledContainer prodEnv larger params nestedAux
      concrete H := {
  container := C.container
  familyIdx := C.familyIdx
  familyIdx_lt := C.familyIdx_lt
  installed := by
    cases C.installed with
    | intro Hsource Hformation Hcompile Hblock Hinstall hinstalled =>
      exact .intro Hsource Hformation Hcompile Hblock Hinstall
        (hinstalled.trans hle)
  lookupName := C.lookupName
  familyName := C.familyName
  numParams := C.numParams
  levelParams := C.levelParams
  constructors := C.constructors
  constructorName := C.constructorName
  familyLookup := hle.constants C.familyLookup
  familyTranslation := ⟨C.familyTranslation.1, C.familyTranslation.2.1,
    C.familyTranslation.2.2.mono hle⟩ }

/-- Universe arity of a selected installed constructor, from the same finite
source derivation. -/
theorem GeneratedFamilyInstalledContainer.constructorUvars
    (C : GeneratedFamilyInstalledContainer prodEnv venv params nestedAux
      concrete H)
    (i : Nat)
    (hi : i < (C.container.types[C.familyIdx]'C.familyIdx_lt).ctors.length) :
    (C.container.types[C.familyIdx]'C.familyIdx_lt).ctors[i].uvars =
      C.container.uvars := by
  cases C.installed with
  | intro Hsource _ _ _ _ _ =>
    apply Hsource.2.2.2.1
    simp only [VInductDecl.constructorConstants, List.mem_flatMap]
    exact ⟨C.container.types[C.familyIdx]'C.familyIdx_lt,
      List.getElem_mem C.familyIdx_lt, List.getElem_mem hi⟩

/-- A well-typed specialization of the selected container family supplies a
well-typed specialization of each constructor at the same argument spine.

The proof uses only the finite installed declaration's source-parameter
formation.  Both normalized parameter telescopes are compared with its
canonical parameter list; the resulting context conversion is closed around
the constructor residual, after which the ordinary dependent-application
lemma applies with literally shared domains. -/
theorem GeneratedFamilyInstalledContainer.specializedConstructorApplicationHasType
    (C : GeneratedFamilyInstalledContainer prodEnv venv params nestedAux
      concrete H)
    (henv : venv.WF)
    (i : Nat)
    (habstractCtor : i <
      (C.container.types[C.familyIdx]'C.familyIdx_lt).ctors.length)
    (levels : List VLevel)
    (hlevelsWF : ∀ level ∈ levels, level.WF outerUvars)
    (hlevelsLength : levels.length = C.container.uvars)
    (ctx : List VExpr) (hctx : OnCtx ctx (venv.IsType outerUvars))
    (baseArgs : List VExpr)
    (hbaseLength : baseArgs.length = C.container.nparams)
    (HfamilyApps : VExpr.WF venv outerUvars ctx
      (VExpr.mkApps
        (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name levels)
        baseArgs)) :
    venv.HasType outerUvars ctx
      (VExpr.mkApps
        (.const
          ((C.container.types[C.familyIdx]'C.familyIdx_lt).ctors[i]'habstractCtor).name
          levels)
        baseArgs)
      (VExpr.applyForallType
        (((C.container.types[C.familyIdx]'C.familyIdx_lt).ctors[i]'habstractCtor).type.instL
          levels) baseArgs) := by
  let family := C.container.types[C.familyIdx]'C.familyIdx_lt
  have habstractCtor' : i < family.ctors.length := by
    simpa [family] using habstractCtor
  rcases Lean4Lean.VerifyInductive.VEnv.InstalledInductCertificate.sourceParameterWF
      C.installed with
    ⟨canonicalParams, Hfamilies, Hconstructors⟩
  have Hfamily := Hfamilies family (List.getElem_mem C.familyIdx_lt)
  have Hconstructor := Hconstructors family
    (List.getElem_mem C.familyIdx_lt) family.ctors[i]
      (List.getElem_mem habstractCtor')
  rcases Hfamily with
    ⟨familyNormalized, familyDomains, familyAfterParams, familyIndices,
      familyResult, familyType, HfamilyDefEq, HfamilyParams,
      _HfamilyIndices, HfamilyCanonical, _HfamilyResult⟩
  rcases Hconstructor with
    ⟨constructorDomains, constructorTail, HconstructorParams,
      HconstructorCanonical⟩
  rcases VExpr.takeForalls_rebuild HfamilyParams with
    ⟨hfamilyNormalized, hfamilyDomains⟩
  rcases VExpr.takeForalls_rebuild HconstructorParams with
    ⟨hconstructorType, hconstructorDomains⟩
  have HfamilyToConstructor : VEnv.IsDefEqCtx venv C.container.uvars []
      familyDomains.reverse constructorDomains.reverse := by
    have HfamilyToCanonical : VEnv.IsDefEqCtx venv C.container.uvars []
        familyDomains.reverse canonicalParams.reverse := by
      exact HfamilyCanonical.symm henv.ordered
    exact VEnv.IsDefEqCtx.transEmpty henv HfamilyToCanonical
      HconstructorCanonical
  have HfamilyToConstructorLevels : VEnv.IsDefEqCtx venv outerUvars []
      (familyDomains.map (VExpr.instL levels)).reverse
      (constructorDomains.map (VExpr.instL levels)).reverse := by
    have Hinst := Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.instL
      hlevelsWF HfamilyToConstructor
    simpa [List.map_reverse] using Hinst
  have HfamilyLookup : venv.constants family.name =
      some family.toVConstant := by
    rw [show family.name = H.sourceName by
      simpa [family] using (C.lookupName.trans C.familyName).symm]
    exact C.familyLookup
  have HconstructorLookup : venv.constants family.ctors[i].name =
      some family.ctors[i].toVConstant :=
    installedInductCertificate_constructorLookup C.installed C.familyIdx i
      C.familyIdx_lt habstractCtor'
  have HfamilyConst₀ : venv.HasType outerUvars []
      (.const family.name levels) (family.type.instL levels) := by
    apply VEnv.HasType.const HfamilyLookup hlevelsWF
    rw [hlevelsLength]
    exact C.familyUvars.symm
  have HconstructorConst₀ : venv.HasType outerUvars []
      (.const family.ctors[i].name levels)
      (family.ctors[i].type.instL levels) := by
    apply VEnv.HasType.const HconstructorLookup hlevelsWF
    rw [hlevelsLength]
    exact (C.constructorUvars i habstractCtor').symm
  have HfamilyNormalizedType : venv.IsDefEq outerUvars []
      (family.type.instL levels)
      ((VExpr.wrapForalls familyDomains familyAfterParams).instL levels)
      (familyType.instL levels) := by
    have Hinst := HfamilyDefEq.instL hlevelsWF
    simpa [hfamilyNormalized] using Hinst
  have HfamilyConstNormalized₀ : venv.HasType outerUvars []
      (.const family.name levels)
      (VExpr.wrapForalls (familyDomains.map (VExpr.instL levels))
        (familyAfterParams.instL levels)) := by
    have Htarget : venv.IsDefEqU outerUvars []
        (family.type.instL levels)
        (VExpr.wrapForalls (familyDomains.map (VExpr.instL levels))
          (familyAfterParams.instL levels)) := by
      refine ⟨familyType.instL levels, ?_⟩
      simpa [VExpr.instL_wrapForalls] using HfamilyNormalizedType
    exact HfamilyConst₀.defeqU_r henv (by trivial) Htarget
  have HconstructorType : family.ctors[i].type =
      VExpr.wrapForalls constructorDomains constructorTail := by
    simpa [family] using hconstructorType
  have HconstructorConstRaw₀ : venv.HasType outerUvars []
      (.const family.ctors[i].name levels)
      (VExpr.wrapForalls
        (constructorDomains.map (VExpr.instL levels))
        (constructorTail.instL levels)) := by
    simpa [HconstructorType, VExpr.instL_wrapForalls] using
      HconstructorConst₀
  have HconstructorTailType : venv.IsType outerUvars
      (constructorDomains.map (VExpr.instL levels)).reverse
      (constructorTail.instL levels) := by
    have Hwhole := HconstructorConstRaw₀.isType henv.ordered (by trivial)
    simpa using
      (VEnv.IsType.wrapForalls_inv henv.ordered (by trivial) Hwhole).2
  have HconstructorTailTypeFamily : venv.IsType outerUvars
      (familyDomains.map (VExpr.instL levels)).reverse
      (constructorTail.instL levels) :=
    HconstructorTailType.defeqDFC henv.ordered
      (HfamilyToConstructorLevels.symm henv.ordered)
  rcases HconstructorTailTypeFamily with
    ⟨tailLevel, HconstructorTailTypeFamily⟩
  have Htail : venv.IsDefEq outerUvars
      (familyDomains.map (VExpr.instL levels)).reverse
      (constructorTail.instL levels) (constructorTail.instL levels)
      (.sort tailLevel) := HconstructorTailTypeFamily
  have hdomainLength : familyDomains.length = constructorDomains.length := by
    have hcontexts := HfamilyToConstructorLevels.length_eq
    simpa using hcontexts
  rcases Lean4Lean.VerifyInductive.VEnv.IsDefEqCtx.closeHeads
      HfamilyToConstructorLevels
      (familyDomains.map (VExpr.instL levels)).length (by simp) Htail with
    ⟨wholeLevel, Hwhole⟩
  have hmapLength :
      (familyDomains.map (VExpr.instL levels)).length =
        (constructorDomains.map (VExpr.instL levels)).length := by
    simp [hdomainLength]
  have hleftDrop :
      (familyDomains.map (VExpr.instL levels)).reverse.drop
          (familyDomains.map (VExpr.instL levels)).length = [] := by
    simp
  have hleftTake :
      ((familyDomains.map (VExpr.instL levels)).reverse.take
          (familyDomains.map (VExpr.instL levels)).length).reverse =
        familyDomains.map (VExpr.instL levels) := by
    have htake :
        (familyDomains.map (VExpr.instL levels)).reverse.take
            (familyDomains.map (VExpr.instL levels)).length =
          (familyDomains.map (VExpr.instL levels)).reverse := by
      simpa using
        (List.take_length
          (l := (familyDomains.map (VExpr.instL levels)).reverse))
    rw [htake, List.reverse_reverse]
  have hrightTake :
      ((constructorDomains.map (VExpr.instL levels)).reverse.take
          (familyDomains.map (VExpr.instL levels)).length).reverse =
        constructorDomains.map (VExpr.instL levels) := by
    rw [hmapLength]
    have hlength : constructorDomains.length =
        (constructorDomains.map (VExpr.instL levels)).reverse.length := by
      simp
    have htake :
        (constructorDomains.map (VExpr.instL levels)).reverse.take
            (constructorDomains.map (VExpr.instL levels)).length =
          (constructorDomains.map (VExpr.instL levels)).reverse := by
      simpa using
        (List.take_length
          (l := (constructorDomains.map (VExpr.instL levels)).reverse))
    rw [htake, List.reverse_reverse]
  have HconstructorWhole : venv.IsDefEqU outerUvars []
      (VExpr.wrapForalls
        (familyDomains.map (VExpr.instL levels))
        (constructorTail.instL levels))
      (VExpr.wrapForalls
        (constructorDomains.map (VExpr.instL levels))
      (constructorTail.instL levels)) := by
    refine ⟨.sort wholeLevel, ?_⟩
    rw [hleftDrop, hleftTake, hrightTake] at Hwhole
    exact Hwhole
  have HconstructorConstNormalized₀ : venv.HasType outerUvars []
      (.const family.ctors[i].name levels)
      (VExpr.wrapForalls
        (familyDomains.map (VExpr.instL levels))
        (constructorTail.instL levels)) :=
    HconstructorConstRaw₀.defeqU_r henv (by trivial)
      HconstructorWhole.symm
  have W : Ctx.LiftN ctx.length 0 [] ctx :=
    by simpa using (Ctx.LiftN.zero (Γ := []) ctx)
  have HfamilyConst : venv.HasType outerUvars ctx
      (.const family.name levels)
      (VExpr.wrapForalls (familyDomains.map (VExpr.instL levels))
        (familyAfterParams.instL levels)) := by
    have Hweak := HfamilyConstNormalized₀.weakN henv.ordered W
    rcases HfamilyConstNormalized₀.isType henv.ordered (by trivial) with
      ⟨_familyLevel, HfamilyType⟩
    have hclosed := HfamilyType.closedN henv.ordered (by trivial)
    rw [hclosed.liftN_eq (Nat.zero_le _)] at Hweak
    simpa [VExpr.liftN] using Hweak
  have HconstructorConst : venv.HasType outerUvars ctx
      (.const family.ctors[i].name levels)
      (VExpr.wrapForalls (familyDomains.map (VExpr.instL levels))
        (constructorTail.instL levels)) := by
    have Hweak := HconstructorConstNormalized₀.weakN henv.ordered W
    rcases HconstructorConstNormalized₀.isType henv.ordered (by trivial) with
      ⟨_constructorLevel, HconstructorType'⟩
    have hclosed := HconstructorType'.closedN henv.ordered (by trivial)
    rw [hclosed.liftN_eq (Nat.zero_le _)] at Hweak
    simpa [VExpr.liftN] using Hweak
  have HconstructorConstRaw : venv.HasType outerUvars ctx
      (.const family.ctors[i].name levels)
      (VExpr.wrapForalls
        (constructorDomains.map (VExpr.instL levels))
        (constructorTail.instL levels)) := by
    have Hweak := HconstructorConstRaw₀.weakN henv.ordered W
    rcases HconstructorConstRaw₀.isType henv.ordered (by trivial) with
      ⟨_constructorRawLevel, HconstructorRawType⟩
    have hclosed := HconstructorRawType.closedN henv.ordered (by trivial)
    rw [hclosed.liftN_eq (Nat.zero_le _)] at Hweak
    simpa [VExpr.liftN] using Hweak
  have Hsame : SameTelescopeDomains baseArgs.length
      (VExpr.wrapForalls
        (familyDomains.map (VExpr.instL levels))
        (constructorTail.instL levels))
      (VExpr.wrapForalls
        (familyDomains.map (VExpr.instL levels))
        (familyAfterParams.instL levels)) := by
    rw [hbaseLength, ← hfamilyDomains]
    simpa using SameTelescopeDomains.wrapForalls
      (familyDomains.map (VExpr.instL levels))
      (constructorTail.instL levels) (familyAfterParams.instL levels)
  have Hnormalized :=
    VEnv.HasType.mkApps_sameTelescopeDomains_exact henv hctx Hsame
      HconstructorConst HfamilyConst HfamilyApps
  have HwholeCtx : venv.IsDefEqU outerUvars ctx
      (VExpr.wrapForalls
        (familyDomains.map (VExpr.instL levels))
        (constructorTail.instL levels))
      (VExpr.wrapForalls
        (constructorDomains.map (VExpr.instL levels))
        (constructorTail.instL levels)) :=
    HconstructorConst.uniqU henv hctx HconstructorConstRaw
  have Harity : SameTelescopeArity baseArgs.length
      (VExpr.wrapForalls
        (familyDomains.map (VExpr.instL levels))
        (constructorTail.instL levels))
      (VExpr.wrapForalls
        (constructorDomains.map (VExpr.instL levels))
        (constructorTail.instL levels)) := by
    rw [hbaseLength, ← hfamilyDomains]
    simpa only [List.length_map] using
      (SameTelescopeArity.wrapForalls _ _ hmapLength
        (constructorTail.instL levels) (constructorTail.instL levels))
  have Hresult :=
    Lean4Lean.VerifyInductive.VEnv.IsDefEqU.applyForallType
      henv hctx Harity HwholeCtx HconstructorConst ⟨_, Hnormalized⟩
  have Hraw := Hnormalized.defeqU_r henv hctx Hresult
  change venv.HasType outerUvars ctx
    (VExpr.mkApps (.const family.ctors[i].name levels) baseArgs)
    (VExpr.applyForallType (family.ctors[i].type.instL levels) baseArgs)
  simpa only [HconstructorType, VExpr.instL_wrapForalls] using Hraw

/-- Well-formedness projection of the exact specialization theorem. -/
theorem GeneratedFamilyInstalledContainer.specializedConstructorApplicationWF
    (C : GeneratedFamilyInstalledContainer prodEnv venv params nestedAux
      concrete H)
    (henv : venv.WF)
    (i : Nat)
    (habstractCtor : i <
      (C.container.types[C.familyIdx]'C.familyIdx_lt).ctors.length)
    (levels : List VLevel)
    (hlevelsWF : ∀ level ∈ levels, level.WF outerUvars)
    (hlevelsLength : levels.length = C.container.uvars)
    (ctx : List VExpr) (hctx : OnCtx ctx (venv.IsType outerUvars))
    (baseArgs : List VExpr)
    (hbaseLength : baseArgs.length = C.container.nparams)
    (HfamilyApps : VExpr.WF venv outerUvars ctx
      (VExpr.mkApps
        (.const (C.container.types[C.familyIdx]'C.familyIdx_lt).name levels)
        baseArgs)) :
    VExpr.WF venv outerUvars ctx
      (VExpr.mkApps
        (.const
          ((C.container.types[C.familyIdx]'C.familyIdx_lt).ctors[i]'habstractCtor).name
          levels)
        baseArgs) :=
  ⟨_, C.specializedConstructorApplicationHasType henv i habstractCtor
    levels hlevelsWF hlevelsLength ctx hctx baseArgs hbaseLength HfamilyApps⟩

/-- Exact concrete/abstract source-constructor pair selected by one
`BuiltAuxiliary` position.  This retains the source telescope used by the
builder and derives its semantic translation from persistent environment
alignment and finite installation, rather than asking for it separately. -/
structure GeneratedFamilyInstalledContainer.BuiltConstructorTranslation
    {ves : VEnvs}
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
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
  sourceTranslation : TrConstant safety (ves.venv safety) sourceInfo
    (((C.container.types[C.familyIdx]'C.familyIdx_lt).ctors[i]'abstractIdx_lt).toVConstant)

/-- The executable builder, production alignment, and installed-container
certificate determine the exact translated source constructor at every
position. -/
theorem GeneratedFamilyInstalledContainer.builtConstructorTranslation
    {ves : VEnvs}
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
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
  have habstractLookup : (ves.venv safety).constants
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
  have Htranslation := (wf.tr (safety := safety)).find?_uniq hlookup'
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

/-- Constructor translation evidence persists with its installed container
under an abstract-environment extension. -/
def GeneratedFamilyInstalledContainer.BuiltConstructorTranslation.mono
    {ves largerVes : VEnvs}
    {C : GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
      params nestedAux concrete H}
    (B : C.BuiltConstructorTranslation i hi)
    (hle : ves.venv safety ≤ largerVes.venv safety) :
    (C.mono hle).BuiltConstructorTranslation (ves := largerVes) i hi := {
  targetIdx_lt := B.targetIdx_lt
  sourceInfo := B.sourceInfo
  sourceTail := B.sourceTail
  sourceLookup := B.sourceLookup
  sourceTelescope := B.sourceTelescope
  targetName := B.targetName
  targetType := B.targetType
  abstractIdx_lt := by simpa [GeneratedFamilyInstalledContainer.mono] using
    B.abstractIdx_lt
  sourceTranslation := ⟨B.sourceTranslation.1, B.sourceTranslation.2.1,
    B.sourceTranslation.2.2.mono hle⟩ }

/-- A generated family header and any one of its generated constructor types
close over exactly the same selected local declarations.  This is a literal
producer fact: the two residual bodies may differ, but the executable
`BuiltAuxiliary` used the same `lctx`/`As` closing operation for both. -/
theorem GeneratedFamilyInstalledContainer.BuiltConstructorTranslation.sameForallPrefix
    {ves : VEnvs}
    (C : GeneratedFamilyInstalledContainer prodEnv (ves.venv safety)
      params nestedAux concrete H)
    (B : C.BuiltConstructorTranslation i hi) :
    Expr.SameForallPrefix H.As.size concrete.type
      (concrete.ctors[i]'(by
        simpa [H.family_eq] using B.targetIdx_lt)).type := by
  rcases H.built.opening with
    ⟨familyTail, _HfamilyTelescope, hfamilyType⟩
  have hsourceType : concrete.type = H.lctx.mkForall H.As
      (familyTail.instantiateRevRange 0 H.nestedNParams H.args) := by
    exact (congrArg InductiveType.type H.family_eq).trans hfamilyType
  have hconstructorType :
      (concrete.ctors[i]'(by
        simpa [H.family_eq] using B.targetIdx_lt)).type =
      H.lctx.mkForall H.As
        (B.sourceTail.instantiateRevRange 0 H.nestedNParams H.args) := by
    have htarget : (H.data.type.ctors[i]'B.targetIdx_lt).type =
        H.lctx.mkForall H.As
          (B.sourceTail.instantiateRevRange 0 H.nestedNParams H.args) :=
      B.targetType
    have hctors : concrete.ctors = H.data.type.ctors :=
      congrArg InductiveType.ctors H.family_eq
    simpa [hctors] using htarget
  rw [hsourceType, hconstructorType]
  exact H.selection.sameForallPrefix H.selectionNodup _ _



end VerifyInductive
end Lean4Lean
