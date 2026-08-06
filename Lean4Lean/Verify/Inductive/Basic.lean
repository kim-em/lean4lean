import Init.Data.Array.Lemmas
import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.Environment.Checker
import Lean4Lean.Verify.TypeChecker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VerifyInductive

/-- Completed output of the mutual-header traversal. -/
structure HeaderCertificate (env : VEnv) (decl : VInductDecl) where
  params : List VExpr
  resultLevel : VLevel
  commonLevels : ∀ type ∈ decl.types, type.resultLevel ≈ resultLevel
  typeShapes : ∀ type ∈ decl.types, decl.TypeShape env params type

theorem typeShape_mono {env env' : VEnv} (henv : env ≤ env')
    (H : VInductDecl.TypeShape env decl params type) :
    VInductDecl.TypeShape env' decl params type := by
  rcases H with
    ⟨normalized, ownParams, afterParams, indices, result, exprType,
      hnormalized, hparamsTake, hindicesTake, hparams, hresult⟩
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hnormalized.mono henv, hparamsTake, hindicesTake,
    hparams.mono henv, hresult.mono henv⟩

def HeaderCertificate.mono {env env' : VEnv} (henv : env ≤ env')
    (H : HeaderCertificate env decl) : HeaderCertificate env' decl where
  params := H.params
  resultLevel := H.resultLevel
  commonLevels := H.commonLevels
  typeShapes type htype := typeShape_mono henv (H.typeShapes type htype)

/-- Prefix invariant threaded through `checkInductiveTypes.loopInd`. -/
structure HeaderPrefixCertificate (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (resultLevel : VLevel) (done : Nat) : Prop where
  commonLevels : ∀ i, i < done → (hi : i < decl.types.length) →
    decl.types[i].resultLevel ≈ resultLevel
  typeShapes : ∀ i, i < done → (hi : i < decl.types.length) →
    decl.TypeShape env params decl.types[i]

/-- The prefix evidence together with the translation of the concrete common
result level retained in `InductiveStats`. -/
structure HeaderLoopCertificate (env : VEnv) (lparams : List Name)
    (decl : VInductDecl) (params : List VExpr)
    (stats : AddInductive.InductiveStats) (done : Nat) where
  resultLevel : VLevel
  commonLevel : VLevel.ofLevel lparams stats.resultLevel = some resultLevel
  headerPrefix : HeaderPrefixCertificate env decl params resultLevel done

theorem HeaderPrefixCertificate.empty (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (resultLevel : VLevel) :
    HeaderPrefixCertificate env decl params resultLevel 0 where
  commonLevels _ h := by omega
  typeShapes _ h := by omega

theorem HeaderPrefixCertificate.push
    (H : HeaderPrefixCertificate env decl params resultLevel done)
    (hindex : done < decl.types.length)
    (hlevel : decl.types[done].resultLevel ≈ resultLevel)
    (hshape : decl.TypeShape env params decl.types[done]) :
    HeaderPrefixCertificate env decl params resultLevel (done + 1) where
  commonLevels i hidone hi := by
    by_cases h : i = done
    · subst i; exact hlevel
    · exact H.commonLevels i (by omega) hi
  typeShapes i hidone hi := by
    by_cases h : i = done
    · subst i; exact hshape
    · exact H.typeShapes i (by omega) hi

/-- Initialize the accumulator with the first checked mutual header. -/
theorem HeaderPrefixCertificate.first
    (hindex : 0 < decl.types.length)
    (hshape : decl.TypeShape env params decl.types[0]) :
    HeaderPrefixCertificate env decl params decl.types[0].resultLevel 1 := by
  exact (HeaderPrefixCertificate.empty env decl params
    decl.types[0].resultLevel).push hindex (by rfl) hshape

/-- Convert the executable common-universe guard into the abstract level
equivalence stored by the header-prefix invariant. -/
theorem HeaderPrefixCertificate.pushOfIsEquiv
    (H : HeaderPrefixCertificate env decl params resultLevel done)
    (hindex : done < decl.types.length)
    (hguard : currentLevel.isEquiv commonLevel = true)
    (hcurrent : VLevel.ofLevel lparams currentLevel =
      some decl.types[done].resultLevel)
    (hcommon : VLevel.ofLevel lparams commonLevel = some resultLevel)
    (hshape : decl.TypeShape env params decl.types[done]) :
    HeaderPrefixCertificate env decl params resultLevel (done + 1) :=
  H.push hindex (Level.isEquiv_wf hguard hcurrent hcommon) hshape

def HeaderPrefixCertificate.complete
    (H : HeaderPrefixCertificate env decl params resultLevel decl.types.length) :
    HeaderCertificate env decl where
  params := params
  resultLevel := resultLevel
  commonLevels type htype := by
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    exact H.commonLevels i hi hi
  typeShapes type htype := by
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    exact H.typeShapes i hi hi

/-- Completed output of the flattened constructor traversal. -/
structure ConstructorCertificate (env : VEnv) (decl : VInductDecl)
    (envTypes : VEnv) (params : List VExpr) : Prop where
  shapes : ∀ owned ∈ decl.ownedConstructors,
    decl.CtorShape envTypes params owned.1 owned.2

/-- Prefix invariant for constructor checking in the exact flattened order
used by recursor-minor and iota-rule generation. -/
structure ConstructorPrefixCertificate (env : VEnv) (decl : VInductDecl)
    (envTypes : VEnv) (params : List VExpr) (done : Nat) : Prop where
  shapes : ∀ i, i < done → (hi : i < decl.ownedConstructors.length) →
    decl.CtorShape envTypes params decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2

theorem ConstructorPrefixCertificate.empty (env : VEnv)
    (decl : VInductDecl) (envTypes : VEnv) (params : List VExpr) :
    ConstructorPrefixCertificate env decl envTypes params 0 where
  shapes _ h := by omega

theorem ConstructorPrefixCertificate.push
    (H : ConstructorPrefixCertificate env decl envTypes params done)
    (hindex : done < decl.ownedConstructors.length)
    (hshape : decl.CtorShape envTypes params
      decl.ownedConstructors[done].1 decl.ownedConstructors[done].2) :
    ConstructorPrefixCertificate env decl envTypes params (done + 1) where
  shapes i hidone hi := by
    by_cases h : i = done
    · subst i; exact hshape
    · exact H.shapes i (by omega) hi

theorem ConstructorPrefixCertificate.complete
    (H : ConstructorPrefixCertificate env decl envTypes params
      decl.ownedConstructors.length) :
    ConstructorCertificate env decl envTypes params where
  shapes owned howned := by
    rcases List.mem_iff_getElem.1 howned with ⟨i, hi, rfl⟩
    exact H.shapes i hi hi

theorem ConstructorCertificate.ctorShape
    (H : ConstructorCertificate env decl envTypes params)
    (htype : type ∈ decl.types) (hctor : ctor ∈ type.ctors) :
    decl.CtorShape envTypes params type ctor := by
  apply H.shapes (type, ctor)
  simp [VInductDecl.ownedConstructors, htype, hctor]

/-- Shapes accumulated by the inner constructor loop for one family. -/
structure ConstructorTypePrefix (envTypes : VEnv) (decl : VInductDecl)
    (params : List VExpr) (target : VInductiveType) (done : Nat) : Prop where
  covered : done ≤ target.ctors.length
  shapes : ∀ i, i < done → (hi : i < target.ctors.length) →
    decl.CtorShape envTypes params target target.ctors[i]

theorem ConstructorTypePrefix.empty (envTypes : VEnv) (decl : VInductDecl)
    (params : List VExpr) (target : VInductiveType) :
    ConstructorTypePrefix envTypes decl params target 0 where
  covered := Nat.zero_le _
  shapes _ h := by omega

theorem ConstructorTypePrefix.push
    (H : ConstructorTypePrefix envTypes decl params target done)
    (hi : done < target.ctors.length)
    (hshape : decl.CtorShape envTypes params target target.ctors[done]) :
    ConstructorTypePrefix envTypes decl params target (done + 1) where
  covered := by omega
  shapes i hidone hi' := by
    by_cases h : i = done
    · subst i; exact hshape
    · exact H.shapes i (by omega) hi'

/-- Shapes accumulated by the outer family loop. -/
structure ConstructorTypesPrefix (envTypes : VEnv) (decl : VInductDecl)
    (params : List VExpr) (done : Nat) : Prop where
  covered : done ≤ decl.types.length
  shapes : ∀ i, i < done → (hi : i < decl.types.length) →
    ∀ j (hj : j < decl.types[i].ctors.length),
      decl.CtorShape envTypes params decl.types[i] decl.types[i].ctors[j]

theorem ConstructorTypesPrefix.empty (envTypes : VEnv)
    (decl : VInductDecl) (params : List VExpr) :
    ConstructorTypesPrefix envTypes decl params 0 where
  covered := Nat.zero_le _
  shapes _ h := by omega

theorem ConstructorTypesPrefix.push
    (H : ConstructorTypesPrefix envTypes decl params done)
    (hi : done < decl.types.length)
    (Htype : ConstructorTypePrefix envTypes decl params decl.types[done]
      decl.types[done].ctors.length) :
    ConstructorTypesPrefix envTypes decl params (done + 1) where
  covered := by omega
  shapes i hidone hi' j hj := by
    by_cases h : i = done
    · subst i; exact Htype.shapes j hj hj
    · exact H.shapes i (by omega) hi' j hj

theorem ConstructorTypesPrefix.complete
    (H : ConstructorTypesPrefix envTypes decl params decl.types.length) :
    ConstructorCertificate env decl envTypes params where
  shapes owned howned := by
    rcases List.mem_flatMap.1 howned with ⟨target, htarget, hctor⟩
    rcases List.mem_iff_getElem.1 htarget with ⟨i, hi, rfl⟩
    simp only [List.mem_map] at hctor
    rcases hctor with ⟨ctor, hctor, hpair⟩
    cases hpair
    rcases List.mem_iff_getElem.1 hctor with ⟨j, hj, hctorEq⟩
    cases hctorEq
    simpa using H.shapes i hi hi j hj

/-- Exact name-set state reached by the production inner constructor loop. -/
inductive ConstructorNameState (ctors : List Constructor) :
    Nat → NameSet → Prop
  | zero : ConstructorNameState ctors 0 {}
  | succ (H : ConstructorNameState ctors i found)
      (hi : i < ctors.length) :
      ConstructorNameState ctors (i + 1) (found.insert ctors[i].name)

/-- Fielded aggregation target for the executable header and constructor
traversals. The public specification remains `VInductDecl.FormationWF`; this
certificate gives the refinement proof stable, named obligations instead of
repeatedly unpacking a large existential. -/
structure FormationCertificate (env : VEnv) (decl : VInductDecl) where
  headers : HeaderCertificate env decl
  envTypes : VEnv
  typesInstalled : env.addConsts decl.typeConstants = some envTypes
  constructors : ConstructorCertificate env decl envTypes headers.params

theorem FormationCertificate.formationWF
    (H : FormationCertificate env decl) : decl.FormationWF env := by
  exact ⟨H.headers.params, H.headers.resultLevel, H.envTypes, H.typesInstalled,
    fun type htype => ⟨H.headers.commonLevels type htype,
      H.headers.typeShapes type htype⟩,
    fun type htype ctor hctor => H.constructors.ctorShape htype hctor⟩

theorem FormationCertificate.declWF
    (H : FormationCertificate env decl) (hsource : decl.SourceWF env) :
    decl.WF env :=
  ⟨hsource, H.formationWF⟩

def FormationCertificate.ofPrefixes
    (Hheaders : HeaderLoopCertificate env lparams decl params stats
      decl.types.length)
    (envTypes : VEnv)
    (htypes : env.addConsts decl.typeConstants = some envTypes)
    (Hctors : ConstructorPrefixCertificate env decl envTypes params
      decl.ownedConstructors.length) :
    FormationCertificate env decl where
  headers := Hheaders.headerPrefix.complete
  envTypes := envTypes
  typesInstalled := htypes
  constructors := Hctors.complete

/-- Build ordered relational coverage from equal lengths and pointwise array-
style evidence. This is the common bridge used by recursor and rule loops. -/
theorem List.forall₂_of_getElem
    {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β}
    (hlen : as.length = bs.length)
    (H : ∀ i (ha : i < as.length) (hb : i < bs.length),
      R as[i] bs[i]) :
    List.Forall₂ R as bs := by
  induction as generalizing bs with
  | nil =>
    have : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst bs
    exact .nil
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have htail : as.length = bs.length := by simpa using hlen
      apply List.Forall₂.cons (H 0 (by simp) (by simp))
      apply ih htail
      intro i ha hb
      have h := H (i + 1) (by simpa) (by simpa)
      change R as[i] bs[i] at h
      exact h

theorem List.Forall₂.getElem
    {R : α → β → Prop} {as : List α} {bs : List β}
    (H : List.Forall₂ R as bs) (i : Nat)
    (ha : i < as.length) (hb : i < bs.length) :
    R as[i] bs[i] := by
  induction H generalizing i with
  | nil => simp at ha
  | cons h _ ih =>
    cases i with
    | zero => exact h
    | succ i => exact ih i (by simpa using ha) (by simpa using hb)

theorem List.Forall₂.length_eq'
    (H : List.Forall₂ R as bs) : as.length = bs.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem List.Forall₂.append'
    (H₁ : List.Forall₂ R as bs) (H₂ : List.Forall₂ R as' bs') :
    List.Forall₂ R (as ++ as') (bs ++ bs') := by
  induction H₁ with
  | nil => exact H₂
  | cons h _ ih => exact .cons h ih

theorem OnCtx.append_right
    (H : OnCtx (xs ++ ys) P) : OnCtx ys P := by
  induction xs with
  | nil => exact H
  | cons x xs ih =>
    exact ih H.1

/-- Remove equally long outer prefixes from a context conversion.  Since
`IsDefEqCtx` is built from the shared innermost suffix outwards, the proof is
just inversion through the two prefixes. -/
theorem VEnv.IsDefEqCtx.dropPrefixes
    (H : VEnv.IsDefEqCtx env U [] (xs ++ Γ₁) (ys ++ Γ₂))
    (hlen : xs.length = ys.length) :
    VEnv.IsDefEqCtx env U [] Γ₁ Γ₂ := by
  induction xs generalizing ys with
  | nil =>
    have : ys = [] := List.eq_nil_of_length_eq_zero hlen.symm
    simpa [this] using H
  | cons _ xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons _ ys =>
      simp only [List.cons_append] at H
      cases H with
      | succ H _ =>
        apply ih H
        simpa using Nat.succ.inj hlen

theorem VInductDecl.paramsDefEq_reflOfAppend
    {decl : VInductDecl} {env : VEnv} {indices params : List VExpr}
    (H : OnCtx (indices.reverse ++ params.reverse)
      (env.IsType decl.uvars)) :
    decl.ParamsDefEq env params params := by
  exact VEnv.IsDefEqCtx.refl (OnCtx.append_right H)

theorem TrInductDeclSkeleton.types_length
    (H : TrInductDeclSkeleton env lparams nparams types isUnsafe decl) :
    types.length = decl.types.length := by
  rcases H with ⟨_, _, _, _, _, _, _, _, htypes⟩
  exact Lean4Lean.VerifyInductive.List.Forall₂.length_eq' htypes

theorem TrInductDeclSkeleton.typeAt
    (H : TrInductDeclSkeleton env lparams nparams types isUnsafe decl)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    ∃ envTypes, env.addConsts decl.typeConstants = some envTypes ∧
      TrInductiveTypeSkeleton env envTypes lparams
        types[i] decl.types[i] := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypesAdded,
    hctorsAdded, htypes⟩
  exact ⟨envTypes, htypesAdded,
    Lean4Lean.VerifyInductive.List.Forall₂.getElem htypes i
      hsource htarget⟩

theorem TrInductDeclSkeleton.typeNameAt
    (H : TrInductDeclSkeleton env lparams nparams types isUnsafe decl)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    types[i].name = decl.types[i].name := by
  rcases Lean4Lean.VerifyInductive.TrInductDeclSkeleton.typeAt
    H i hsource htarget with ⟨_, _, Htype⟩
  exact Htype.header.name.symm

theorem TrInductiveTypeSkeleton.materialized
    (H : TrInductiveTypeSkeleton env envTypes lparams type target) :
    TrInductiveType env envTypes lparams type
      (target.toVInductiveType numIndices resultLevel) where
  header := H.header
  ctors := H.ctors

/-- Once the executable header metadata has been collected, the metadata-free
source translation becomes the ordinary declaration translation expected by
the later constructor, compilation, and environment-extension layers. -/
theorem TrInductDeclSkeleton.materialized
    (H : TrInductDeclSkeleton env lparams nparams types isUnsafe skeleton)
    (Hmaterialize : skeleton.materialize metadata = some decl) :
    TrInductDecl env lparams nparams types isUnsafe decl := by
  rcases H with ⟨hsource, huvars, hnparams, hunsafe,
    envTypes, envCtors, htypesAdded, hctorsAdded, htypes⟩
  have hfields := VInductDeclSkeleton.materialize_fields Hmaterialize
  have herase := VInductDeclSkeleton.materialize_toSkeleton Hmaterialize
  have htypeConstants : decl.typeConstants = skeleton.typeConstants := by
    rw [← VInductDecl.toSkeleton_typeConstants decl, herase]
  have hconstructorConstants :
      decl.constructorConstants = skeleton.constructorConstants := by
    rw [← VInductDecl.toSkeleton_constructorConstants decl, herase]
  refine ⟨hsource metadata decl Hmaterialize,
    hfields.1.trans huvars,
    hfields.2.1.trans hnparams,
    hfields.2.2.1.trans hunsafe,
    envTypes, envCtors, ?_, ?_, ?_⟩
  · simpa [htypeConstants] using htypesAdded
  · simpa [hconstructorConstants] using hctorsAdded
  · have hlength : types.length = decl.types.length := by
      calc
        types.length = skeleton.types.length :=
          Lean4Lean.VerifyInductive.List.Forall₂.length_eq' htypes
        _ = decl.types.length := hfields.2.2.2.symm
    apply List.forall₂_of_getElem hlength
    intro i hsourceIdx htargetIdx
    have hskeletonIdx : i < skeleton.types.length := by
      rw [← Lean4Lean.VerifyInductive.List.Forall₂.length_eq' htypes]
      exact hsourceIdx
    have htranslated := Lean4Lean.VerifyInductive.List.Forall₂.getElem
      htypes i hsourceIdx hskeletonIdx
    rcases VInductDeclSkeleton.materialize_typeAt Hmaterialize
        hskeletonIdx with ⟨data, hdata, htarget⟩
    have htarget' : decl.types[i] =
        skeleton.types[i].toVInductiveType data.1 data.2 := by
      simpa [List.getElem?_eq_getElem htargetIdx] using htarget
    rw [htarget']
    exact Lean4Lean.VerifyInductive.TrInductiveTypeSkeleton.materialized
      htranslated

theorem TrInductDecl.types_length
    (H : TrInductDecl env lparams nparams types isUnsafe decl) :
    types.length = decl.types.length := by
  rcases H with ⟨_, _, _, _, _, _, _, _, htypes⟩
  exact Lean4Lean.VerifyInductive.List.Forall₂.length_eq' htypes

theorem TrInductDecl.typeAt
    (H : TrInductDecl env lparams nparams types isUnsafe decl)
    (i : Nat) (hsource : i < types.length)
    (htarget : i < decl.types.length) :
    ∃ envTypes, env.addConsts decl.typeConstants = some envTypes ∧
      TrInductiveType env envTypes lparams types[i] decl.types[i] := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypesAdded,
    hctorsAdded, htypes⟩
  exact ⟨envTypes, htypesAdded,
    Lean4Lean.VerifyInductive.List.Forall₂.getElem htypes i hsource htarget⟩

theorem TrInductiveType.ctors_length
    (H : TrInductiveType env envTypes lparams type target) :
    type.ctors.length = target.ctors.length :=
  Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.ctors

theorem TrInductiveType.ctorAt
    (H : TrInductiveType env envTypes lparams type target)
    (i : Nat) (hsource : i < type.ctors.length)
    (htarget : i < target.ctors.length) :
    TrSourceConst envTypes lparams type.ctors[i].name type.ctors[i].type
      target.ctors[i] :=
  Lean4Lean.VerifyInductive.List.Forall₂.getElem H.ctors i hsource htarget

/-- Inductive metadata does not affect translation of the source header:
only visibility, universe parameters, name, and type cross the production /
abstract boundary. -/
theorem TrSourceConst.inductInfo
    (H : TrSourceConst env lparams name type ci')
    (hlevelParams : info.levelParams = lparams)
    (hname : info.name = name)
    (htype : info.type = type)
    (hvisible : safety ≤
      (if info.isUnsafe then DefinitionSafety.unsafe else .safe)) :
    TrConstVal safety env (.inductInfo info) ci' := by
  subst lparams
  subst name
  subst type
  constructor
  · exact ⟨by simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
        ConstantInfo.isPartial] using hvisible,
      H.uvars.symm, H.type⟩
  · exact H.name.symm

/-- The complete metadata-enriched production header array still translates
pointwise to the abstract mutual type constants. -/
theorem AddInductive.inductiveTypeInfos.translated
    {decl : VInductDecl}
    (Htypes : List.Forall₂
      (TrInductiveType env envTypes lparams)
      indTypes.toList decl.types)
    (hindices : stats.nindices.toList = decl.types.map (·.numIndices))
    (hvisible : safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe)) :
    List.Forall₂
      (fun info (type : VInductiveType) =>
        TrConstVal safety env (.inductInfo info) type.toVConstVal ∧
          type.toVConstant.WF env)
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams).toList
      decl.types := by
  have htypesLength : indTypes.size = decl.types.length := by
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
  have hindicesLength : stats.nindices.size = indTypes.size := by
    rw [Array.size_eq_length_toList, hindices, List.length_map]
    simpa using htypesLength.symm
  have hinfosLength :
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe lparams).toList.length = decl.types.length := by
    simp [AddInductive.inductiveTypeInfos, hindicesLength, htypesLength]
  apply List.forall₂_of_getElem hinfosLength
  intro i hiInfo hiTarget
  have hiSource : i < indTypes.toList.length := by
    simpa [htypesLength] using hiTarget
  have Htype := Lean4Lean.VerifyInductive.List.Forall₂.getElem Htypes i
    hiSource hiTarget
  constructor
  · apply Lean4Lean.VerifyInductive.TrSourceConst.inductInfo Htype.header
    · simp [AddInductive.inductiveTypeInfos]
    · simp [AddInductive.inductiveTypeInfos]
    · simp [AddInductive.inductiveTypeInfos]
    · simpa [AddInductive.inductiveTypeInfos, hindicesLength] using hvisible
  · exact Htype.header.wf

def ownedConstructors
    (types : List InductiveType) : List (InductiveType × Constructor) :=
  types.flatMap fun type => type.ctors.map (type, ·)

def TrOwnedConstructor (env envTypes : VEnv) (lparams : List Name) :
    (InductiveType × Constructor) →
      (VInductiveType × VConstVal) → Prop
  | (type, ctor), (target, ctor') =>
    TrInductiveType env envTypes lparams type target ∧
      TrSourceConst envTypes lparams ctor.name ctor.type ctor'

theorem TrInductiveType.ownedConstructors
    (H : TrInductiveType env envTypes lparams type target) :
    List.Forall₂ (TrOwnedConstructor env envTypes lparams)
      (type.ctors.map (type, ·)) (target.ctors.map (target, ·)) := by
  have aux : ∀ {ctors ctors'},
      List.Forall₂ (fun ctor ctor' =>
        TrSourceConst envTypes lparams ctor.name ctor.type ctor')
        ctors ctors' →
      List.Forall₂ (TrOwnedConstructor env envTypes lparams)
        (ctors.map (type, ·)) (ctors'.map (target, ·)) := by
    intro ctors ctors' hctors
    induction hctors with
    | nil => exact .nil
    | cons h _ ih => exact .cons ⟨H, h⟩ ih
  exact aux H.ctors

theorem TrInductDecl.ownedConstructors
    (H : TrInductDecl env lparams nparams types isUnsafe decl) :
    ∃ envTypes,
      env.addConsts decl.typeConstants = some envTypes ∧
      List.Forall₂ (TrOwnedConstructor env envTypes lparams)
        (Lean4Lean.VerifyInductive.ownedConstructors types)
        decl.ownedConstructors := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypesAdded,
    hctorsAdded, htypes⟩
  refine ⟨envTypes, htypesAdded, ?_⟩
  have aux : ∀ {types targets},
      List.Forall₂ (TrInductiveType env envTypes lparams) types targets →
      List.Forall₂ (TrOwnedConstructor env envTypes lparams)
        (Lean4Lean.VerifyInductive.ownedConstructors types)
        (targets.flatMap fun target => target.ctors.map (target, ·)) := by
    intro types targets htypes
    induction htypes with
    | nil => exact .nil
    | cons h _ ih =>
      simpa [Lean4Lean.VerifyInductive.ownedConstructors] using
        Lean4Lean.VerifyInductive.List.Forall₂.append'
          (Lean4Lean.VerifyInductive.TrInductiveType.ownedConstructors h) ih
  simpa [VInductDecl.ownedConstructors] using aux htypes

theorem TrInductDecl.ownedConstructors_length
    (H : TrInductDecl env lparams nparams types isUnsafe decl) :
    (Lean4Lean.VerifyInductive.ownedConstructors types).length =
      decl.ownedConstructors.length := by
  rcases Lean4Lean.VerifyInductive.TrInductDecl.ownedConstructors H with
    ⟨_, _, hctors⟩
  exact Lean4Lean.VerifyInductive.List.Forall₂.length_eq' hctors

theorem TrInductDecl.ownedConstructorAt
    (H : TrInductDecl env lparams nparams types isUnsafe decl)
    (i : Nat)
    (hsource : i < (Lean4Lean.VerifyInductive.ownedConstructors types).length)
    (htarget : i < decl.ownedConstructors.length) :
    ∃ envTypes, env.addConsts decl.typeConstants = some envTypes ∧
      TrOwnedConstructor env envTypes lparams
        (Lean4Lean.VerifyInductive.ownedConstructors types)[i]
        decl.ownedConstructors[i] := by
  rcases Lean4Lean.VerifyInductive.TrInductDecl.ownedConstructors H with
    ⟨envTypes, htypes, hctors⟩
  exact ⟨envTypes, htypes,
    Lean4Lean.VerifyInductive.List.Forall₂.getElem hctors i hsource htarget⟩

/-- Indexed output certificate for one recursor per mutual-family member. -/
structure RecursorCertificate (decl : VInductDecl)
    (recursors : List VConstVal) : Prop where
  length : recursors.length = decl.types.length
  shapes : ∀ i (htype : i < decl.types.length)
      (hrec : i < recursors.length),
    Nonempty (decl.RecursorShape decl.types[i] recursors[i])

/-- Append-oriented invariant matching the recursor-generation loop. -/
structure RecursorBuildCertificate (decl : VInductDecl)
    (recursors : List VConstVal) : Prop where
  covered : recursors.length ≤ decl.types.length
  shapes : ∀ i (hrec : i < recursors.length)
      (htype : i < decl.types.length),
    Nonempty (decl.RecursorShape decl.types[i] recursors[i])

theorem RecursorBuildCertificate.empty (decl : VInductDecl) :
    RecursorBuildCertificate decl [] where
  covered := Nat.zero_le _
  shapes _ h := by simp at h

theorem RecursorBuildCertificate.push
    (H : RecursorBuildCertificate decl recursors)
    (hnext : recursors.length < decl.types.length)
    (hshape : Nonempty
      (decl.RecursorShape decl.types[recursors.length] recursor)) :
    RecursorBuildCertificate decl (recursors ++ [recursor]) where
  covered := by simp; omega
  shapes i hrec htype := by
    by_cases hi : i < recursors.length
    · simpa [List.getElem_append, hi] using H.shapes i hi htype
    · have hieq : i = recursors.length := by simp at hrec; omega
      subst i
      simpa using hshape

theorem RecursorBuildCertificate.complete
    (H : RecursorBuildCertificate decl recursors)
    (hcomplete : recursors.length = decl.types.length) :
    RecursorCertificate decl recursors where
  length := hcomplete
  shapes i htype hrec := H.shapes i hrec htype

theorem RecursorCertificate.forall₂
    (H : RecursorCertificate decl recursors) :
    List.Forall₂ (fun type recursor =>
      Nonempty (decl.RecursorShape type recursor))
      decl.types recursors := by
  apply List.forall₂_of_getElem H.length.symm
  intro i htype hrec
  exact H.shapes i htype hrec

/-- Indexed output certificate for exactly one iota rule per owned
constructor, in the same flattened order used for minors. -/
structure IotaCertificate (env : VEnv) (decl : VInductDecl)
    (block : VInductBlock) : Prop where
  length : block.rules.length = decl.ownedConstructors.length
  rules : ∀ i (hctor : i < decl.ownedConstructors.length)
      (hrule : i < block.rules.length),
    Nonempty (decl.IotaRule env block decl.ownedConstructors[i].1
      decl.ownedConstructors[i].2 block.rules[i])

theorem IotaCertificate.forall₂
    (H : IotaCertificate env decl block) :
    List.Forall₂ (fun owned rule =>
      Nonempty (decl.IotaRule env block owned.1 owned.2 rule))
      decl.ownedConstructors block.rules := by
  apply List.forall₂_of_getElem H.length.symm
  intro i hctor hrule
  exact H.rules i hctor hrule

/-- Generator-facing form of ordinary compilation. Its indexed fields match
the loops in `mkRecInfos` and `mkRecRules`; `ordinary` below converts them to
the independent list-relational specification. -/
structure OrdinaryCompilationCertificate (env : VEnv)
    (decl : VInductDecl) (block : VInductBlock) : Prop where
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  recursors : RecursorCertificate decl block.recursors
  rules : IotaCertificate env decl block
  names : List.Nodup
    ((block.types ++ block.ctors ++ block.recursors).map (·.name))

theorem OrdinaryCompilationCertificate.ordinary
    (H : OrdinaryCompilationCertificate env decl block) :
    decl.OrdinaryCompilation env block where
  types := H.types
  ctors := H.ctors
  recursors := H.recursors.forall₂
  rules := H.rules.forall₂
  names := H.names

theorem OrdinaryCompilationCertificate.compilesTo
    (H : OrdinaryCompilationCertificate env decl block) :
    decl.CompilesTo env block :=
  .ordinary H.ordinary

/-- Verification state for the outer inductive-construction monad. The local
context is represented by the same `MLCtx` used by the typechecker proof, while
the production reader retains the independently generated `_ind_fresh` names. -/
structure ContextWF (c : AddInductive.Context) where
  venv : VEnv
  checking : CheckingEnv.Valid c.safety c.env venv
  mlctx : TypeChecker.MLCtx
  mlctx_wf : mlctx.WF venv c.lparams
  lctx_eq : mlctx.lctx = c.lctx
  ngen_prefix : c.ngen.namePrefix = `_ind_fresh
  indFresh : ∀ fv ∈ mlctx.vlctx.fvars, c.ngen.Reserves fv
  kernelFresh : ∀ fv ∈ mlctx.vlctx.fvars,
    ({} : TypeChecker.State).ngen.Reserves fv

def initialContext (env : Environment) (lparams : List Name)
    (safety : DefinitionSafety) (allowPrimitive : Bool) (fuel : FuelConfig) :
    AddInductive.Context where
  env; lparams; safety; allowPrimitive; fuel

def ContextWF.initial {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (safety : DefinitionSafety) (lparams : List Name)
    (allowPrimitive : Bool) (fuel : FuelConfig) :
    ContextWF (initialContext env lparams safety allowPrimitive fuel) where
  venv := ves.venv safety
  checking := (wf.tr (safety := safety)).toCheckingValid
    (wf.hasPrimitives (safety := safety)) wf.safePrimitives
  mlctx := .nil
  mlctx_wf := trivial
  lctx_eq := rfl
  ngen_prefix := rfl
  indFresh := nofun
  kernelFresh := nofun

/-- Retain the local checker state while moving to a production and abstract
environment pair known to represent the same extension. -/
def ContextWF.withEnv (H : ContextWF c)
    (hchecking : CheckingEnv.Valid c.safety env' venv')
    (hle : H.venv ≤ venv') :
    ContextWF { c with env := env' } where
  venv := venv'
  checking := hchecking
  mlctx := H.mlctx
  mlctx_wf := H.mlctx_wf.mono hle
  lctx_eq := H.lctx_eq
  ngen_prefix := H.ngen_prefix
  indFresh := H.indFresh
  kernelFresh := H.kernelFresh

theorem ContextWF.current_not_mem (H : ContextWF c) :
    ⟨c.ngen.curr⟩ ∉ H.mlctx.vlctx.fvars := fun hmem =>
  c.ngen.not_reserves_self (H.indFresh _ hmem)

theorem ContextWF.kernel_reserves_current (H : ContextWF c) :
    ({} : TypeChecker.State).ngen.Reserves ⟨c.ngen.curr⟩ := by
  apply NameGenerator.Reserves.num_of_prefix_ne
  simp [H.ngen_prefix]

def ContextWF.withLocalDecl (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    ContextWF { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi } where
  venv := H.venv
  checking := H.checking
  mlctx := .vlam ⟨c.ngen.curr⟩ name ty ty' bi H.mlctx
  mlctx_wf := ⟨H.mlctx_wf,
    H.mlctx_wf.tr.find?_eq_none.2 H.current_not_mem, htr, hty⟩
  lctx_eq := by
    change H.mlctx.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi =
      c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi
    rw [H.lctx_eq]
  ngen_prefix := by
    change c.ngen.namePrefix = `_ind_fresh
    exact H.ngen_prefix
  indFresh := by
    intro fv hmem
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact c.ngen.next_reserves_self
    · exact (H.indFresh _ hmem).mono NameGenerator.LE.next
  kernelFresh := by
    intro fv hmem
    simp only [TypeChecker.MLCtx.vlctx, VLCtx.fvars_cons_some,
      List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact H.kernel_reserves_current
    · exact H.kernelFresh _ hmem

theorem ContextWF.withLocalDecl_venv (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).venv = H.venv := rfl

theorem ContextWF.withLocalDecl_toCtx (H : ContextWF c)
    (htr : TrExprS H.venv c.lparams H.mlctx.vlctx ty ty')
    (hty : H.venv.IsType c.lparams.length H.mlctx.vlctx.toCtx ty') :
    (H.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx.toCtx =
      ty' :: H.mlctx.vlctx.toCtx := rfl

theorem withLocalDecl.WF {k : Expr → AddInductive.M α} (Hc : ContextWF c)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (Hk : (k (.fvar ⟨c.ngen.curr⟩)
      { c with
        ngen := c.ngen.next
        lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }).WF Q) :
    (Lean4Lean.withLocalDecl name bi ty k c).WF Q := by
  have _Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  exact Hk

/-- Invert the syntax-directed part of a translated forall while retaining the
definitional equality introduced by normalization.  Header and constructor
loops use this after `whnf`: the production expression is syntactically a
forall, but its abstract translation need only be definitionally equal to one. -/
theorem TrExpr.forallE_source
    (H : TrExpr env Us Δ (.forallE name dom body bi) type') :
    ∃ dom' body',
      TrExprS env Us Δ dom dom' ∧
      TrExprS env Us ((none, .vlam dom') :: Δ) body body' ∧
      env.IsType Us.length Δ.toCtx dom' ∧
      env.IsType Us.length (dom' :: Δ.toCtx) body' ∧
      env.IsDefEqU Us.length Δ.toCtx (.forallE dom' body') type' := by
  rcases H with ⟨_, Hsyntax, Hdefeq⟩
  cases Hsyntax with
  | forallE HdomType HbodyType Hdom Hbody =>
    exact ⟨_, _, Hdom, Hbody, HdomType, HbodyType, Hdefeq⟩

/-- Invert a production sort after normalization, retaining both its universe
translation and its definitional equality to the abstract source tail. -/
theorem TrExpr.sort_source
    (H : TrExpr env Us Δ (.sort level) type') :
    ∃ level', VLevel.ofLevel Us level = some level' ∧
      env.IsDefEqU Us.length Δ.toCtx (.sort level') type' := by
  rcases H with ⟨_, Hsyntax, Hdefeq⟩
  cases Hsyntax with
  | sort Hlevel => exact ⟨_, Hlevel, Hdefeq⟩

/-- A translated production sort pins the type of the abstract conversion to
the successor sort, not merely to an existentially hidden type. -/
theorem TrExpr.sort_result
    (henv : VEnv.WF env) (hctx : OnCtx Δ.toCtx (env.IsType Us.length))
    (H : TrExpr env Us Δ (.sort level) type') :
    ∃ level', VLevel.ofLevel Us level = some level' ∧
      env.IsDefEq Us.length Δ.toCtx type' (.sort level')
        (.sort (.succ level')) := by
  rcases TrExpr.sort_source H with ⟨level', hlevel, typeEq⟩
  exact ⟨level', hlevel, typeEq.symm.of_r henv hctx
    (.sort (.of_ofLevel hlevel))⟩

/-- Aggregates the final `ensureSort` translation with the independently
recorded parameter/index telescope into the public `TypeShape` judgment. -/
theorem TrExpr.typeShape
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    (henv : VEnv.WF env) (hctx : VLCtx.WF env Us.length Δ)
    (huvars : Us.length = decl.uvars)
    (hctxEq : Δ.toCtx = indices.reverse ++ ownParams.reverse)
    (hheader : env.IsDefEq decl.uvars [] target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq env params ownParams)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (H : TrExpr env Us Δ (.sort level) result) :
    decl.TypeShape env params target := by
  rcases TrExpr.sort_result henv hctx.toCtx H with
    ⟨resultLevel, hresultLevel, hresult⟩
  have hlevelEq := hlevel resultLevel hresultLevel
  subst resultLevel
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hheader, hparamsTake, hindicesTake, hparams,
    by simpa [huvars, hctxEq] using hresult⟩

/-- Context-conversion form of `typeShape`.  This is the form needed by the
executable telescope because annotation consumption changes binder domains
definitionally, while preserving the same de Bruijn context shape. -/
theorem TrExpr.typeShapeOfDefEqCtx
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    (henv : VEnv.WF env) (hctx : VLCtx.WF env Us.length Δ)
    (huvars : Us.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx env Us.length []
      (indices.reverse ++ ownParams.reverse) Δ.toCtx)
    (hheader : env.IsDefEq decl.uvars [] target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq env params ownParams)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (H : TrExpr env Us Δ (.sort level) result) :
    decl.TypeShape env params target := by
  rcases TrExpr.sort_result henv hctx.toCtx H with
    ⟨resultLevel, hresultLevel, hresult⟩
  have hlevelEq := hlevel resultLevel hresultLevel
  subst resultLevel
  have hresult' := hresult.defeqDFC henv.ordered (hctxEq.symm henv.ordered)
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hheader, hparamsTake, hindicesTake, hparams,
    by simpa [huvars] using hresult'⟩

/-- Context- and result-conversion form of `typeShape`.  Repeated executable
`whnf` calls need only remain definitionally equal to the unconsumed source
telescope; they need not choose that telescope's exact syntax. -/
theorem TrExpr.typeShapeOfDefEqCtxResult
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result translatedResult exprType : VExpr}
    (henv : VEnv.WF env) (hctx : VLCtx.WF env Us.length Δ)
    (huvars : Us.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx env Us.length []
      (indices.reverse ++ ownParams.reverse) Δ.toCtx)
    (hheader : env.IsDefEq decl.uvars [] target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq env params ownParams)
    (hresultEq : env.IsDefEqU Us.length Δ.toCtx result translatedResult)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (H : TrExpr env Us Δ (.sort level) translatedResult) :
    decl.TypeShape env params target := by
  rcases TrExpr.sort_result henv hctx.toCtx H with
    ⟨resultLevel, hresultLevel, htranslated⟩
  have hlevelEq := hlevel resultLevel hresultLevel
  subst resultLevel
  have hsourceType := htranslated.hasType.1.defeqU_l henv hctx.toCtx
    hresultEq.symm
  have hsourceEqU := hresultEq.trans henv hctx.toCtx ⟨_, htranslated⟩
  have hsourceEq := hsourceEqU.of_l henv hctx.toCtx hsourceType
  have hsourceEq' := hsourceEq.defeqDFC henv.ordered
    (hctxEq.symm henv.ordered)
  exact ⟨normalized, ownParams, afterParams, indices, result, exprType,
    hheader, hparamsTake, hindicesTake, hparams,
    by simpa [huvars] using hsourceEq'⟩

/-- Close a sort-level definitional equality over a dependent forall
telescope.  This is the abstraction step needed when the executable checker
performs a fresh `whnf` after opening each binder. -/
theorem VExpr.wrapForalls_defeq
    {env : VEnv} {U : Nat} {domains Γ : List VExpr}
    {body body' : VExpr} {bodyLevel : VLevel}
    (hctx : OnCtx (domains.reverse ++ Γ) (env.IsType U))
    (hbody : env.IsDefEq U (domains.reverse ++ Γ)
      body body' (.sort bodyLevel)) :
    ∃ resultLevel, env.IsDefEq U Γ
      (VExpr.wrapForalls domains body)
      (VExpr.wrapForalls domains body') (.sort resultLevel) := by
  induction domains generalizing Γ with
  | nil =>
    exact ⟨bodyLevel, by simpa [VExpr.wrapForalls] using hbody⟩
  | cons dom domains ih =>
    have hctx' : OnCtx (domains.reverse ++ (dom :: Γ))
        (env.IsType U) := by
      simpa [List.reverse_cons, List.append_assoc] using hctx
    have hdomCtx : OnCtx (dom :: Γ) (env.IsType U) :=
      OnCtx.append_right hctx'
    rcases hdomCtx.2 with ⟨domLevel, hdom⟩
    rcases ih hctx' (by
      simpa [List.reverse_cons, List.append_assoc] using hbody) with
      ⟨resultLevel, hrest⟩
    exact ⟨.imax domLevel resultLevel, .forallEDF hdom hrest⟩

/-- Opening a source binder with the fresh free variable chosen by the
production checker leaves its abstract body unchanged: the extended `VLCtx`
maps that free variable back to the new outermost de Bruijn variable. -/
theorem ContextWF.instantiateFresh (Hc : ContextWF c)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam ty') :: Hc.mlctx.vlctx) body body') :
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
    TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
      (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body' := by
  dsimp only
  rw [Expr.instantiate1_eq]
  exact hbody.inst_fvar Hc.checking.tr.wf.ordered
    (Hc.withLocalDecl htr hty).mlctx_wf.tr.wf

/-- Instantiate a source binder with an existing translated argument whose
cached type is only definitionally equal to the binder domain. -/
theorem ContextWF.instantiateDefEq (Hc : ContextWF c)
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (harg : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx arg arg')
    (hargType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      arg' argType')
    (heq : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      dom' argType') :
    TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 arg) (body'.inst arg') := by
  have hargType' := hargType.defeqU_r Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx heq.symm
  rw [Expr.instantiate1_eq]
  exact hbody.inst Hc.checking.tr.wf.ordered hargType' harg

/-- Semantic certificate for the production checker's removal of binder type
annotations.  The consumed syntax may translate to a different abstract term,
but it must remain a type definitionally equal to the source domain. -/
structure ContextWF.ConsumedDomain (Hc : ContextWF c)
    (dom : Expr) (source' consumed' : VExpr) : Prop where
  source : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom source'
  consumed : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
    dom.consumeTypeAnnotations consumed'
  isType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx consumed'
  source_defeq : ∃ u, Hc.venv.IsDefEq c.lparams.length Hc.mlctx.vlctx.toCtx
    source' consumed' (.sort u)

theorem Expr.consumeTypeAnnotations_eq_self {dom : Expr}
    (hopt : dom.isOptParam = false) (hauto : dom.isAutoParam = false)
    (hout : dom.isOutParam = false) (hsemi : dom.isSemiOutParam = false) :
    dom.consumeTypeAnnotations = dom := by
  simp [hopt, hauto, hout, hsemi]

/-- Removing binder annotations only selects subexpressions of the original
domain, so it cannot introduce a new free-variable dependency. -/
theorem Expr.consumeTypeAnnotations_fvarsIn
    (H : FVarsIn P e) : FVarsIn P e.consumeTypeAnnotations := by
  rw (occs := .pos [1]) [Expr.consumeTypeAnnotations_eq]
  split
  · rename_i hannotation
    cases e <;> simp_all [Expr.isOptParam, Expr.isAutoParam,
      Expr.isAppOfArity, Expr.appFn!, Expr.appArg!, FVarsIn,
      -Expr.consumeTypeAnnotations_eq]
    case app fn arg =>
      cases fn <;> simp_all [Expr.isAppOfArity, FVarsIn,
        -Expr.consumeTypeAnnotations_eq]
      case app fn' arg' =>
        exact Expr.consumeTypeAnnotations_fvarsIn H.1.2
  · split
    · cases e <;> simp_all [Expr.isOutParam, Expr.isSemiOutParam,
        Expr.isAppOfArity, Expr.appArg!, FVarsIn,
        -Expr.consumeTypeAnnotations_eq]
      case app fn arg =>
        exact Expr.consumeTypeAnnotations_fvarsIn H.2
    · exact H
termination_by e

/-- Domains without a leading type annotation need no semantic transport. -/
theorem ContextWF.ConsumedDomain.unchanged (Hc : ContextWF c)
    (heq : dom.consumeTypeAnnotations = dom)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom') :
    Hc.ConsumedDomain dom dom' dom' := by
  rcases hty with ⟨u, hty⟩
  exact {
    source := htr
    consumed := heq.symm ▸ htr
    isType := ⟨u, hty⟩
    source_defeq := ⟨u, hty⟩ }

theorem ContextWF.ConsumedDomain.unannotated (Hc : ContextWF c)
    (hopt : dom.isOptParam = false) (hauto : dom.isAutoParam = false)
    (hout : dom.isOutParam = false) (hsemi : dom.isSemiOutParam = false)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom') :
    Hc.ConsumedDomain dom dom' dom' :=
  .unchanged Hc (Expr.consumeTypeAnnotations_eq_self hopt hauto hout hsemi) htr hty

/-- Transport the source body translation to the annotation-consumed binder
type.  This is the bridge needed before opening the binder with the production
free variable. -/
theorem ContextWF.ConsumedDomain.body
    {c : AddInductive.Context} (Hc : ContextWF c)
    {dom body : Expr} {source' consumed' body' : VExpr}
    (H : Hc.ConsumedDomain dom source' consumed')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam source') :: Hc.mlctx.vlctx) body body') :
    ∃ body'', TrExprS Hc.venv c.lparams
        ((none, .vlam consumed') :: Hc.mlctx.vlctx) body body'' ∧
      Hc.venv.IsDefEqU c.lparams.length
        (source' :: Hc.mlctx.vlctx.toCtx) body' body'' := by
  rcases H.source_defeq with ⟨_, hdom⟩
  have hctx : VLCtx.IsDefEq Hc.venv c.lparams.length
      ((none, .vlam source') :: Hc.mlctx.vlctx)
      ((none, .vlam consumed') :: Hc.mlctx.vlctx) :=
    VLCtx.IsDefEq.cons
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) nofun (.vlam hdom)
  rcases hbody.defeqDFC Hc.checking.tr.wf hctx with ⟨body'', hbody''⟩
  exact ⟨body'', hbody'', hbody.uniq Hc.checking.tr.wf hctx hbody''⟩

/-- Move the source/body conversion produced by `body` into the
annotation-consumed context installed by the executable checker. -/
theorem ContextWF.ConsumedDomain.bodyDefEqConsumed
    {c : AddInductive.Context} (Hc : ContextWF c)
    {dom : Expr} {source' consumed' sourceBody body'' : VExpr}
    (H : Hc.ConsumedDomain dom source' consumed')
    (hbodyEq : Hc.venv.IsDefEqU c.lparams.length
      (source' :: Hc.mlctx.vlctx.toCtx) sourceBody body'') :
    Hc.venv.IsDefEqU c.lparams.length
      (consumed' :: Hc.mlctx.vlctx.toCtx) sourceBody body'' := by
  rcases H.source_defeq with ⟨_, hsource⟩
  have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (source' :: Hc.mlctx.vlctx.toCtx)
      (consumed' :: Hc.mlctx.vlctx.toCtx) :=
    .succ (.refl Hc.mlctx_wf.tr.wf.toCtx) hsource
  exact hbodyEq.defeqDFC Hc.checking.tr.wf.ordered hctx

/-- Semantic compatibility required of Lean's opaque annotation erasure.
It is kept as one named boundary condition until the translations of
`OptParam`, `AutoParam`, and output-parameter wrappers are verified directly. -/
def ConsumeTypeAnnotationsCompat : Prop :=
  ∀ (c : AddInductive.Context) (Hc : ContextWF c)
    {dom : Expr} {source' : VExpr},
    TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom source' →
    Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx source' →
    ∃ consumed', Hc.ConsumedDomain dom source' consumed'

def ContextWF.typeChecker (H : ContextWF c) : TypeChecker.VContext :=
  TypeChecker.VContext.mkCheckingValidMLC H.checking H.mlctx H.mlctx_wf c.fuel

@[simp] theorem ContextWF.typeChecker_lctx (H : ContextWF c) :
    H.typeChecker.lctx = c.lctx := by
  simp [ContextWF.typeChecker, TypeChecker.VContext.mkCheckingValidMLC, H.lctx_eq]

/-- Reuse a verified typechecker computation inside `AddInductive.M`. -/
theorem liftTypeChecker.WF {x : TypeChecker.M α} (Hc : ContextWF c)
    (Hx : TypeChecker.M.WF Hc.typeChecker {} x fun a _ => Q a) :
    ((monadLift x : AddInductive.M α) c).WF Q := by
  change (TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel x).WF Q
  rw [← Hc.lctx_eq]
  exact TypeChecker.M.WF.runCheckingValidMLC Hc.kernelFresh Hx

theorem checkTypeInContext.WF (Hc : ContextWF c)
    (hfvars : e.FVarsIn (· ∈ Hc.mlctx.vlctx.fvars)) :
    ((monadLift (TypeChecker.checkType e) : AddInductive.M Expr) c).WF fun ty =>
      ∃ e' ty', TrTyping Hc.venv c.lparams Hc.mlctx.vlctx e ty e' ty' :=
  liftTypeChecker.WF Hc (TypeChecker.checkType.WF hfvars)

theorem whnfInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' :=
  liftTypeChecker.WF Hc (TypeChecker.whnf.WF he)

/-- `whnf` preserves every admissible free-variable scope of its input, in
addition to preserving the abstract expression up to definitional equality.
The ordinary wrapper above projects this fact away; later mutual headers need
it to show normalization cannot introduce ambient or future cached
parameters. -/
theorem whnfInContext.scopeWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.whnf e) : AddInductive.M Expr) c).WF fun e₁ =>
      FVarsBelow Hc.mlctx.vlctx e e₁ ∧
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' :=
  liftTypeChecker.WF Hc
    ((TypeChecker.Inner.whnf.WF he).run)

theorem ensureSortInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.ensureSort e e₀) : AddInductive.M Expr) c).WF fun e₁ =>
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx e₁ e' ∧ ∃ u, e₁ = .sort u :=
  liftTypeChecker.WF Hc (TypeChecker.ensureSort.WF he)

theorem ensureSortInContext.scopeWF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.ensureSort e e₀) : AddInductive.M Expr) c).WF
      fun e₁ => Hc.typeChecker.FVarsBelow e e₁ ∧
        Hc.typeChecker.TrExpr e₁ e' ∧
        ∃ u, e₁ = .sort u := by
  change Hc.typeChecker.TrExprS e e' at he
  apply liftTypeChecker.WF (Q := fun e₁ =>
    Hc.typeChecker.FVarsBelow e e₁ ∧
      Hc.typeChecker.TrExpr e₁ e' ∧
      ∃ u, e₁ = .sort u) Hc
  simpa only [TypeChecker.ensureSort] using
    (TypeChecker.Inner.ensureSortCore.WF he).run.mono
      (fun _ _ _ h => And.intro h.2.2 (And.intro h.2.1 h.1))

theorem ensureTypeInContext.WF (Hc : ContextWF c)
    (he : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e') :
    ((monadLift (TypeChecker.ensureType e) : AddInductive.M Expr) c).WF fun sort =>
      ∃ e'', TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e e'' ∧
        ∃ u u', sort = .sort u ∧ VLevel.ofLevel c.lparams u = some u' ∧
          Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx e'' (.sort u') :=
  liftTypeChecker.WF Hc (TypeChecker.ensureType.WF he)

theorem isDefEqInContext.WF (Hc : ContextWF c)
    (he₁ : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e₁ e₁')
    (he₂ : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx e₂ e₂') :
    ((monadLift (TypeChecker.isDefEq e₁ e₂) : AddInductive.M Bool) c).WF fun b =>
      b → Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx e₁' e₂' :=
  liftTypeChecker.WF Hc (TypeChecker.isDefEq.WF he₁ he₂)

theorem checkNoMVarNoFVar.closed
    (H : Kernel.Environment.checkNoMVarNoFVar env name e = .ok ()) :
    e.FVarsIn fun _ => False := by
  have hm : e.hasMVar = false := by
    cases hm : e.hasMVar
    · rfl
    · have he : Kernel.Environment.checkNoMVar env name e =
          .error (.declHasMVars env name e) := by
        unfold Kernel.Environment.checkNoMVar
        rw [hm]
        change Except.error _ = Except.error _
        rfl
      rw [Kernel.Environment.checkNoMVarNoFVar, he] at H
      contradiction
  have hf : e.hasFVar = false := by
    have hmok : Kernel.Environment.checkNoMVar env name e = .ok () := by
      unfold Kernel.Environment.checkNoMVar
      rw [hm]
      rfl
    cases hf : e.hasFVar
    · rfl
    · have he : Kernel.Environment.checkNoFVar env name e =
          .error (.declHasFVars env name e) := by
        unfold Kernel.Environment.checkNoFVar
        rw [hf]
        change Except.error _ = Except.error _
        rfl
      rw [Kernel.Environment.checkNoMVarNoFVar, hmok, he] at H
      contradiction
  apply Lean4Lean.fvarsIn_iff.mpr
  refine ⟨?_, Lean4Lean.fvarsIn_iff_hasMVar.mpr hm⟩
  · intro fv hmem
    rw [Lean4Lean.fvarsList_eq_nil.2 hf] at hmem
    contradiction

theorem checkClosedType.WF (Hc : ContextWF c) :
    (AddInductive.checkClosedType name type c).WF fun checkedType =>
      ∃ type' checkedType',
        TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
          type checkedType type' checkedType' := by
  change (c.env.checkNoMVarNoFVar name type >>= fun _ =>
    TypeChecker.M.run c.env c.safety c.lctx c.lparams c.fuel
      (TypeChecker.checkType type)).WF _
  have hno : (c.env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := c.env) (name := name) h
  exact hno.bind fun _ hclosed =>
    checkTypeInContext.WF Hc (hclosed.mono fun _ h => False.elim h)

namespace checkInductiveTypes.loopType

/-- Abstract images of the concrete parameter cache after `done` parameter
binders and `depth` subsequent index binders.  Its recursive presentation
matches the executable `Array.push` order exactly. -/
def cachedParamVars : Nat → Nat → List VExpr
  | 0, _ => []
  | done + 1, depth =>
    (cachedParamVars done depth).map (fun e => e.liftN 1 0) ++
      [.bvar depth]

@[simp] theorem cachedParamVars_zero : cachedParamVars 0 depth = [] := rfl

@[simp] theorem cachedParamVars_succ :
    cachedParamVars (done + 1) depth =
      (cachedParamVars done depth).map (fun e => e.liftN 1 0) ++
        [.bvar depth] := rfl

@[simp] theorem cachedParamVars_length :
    (cachedParamVars done depth).length = done := by
  induction done with
  | zero => rfl
  | succ done ih => simp [cachedParamVars_succ, ih]

theorem cachedParamVars_getElem? :
    (cachedParamVars done depth)[i]? =
      if i < done then some (.bvar (depth + (done - 1 - i))) else none := by
  induction done generalizing depth i with
  | zero => simp
  | succ done ih =>
    simp only [cachedParamVars_succ]
    by_cases hprior : i < done
    · rw [List.getElem?_append_left (by simp [hprior])]
      rw [List.getElem?_map, ih]
      simp only [hprior, if_true, Option.map_some]
      simp [VExpr.liftN]
      congr 2
      omega
    · by_cases hcurrent : i < done + 1
      · have hieq : i = done := by omega
        subst i
        simp
      · have hout : done + 1 ≤ i := by omega
        rw [List.getElem?_eq_none_iff.2 (by simp; omega)]
        simp [hcurrent]

@[simp] theorem cachedParamVars_depth_succ :
    cachedParamVars done (depth + 1) =
      (cachedParamVars done depth).map (fun e => e.liftN 1 0) := by
  induction done with
  | zero => rfl
  | succ done ih =>
    simp [cachedParamVars_succ, ih, List.map_map, VExpr.liftN,
      Function.comp_def]

theorem cachedParamVars_eq_paramVars (decl : VInductDecl) :
    cachedParamVars decl.nparams depth = decl.paramVars depth := by
  apply List.ext_getElem?
  intro i
  rw [cachedParamVars_getElem?]
  by_cases hi : i < decl.nparams
  · rw [VInductDecl.paramVars, List.getElem?_map]
    rw [List.getElem?_reverse (by simp [hi])]
    have hj : decl.nparams - 1 - i < decl.nparams := by omega
    simp [hi, hj]
  · rw [List.getElem?_eq_none_iff.2 (by
      simp [VInductDecl.paramVars]
      omega)]
    simp [hi]

/-- Local invariant for the first header's common-parameter branch. -/
structure ParameterCachePrefix (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (done depth : Nat) : Prop where
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (cachedParamVars done depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

/-- A concrete cached parameter and the free-variable declaration that owns
it in the retained verifier context. -/
def CachedParameterDecl (param : Expr)
    (entry : Option (FVarId × List FVarId) × VLocalDecl) : Prop :=
  ∃ fv deps type,
    param = .fvar fv ∧ entry = (some (fv, deps), .vlam type)

/-- Structural companion to `ParameterCachePrefix`.  Cached parameter local
declarations form an exact suffix of the retained context; every index added
after the parameter phase belongs to `ambientDecls`.  The reverse is
intentional:
the executable array stores parameters from oldest to newest, while local
declarations are pushed at the head.

This suffix decomposition is what lets later mutual headers discard ambient
indices and not-yet-used cached parameters before applying
`TrExprS.uninstantiateAfterWeakFV`. -/
structure ParameterContextSuffix (Hc : ContextWF c)
    (stats : AddInductive.InductiveStats) (depth : Nat) : Type where
  ambientDecls : VLCtx
  parameterDecls : VLCtx
  context : Hc.mlctx.vlctx = ambientDecls ++ parameterDecls
  prefixLength : ambientDecls.length = depth
  cached : List.Forall₂ CachedParameterDecl
    stats.params.toList.reverse parameterDecls
  narrowParams : List.Forall₂
    (TrExprS Hc.venv c.lparams parameterDecls)
    stats.params.toList (cachedParamVars stats.params.size 0)

/-- Reindex a parameter cache across statistics updates that leave the
cached parameter array unchanged. -/
def ParameterCachePrefix.reindex
    (H : ParameterCachePrefix env Us Δ stats done depth)
    (hparams : stats'.params = stats.params) :
    ParameterCachePrefix env Us Δ stats' done depth where
  params := by rw [hparams]; exact H.params
  paramFVars := by rw [hparams]; exact H.paramFVars

/-- Reindex the exact cached suffix across a statistics update that changes
only per-header output fields. -/
def ParameterContextSuffix.reindex
    (H : ParameterContextSuffix Hc stats depth)
    (hparams : stats'.params = stats.params) :
    ParameterContextSuffix Hc stats' depth where
  ambientDecls := H.ambientDecls
  parameterDecls := H.parameterDecls
  context := H.context
  prefixLength := H.prefixLength
  cached := by rw [hparams]; exact H.cached
  narrowParams := by rw [hparams]; exact H.narrowParams

@[simp] theorem _root_.Lean4Lean.VExpr.containsAnyConst_liftN
    {e : VExpr} {n k : Nat} {names : List Name} :
    (e.liftN n k).containsAnyConst names = e.containsAnyConst names := by
  induction e generalizing k <;>
    simp [VExpr.liftN, VExpr.containsAnyConst, *]

def _root_.Lean4Lean.checkPositivityStep.VLCtx.NoIndConsts
    (names : List Name) (Δ : VLCtx) : Prop :=
  ∀ {v mapped type}, Δ.find? v = some (mapped, type) →
    mapped.containsAnyConst names = false

theorem _root_.Lean4Lean.checkPositivityStep.VLCtx.NoIndConsts.cons
    {Δ : VLCtx} {names : List Name}
    {ofv : Option (FVarId × List FVarId)} {d : VLocalDecl}
    (H : checkPositivityStep.VLCtx.NoIndConsts names Δ)
    (hvalue : d.value.containsAnyConst names = false) :
    checkPositivityStep.VLCtx.NoIndConsts names ((ofv, d) :: Δ) := by
  intro v mapped type hfind
  simp only [VLCtx.find?] at hfind
  split at hfind
  · cases hfind
    exact hvalue
  · simp at hfind
    rcases hfind with ⟨old, _type, hfind, hmap, _⟩
    rw [← hmap]
    simpa only [VExpr.containsAnyConst_liftN] using H hfind

abbrev _root_.Lean4Lean.VLCtx.NoIndConsts :=
  checkPositivityStep.VLCtx.NoIndConsts

theorem _root_.Lean4Lean.VLCtx.NoIndConsts.cons
    {Δ : VLCtx} {names : List Name}
    {ofv : Option (FVarId × List FVarId)} {d : VLocalDecl}
    (H : VLCtx.NoIndConsts names Δ)
    (hvalue : d.value.containsAnyConst names = false) :
    VLCtx.NoIndConsts names ((ofv, d) :: Δ) :=
  checkPositivityStep.VLCtx.NoIndConsts.cons H hvalue

theorem ParameterContextSuffix.noIndConsts
    (H : ParameterContextSuffix Hc stats depth) (names : List Name) :
    checkPositivityStep.VLCtx.NoIndConsts names H.parameterDecls := by
  have go : ∀ {params : List Expr} {entries : VLCtx},
      List.Forall₂ CachedParameterDecl params entries →
      checkPositivityStep.VLCtx.NoIndConsts names entries := by
    intro params entries hcached
    induction hcached with
    | nil =>
      intro v mapped type hfind
      simp [VLCtx.find?] at hfind
    | @cons param entry params entries hentry _ ih =>
      rcases hentry with ⟨fv, deps, type, rfl, rfl⟩
      exact checkPositivityStep.VLCtx.NoIndConsts.cons ih rfl
  intro v mapped type hfind
  exact go H.cached hfind

/-- A semantic header scope embedded in the larger executable local context.
`expanded` is the literal weakening of the narrow scope; it is kept separate
from `runtime` because annotation consumption can replace an installed binder
domain by a merely definitionally equal expression. -/
structure NarrowRuntimeScope (env : VEnv) (Us : List Name)
    (scope runtime : VLCtx) : Type where
  expanded : VLCtx
  shift : Lift
  lift : VLCtx.FVLift' scope expanded 0 shift 0
  context : VLCtx.IsDefEq env Us.length expanded runtime
  upset : IsFVarUpSet (· ∈ scope.fvars) runtime
  noBV : scope.NoBV
  noIndConsts : ∀ names,
    checkPositivityStep.VLCtx.NoIndConsts names scope

def NarrowRuntimeScope.mono {env env' : VEnv} (henv : env ≤ env')
    (H : NarrowRuntimeScope env Us scope runtime) :
    NarrowRuntimeScope env' Us scope runtime where
  expanded := H.expanded
  shift := H.shift
  lift := H.lift
  context := H.context.mono henv
  upset := H.upset
  noBV := H.noBV
  noIndConsts := H.noIndConsts

theorem NarrowRuntimeScope.scopeWF
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF) :
    scope.WF env Us.length :=
  H.lift.wf henv H.context.wf

/-- Restrict a translated concrete expression to its semantic header scope.
The source-side free-variable premise is the deliberate ownership boundary:
ambient declarations retained by the executable loop may not occur. -/
theorem NarrowRuntimeScope.restrict
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (htr : TrExprS env Us runtime e e')
    (hclosed : Closed e 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) e) :
    ∃ e', TrExprS env Us scope e e' := by
  exact htr.weakFV'_inv henv H.lift
    (H.context.symm henv.ordered) hclosed hfvars

/-- Restriction together with the definitional equality obtained by
weakening the narrowed translation back into the executable context. -/
theorem NarrowRuntimeScope.restrictEq
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (htr : TrExprS env Us runtime e e')
    (hclosed : Closed e 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) e) :
    ∃ narrow', TrExprS env Us scope e narrow' ∧
      env.IsDefEqU Us.length runtime.toCtx e'
        (narrow'.lift' H.shift) := by
  rcases H.restrict henv htr hclosed hfvars with ⟨narrow', hnarrow⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  exact ⟨narrow', hnarrow,
    htr.uniq henv (H.context.symm henv.ordered) hweak⟩

/-- The abstract target computed in the executable context is the weakening
of the independently translated narrow target. -/
theorem NarrowRuntimeScope.fullTargetEq
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExpr env Us runtime e full') :
    env.IsDefEqU Us.length runtime.toCtx
      (narrow'.lift' H.shift) full' := by
  rcases hfull with ⟨source', hsource, hsourceEq⟩
  have hweak : TrExprS env Us H.expanded e
      (narrow'.lift' H.shift) := by
    simpa using hnarrow.weakFV' henv.ordered H.lift H.context.wf
  have hsourceEq' := hweak.uniq henv H.context hsource
  exact (hsourceEq'.defeqDFC henv.ordered H.context.defeqCtx).trans
    henv (H.context.symm henv.ordered).wf.toCtx hsourceEq

/-- Restrict a runtime expression translation whose target is already known
in the semantic scope.  This packages the inverse-weakening argument needed
after executable WHNF: restrict the normalized source translation, compare
both weakened targets in the runtime context, then cancel the weakening. -/
theorem NarrowRuntimeScope.restrictTrExpr
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope input narrowTarget)
    (hfullInput : TrExpr env Us runtime input fullTarget)
    (hfullResult : TrExpr env Us runtime result fullTarget)
    (hclosed : Closed result 0)
    (hfvars : FVarsIn (· ∈ scope.fvars) result) :
    TrExpr env Us scope result narrowTarget := by
  rcases hfullResult with ⟨resultFull, hresultFull, hresultTarget⟩
  rcases H.restrictEq henv hresultFull hclosed hfvars with
    ⟨resultNarrow, hresultNarrow, hresultLift⟩
  have htargetLift := H.fullTargetEq henv hnarrow hfullInput
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hlift : env.IsDefEqU Us.length runtime.toCtx
      (resultNarrow.lift' H.shift) (narrowTarget.lift' H.shift) :=
    (hresultLift.symm.trans henv hruntimeWF hresultTarget).trans
      henv hruntimeWF htargetLift.symm
  have hexpanded := hlift.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  have hnarrowEq : env.IsDefEqU Us.length scope.toCtx
      resultNarrow narrowTarget :=
    (VEnv.IsDefEqU.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
      hexpanded
  exact ⟨resultNarrow, hresultNarrow, hnarrowEq⟩

/-- Transfer a runtime typing result for a translated concrete expression
back to its independently translated target in the narrow scope. -/
theorem NarrowRuntimeScope.hasTypeOfFull
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExprS env Us runtime e full')
    (htype : env.HasType Us.length runtime.toCtx full' (.sort u)) :
    env.HasType Us.length scope.toCtx narrow' (.sort u) := by
  have htarget := H.fullTargetEq henv hnarrow
    (hfull.trExpr henv (H.context.symm henv.ordered).wf)
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hliftTyped := htype.defeqU_l henv hruntimeWF htarget.symm
  have hexpanded := hliftTyped.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  exact (VEnv.HasType.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
    hexpanded

/-- Move a successful runtime result-sort check back to the independent
narrow header scope.  Both translations are tied to the same concrete
residual, so uniqueness in the runtime context followed by inverse weakening
provides the narrow result equality. -/
theorem NarrowRuntimeScope.resultSort
    (H : NarrowRuntimeScope env Us scope runtime)
    (henv : env.WF)
    (hnarrow : TrExprS env Us scope e narrow')
    (hfull : TrExpr env Us runtime e full')
    (hsort : TrExpr env Us runtime (.sort level) full') :
    TrExpr env Us scope (.sort level) narrow' := by
  rcases hsort with ⟨sortFull, hsortFull, hsortTarget⟩
  have hclosed : Closed (.sort level) 0 := trivial
  have hfvars : FVarsIn (· ∈ scope.fvars) (.sort level) := by
    simpa [FVarsIn] using hsortFull.fvarsIn
  rcases H.restrictEq henv hsortFull hclosed hfvars with
    ⟨sortNarrow, hsortNarrow, hsortLift⟩
  have htarget := H.fullTargetEq henv hnarrow hfull
  have hruntimeWF := (H.context.symm henv.ordered).wf.toCtx
  have hlift : env.IsDefEqU Us.length runtime.toCtx
      (sortNarrow.lift' H.shift) (narrow'.lift' H.shift) :=
    hsortLift.symm.trans henv hruntimeWF <|
      hsortTarget.trans henv hruntimeWF htarget.symm
  have hexpanded := hlift.defeqDFC henv.ordered
    (H.context.defeqCtx.symm henv.ordered)
  have hnarrowEq : env.IsDefEqU Us.length scope.toCtx
      sortNarrow narrow' :=
    (VEnv.IsDefEqU.weak'_iff henv H.context.wf.toCtx H.lift.toCtx).1
      hexpanded
  exact ⟨sortNarrow, hsortNarrow, hnarrowEq⟩

/-- Extend the embedding by a generated index free variable.  The new
runtime domain need only be definitionally equal to the weakened semantic
domain. -/
def NarrowRuntimeScope.withIndex
    (H : NarrowRuntimeScope env Us scope runtime)
    (hnewRuntime : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam runtimeType) :: runtime))
    (hdeps : deps ⊆ scope.fvars)
    (hdomain : env.IsDefEq Us.length H.expanded.toCtx
      (indexType.lift' H.shift) runtimeType (.sort u)) :
    NarrowRuntimeScope env Us
      ((some (fv, deps), .vlam indexType) :: scope)
      ((some (fv, deps), .vlam runtimeType) :: runtime) where
  expanded :=
    (some (fv, deps), .vlam (indexType.lift' H.shift)) :: H.expanded
  shift := H.shift.consN 1
  lift := H.lift.cons_fvar (fv, deps) (.vlam indexType) hdeps
  context := .cons H.context (by
    have hfresh := hnewRuntime.2.1
    simpa [H.context.fvars] using hfresh) (.vlam hdomain)
  upset := by
    have hfresh := hnewRuntime.2.1
    refine ⟨?_, ?_⟩
    · apply (IsFVarUpSet.congr hnewRuntime.1.fvwf ?_).2 H.upset
      intro fv' hmem
      simp only [VLCtx.fvars_cons_some, List.mem_cons]
      constructor
      · intro h
        rcases h with rfl | h
        · exact False.elim (hfresh _ _ rfl |>.1 hmem)
        · exact h
      · exact Or.inr
    · intro _ dep hdep
      exact List.mem_cons_of_mem _ (hdeps hdep)
  noBV := by
    change scope.bvars = 0
    exact H.noBV
  noIndConsts := fun names =>
    checkPositivityStep.VLCtx.NoIndConsts.cons
      (H.noIndConsts names) rfl

/-- At the parameter/index boundary, discard the ambient prefix retained
from previously checked mutual headers and keep the exact cached-parameter
suffix as the semantic scope. -/
def NarrowRuntimeScope.ofParameterSuffix
    (Hc : ContextWF c)
    (Hsuffix : ParameterContextSuffix Hc stats depth) :
    NarrowRuntimeScope Hc.venv c.lparams Hsuffix.parameterDecls
      Hc.mlctx.vlctx := by
  have hambient : Hsuffix.ambientDecls.NoBV := by
    apply VLCtx.NoBV.leftOfAppend Hsuffix.ambientDecls
      Hsuffix.parameterDecls
    rw [← Hsuffix.context]
    exact Hc.mlctx.noBV
  let W := VLCtx.FVLift.to_append Hsuffix.parameterDecls hambient
  refine {
    expanded := Hc.mlctx.vlctx
    shift := .skipN .refl Hsuffix.ambientDecls.toCtx.length
    lift := ?_
    context := .refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
    upset := ?_
    noBV := ?_
    noIndConsts := Hsuffix.noIndConsts }
  · rw [Hsuffix.context]
    exact W.toFVLift'
  · have hwf : VLCtx.WF Hc.venv c.lparams.length
        (Hsuffix.ambientDecls ++ Hsuffix.parameterDecls) := by
      rw [← Hsuffix.context]
      exact Hc.mlctx_wf.tr.wf
    simpa [Hsuffix.context] using
      (IsFVarUpSet.suffixFVars Hsuffix.parameterDecls
        Hsuffix.ambientDecls hwf)
  · have hfull : (Hsuffix.ambientDecls ++
        Hsuffix.parameterDecls).NoBV := by
      rw [← Hsuffix.context]
      exact Hc.mlctx.noBV
    change Hsuffix.parameterDecls.bvars = 0
    change (Hsuffix.ambientDecls ++
      Hsuffix.parameterDecls).bvars = 0 at hfull
    rw [VLCtx.bvars_append] at hfull
    omega

/-- Relate a domain translated in the semantic scope to the annotation-
consumed domain installed by the executable checker. -/
theorem NarrowRuntimeScope.consumedDomain
    (Hc : ContextWF c)
    (H : NarrowRuntimeScope Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hdom : Hc.ConsumedDomain dom sourceDom consumedDom)
    (hnarrow : TrExprS Hc.venv c.lparams scope dom indexType) :
    ∃ u, Hc.venv.IsDefEq c.lparams.length H.expanded.toCtx
      (indexType.lift' H.shift) consumedDom (.sort u) := by
  have hweak : TrExprS Hc.venv c.lparams H.expanded dom
      (indexType.lift' H.shift) := by
    simpa using hnarrow.weakFV' Hc.checking.tr.wf.ordered H.lift
      H.context.wf
  have hsource := hweak.uniq Hc.checking.tr.wf H.context Hdom.source
  rcases Hdom.source_defeq with ⟨u, hsourceConsumed⟩
  have hsourceConsumed' := hsourceConsumed.defeqDFC
    Hc.checking.tr.wf.ordered
    (H.context.defeqCtx.symm Hc.checking.tr.wf.ordered)
  have hdomainU := hsource.trans Hc.checking.tr.wf H.context.wf.toCtx
    ⟨_, hsourceConsumed'⟩
  exact ⟨u, hdomainU.of_r Hc.checking.tr.wf H.context.wf.toCtx
    hsourceConsumed'.hasType.2⟩

/-- Shape of the CPS-retained runtime context after the first header has fixed
the block-wide parameter telescope.  Header indices form an ambient prefix;
the common parameters remain an exact suffix. -/
structure AmbientParamContext (Hc : ContextWF c) (params : List VExpr)
    (depth : Nat) where
  ambient : List VExpr
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (ambient ++ params.reverse) Hc.mlctx.vlctx.toCtx
  length : ambient.length = depth

/-- The exact cached-parameter suffix represents the common abstract
parameter telescope fixed by the first header.  The ambient prefixes may
differ definitionally, but have the same recorded depth and can be inverted
away from the context conversion. -/
theorem ParameterContextSuffix.paramsDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hambient : AmbientParamContext Hc params depth)
    (hparams : params.length = stats.params.size) :
    VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      params.reverse Hsuffix.parameterDecls.toCtx := by
  have hcontext : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (Hambient.ambient ++ params.reverse)
      (Hsuffix.ambientDecls.toCtx ++ Hsuffix.parameterDecls.toCtx) := by
    simpa [Hsuffix.context] using Hambient.context
  have hparameterCtx : Hsuffix.parameterDecls.toCtx.length =
      stats.params.size := by
    have hcachedLength : ∀ {ps : List Expr} {decls : VLCtx},
        List.Forall₂ CachedParameterDecl ps decls →
        decls.toCtx.length = ps.length := by
      intro ps decls hcached
      induction hcached with
      | nil => rfl
      | cons h _ ih =>
        rcases h with ⟨fv, deps, type, rfl, rfl⟩
        simp [VLCtx.toCtx, ih]
    simpa using hcachedLength Hsuffix.cached
  have hprefix : Hambient.ambient.length =
      Hsuffix.ambientDecls.toCtx.length := by
    have hlength := hcontext.length_eq
    simp only [List.length_append, List.length_reverse] at hlength
    omega
  exact VEnv.IsDefEqCtx.dropPrefixes hcontext hprefix

/-- Source-side account of the header telescope consumed by `loopType`.
`root` is the original normalized header and `current` is its unconsumed
suffix.  The context relation records that annotation erasure may change a
binder domain without changing the abstract telescope up to definitional
equality. -/
structure HeaderTelescopeCertificate (Hc : ContextWF c)
    (root current : VExpr) (params indices : List VExpr) where
  rebuild : root = VExpr.wrapForalls (params ++ indices) current
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx

theorem HeaderTelescopeCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c} {root : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx) :
    HeaderTelescopeCertificate Hc root root [] [] where
  rebuild := by simp [VExpr.wrapForalls]
  context := by simpa using hctx

/-- Consume a common-parameter binder.  This operation is restricted to the
parameter phase, before any index binder has been seen. -/
theorem HeaderTelescopeCertificate.withParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeCertificate Hc root (.forallE sourceDom body)
      params [])
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body (params ++ [sourceDom]) [] where
  rebuild := by
    simpa [VExpr.wrapForalls, VExpr.wrapForalls_append] using H.rebuild
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (sourceDom :: params.reverse)
      (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      exact .succ H.context
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (H.context.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_nil, List.nil_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx

/-- Consume an index binder after the common parameters. -/
theorem HeaderTelescopeCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeCertificate Hc root (.forallE sourceDom body)
      params indices)
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body params (indices ++ [sourceDom]) where
  rebuild := by
    simpa [VExpr.wrapForalls, VExpr.wrapForalls_append] using H.rebuild
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (sourceDom :: (indices.reverse ++ params.reverse))
      (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      exact .succ H.context
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (H.context.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.cons_append, List.nil_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx

theorem HeaderTelescopeCertificate.takeParameters
    (H : HeaderTelescopeCertificate Hc root current params indices)
    (hlen : params.length = nparams) :
    root.takeForalls nparams =
      some (params, VExpr.wrapForalls indices current) := by
  subst nparams
  rw [H.rebuild, VExpr.takeForalls_wrapForalls_append]

theorem HeaderTelescopeCertificate.takeIndices
    (_H : HeaderTelescopeCertificate Hc root current params indices)
    (hlen : indices.length = nindices) :
    (VExpr.wrapForalls indices current).takeForalls nindices =
      some (indices, current) := by
  subst nindices
  exact VExpr.takeForalls_wrapForalls indices current

/-- Type-valued state carried by the executable telescope loop.  It owns the
source parameter and index lists, and synchronizes their lengths with the two
counters maintained by `loopType`. -/
structure HeaderTelescopeLoopCertificate (Hc : ContextWF c)
    (root current : VExpr) (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  telescope : HeaderTelescopeCertificate Hc root current params indices
  parameterCount : params.length = i
  indexCount : indices.length = nindices

/-- Definitional, rather than syntactic, header-telescope accumulator.  Its
`header` field relates the independent source header to the telescope
synthesized from every binder exposed by the executable per-binder `whnf`.
This is the state used by the complete loop refinement. -/
structure HeaderSynthesisCertificate (Hc : ContextWF c)
    (target : VInductiveTypeSkeleton) (current : VExpr)
    (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  parameterCount : params.length = i
  indexCount : indices.length = nindices
  context : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
    (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx
  currentType : Hc.venv.IsType c.lparams.length
    (indices.reverse ++ params.reverse) current
  exprType : VExpr
  header : Hc.venv.IsDefEq c.lparams.length [] target.type
    (VExpr.wrapForalls (params ++ indices) current) exprType

def HeaderSynthesisCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c}
    {target : VInductiveTypeSkeleton} {current exprType : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx)
    (hcurrent : Hc.venv.IsType c.lparams.length [] current)
    (hheader : Hc.venv.IsDefEq c.lparams.length []
      target.type current exprType) :
    HeaderSynthesisCertificate Hc target current 0 0 where
  params := []
  indices := []
  parameterCount := rfl
  indexCount := rfl
  context := by simpa using hctx
  currentType := hcurrent
  exprType := exprType
  header := by simpa [VExpr.wrapForalls] using hheader

def HeaderSynthesisCertificate.withParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom body) i nindices)
    (hindices : H.indices = [])
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderSynthesisCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      target body (i + 1) nindices where
  params := H.params ++ [sourceDom]
  indices := []
  parameterCount := by simp [H.parameterCount]
  indexCount := by simpa [hindices] using H.indexCount
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        (sourceDom :: H.params.reverse)
        (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      have hOld : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
          H.params.reverse Hc.mlctx.vlctx.toCtx := by
        simpa [hindices] using H.context
      exact .succ hOld
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (hOld.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_nil, List.nil_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx
  currentType := by
    have htype := H.currentType.forallE_inv Hc.checking.tr.wf.ordered |>.2
    simpa [hindices, ContextWF.withLocalDecl_venv] using htype
  exprType := H.exprType
  header := by
    simpa [hindices, VExpr.wrapForalls, VExpr.wrapForalls_append,
      ContextWF.withLocalDecl_venv]
      using H.header

def HeaderSynthesisCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom body) i nindices)
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderSynthesisCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      target body i (nindices + 1) where
  params := H.params
  indices := H.indices ++ [sourceDom]
  parameterCount := H.parameterCount
  indexCount := by simp [H.indexCount]
  context := by
    have hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
        (sourceDom :: (H.indices.reverse ++ H.params.reverse))
        (consumedDom :: Hc.mlctx.vlctx.toCtx) := by
      rcases hdom.source_defeq with ⟨_, hsource⟩
      exact .succ H.context
        (hsource.defeqDFC Hc.checking.tr.wf.ordered
          (H.context.symm Hc.checking.tr.wf.ordered))
    simpa only [List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.cons_append, List.nil_append,
      ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hctx
  currentType := by
    have htype := H.currentType.forallE_inv Hc.checking.tr.wf.ordered |>.2
    simpa [List.reverse_append, ContextWF.withLocalDecl_venv] using htype
  exprType := H.exprType
  header := by
    simpa [VExpr.wrapForalls, VExpr.wrapForalls_append,
      ContextWF.withLocalDecl_venv] using H.header

/-- Replace the residual telescope by a definitionally equal normal form and
close that equality over every already discovered binder. -/
noncomputable def HeaderSynthesisCertificate.normalize
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderSynthesisCertificate Hc target current i nindices)
    (heq : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx current next) :
    HeaderSynthesisCertificate Hc target next i nindices := by
  have heq' := heq.defeqDFC Hc.checking.tr.wf.ordered
    (H.context.symm Hc.checking.tr.wf.ordered)
  let currentLevel := Classical.choose H.currentType
  have hcurrent := Classical.choose_spec H.currentType
  have heqTyped := heq'.of_l Hc.checking.tr.wf H.context.isType hcurrent
  have heqTyped' : Hc.venv.IsDefEq c.lparams.length
      ((H.params ++ H.indices).reverse ++ []) current next
      (.sort currentLevel) := by
    simpa [List.reverse_append] using heqTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
      (domains := H.params ++ H.indices) (Γ := [])
      (by simpa [List.reverse_append] using H.context.isType)
      heqTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params
    indices := H.indices
    parameterCount := H.parameterCount
    indexCount := H.indexCount
    context := H.context
    currentType := H.currentType.defeqU_l Hc.checking.tr.wf
      H.context.isType heq'
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r Hc.checking.tr.wf (by trivial)
      (by simpa using hwrapped) }

/-- Definitional header synthesis in a context narrower than the executable
reader context.  Later mutual headers retain indices introduced while
checking earlier family members; those declarations must not become part of
the later header's semantic telescope. -/
structure NarrowHeaderSynthesisCertificate
    (env : VEnv) (Us : List Name) (target : VInductiveTypeSkeleton)
    (scope : VLCtx) (current : VExpr) (i nindices : Nat) : Type where
  params : List VExpr
  indices : List VExpr
  parameterCount : params.length = i
  indexCount : indices.length = nindices
  scopeCtx : scope.toCtx = indices.reverse ++ params.reverse
  scopeWF : scope.WF env Us.length
  currentType : env.IsType Us.length scope.toCtx current
  exprType : VExpr
  header : env.IsDefEq Us.length [] target.type
    (VExpr.wrapForalls (params ++ indices) current) exprType

def NarrowHeaderSynthesisCertificate.empty
    {exprType : VExpr}
    (_htarget : env.IsType Us.length [] target.type)
    (hcurrent : env.IsType Us.length [] current)
    (hheader : env.IsDefEq Us.length [] target.type current exprType) :
    NarrowHeaderSynthesisCertificate env Us target [] current 0 0 where
  params := []
  indices := []
  parameterCount := rfl
  indexCount := rfl
  scopeCtx := rfl
  scopeWF := by trivial
  currentType := hcurrent
  exprType := exprType
  header := by simpa [VExpr.wrapForalls] using hheader

/-- Replace the current residual by a definitionally equal forall over the
next cached common-parameter type, then move that binder into the narrow
scope. -/
noncomputable def NarrowHeaderSynthesisCertificate.withParameter
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope
      (.forallE sourceDom sourceBody) i 0)
    (hindices : H.indices = [])
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hstep : env.IsDefEqU Us.length scope.toCtx
      (.forallE sourceDom sourceBody) (.forallE paramType next)) :
    NarrowHeaderSynthesisCertificate env Us target
      ((some (fv, deps), .vlam paramType) :: scope) next (i + 1) 0 := by
  have hforallType : env.IsType Us.length scope.toCtx
      (.forallE paramType next) :=
    H.currentType.defeqU_l henv H.scopeWF.toCtx hstep
  have hnextType := hforallType.forallE_inv henv.ordered |>.2
  have hstepTyped := hstep.of_l henv H.scopeWF.toCtx
    (Classical.choose_spec H.currentType)
  have hparamsCtx : OnCtx H.params.reverse (env.IsType Us.length) := by
    simpa [hindices, H.scopeCtx] using H.scopeWF.toCtx
  have hstepTyped' : env.IsDefEq Us.length (H.params.reverse ++ [])
      (.forallE sourceDom sourceBody) (.forallE paramType next)
      (.sort (Classical.choose H.currentType)) := by
    simpa [hindices, H.scopeCtx] using hstepTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
    (domains := H.params) (Γ := []) (by simpa using hparamsCtx)
      hstepTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params ++ [paramType]
    indices := []
    parameterCount := by simp [H.parameterCount]
    indexCount := rfl
    scopeCtx := by simp [VLCtx.toCtx, H.scopeCtx, hindices]
    scopeWF := hscopeWF
    currentType := hnextType
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r henv (by trivial) <| by
      simpa [hindices, VExpr.wrapForalls, VExpr.wrapForalls_append]
        using hwrapped }

/-- Move a definitionally equal residual forall into the narrow index
telescope. -/
noncomputable def NarrowHeaderSynthesisCertificate.withIndex
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope
      (.forallE sourceDom sourceBody) i nindices)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam indexType) :: scope))
    (hstep : env.IsDefEqU Us.length scope.toCtx
      (.forallE sourceDom sourceBody) (.forallE indexType next)) :
    NarrowHeaderSynthesisCertificate env Us target
      ((some (fv, deps), .vlam indexType) :: scope)
      next i (nindices + 1) := by
  have hforallType : env.IsType Us.length scope.toCtx
      (.forallE indexType next) :=
    H.currentType.defeqU_l henv H.scopeWF.toCtx hstep
  have hnextType := hforallType.forallE_inv henv.ordered |>.2
  have hstepTyped := hstep.of_l henv H.scopeWF.toCtx
    (Classical.choose_spec H.currentType)
  have hdomainsCtx : OnCtx (H.params ++ H.indices).reverse
      (env.IsType Us.length) := by
    simpa [List.reverse_append, ← H.scopeCtx] using H.scopeWF.toCtx
  have hstepTyped' : env.IsDefEq Us.length
      ((H.params ++ H.indices).reverse ++ [])
      (.forallE sourceDom sourceBody) (.forallE indexType next)
      (.sort (Classical.choose H.currentType)) := by
    simpa [List.reverse_append, H.scopeCtx] using hstepTyped
  have hwrappedExists := VExpr.wrapForalls_defeq
    (domains := H.params ++ H.indices) (Γ := [])
      (by simpa using hdomainsCtx) hstepTyped'
  have hwrapped := Classical.choose_spec hwrappedExists
  exact {
    params := H.params
    indices := H.indices ++ [indexType]
    parameterCount := H.parameterCount
    indexCount := by simp [H.indexCount]
    scopeCtx := by
      simp [VLCtx.toCtx, H.scopeCtx, List.reverse_append]
    scopeWF := hscopeWF
    currentType := hnextType
    exprType := .sort (Classical.choose hwrappedExists)
    header := H.header.trans_r henv (by trivial) <| by
      simpa [VExpr.wrapForalls, VExpr.wrapForalls_append,
        List.append_assoc] using hwrapped }

/-- Build the semantic parameter transition from the narrowed syntax
translation and the executable comparison/normalization witnesses. -/
theorem NarrowHeaderSynthesisCertificate.consumeParameter
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope current i 0)
    (hindices : H.indices = [])
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hdomain : ∃ sourceDom',
      TrExprS env Us scope dom sourceDom' ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom' paramType)
    (htransition : ∃ sourceBody' normalized',
      TrExprS env Us ((none, .vlam paramType) :: scope)
        body sourceBody' ∧
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        normalized normalized' ∧
      env.IsDefEqU Us.length (paramType :: scope.toCtx)
        sourceBody' normalized') :
    ∃ normalized',
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        normalized normalized' ∧
      Nonempty (NarrowHeaderSynthesisCertificate env Us target
        ((some (fv, deps), .vlam paramType) :: scope)
        normalized' (i + 1) 0) := by
  cases htype with
  | forallE hdomType hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom', hsourceDom, hsourceDomEq⟩
    rcases htransition with
      ⟨sourceBody', normalized', hsourceBody, hnormalized,
        hsourceBodyEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx
        _ paramType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam paramType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    have hsourceBodyEq' := hsourceBodyEq.defeqDFC henv.ordered
      (hbodyCtx.symm henv.ordered).defeqCtx
    have hbodyOldCtx := hbodyCtx.wf.toCtx
    have hbodyEq : env.IsDefEqU Us.length (_ :: scope.toCtx)
        _ normalized' :=
      (hbody.uniq henv hbodyCtx hsourceBody).trans henv hbodyOldCtx
        hsourceBodyEq'
    have hbodyTyped := hbodyEq.of_l henv hbodyOldCtx
      (Classical.choose_spec hbodyType)
    have hstep : env.IsDefEqU Us.length scope.toCtx
        (.forallE _ _) (.forallE paramType normalized') :=
      ⟨_, .forallEDF hdomTyped hbodyTyped⟩
    exact ⟨normalized', hnormalized,
      ⟨H.withParameter henv hindices hscopeWF hstep⟩⟩

/-- Build the semantic index transition from the narrowed syntax
translation and the executable comparison/normalization witnesses. -/
theorem NarrowHeaderSynthesisCertificate.consumeIndex
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope current i
      nindices)
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam indexType) :: scope))
    (hdomain : ∃ sourceDom',
      TrExprS env Us scope dom sourceDom' ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom' indexType)
    (htransition : ∃ sourceBody' normalized',
      TrExprS env Us ((none, .vlam indexType) :: scope)
        body sourceBody' ∧
      TrExprS env Us ((some (fv, deps), .vlam indexType) :: scope)
        normalized normalized' ∧
      env.IsDefEqU Us.length (indexType :: scope.toCtx)
        sourceBody' normalized') :
    ∃ normalized',
      TrExprS env Us ((some (fv, deps), .vlam indexType) :: scope)
        normalized normalized' ∧
      ∃ H' : NarrowHeaderSynthesisCertificate env Us target
        ((some (fv, deps), .vlam indexType) :: scope)
        normalized' i (nindices + 1), H'.params = H.params := by
  cases htype with
  | forallE hdomType hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom', hsourceDom, hsourceDomEq⟩
    rcases htransition with
      ⟨sourceBody', normalized', hsourceBody, hnormalized,
        hsourceBodyEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx
        _ indexType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam indexType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    have hsourceBodyEq' := hsourceBodyEq.defeqDFC henv.ordered
      (hbodyCtx.symm henv.ordered).defeqCtx
    have hbodyOldCtx := hbodyCtx.wf.toCtx
    have hbodyEq : env.IsDefEqU Us.length (_ :: scope.toCtx)
        _ normalized' :=
      (hbody.uniq henv hbodyCtx hsourceBody).trans henv hbodyOldCtx
        hsourceBodyEq'
    have hbodyTyped := hbodyEq.of_l henv hbodyOldCtx
      (Classical.choose_spec hbodyType)
    have hstep : env.IsDefEqU Us.length scope.toCtx
        (.forallE _ _) (.forallE indexType normalized') :=
      ⟨_, .forallEDF hdomTyped hbodyTyped⟩
    exact ⟨normalized', hnormalized,
      H.withIndex henv hscopeWF hstep, rfl⟩

theorem NarrowHeaderSynthesisCertificate.typeShape
    {decl : VInductDecl} {target : VInductiveType}
    (H : NarrowHeaderSynthesisCertificate env Us target.toSkeleton
      scope current decl.nparams target.numIndices)
    (henv : env.WF)
    (huvars : Us.length = decl.uvars)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    decl.TypeShape env H.params target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  have hctxType : OnCtx (H.indices.reverse ++ H.params.reverse)
      (env.IsType decl.uvars) := by
    simpa [huvars, ← H.scopeCtx] using H.scopeWF.toCtx
  apply TrExpr.typeShape (decl := decl) (target := target)
    (params := H.params) (ownParams := H.params) (indices := H.indices)
    (normalized := VExpr.wrapForalls (H.params ++ H.indices) current)
    (afterParams := VExpr.wrapForalls H.indices current)
    (result := current) (exprType := H.exprType)
    henv H.scopeWF huvars H.scopeCtx
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hlevel hsort

theorem NarrowHeaderSynthesisCertificate.typeShapeWithParams
    {decl : VInductDecl} {target : VInductiveType}
    {commonParams : List VExpr}
    (H : NarrowHeaderSynthesisCertificate env Us target.toSkeleton
      scope current decl.nparams target.numIndices)
    (henv : env.WF)
    (huvars : Us.length = decl.uvars)
    (hparams : decl.ParamsDefEq env commonParams H.params)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel Us level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    decl.TypeShape env commonParams target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  apply TrExpr.typeShape (decl := decl) (target := target)
    (params := commonParams) (ownParams := H.params)
    (indices := H.indices)
    (normalized := VExpr.wrapForalls (H.params ++ H.indices) current)
    (afterParams := VExpr.wrapForalls H.indices current)
    (result := current) (exprType := H.exprType)
    henv H.scopeWF huvars H.scopeCtx
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake hparams hlevel hsort

theorem HeaderSynthesisCertificate.typeShapeWithParams
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    {params : List VExpr}
    (H : HeaderSynthesisCertificate Hc target.toSkeleton current
      decl.nparams target.numIndices)
    (huvars : c.lparams.length = decl.uvars)
    (hparams : decl.ParamsDefEq Hc.venv params H.params)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel c.lparams level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv params target := by
  have hparamsTake :
      (VExpr.wrapForalls (H.params ++ H.indices) current).takeForalls
        decl.nparams =
      some (H.params, VExpr.wrapForalls H.indices current) := by
    simpa only [H.parameterCount] using
      VExpr.takeForalls_wrapForalls_append H.params H.indices current
  have hindicesTake :
      (VExpr.wrapForalls H.indices current).takeForalls target.numIndices =
      some (H.indices, current) := by
    simpa only [H.indexCount] using
      VExpr.takeForalls_wrapForalls H.indices current
  apply TrExpr.typeShapeOfDefEqCtx Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
    huvars H.context
    (by simpa [huvars, VInductiveType.toSkeleton] using H.header)
    hparamsTake hindicesTake
    hparams hlevel hsort

theorem HeaderSynthesisCertificate.typeShape
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    (H : HeaderSynthesisCertificate Hc target.toSkeleton current
      decl.nparams target.numIndices)
    (huvars : c.lparams.length = decl.uvars)
    (hlevel : ∀ resultLevel,
      VLevel.ofLevel c.lparams level = some resultLevel →
      resultLevel = target.resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv H.params target := by
  have hctxType : OnCtx (H.indices.reverse ++ H.params.reverse)
      (Hc.venv.IsType decl.uvars) := by
    simpa [huvars] using H.context.isType
  exact H.typeShapeWithParams huvars
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hlevel hsort

/-- Materialize the two semantic header fields from the successful executable
tail.  Unlike `typeShape`, this theorem does not require either field to have
been chosen before the traversal: the index counter and translated sort are
used to construct the target itself. -/
theorem HeaderSynthesisCertificate.synthesizedTypeShape
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveTypeSkeleton}
    (H : HeaderSynthesisCertificate Hc target current
      decl.nparams nindices)
    (huvars : c.lparams.length = decl.uvars)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    decl.TypeShape Hc.venv H.params
      (target.toVInductiveType nindices resultLevel) := by
  apply H.typeShape (target := target.toVInductiveType nindices resultLevel)
    huvars
  · intro resultLevel' hofLevel'
    rw [hofLevel] at hofLevel'
    cases hofLevel'
    rfl
  · exact hsort

/-- Persistent result of checking one metadata-free source header.  The final
mutual declaration need not exist yet; only its two block-wide counters are
relevant to `TypeShape`.  This lets the outer traversal accumulate checked
headers and materialize the declaration after every family member has
supplied its metadata. -/
structure SynthesizedHeader (env : VEnv) (uvars nparams : Nat)
    (params : List VExpr) (source : VInductiveTypeSkeleton)
    (numIndices : Nat) (resultLevel : VLevel) : Prop where
  parameterCount : params.length = nparams
  typeShape : ∀ decl : VInductDecl,
    decl.uvars = uvars → decl.nparams = nparams →
    decl.TypeShape env params
      (source.toVInductiveType numIndices resultLevel)

theorem NarrowHeaderSynthesisCertificate.synthesizedHeaderWithParams
    {source : VInductiveTypeSkeleton} {commonParams : List VExpr}
    (H : NarrowHeaderSynthesisCertificate env Us source scope current
      nparams nindices)
    (henv : env.WF)
    (huvars : Us.length = uvars)
    (hparams : VEnv.IsDefEqCtx env uvars []
      commonParams.reverse H.params.reverse)
    (hofLevel : VLevel.ofLevel Us level = some resultLevel)
    (hsort : TrExpr env Us scope (.sort level) current) :
    SynthesizedHeader env uvars nparams commonParams source
      nindices resultLevel where
  parameterCount := by
    simpa [H.parameterCount] using hparams.length_eq
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : Us.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    have hparams' : decl.ParamsDefEq env commonParams H.params := by
      simpa [VInductDecl.ParamsDefEq, hdeclUvars] using hparams
    subst nparams
    apply H.typeShapeWithParams
      (target := source.toVInductiveType nindices resultLevel)
      henv huvars' hparams'
    · intro resultLevel' hofLevel'
      rw [hofLevel] at hofLevel'
      cases hofLevel'
      rfl
    · exact hsort

theorem HeaderSynthesisCertificate.synthesizedHeader
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : VInductiveTypeSkeleton}
    (H : HeaderSynthesisCertificate Hc source current nparams nindices)
    (huvars : c.lparams.length = uvars)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    SynthesizedHeader Hc.venv uvars nparams H.params source
      nindices resultLevel where
  parameterCount := H.parameterCount
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : c.lparams.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    subst nparams
    apply H.synthesizedTypeShape (decl := decl)
    · exact huvars'
    · exact hofLevel
    · exact hsort

/-- Later mutual headers use the first header's parameter telescope.  Their
own synthesized domains are connected to it by the successful executable
`isDefEq` checks, represented here independently of the not-yet-materialized
declaration. -/
theorem HeaderSynthesisCertificate.synthesizedHeaderWithParams
    {c : AddInductive.Context} {Hc : ContextWF c}
    {source : VInductiveTypeSkeleton} {commonParams : List VExpr}
    (H : HeaderSynthesisCertificate Hc source current nparams nindices)
    (huvars : c.lparams.length = uvars)
    (hparams : VEnv.IsDefEqCtx Hc.venv uvars []
      commonParams.reverse H.params.reverse)
    (hofLevel : VLevel.ofLevel c.lparams level = some resultLevel)
    (hsort : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      (.sort level) current) :
    SynthesizedHeader Hc.venv uvars nparams commonParams source
      nindices resultLevel where
  parameterCount := by
    simpa [H.parameterCount] using hparams.length_eq
  typeShape decl hdeclUvars hdeclParams := by
    have huvars' : c.lparams.length = decl.uvars :=
      huvars.trans hdeclUvars.symm
    have hparams' : decl.ParamsDefEq Hc.venv commonParams H.params := by
      simpa [VInductDecl.ParamsDefEq, hdeclUvars] using hparams
    subst nparams
    apply H.typeShapeWithParams
      (target := source.toVInductiveType nindices resultLevel)
      huvars' hparams'
    · intro resultLevel' hofLevel'
      rw [hofLevel] at hofLevel'
      cases hofLevel'
      rfl
    · exact hsort

structure SynthesizedHeaderMetadata (env : VEnv) (uvars nparams : Nat)
    (params : List VExpr) (commonLevel : VLevel)
    (source : VInductiveTypeSkeleton) (data : Nat × VLevel) : Prop where
  header : SynthesizedHeader env uvars nparams params source data.1 data.2
  commonLevel : data.2 ≈ commonLevel

/-- Prefix of the metadata list built by the outer mutual-header traversal.
`Forall₂` fixes both ordering and cardinality, so later materialization cannot
associate a checked arity or universe with the wrong family member. -/
structure SynthesizedHeaderPrefix (env : VEnv)
    (skeleton : VInductDeclSkeleton) (params : List VExpr)
    (commonLevel : VLevel) (metadata : List (Nat × VLevel))
    (done : Nat) : Prop where
  parameterCount : params.length = skeleton.nparams
  covered : done ≤ skeleton.types.length
  checked : List.Forall₂
    (SynthesizedHeaderMetadata env skeleton.uvars skeleton.nparams
      params commonLevel)
    (skeleton.types.take done) metadata

theorem SynthesizedHeaderPrefix.first
    (hindex : 0 < skeleton.types.length)
    (Hheader : SynthesizedHeader env skeleton.uvars skeleton.nparams
      params skeleton.types[0] nindices resultLevel) :
    SynthesizedHeaderPrefix env skeleton params resultLevel
      [(nindices, resultLevel)] 1 where
  parameterCount := Hheader.parameterCount
  covered := by omega
  checked := by
    rw [List.take_succ_eq_append_getElem hindex]
    simp only [List.take_zero, List.nil_append]
    exact .cons ⟨Hheader, by rfl⟩ .nil

theorem SynthesizedHeaderPrefix.push
    (H : SynthesizedHeaderPrefix env skeleton params commonLevel
      metadata done)
    (hindex : done < skeleton.types.length)
    (Hheader : SynthesizedHeader env skeleton.uvars skeleton.nparams
      params skeleton.types[done] nindices resultLevel)
    (hlevel : resultLevel ≈ commonLevel) :
    SynthesizedHeaderPrefix env skeleton params commonLevel
      (metadata ++ [(nindices, resultLevel)]) (done + 1) where
  parameterCount := H.parameterCount
  covered := by omega
  checked := by
    rw [List.take_succ_eq_append_getElem hindex]
    exact Lean4Lean.VerifyInductive.List.Forall₂.append' H.checked
      (.cons ⟨Hheader, hlevel⟩ .nil)

/-- Once every header has been visited, exact materialization turns the
metadata-prefix invariant into the public formation header certificate. -/
def SynthesizedHeaderPrefix.complete
    (H : SynthesizedHeaderPrefix env skeleton params commonLevel metadata
      skeleton.types.length)
    (Hmaterialize : skeleton.materialize metadata = some decl) :
    HeaderCertificate env decl := by
  have hfields := VInductDeclSkeleton.materialize_fields Hmaterialize
  have hcheckedLength :
      (skeleton.types.take skeleton.types.length).length = metadata.length :=
    Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.checked
  have hmetadata : metadata.length = skeleton.types.length := by
    simpa using hcheckedLength.symm
  have checkedAt : ∀ i (hi : i < skeleton.types.length),
      SynthesizedHeaderMetadata env skeleton.uvars skeleton.nparams
        params commonLevel skeleton.types[i] metadata[i] := by
    intro i hi
    simpa using Lean4Lean.VerifyInductive.List.Forall₂.getElem H.checked i
      (by simpa using hi) (by simpa [hmetadata] using hi)
  have materializedAt : ∀ i (hi : i < skeleton.types.length),
      decl.types[i]'(by omega) =
        skeleton.types[i].toVInductiveType metadata[i].1 metadata[i].2 := by
    intro i hi
    rcases VInductDeclSkeleton.materialize_typeAt Hmaterialize hi with
      ⟨data, hdata, htarget⟩
    have hmetadataGet : metadata[i]? = some metadata[i] := by
      simp [hmetadata, hi]
    have hdataEq : data = metadata[i] := by
      rw [hmetadataGet] at hdata
      cases hdata
      rfl
    subst data
    rw [List.getElem?_eq_getElem (by omega)] at htarget
    exact Option.some.inj htarget
  refine {
    params := params
    resultLevel := commonLevel
    commonLevels := ?_
    typeShapes := ?_ }
  · intro type htype
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    have hskeleton : i < skeleton.types.length := by omega
    rw [materializedAt i hskeleton]
    exact (checkedAt i hskeleton).commonLevel
  · intro type htype
    rcases List.mem_iff_getElem.1 htype with ⟨i, hi, rfl⟩
    have hskeleton : i < skeleton.types.length := by omega
    rw [materializedAt i hskeleton]
    exact (checkedAt i hskeleton).header.typeShape decl
      hfields.1 hfields.2.1

/-- Exact coverage makes skeleton materialization total and packages the
resulting formation-header certificate. -/
theorem SynthesizedHeaderPrefix.materializes
    (H : SynthesizedHeaderPrefix env skeleton params commonLevel metadata
      skeleton.types.length) :
    ∃ decl, skeleton.materialize metadata = some decl ∧
      Nonempty (HeaderCertificate env decl) := by
  have hmetadata : metadata.length = skeleton.types.length := by
    have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
      H.checked
    simpa using hlength.symm
  cases hmaterialize : skeleton.materialize metadata with
  | none => simp [VInductDeclSkeleton.materialize, hmetadata] at hmaterialize
  | some decl => exact ⟨decl, rfl, ⟨H.complete hmaterialize⟩⟩

def HeaderTelescopeLoopCertificate.empty
    {c : AddInductive.Context} {Hc : ContextWF c} {root : VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx) :
    HeaderTelescopeLoopCertificate Hc root root 0 0 where
  params := []
  indices := []
  telescope := .empty hctx
  parameterCount := rfl
  indexCount := rfl

def HeaderTelescopeLoopCertificate.withParameter
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom body) i nindices)
    (hindices : H.indices = [])
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeLoopCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body (i + 1) nindices where
  params := H.params ++ [sourceDom]
  indices := []
  telescope := by
    have Htel := H.telescope
    rw [hindices] at Htel
    exact Htel.withParameter hdom
  parameterCount := by simp [H.parameterCount]
  indexCount := by simpa [hindices] using H.indexCount

def HeaderTelescopeLoopCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom body) i nindices)
    (hdom : Hc.ConsumedDomain dom sourceDom consumedDom) :
    HeaderTelescopeLoopCertificate
      (Hc.withLocalDecl (name := name) (bi := bi)
        hdom.consumed hdom.isType)
      root body i (nindices + 1) where
  params := H.params
  indices := H.indices ++ [sourceDom]
  telescope := H.telescope.withIndex hdom
  parameterCount := H.parameterCount
  indexCount := by simp [H.indexCount]

theorem HeaderTelescopeLoopCertificate.takeParameters
    (H : HeaderTelescopeLoopCertificate Hc root current i nindices) :
    root.takeForalls i =
      some (H.params, VExpr.wrapForalls H.indices current) :=
  H.telescope.takeParameters H.parameterCount

theorem HeaderTelescopeLoopCertificate.takeIndices
    (H : HeaderTelescopeLoopCertificate Hc root current i nindices) :
    (VExpr.wrapForalls H.indices current).takeForalls nindices =
      some (H.indices, current) :=
  H.telescope.takeIndices H.indexCount

def AmbientParamContext.ofFirst
    {c : AddInductive.Context} {Hc : ContextWF c}
    {indices params : List VExpr}
    (hctx : Hc.mlctx.vlctx.toCtx = indices.reverse ++ params.reverse) :
    AmbientParamContext Hc params indices.length where
  ambient := indices.reverse
  context := by
    have hwf : OnCtx (indices.reverse ++ params.reverse)
        (Hc.venv.IsType c.lparams.length) := hctx ▸ Hc.mlctx_wf.tr.wf.toCtx
    simpa [hctx] using VEnv.IsDefEqCtx.refl hwf
  length := by simp

def AmbientParamContext.ofFirstDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {indices params : List VExpr}
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx) :
    AmbientParamContext Hc params indices.length where
  ambient := indices.reverse
  context := hctx
  length := by simp

def AmbientParamContext.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : AmbientParamContext Hc params depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (hsource : ∃ u, Hc.venv.IsDefEq c.lparams.length
      Hc.mlctx.vlctx.toCtx sourceTy ty' (.sort u)) :
    AmbientParamContext
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      params (depth + 1) where
  ambient := sourceTy :: H.ambient
  context := by
    rcases hsource with ⟨u, hsource⟩
    change VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (sourceTy :: (H.ambient ++ params.reverse))
      (ty' :: Hc.mlctx.vlctx.toCtx)
    exact .succ H.context
      (hsource.defeqDFC Hc.checking.tr.wf.ordered
        (H.context.symm Hc.checking.tr.wf.ordered))
  length := by simp [H.length]

theorem ParameterCachePrefix.empty
    (hparams : stats.params = #[]) :
    ParameterCachePrefix env Us Δ stats 0 depth := by
  refine ⟨?_, ?_⟩
  · simpa [hparams]
  · simp [hparams]

def ParameterContextSuffix.empty
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (hparams : stats.params = #[]) :
    ParameterContextSuffix Hc stats 0 where
  ambientDecls := []
  parameterDecls := []
  context := by simpa using hctx
  prefixLength := rfl
  cached := by simp [hparams]
  narrowParams := by simp [hparams, cachedParamVars]

/-- The first-header parameter branch extends the cached suffix itself.  The
empty-prefix premise records that parameters are all introduced before any
index binder. -/
def ParameterContextSuffix.push
    (Hc : ContextWF c)
    (H : ParameterContextSuffix Hc stats 0)
    (hprefix : H.ambientDecls = [])
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterContextSuffix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
      0 := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  refine {
    ambientDecls := []
    parameterDecls := entry :: H.parameterDecls
    context := ?_
    prefixLength := rfl
    cached := ?_
    narrowParams := ?_ }
  · have hcontext := H.context
    rw [hprefix] at hcontext
    change entry :: Hc.mlctx.vlctx = [] ++ entry :: H.parameterDecls
    simp only [List.nil_append]
    simpa using congrArg (entry :: ·) hcontext
  · simp only [Array.toList_push, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    exact .cons ⟨⟨c.ngen.curr⟩, ty.fvarsList, ty', rfl, rfl⟩
      H.cached
  · let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
    let W : VLCtx.FVLift H.parameterDecls
        (entry :: H.parameterDecls) 0 1 0 :=
      .skip_fvar _ _ .refl
    have hscope : Hc.mlctx.vlctx = H.parameterDecls := by
      simpa [hprefix] using H.context
    have hnarrowWF : VLCtx.WF Hc'.venv c.lparams.length
        (entry :: H.parameterDecls) := by
      change VLCtx.WF Hc.venv c.lparams.length
        (entry :: H.parameterDecls)
      refine ⟨?_, ?_, ?_⟩
      · simpa [hscope] using Hc.mlctx_wf.tr.wf
      · intro fv deps heq
        simp only [entry, Option.some.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact ⟨by simpa [hscope] using Hc.current_not_mem,
          by simpa [hscope] using htr.fvarsList⟩
      · change Hc.venv.IsType c.lparams.length
          H.parameterDecls.toCtx ty'
        simpa [hscope] using hty
    have hold : List.Forall₂
        (TrExprS Hc'.venv c.lparams (entry :: H.parameterDecls))
        stats.params.toList
        ((cachedParamVars stats.params.size 0).map
          fun e => e.liftN 1 0) := by
      have weakAll : ∀ {as bs},
          List.Forall₂
              (TrExprS Hc.venv c.lparams H.parameterDecls) as bs →
            List.Forall₂
              (TrExprS Hc'.venv c.lparams (entry :: H.parameterDecls))
              as (bs.map fun e => e.liftN 1 0) := by
        intro as bs hp
        induction hp with
        | nil => exact .nil
        | cons h _ ih =>
          exact .cons
            (h.weakFV Hc.checking.tr.wf.ordered W hnarrowWF) ih
      exact weakAll H.narrowParams
    have hnew : TrExprS Hc'.venv c.lparams
        (entry :: H.parameterDecls)
        (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
      apply TrExprS.fvar (A := ty'.lift)
      simp [entry, VLCtx.find?, VLCtx.next, VLocalDecl.value,
        VLocalDecl.type]
    simpa [Array.toList_push, cachedParamVars_succ] using
      Lean4Lean.VerifyInductive.List.Forall₂.append' hold
        (.cons hnew .nil)

/-- Index binders extend only the ambient prefix and preserve the exact
cached-parameter suffix. -/
def ParameterContextSuffix.withIndex
    (Hc : ContextWF c)
    (H : ParameterContextSuffix Hc stats depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterContextSuffix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      stats (depth + 1) := by
  let entry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty')
  refine {
    ambientDecls := entry :: H.ambientDecls
    parameterDecls := H.parameterDecls
    context := ?_
    prefixLength := by simp [H.prefixLength]
    cached := H.cached
    narrowParams := H.narrowParams }
  change entry :: Hc.mlctx.vlctx =
    (entry :: H.ambientDecls) ++ H.parameterDecls
  simp only [List.cons_append]
  rw [H.context]

theorem ParameterContextSuffix.parameterDecls_length
    (H : ParameterContextSuffix Hc stats depth) :
    H.parameterDecls.length = stats.params.size := by
  have hlength := Lean4Lean.VerifyInductive.List.Forall₂.length_eq'
    H.cached
  simpa using hlength.symm

/-- Locate executable parameter `i` in the reverse-ordered local-context
suffix. -/
theorem ParameterContextSuffix.parameterAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size)
    (hj : stats.params.size - 1 - i < H.parameterDecls.length) :
    CachedParameterDecl stats.params[i]
      H.parameterDecls[stats.params.size - 1 - i] := by
  let j := stats.params.size - 1 - i
  have hj' : j < stats.params.size := by
    dsimp [j]
    omega
  have hleft : j < stats.params.toList.reverse.length := by
    simpa using hj'
  have hright : j < H.parameterDecls.length := by
    exact hj
  have hcached := Lean4Lean.VerifyInductive.List.Forall₂.getElem
    H.cached j hleft hright
  simp only [List.getElem_reverse, Array.getElem_toList] at hcached
  change CachedParameterDecl stats.params[stats.params.size - 1 - j]
    H.parameterDecls[j] at hcached
  dsimp [j] at hcached ⊢
  have hindex : stats.params.size - 1 -
      (stats.params.size - 1 - i) = i := by omega
  have helem :
      stats.params[stats.params.size - 1 -
        (stats.params.size - 1 - i)] = stats.params[i] :=
    getElem_congr rfl hindex (by omega)
  rw [← helem]
  exact hcached

/-- Split the cached-parameter suffix at executable array index `i`.  Entries
in `newer` are precisely the cached declarations introduced after parameter
`i`; `older` contains those introduced before it. -/
theorem ParameterContextSuffix.splitAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size) :
    ∃ newer entry older,
      H.parameterDecls = newer ++ entry :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      CachedParameterDecl stats.params[i] entry := by
  let j := stats.params.size - 1 - i
  have hj : j < H.parameterDecls.length := by
    rw [H.parameterDecls_length]
    dsimp [j]
    omega
  refine ⟨H.parameterDecls.take j, H.parameterDecls[j],
    H.parameterDecls.drop (j + 1), ?_, ?_, ?_⟩
  · calc
      H.parameterDecls =
          H.parameterDecls.take j ++ H.parameterDecls.drop j :=
        (List.take_append_drop j H.parameterDecls).symm
      _ = H.parameterDecls.take j ++
          H.parameterDecls[j] :: H.parameterDecls.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]
  · simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj), j]
  · exact H.parameterAt hi hj

/-- Expose the exact `FVLift` that removes the ambient declarations and the
cached parameters newer than executable parameter `i`, leaving that
parameter as the head of the retained suffix. -/
theorem ParameterContextSuffix.fvLiftAt
    (H : ParameterContextSuffix Hc stats depth)
    (hi : i < stats.params.size) :
    ∃ added newer older fv deps paramType,
      H.parameterDecls =
        newer ++ (some (fv, deps), .vlam paramType) :: older ∧
      newer.length = stats.params.size - 1 - i ∧
      added = H.ambientDecls ++ newer ∧
      Hc.mlctx.vlctx =
        added ++ (some (fv, deps), .vlam paramType) :: older ∧
      stats.params[i] = .fvar fv ∧
      VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
        Hc.mlctx.vlctx
        0 (VLCtx.toCtx added).length 0 := by
  rcases H.splitAt hi with
    ⟨newer, entry, older, hdecls, hnewer, hcached⟩
  rcases hcached with ⟨fv, deps, paramType, hparam, rfl⟩
  let added := H.ambientDecls ++ newer
  have hcontext : Hc.mlctx.vlctx =
      added ++ (some (fv, deps), .vlam paramType) :: older := by
    rw [H.context, hdecls]
    simp only [added, List.append_assoc]
  have hfullNoBV :
      (added ++ (some (fv, deps), .vlam paramType) :: older).NoBV := by
    rw [← hcontext]
    exact Hc.mlctx.noBV
  have hadded : added.NoBV :=
    VLCtx.NoBV.leftOfAppend added
      ((some (fv, deps), .vlam paramType) :: older)
      hfullNoBV
  have hlift := VLCtx.FVLift.to_append
    ((some (fv, deps), .vlam paramType) :: older) hadded
  rw [← hcontext] at hlift
  exact ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, rfl,
    hcontext, hparam, hlift⟩

/-- Narrow concrete scope immediately before consuming cached parameter `i`.
Only parameters already consumed by this later header may occur; ambient
indices and the current-or-future cached parameters are excluded. -/
structure LaterParameterScope
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (i : Nat) (e : Expr) : Type where
  added : VLCtx
  newer : VLCtx
  older : VLCtx
  fv : FVarId
  deps : List FVarId
  paramType : VExpr
  parameterDecls : Hsuffix.parameterDecls =
    newer ++ (some (fv, deps), .vlam paramType) :: older
  newerLength : newer.length = stats.params.size - 1 - i
  addedEq : added = Hsuffix.ambientDecls ++ newer
  context : Hc.mlctx.vlctx =
    added ++ (some (fv, deps), .vlam paramType) :: older
  parameter : stats.params[i]! = .fvar fv
  lift : VLCtx.FVLift ((some (fv, deps), .vlam paramType) :: older)
    Hc.mlctx.vlctx 0 (VLCtx.toCtx added).length 0
  fvars : FVarsIn (· ∈ older.fvars) e

theorem LaterParameterScope.olderLength
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : LaterParameterScope Hsuffix i e)
    (hi : i < stats.params.size) :
    H.older.length = i := by
  have htotal := Hsuffix.parameterDecls_length
  have hparts := congrArg List.length H.parameterDecls
  simp only [List.length_append, List.length_cons] at hparts
  rw [htotal, H.newerLength] at hparts
  omega

theorem LaterParameterScope.older_eq_nil
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : LaterParameterScope Hsuffix 0 e)
    (hi : 0 < stats.params.size) : H.older = [] :=
  List.eq_nil_of_length_eq_zero (H.olderLength hi)

/-- After the final cached parameter is consumed, the accumulated narrow
scope is exactly the complete cached-parameter suffix. -/
theorem LaterParameterScope.completedScope
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth} {e : Expr}
    (H : LaterParameterScope Hsuffix i e)
    (hdone : i + 1 = stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hsuffix.parameterDecls := by
  have hnewerLength : H.newer.length = 0 := by
    rw [H.newerLength]
    omega
  have hnewer : H.newer = [] :=
    List.eq_nil_of_length_eq_zero hnewerLength
  rw [H.parameterDecls, hnewer]
  simp

/-- Consecutive cached-parameter scopes agree on the consumed suffix. -/
theorem LaterParameterScope.nextOlder
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {e next : Expr}
    (H : LaterParameterScope Hsuffix i e)
    (Hnext : LaterParameterScope Hsuffix (i + 1) next)
    (hi : i + 1 < stats.params.size) :
    (some (H.fv, H.deps), .vlam H.paramType) :: H.older =
      Hnext.older := by
  let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (Hnext.fv, Hnext.deps), .vlam Hnext.paramType)
  have hdecomp :
      H.newer ++ currentEntry :: H.older =
        (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
    calc
      H.newer ++ currentEntry :: H.older =
          Hsuffix.parameterDecls := H.parameterDecls.symm
      _ = Hnext.newer ++ nextEntry :: Hnext.older :=
        Hnext.parameterDecls
      _ = (Hnext.newer ++ [nextEntry]) ++ Hnext.older := by
        simp [List.append_assoc]
  have hprefixLength :
      H.newer.length = (Hnext.newer ++ [nextEntry]).length := by
    simp only [List.length_append, List.length_singleton]
    rw [H.newerLength, Hnext.newerLength]
    omega
  simpa only [currentEntry] using
    List.append_inj_right hdecomp hprefixLength

theorem LaterParameterScope.openedFVars
    (H : LaterParameterScope Hsuffix i body) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1' (.fvar H.fv)) := by
  apply (H.fvars.mono fun fv hfv => by
    rw [VLCtx.fvars_cons_some]
    exact List.mem_cons_of_mem H.fv hfv).instantiate1
  simp only [FVarsIn]
  rw [VLCtx.fvars_cons_some]
  exact List.mem_cons_self

theorem LaterParameterScope.openedUpSet
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : LaterParameterScope Hsuffix i body) :
    IsFVarUpSet
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      Hc.mlctx.vlctx := by
  rw [H.context]
  exact IsFVarUpSet.suffixFVars
    ((some (H.fv, H.deps), .vlam H.paramType) :: H.older) H.added
    (by simpa [H.context] using Hc.mlctx_wf.tr.wf)

/-- Substitution of the current cached parameter, followed by an executable
normalization step, cannot introduce dependencies outside the newly consumed
parameter scope. -/
theorem LaterParameterScope.consumedFVars
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr}
    (H : LaterParameterScope Hsuffix i body)
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized := by
  have hopened : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  exact hbelow _ H.openedUpSet hopened

/-- Forget the ambient prefix, the not-yet-consumed cached parameters, and
the current cached parameter.  A source domain at this point may depend only
on the already consumed parameters in `older`. -/
theorem LaterParameterScope.olderLift
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : LaterParameterScope Hsuffix i body) :
    VLCtx.FVLift H.older Hc.mlctx.vlctx 0
      (VLCtx.toCtx H.added).length.succ 0 := by
  let current : Option (FVarId × List FVarId) × VLocalDecl :=
    (some (H.fv, H.deps), .vlam H.paramType)
  have hcontext : Hc.mlctx.vlctx =
      (H.added ++ [current]) ++ H.older := by
    simpa only [current, List.append_assoc, List.singleton_append]
      using H.context
  have hfullNoBV : ((H.added ++ [current]) ++ H.older).NoBV := by
    rw [← hcontext]
    exact Hc.mlctx.noBV
  have hprefixNoBV : (H.added ++ [current]).NoBV :=
    VLCtx.NoBV.leftOfAppend (H.added ++ [current]) H.older hfullNoBV
  have hlift := VLCtx.FVLift.to_append H.older hprefixNoBV
  rw [← hcontext] at hlift
  simpa [current, VLCtx.toCtx] using hlift

/-- Restrict a translated later-header domain to precisely the cached
parameters already consumed by this header. -/
theorem LaterParameterScope.domainTranslation
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {name : Name} {dom body : Expr} {bi : BinderInfo} {dom' : VExpr}
    (H : LaterParameterScope Hsuffix i (.forallE name dom body bi))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom') :
    ∃ sourceDom', TrExprS Hc.venv c.lparams H.older dom sourceDom' := by
  have hclosed : Closed dom 0 := by
    have := hdom.closed
    simpa [Hc.mlctx.noBV] using this
  exact hdom.weakFV_inv Hc.checking.tr.wf H.olderLift
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hclosed H.fvars.1

/-- Recover every premise needed by the executable cached-parameter branch
from the retained local-context translation. -/
theorem LaterParameterScope.typing
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr}
    (H : LaterParameterScope Hsuffix i body) :
    ∃ paramTy paramTy' param',
      (AddInductive.getType stats.params[i]! c).WF
        (fun ty => ty = paramTy) ∧
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy' ∧
      paramTy' = H.paramType.lift.liftN
        (VLCtx.toCtx H.added).length 0 ∧
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        stats.params[i]! param' ∧
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        param' paramTy' := by
  have hhead : VLCtx.find?
      ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
      (.inr H.fv) = some (.bvar 0, H.paramType.lift) := by
    simp [VLCtx.find?, VLCtx.next, VLocalDecl.value, VLocalDecl.type]
  have hfull := H.lift.find? Hc.mlctx_wf.tr.wf hhead
  rcases hfull with hfull
  let param' := (VExpr.bvar 0).liftN (VLCtx.toCtx H.added).length 0
  let paramTy' := H.paramType.lift.liftN
    (VLCtx.toCtx H.added).length 0
  have hfind : Hc.mlctx.vlctx.find? (.inr H.fv) =
      some (param', paramTy') := by
    simpa [param', paramTy'] using hfull
  have hfv : H.fv ∈ Hc.mlctx.vlctx.fvars :=
    VLCtx.find?_eq_some.1 ⟨_, hfind⟩
  have hlocal :=
    (Hc.mlctx_wf.tr.find?_eq_some (fv := H.fv)).2 hfv
  rcases hlocal with ⟨localDecl, hlocal⟩
  have hlocal' : c.lctx.find? H.fv = some localDecl := by
    rw [← Hc.lctx_eq]
    exact hlocal
  have hlist := hlocal
  rw [Hc.mlctx_wf.tr.1.find?_eq_find?_toList] at hlist
  have hid : H.fv = localDecl.fvarId := by
    simpa using List.find?_some hlist
  have hmem : localDecl ∈ Hc.mlctx.lctx.toList :=
    List.mem_of_find?_eq_some hlist
  rcases Hc.mlctx_wf.tr.find?_of_mem Hc.checking.tr.wf hmem with
    ⟨value', type', hfind', _hvalueBelow, _htypeBelow,
      _hvalue, htype⟩
  rw [← hid] at hfind'
  rw [hfind] at hfind'
  cases hfind'
  refine ⟨localDecl.type, paramTy', param', ?_, htype, rfl, ?_, ?_⟩
  · intro ty hrun
    rw [H.parameter] at hrun
    change Except.ok ((c.lctx.get! H.fv).type) = Except.ok ty at hrun
    simp [LocalContext.get!, hlocal'] at hrun
    exact hrun.symm
  · rw [H.parameter]
    exact .fvar hfind
  · exact Hc.mlctx_wf.tr.wf.find?_wf Hc.checking.tr.wf hfind

/-- The successful executable comparison of a later parameter domain with
its cached local type descends to the narrowed, abstract context. -/
theorem LaterParameterScope.domainDefEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {name : Name} {dom body : Expr} {bi : BinderInfo}
    {dom' paramTy' : VExpr}
    (H : LaterParameterScope Hsuffix i (.forallE name dom body bi))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hparamTyEq : paramTy' = H.paramType.lift.liftN
      (VLCtx.toCtx H.added).length 0)
    (heq : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      dom' paramTy') :
    ∃ sourceDom',
      TrExprS Hc.venv c.lparams H.older dom sourceDom' ∧
      Hc.venv.IsDefEqU c.lparams.length H.older.toCtx
        sourceDom' H.paramType := by
  rcases H.domainTranslation hdom with ⟨sourceDom', hsourceDom⟩
  have hweak := hsourceDom.weakFV Hc.checking.tr.wf.ordered
    H.olderLift Hc.mlctx_wf.tr.wf
  have htranslated : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx dom'
      (sourceDom'.liftN (VLCtx.toCtx H.added).length.succ 0) :=
    hdom.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hweak
  rw [hparamTyEq] at heq
  have hfull := htranslated.symm.trans Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx heq
  have hfull' : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx
      (sourceDom'.liftN (VLCtx.toCtx H.added).length.succ 0)
      (H.paramType.liftN (VLCtx.toCtx H.added).length.succ 0) := by
    simpa [Nat.succ_eq_add_one, VExpr.liftN_liftN, Nat.add_comm]
      using hfull
  exact ⟨sourceDom', hsourceDom,
    (VEnv.IsDefEqU.weakN_iff Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx
      H.olderLift.toCtx).1 hfull'⟩

/-- A closed source header starts the later-parameter traversal with an empty
free-variable scope. -/
noncomputable def LaterParameterScope.ofNoFVars
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    (hi : i < stats.params.size)
    (hfvars : FVarsIn (fun _ => False) e) :
    LaterParameterScope Hsuffix i e :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, hadd,
        hcontext, hparam, hlift⟩
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hfvars.mono fun _ h => False.elim h }⟩

/-- Advance the narrow scope after substituting cached parameter `i` and
normalizing the resulting body.  The next parameter's older suffix is
exactly the current cached declaration followed by the current older suffix.
-/
noncomputable def LaterParameterScope.next
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr}
    (H : LaterParameterScope Hsuffix i body)
    (hi : i + 1 < stats.params.size)
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized) :
    LaterParameterScope Hsuffix (i + 1) normalized :=
  Classical.choice <| by
    rcases Hsuffix.fvLiftAt hi with
      ⟨added, newer, older, fv, deps, paramType, hdecls, hnewer, hadd,
        hcontext, hparam, hlift⟩
    let currentEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (H.fv, H.deps), .vlam H.paramType)
    let nextEntry : Option (FVarId × List FVarId) × VLocalDecl :=
      (some (fv, deps), .vlam paramType)
    have hdecomp :
        H.newer ++ currentEntry :: H.older =
          (newer ++ [nextEntry]) ++ older := by
      calc
        H.newer ++ currentEntry :: H.older =
            Hsuffix.parameterDecls := H.parameterDecls.symm
        _ = newer ++ nextEntry :: older := hdecls
        _ = (newer ++ [nextEntry]) ++ older := by
          simp [List.append_assoc]
    have hprefixLength :
        H.newer.length = (newer ++ [nextEntry]).length := by
      simp only [List.length_append, List.length_singleton]
      rw [H.newerLength, hnewer]
      omega
    have htail : currentEntry :: H.older = older :=
      List.append_inj_right hdecomp hprefixLength
    have hopened : FVarsIn
        (· ∈ VLCtx.fvars (currentEntry :: H.older))
        (body.instantiate1 stats.params[i]!) := by
      rw [Expr.instantiate1_eq, H.parameter]
      exact H.openedFVars
    have hnormalized : FVarsIn
        (· ∈ VLCtx.fvars (currentEntry :: H.older)) normalized :=
      hbelow _ H.openedUpSet hopened
    have hnextFVars : FVarsIn (· ∈ VLCtx.fvars older) normalized := by
      rw [← htail]
      exact hnormalized
    exact ⟨{
      added := added
      newer := newer
      older := older
      fv := fv
      deps := deps
      paramType := paramType
      parameterDecls := hdecls
      newerLength := hnewer
      addedEq := hadd
      context := hcontext
      parameter := by
        simpa [Array.getElem!_eq_getD, hi] using hparam
      lift := hlift
      fvars := hnextFVars }⟩

/-- The core later-parameter abstraction step.  Translation of the
executable cached substitution is first restricted to the current-and-older
parameter suffix, then the cached free variable is turned back into the
source binder. -/
theorem LaterParameterScope.uninstantiateEq
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr} {body' : VExpr}
    (H : LaterParameterScope Hsuffix i body)
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body') :
    ∃ body'', TrExprS Hc.venv c.lparams
        ((none, .vlam H.paramType) :: H.older) body body'' ∧
      Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        body' (body''.liftN (VLCtx.toCtx H.added).length 0) := by
  have hopened' : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1' (.fvar H.fv)) body' := by
    simpa [Expr.instantiate1_eq, H.parameter] using hopened
  have hsuffixWF := H.lift.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
  have hfresh : H.fv ∉ H.older.fvars :=
    (hsuffixWF.2.1 H.fv H.deps rfl).1
  have hsourceFresh : FVarsIn (· ≠ H.fv) body :=
    H.fvars.mono fun fv hfv heq => by
      subst fv
      exact hfresh hfv
  have hopenedClosed : Closed (body.instantiate1' (.fvar H.fv)) 0 := by
    have := hopened'.closed
    simpa [Hc.mlctx.noBV] using this
  exact hopened'.uninstantiateAfterWeakFV_eq Hc.checking.tr.wf H.lift
    (.refl Hc.checking.tr.wf.ordered Hc.mlctx_wf.tr.wf)
    hopenedClosed H.openedFVars hsourceFresh

/-- The core later-parameter abstraction step without exposing the equality
back to the retained runtime context. -/
theorem LaterParameterScope.uninstantiate
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body : Expr} {body' : VExpr}
    (H : LaterParameterScope Hsuffix i body)
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body') :
    ∃ body'', TrExprS Hc.venv c.lparams
      ((none, .vlam H.paramType) :: H.older) body body'' := by
  rcases H.uninstantiateEq hopened with ⟨body'', hbody'', _⟩
  exact ⟨body'', hbody''⟩

/-- Restrict the post-substitution normal form to the consumed-parameter
suffix and relate it to the reconstructed source body.  This is the semantic
state transition used by the later-header telescope accumulator. -/
theorem LaterParameterScope.normalizedBody
    {c : AddInductive.Context} {Hc : ContextWF c}
    {stats : AddInductive.InductiveStats} {depth i : Nat}
    {Hsuffix : ParameterContextSuffix Hc stats depth}
    {body normalized : Expr} {body' : VExpr}
    (H : LaterParameterScope Hsuffix i body)
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body')
    (hbelow : FVarsBelow Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) normalized)
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized body') :
    ∃ sourceBody' normalized',
      TrExprS Hc.venv c.lparams
        ((none, .vlam H.paramType) :: H.older) body sourceBody' ∧
      TrExprS Hc.venv c.lparams
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older)
        normalized normalized' ∧
      Hc.venv.IsDefEqU c.lparams.length
        ((H.paramType :: H.older.toCtx)) sourceBody' normalized' := by
  rcases H.uninstantiateEq hopened with
    ⟨sourceBody', hsourceBody, hopenedEq⟩
  rcases hnormalized with ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
  have hopenedFVars : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      (body.instantiate1 stats.params[i]!) := by
    rw [Expr.instantiate1_eq, H.parameter]
    exact H.openedFVars
  have hnormalizedFVars : FVarsIn
      (· ∈ VLCtx.fvars
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      normalized :=
    hbelow _ H.openedUpSet hopenedFVars
  have hnormalizedClosed : Closed normalized 0 := by
    have := hnormalizedFull.closed
    simpa [Hc.mlctx.noBV] using this
  rcases hnormalizedFull.weakFV_inv Hc.checking.tr.wf H.lift
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      hnormalizedClosed hnormalizedFVars with
    ⟨normalized', hnormalized'⟩
  have hnormalizedWeak := hnormalized'.weakFV
    Hc.checking.tr.wf.ordered H.lift Hc.mlctx_wf.tr.wf
  have hnormalizedUniq := hnormalizedFull.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hnormalizedWeak
  have hfull : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx
      (sourceBody'.liftN (VLCtx.toCtx H.added).length 0)
      (normalized'.liftN (VLCtx.toCtx H.added).length 0) :=
    hopenedEq.symm.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
      (hnormalizeEq.symm.trans Hc.checking.tr.wf
        Hc.mlctx_wf.tr.wf.toCtx hnormalizedUniq)
  have hnarrow : Hc.venv.IsDefEqU c.lparams.length
      (VLCtx.toCtx
        ((some (H.fv, H.deps), .vlam H.paramType) :: H.older))
      sourceBody' normalized' :=
    (VEnv.IsDefEqU.weakN_iff Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx H.lift.toCtx).1 hfull
  exact ⟨sourceBody', normalized', hsourceBody, hnormalized',
    by simpa [VLCtx.toCtx] using hnarrow⟩

/-- Adding a common parameter weakens every cached parameter translation and
appends the newly generated free variable, whose abstract image is `bvar 0`.
This is the exact state update performed by `loopType` on the first header. -/
theorem ParameterCachePrefix.push
    (Hc : ContextWF c)
    (H : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx stats done 0)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterCachePrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
      (done + 1) 0 := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have hold : List.Forall₂
      (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
      stats.params.toList
      ((cachedParamVars done 0).map fun e => e.liftN 1 0) := by
    have mapRight : ∀ {as bs},
        List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) as bs →
        List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) as
          (bs.map fun e => e.liftN 1 0) := by
      intro as bs hp
      induction hp with
      | nil => exact .nil
      | cons h _ ih =>
        exact .cons
          (h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf) ih
    exact mapRight H.params
  have hfresh : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
      (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
    exact TrExprS.fvar (A := ty'.lift) (by
      change VLCtx.find? ((some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty') ::
        Hc.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
      simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
        VLocalDecl.value, VLocalDecl.type])
  refine ⟨?_, ?_⟩
  · simpa using Lean4Lean.VerifyInductive.List.Forall₂.append'
      hold (.cons hfresh .nil)
  · intro param hparam
    simp only [Array.mem_push] at hparam
    rcases hparam with hparam | rfl
    · exact H.paramFVars param hparam
    · exact ⟨⟨c.ngen.curr⟩, rfl⟩

/-- Index binders do not change the concrete parameter cache; they uniformly
shift its abstract de Bruijn interpretation. -/
theorem ParameterCachePrefix.withIndex
    (Hc : ContextWF c)
    (H : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx stats
      done depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ParameterCachePrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats done (depth + 1) := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  refine ⟨?_, H.paramFVars⟩
  rw [cachedParamVars_depth_succ]
  have mapRight : ∀ {as bs},
      List.Forall₂ (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) as bs →
      List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) as
        (bs.map fun e => e.liftN 1 0) := by
    intro as bs hp
    induction hp with
    | nil => exact .nil
    | cons h _ ih =>
      exact .cons
        (h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf) ih
  exact mapRight H.params

theorem ParameterCachePrefix.complete
    {decl : VInductDecl}
    (H : ParameterCachePrefix env Us Δ stats decl.nparams depth) :
    List.Forall₂ (TrExprS env Us Δ) stats.params.toList
      (decl.paramVars depth) := by
  rw [← cachedParamVars_eq_paramVars decl]
  exact H.params

/-- Fuel exhaustion cannot produce a successful result. -/
theorem zero.WF :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      0 k c).WF Q := by
  intro _ h
  simp [AddInductive.checkInductiveTypes.loopType] at h

/-- Base case of the header telescope traversal.  This theorem deliberately
states only the executable control-flow fact; the caller's continuation owns
the declarative result-sort and accumulated-telescope obligations. -/
theorem result.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hi : i = nparams)
    (Hk : (k type stats nindices c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      (fuel + 1) k c).WF Q := by
  subst i
  cases type <;>
    simp_all [AddInductive.checkInductiveTypes.loopType]

/-- A non-forall tail with the wrong number of common parameters is rejected,
so this branch is semantically vacuous. -/
theorem parameterMismatch.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hi : i ≠ nparams) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      (fuel + 1) k c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkInductiveTypes.loopType]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Verification step for an index binder.  `hdom`/`hdomType` are stated for
the annotation-consumed domain actually installed in the production local
context; deriving them from the source domain is the separate
`consumeTypeAnnotations` compatibility obligation. -/
theorem index.WF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      dom.consumeTypeAnnotations dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ normalized,
      TrExpr (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).venv
        c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams
        stats normalized i (nindices + 1) fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_neg hi]
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => do
      let type := body.instantiate1 arg
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) i (nindices + 1) fuel k)
    Hc hdom hdomType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    hdom hdomType hbody
  exact (whnfInContext.WF Hc' hopened).bind fun normalized hnormalized =>
    Hrec normalized hnormalized

/-- Index verification with the WHNF free-variable bound retained for
narrow-scope consumers. -/
theorem index.scopeWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      dom.consumeTypeAnnotations dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ normalized,
      FVarsBelow
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
      TrExpr (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).venv
        c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams
        stats normalized i (nindices + 1) fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_neg hi]
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => do
      let type := body.instantiate1 arg
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) i (nindices + 1) fuel k)
    Hc hdom hdomType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    hdom hdomType hbody
  exact (whnfInContext.scopeWF Hc' hopened).bind
    fun normalized hnormalized =>
      Hrec normalized hnormalized.1 hnormalized.2

/-- Source-facing index step: consume the domain certificate and transport the
source body automatically before invoking `index.WF`. -/
theorem index.sourceWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact index.WF Hc hi Hdom.consumed Hdom.isType hbody''
    (fun normalized hnormalized => Hrec body'' hbodyEq normalized hnormalized)

/-- Source-facing index step retaining the WHNF free-variable bound. -/
theorem index.sourceScopeWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        FVarsBelow
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) normalized →
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact index.scopeWF Hc hi Hdom.consumed Hdom.isType hbody''
    (fun normalized hbelow hnormalized =>
      Hrec body'' hbodyEq normalized hbelow hnormalized)

/-- Index-step wrapper that transports the first-header parameter cache under
the newly introduced index binder. -/
theorem index.cacheWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx stats done (depth + 1) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.sourceWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hdom hbody
  intro body'' hbodyEq normalized hnormalized
  exact Hrec body'' hbodyEq normalized hnormalized
    (Hcache.withIndex Hc Hdom.consumed Hdom.isType)

/-- Index-step wrapper carrying the translated parameter cache and the exact
source telescope/counter state in lockstep. -/
theorem index.cacheTelescopeWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Htelescope : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom' sourceBody') i nindices)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx stats done (depth + 1) →
        HeaderTelescopeLoopCertificate
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType)
          root sourceBody' i (nindices + 1) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.cacheWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' :
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  exact Hrec body'' hbodyEq'' normalized hnormalized Hcache'
    (Htelescope.withIndex Hdom)

/-- Complete index branch for the synthesized header telescope.  The source
body conversion and the following executable `whnf` are composed before the
recursive state is exposed. -/
theorem index.cacheSynthesisWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hsynthesis : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom' sourceBody') i nindices)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_hvenv : Hc'.venv = Hc.venv)
      (_hlparams : c'.lparams = c.lparams)
      (normalized : Expr) (next : VExpr),
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx normalized next →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats done (depth + 1) →
      ParameterContextSuffix Hc' stats (depth + 1) →
      HeaderSynthesisCertificate Hc' target next i (nindices + 1) →
      (AddInductive.checkInductiveTypes.loopType nparams stats normalized
        i (nindices + 1) fuel k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.cacheWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' : Hc'.venv.IsDefEqU c.lparams.length
      Hc'.mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [Hc', ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  rcases hnormalized with ⟨next, hnext, hnextEq⟩
  have hsourceNext := hbodyEq''.trans Hc'.checking.tr.wf
    Hc'.mlctx_wf.tr.wf.toCtx hnextEq.symm
  exact Hrec Hc' rfl rfl normalized next hnext Hcache'
    (Hsuffix.withIndex Hc Hdom.consumed Hdom.isType)
    ((Hsynthesis.withIndex Hdom).normalize hsourceNext)

/-- Later-header index step carrying both the translated parameter cache and
the ambient-prefix shape used at the constructor boundary. -/
theorem index.runtimeStateWF
    (Hc : ContextWF c) (hi : ¬ i < nparams)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done depth)
    (Hambient : AmbientParamContext Hc params depth)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx stats done (depth + 1) →
        AmbientParamContext
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType) params (depth + 1) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          i (nindices + 1) fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply index.cacheWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  exact Hrec body'' hbodyEq normalized hnormalized Hcache'
    (Hambient.withIndex Hdom.consumed Hdom.isType Hdom.source_defeq)

/-- Verification step for a common parameter of the first mutual header.  In
addition to the opened-body relation, the continuation sees the exact fresh
free variable appended to the executable parameter cache. -/
theorem firstParameter.WF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      dom.consumeTypeAnnotations dom')
    (hdomType : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ normalized,
      TrExpr (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).venv
        c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType).mlctx.vlctx
        normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        normalized (i + 1) nindices fuel k
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_pos hempty]
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun param => do
      let stats := { stats with params := stats.params.push param }
      let type := body.instantiate1 param
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k)
    Hc hdom hdomType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) hdom hdomType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    hdom hdomType hbody
  exact (whnfInContext.WF Hc' hopened).bind fun normalized hnormalized =>
    Hrec normalized hnormalized

/-- Source-facing first-parameter step, including annotation-domain and body
transport. -/
theorem firstParameter.sourceWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  exact firstParameter.WF Hc hi hempty Hdom.consumed Hdom.isType hbody''
    (fun normalized hnormalized => Hrec body'' hbodyEq normalized hnormalized)

/-- First-parameter wrapper synchronized with the executable cache push. -/
theorem firstParameter.cacheWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          (done + 1) 0 →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply firstParameter.sourceWF (stats := stats) (nparams := nparams) (i := i)
    (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hdom hbody
  intro body'' hbodyEq normalized hnormalized
  exact Hrec body'' hbodyEq normalized hnormalized
    (Hcache.push Hc Hdom.consumed Hdom.isType)

/-- First-parameter wrapper carrying the cache and source telescope counters
through the same successful executable branch. -/
theorem firstParameter.cacheTelescopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
    (Htelescope : HeaderTelescopeLoopCertificate Hc root
      (.forallE sourceDom' sourceBody') i nindices)
    (hindices : Htelescope.indices = [])
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' →
      ∀ normalized,
        TrExpr (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx normalized body'' →
        ParameterCachePrefix
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          (done + 1) 0 →
        HeaderTelescopeLoopCertificate
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType)
          root sourceBody' (i + 1) nindices →
        (AddInductive.checkInductiveTypes.loopType nparams
          { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
          normalized (i + 1) nindices fuel k
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply firstParameter.cacheWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' :
      (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv.IsDefEqU c.lparams.length
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  exact Hrec body'' hbodyEq'' normalized hnormalized Hcache'
    (Htelescope.withParameter hindices Hdom)

/-- Complete first-parameter branch for the synthesized header telescope. -/
theorem firstParameter.cacheSynthesisWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats done 0)
    (Hsuffix : ParameterContextSuffix Hc stats 0)
    (hprefix : Hsuffix.ambientDecls = [])
    (Hsynthesis : HeaderSynthesisCertificate Hc target
      (.forallE sourceDom' sourceBody') i nindices)
    (hindices : Hsynthesis.indices = [])
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_hvenv : Hc'.venv = Hc.venv)
      (_hlparams : c'.lparams = c.lparams)
      (normalized : Expr) (next : VExpr),
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx normalized next →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        (done + 1) 0 →
      ParameterContextSuffix Hc'
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        0 →
      (Hsynthesis' : HeaderSynthesisCertificate
        Hc' target next (i + 1) nindices) →
      Hsynthesis'.indices = [] →
      (AddInductive.checkInductiveTypes.loopType nparams
        { stats with params := stats.params.push (.fvar ⟨c.ngen.curr⟩) }
        normalized (i + 1) nindices fuel k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply firstParameter.cacheWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hempty Hcache Hdom hbody
  intro body'' hbodyEq normalized hnormalized Hcache'
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  have hbodyEq' := Hdom.bodyDefEqConsumed Hc hbodyEq
  have hbodyEq'' : Hc'.venv.IsDefEqU c.lparams.length
      Hc'.mlctx.vlctx.toCtx sourceBody' body'' := by
    simpa only [Hc', ContextWF.withLocalDecl_venv,
      ContextWF.withLocalDecl_toCtx] using hbodyEq'
  rcases hnormalized with ⟨next, hnext, hnextEq⟩
  have hsourceNext := hbodyEq''.trans Hc'.checking.tr.wf
    Hc'.mlctx_wf.tr.wf.toCtx hnextEq.symm
  let Hsynthesis' :=
    (Hsynthesis.withParameter hindices Hdom).normalize hsourceNext
  exact Hrec Hc' rfl rfl normalized next hnext Hcache'
    (Hsuffix.push Hc hprefix Hdom.consumed Hdom.isType)
    Hsynthesis' (by rfl)

/-- Verification step for a common parameter of a later mutual header.  The
executable checker reuses the cached free variable and requires the new domain
to be definitionally equal to its local type. -/
theorem laterParameter.WF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hget : (AddInductive.getType stats.params[i]! c).WF (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hopened : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      (body.instantiate1 stats.params[i]!) body')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      ∀ normalized, TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized body' →
      (AddInductive.checkInductiveTypes.loopType nparams stats normalized
        (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_neg (by simp [hnonempty])]
  change (AddInductive.getType stats.params[i]! c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other "parameters of all inductive datatypes must match"
      let type := body.instantiate1 stats.params[i]!
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k) :
      AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · exact (whnfInContext.WF Hc hopened).bind fun normalized hnormalized =>
      Hrec (hequal rfl) normalized hnormalized

/-- Source-facing later-parameter step.  The successful executable equality
check supplies exactly the conversion needed to instantiate the translated
source body with the cached parameter. -/
theorem laterParameter.sourceWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hget : (AddInductive.getType stats.params[i]! c).WF (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      stats.params[i]! param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      ∀ normalized,
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_neg (by simp [hnonempty])]
  change (AddInductive.getType stats.params[i]! c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other "parameters of all inductive datatypes must match"
      let type := body.instantiate1 stats.params[i]!
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k) :
      AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq := hequal rfl
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    exact (whnfInContext.WF Hc hopened).bind fun normalized hnormalized =>
      Hrec heq normalized hnormalized

/-- Complete cached-parameter step with the narrow concrete scope and the
reconstructed source binder exposed to the continuation. -/
theorem laterParameter.scopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hscope : LaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (hget : (AddInductive.getType stats.params[i]! c).WF
      (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      stats.params[i]! param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      dom' paramTy' →
      (∃ sourceBody', TrExprS Hc.venv c.lparams
        ((none, .vlam Hscope.paramType) :: Hscope.older)
          body sourceBody') →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx
          (body.instantiate1 stats.params[i]!) normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        (∃ sourceBody' normalized',
          TrExprS Hc.venv c.lparams
            ((none, .vlam Hscope.paramType) :: Hscope.older)
            body sourceBody' ∧
          TrExprS Hc.venv c.lparams
            ((some (Hscope.fv, Hscope.deps),
              .vlam Hscope.paramType) :: Hscope.older)
            normalized normalized' ∧
          Hc.venv.IsDefEqU c.lparams.length
            (Hscope.paramType :: Hscope.older.toCtx)
            sourceBody' normalized') →
        (i + 1 < stats.params.size →
          LaterParameterScope Hsuffix (i + 1) normalized) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopType]
  rw [if_pos hi, if_neg (by simp [hnonempty])]
  change (AddInductive.getType stats.params[i]! c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other "parameters of all inductive datatypes must match"
      let type := body.instantiate1 stats.params[i]!
      AddInductive.checkInductiveTypes.loopType nparams stats
        (← TypeChecker.whnf type) (i + 1) nindices fuel k) :
      AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind
    fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq := hequal rfl
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    let Hbody : LaterParameterScope Hsuffix i body := {
      Hscope with fvars := Hscope.fvars.2 }
    have habstract := Hbody.uninstantiate hopened
    exact (whnfInContext.scopeWF Hc hopened).bind
      fun normalized hnormalized =>
      Hrec heq habstract normalized hnormalized.1 hnormalized.2
        (Hbody.normalizedBody hopened hnormalized.1 hnormalized.2)
        (fun hnext => Hbody.next hnext hnormalized.1)

/-- Complete cached-parameter step driven only by the retained scope.  In
particular, lookup of the cached concrete parameter and all of its abstract
typing data are consequences of `Hscope`, rather than premises supplied by
the caller. -/
theorem laterParameter.checkedScopeWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hscope : LaterParameterScope Hsuffix i
      (.forallE name dom body bi))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (Hrec : ∀ {paramTy' param'},
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        stats.params[i]! param' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        param' paramTy' →
      Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      (∃ sourceDom',
        TrExprS Hc.venv c.lparams Hscope.older dom sourceDom' ∧
        Hc.venv.IsDefEqU c.lparams.length Hscope.older.toCtx
          sourceDom' Hscope.paramType) →
      (∃ sourceBody', TrExprS Hc.venv c.lparams
        ((none, .vlam Hscope.paramType) :: Hscope.older)
          body sourceBody') →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx
          (body.instantiate1 stats.params[i]!) normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        (∃ sourceBody' normalized',
          TrExprS Hc.venv c.lparams
            ((none, .vlam Hscope.paramType) :: Hscope.older)
            body sourceBody' ∧
          TrExprS Hc.venv c.lparams
            ((some (Hscope.fv, Hscope.deps),
              .vlam Hscope.paramType) :: Hscope.older)
            normalized normalized' ∧
          Hc.venv.IsDefEqU c.lparams.length
            (Hscope.paramType :: Hscope.older.toCtx)
            sourceBody' normalized') →
        (i + 1 < stats.params.size →
          LaterParameterScope Hsuffix (i + 1) normalized) →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  rcases Hscope.typing with
    ⟨paramTy, paramTy', param', hget, hparamTy, hparamTyEq,
      hparam, hparamType⟩
  apply laterParameter.scopeWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hnonempty Hsuffix Hscope hget hdom hbody hparamTy hparam hparamType
  intro heq habstract normalized hbelow hnormalized htransition hnext
  exact Hrec hparam hparamType heq
    (Hscope.domainDefEq hdom hparamTyEq heq) habstract
    normalized hbelow hnormalized htransition hnext

/-- Reusing a cached parameter does not alter the retained ambient-prefix
shape. -/
theorem laterParameter.runtimeStateWF
    (Hc : ContextWF c) (hi : i < nparams)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hambient : AmbientParamContext Hc params depth)
    (hget : (AddInductive.getType stats.params[i]! c).WF
      (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
      stats.params[i]! param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      ∀ normalized,
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized
          (body'.inst param') →
        AmbientParamContext Hc params depth →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized
          (i + 1) nindices fuel k c).WF Q) :
    (AddInductive.checkInductiveTypes.loopType nparams stats
      (.forallE name dom body bi) i nindices (fuel + 1) k c).WF Q := by
  apply laterParameter.sourceWF (stats := stats) (nparams := nparams)
    (i := i) (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
    Hc hi hnonempty hget hdom hbody hparamTy hparam hparamType
  intro heq normalized hnormalized
  exact Hrec heq normalized hnormalized Hambient

/-- Recursive verifier for the first mutual header.  It follows the concrete
fuel recursion and carries both the parameter cache and the synthesized
abstract telescope to the terminal continuation. -/
theorem firstHeaderSynthesisWF
    {target : VInductiveTypeSkeleton}
    {baseLevels : List Level} {baseNindices : Array Nat}
    {baseConsts : Array Expr}
    {R : VEnv → Prop}
    {α : Type} (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M α) (Q : α → Prop)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hresult : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {type' : Expr}
      {current' : VExpr} {i' nindices' : Nat}
      (Hc' : ContextWF c'),
      c'.lparams = Us →
      stats'.indConsts.isEmpty = true →
      stats'.levels = baseLevels →
      stats'.nindices = baseNindices →
      stats'.indConsts = baseConsts →
      R Hc'.venv →
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      i' = nparams →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' i' nindices' →
      ParameterContextSuffix Hc' stats' nindices' →
      HeaderSynthesisCertificate Hc' target current' i' nindices' →
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx type' current' →
      (k type' stats' nindices' c').WF Q)
    (Hc : ContextWF c)
    (hlparams : c.lparams = Us)
    (hempty : stats.indConsts.isEmpty = true)
    (hlevelsStable : stats.levels = baseLevels)
    (hnindicesStable : stats.nindices = baseNindices)
    (hconstsStable : stats.indConsts = baseConsts)
    (HR : R Hc.venv)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats i nindices)
    (Hsuffix : ParameterContextSuffix Hc stats nindices)
    (Hsynthesis : HeaderSynthesisCertificate Hc target current i nindices)
    (hphase : i < nparams → Hsynthesis.indices = [] ∧ nindices = 0)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i nindices
      fuel k c).WF Q := by
  induction fuel generalizing c stats type current i nindices with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htype with
      | forallE hdomType hbodyType hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom, Hdom⟩
        by_cases hi : i < nparams
        · rcases hphase hi with ⟨hindices, hnindices⟩
          subst nindices
          have hambient : Hsuffix.ambientDecls = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using Hsuffix.prefixLength
          apply firstParameter.cacheSynthesisWF
            (nparams := nparams) (fuel := fuel) (k := k) (Q := Q)
            Hc hi hempty (by simpa using Hcache) Hsuffix hambient
            Hsynthesis hindices Hdom hbody
          intro c' Hc' hvenv' hlparams' normalized next hnext Hcache' Hsuffix'
            Hsynthesis' hindices'
          apply ih Hc' (hlparams'.trans hlparams) (by simpa using hempty)
            (by simpa using hlevelsStable)
            (by simpa using hnindicesStable)
            (by simpa using hconstsStable)
            (by rw [hvenv']; exact HR)
            Hcache' Hsuffix' Hsynthesis'
          · intro _
            exact ⟨hindices', rfl⟩
          · exact hnext
        · apply index.cacheSynthesisWF
            (nparams := nparams) (fuel := fuel) (k := k) (Q := Q)
            Hc hi Hcache Hsuffix Hsynthesis Hdom hbody
          intro c' Hc' hvenv' hlparams' normalized next hnext Hcache' Hsuffix'
            Hsynthesis'
          apply ih Hc' (hlparams'.trans hlparams) hempty hlevelsStable
            hnindicesStable hconstsStable
            (by rw [hvenv']; exact HR)
            Hcache' Hsuffix' Hsynthesis'
          · intro hlt
            exact False.elim (hi hlt)
          · exact hnext
    · by_cases hi : i = nparams
      · exact result.WF hforall hi
          (Hresult Hc hlparams hempty hlevelsStable hnindicesStable
            hconstsStable HR hforall hi Hcache Hsuffix Hsynthesis htype)
      · exact parameterMismatch.WF hforall hi

/-- Follow the executable later-header loop through all cached common
parameters.  The retained suffix supplies each cached lookup and advances
after the executable normalization step.  Once `i = nparams`, ownership of
the unchanged loop state passes to the index/result verifier. -/
theorem laterParametersWF
    {alpha : Type} (Hc : ContextWF c)
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (Hresult : ∀ {type' current' i' fuel'},
      i' = nparams →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type' current' →
      (AddInductive.checkInductiveTypes.loopType nparams stats type' i'
        nindices fuel' k c).WF Q)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (hparams : stats.params.size = nparams)
    (hbound : i ≤ nparams)
    (Hscope : i < stats.params.size →
      LaterParameterScope Hsuffix i type)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type current) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i
      nindices fuel k c).WF Q := by
  induction fuel generalizing type current i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hi : i < nparams
    · by_cases hforall : ∃ name dom body bi,
          type = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        rcases TrExpr.forallE_source htype with
          ⟨dom', body', hdom, hbody, _hdomType, _hbodyType, _hcurrent⟩
        have histats : i < stats.params.size := by
          simpa [hparams] using hi
        apply laterParameter.checkedScopeWF
          (stats := stats) (nparams := nparams) (i := i)
          (nindices := nindices) (fuel := fuel) (k := k) (Q := Q)
          Hc hi hnonempty Hsuffix (Hscope histats) hdom hbody
        intro paramTy' param' _hparam _hparamType _heq _hdomain
          _habstract normalized _hbelow hnormalized _htransition hnext
        apply ih (i := i + 1) (current := body'.inst param')
        · omega
        · intro hlt
          exact hnext hlt
        · exact hnormalized
      · exact parameterMismatch.WF hforall (Nat.ne_of_lt hi)
    · have hieq : i = nparams := by omega
      exact Hresult hieq htype

/-- Cached-parameter recursion with the independent narrow header telescope
accumulated in lockstep.  The executable reader context remains unchanged;
the synthesis scope grows only by the parameters consumed by this header. -/
theorem laterParameterSynthesisWF
    {alpha : Type} (Hc : ContextWF c)
    {target : VInductiveTypeSkeleton}
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (hnonempty : stats.indConsts.isEmpty = false)
    (Hsuffix : ParameterContextSuffix Hc stats depth)
    (Hresult : ∀ {type' narrowCurrent fullCurrent scope' i' fuel'},
      i' = nparams →
      NarrowHeaderSynthesisCertificate Hc.venv c.lparams target
        scope' narrowCurrent i' 0 →
      scope' = Hsuffix.parameterDecls →
      TrExprS Hc.venv c.lparams scope' type' narrowCurrent →
      FVarsIn (· ∈ scope'.fvars) type' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type' fullCurrent →
      (AddInductive.checkInductiveTypes.loopType nparams stats type' i'
        0 fuel' k c).WF Q)
    (hparams : stats.params.size = nparams)
    (hbound : i ≤ nparams)
    (Hscope : ∀ _h : i < stats.params.size,
      LaterParameterScope Hsuffix i type)
    (hscopeEq : ∀ h : i < stats.params.size,
      scope = (Hscope h).older)
    (hcompleteScope : i = nparams →
      scope = Hsuffix.parameterDecls)
    (Hsynthesis : NarrowHeaderSynthesisCertificate Hc.venv c.lparams
      target scope narrowCurrent i 0)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFVars : FVarsIn (· ∈ scope.fvars) type)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type i
      0 fuel k c).WF Q := by
  induction fuel generalizing type scope narrowCurrent fullCurrent i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hi : i < nparams
    · by_cases hforall : ∃ name dom body bi,
          type = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        rcases TrExpr.forallE_source htypeFull with
          ⟨dom', body', hdom, hbody, _hdomType, _hbodyType, _hcurrent⟩
        have histats : i < stats.params.size := by
          simpa [hparams] using hi
        let Hcurrent := Hscope histats
        have hscope : scope = Hcurrent.older := hscopeEq histats
        subst scope
        apply laterParameter.checkedScopeWF
          (stats := stats) (nparams := nparams) (i := i)
          (nindices := 0) (fuel := fuel) (k := k) (Q := Q)
          Hc hi hnonempty Hsuffix Hcurrent hdom hbody
        intro paramTy' param' _hparam _hparamType _heq hdomain
          _habstract normalized hbelow hnormalized htransition hnext
        have hindices : Hsynthesis.indices = [] :=
          List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
        have hcurrentWF := Hcurrent.lift.wf Hc.checking.tr.wf
          Hc.mlctx_wf.tr.wf
        rcases Hsynthesis.consumeParameter Hc.checking.tr.wf hindices
            htypeNarrow hcurrentWF hdomain htransition with
          ⟨normalized', hnormalized', ⟨Hsynthesis'⟩⟩
        let Hbody : LaterParameterScope Hsuffix i body := {
          Hcurrent with fvars := Hcurrent.fvars.2 }
        exact ih (i := i + 1)
          (scope := (some (Hcurrent.fv, Hcurrent.deps),
            .vlam Hcurrent.paramType) :: Hcurrent.older)
          (narrowCurrent := normalized')
          (fullCurrent := body'.inst param')
          (hbound := by omega)
          (Hscope := fun hlt => hnext hlt)
          (hscopeEq := fun hlt =>
            Hcurrent.nextOlder (hnext hlt) hlt)
          (hcompleteScope := fun heq => by
            have hdone : i + 1 = stats.params.size := by
              rw [hparams]
              exact heq
            exact Hcurrent.completedScope hdone)
          Hsynthesis' hnormalized'
          (Hbody.consumedFVars hbelow) hnormalized
      · exact parameterMismatch.WF hforall (Nat.ne_of_lt hi)
    · have hieq : i = nparams := by omega
      exact Hresult hieq Hsynthesis (hcompleteScope hieq)
        htypeNarrow htypeFVars htypeFull

/-- Traverse the index suffix of a later mutual header while keeping its
semantic telescope independent of ambient declarations retained by the
executable checker. -/
theorem laterIndexSynthesisWF
    {alpha : Type} {target : VInductiveTypeSkeleton}
    {commonParams : List VExpr}
    {paramU : Nat}
    {R : VEnv → Prop}
    (k : Expr → AddInductive.InductiveStats → Nat →
      AddInductive.M alpha) (Q : alpha → Prop)
    (Hresult : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      (_hlparams : c'.lparams = c.lparams)
      {type' narrowCurrent fullCurrent scope' nindices' fuel'},
      (¬ ∃ name dom body bi, type' = .forallE name dom body bi) →
      (Hsynthesis' : NarrowHeaderSynthesisCertificate Hc'.venv c'.lparams
        target scope' narrowCurrent nparams nindices') →
      NarrowRuntimeScope Hc'.venv c'.lparams scope' Hc'.mlctx.vlctx →
      TrExprS Hc'.venv c'.lparams scope' type' narrowCurrent →
      FVarsIn (· ∈ scope'.fvars) type' →
      TrExpr Hc'.venv c'.lparams Hc'.mlctx.vlctx type' fullCurrent →
      ParameterCachePrefix Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats nparams (depth + nindices') →
      ParameterContextSuffix Hc' stats (depth + nindices') →
      AmbientParamContext Hc' commonParams (depth + nindices') →
      R Hc'.venv →
      VEnv.IsDefEqCtx Hc'.venv paramU []
        commonParams.reverse Hsynthesis'.params.reverse →
      (AddInductive.checkInductiveTypes.loopType nparams stats type'
        nparams nindices' (fuel' + 1) k c').WF Q)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hc : ContextWF c)
    (Hcache : ParameterCachePrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats nparams (depth + nindices))
    (Hsuffix : ParameterContextSuffix Hc stats (depth + nindices))
    (Hambient : AmbientParamContext Hc commonParams
      (depth + nindices))
    (HR : R Hc.venv)
    (Hsynthesis : NarrowHeaderSynthesisCertificate Hc.venv c.lparams
      target scope narrowCurrent nparams nindices)
    (Hparams : VEnv.IsDefEqCtx Hc.venv paramU []
      commonParams.reverse Hsynthesis.params.reverse)
    (Hruntime : NarrowRuntimeScope Hc.venv c.lparams
      scope Hc.mlctx.vlctx)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFVars : FVarsIn (· ∈ scope.fvars) type)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent) :
    (AddInductive.checkInductiveTypes.loopType nparams stats type
      nparams nindices fuel k c).WF Q := by
  induction fuel generalizing c type scope narrowCurrent fullCurrent
      nindices with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htypeNarrow with
      | @forallE indexType narrowBody _ _ _ _ _
          hdomType _hbodyType hdomNarrow hbodyNarrow =>
        rcases TrExpr.forallE_source htypeFull with
          ⟨sourceDom, fullBody, hdomFull, hbodyFull,
            hdomFullType, _hbodyFullType, _hfullCurrent⟩
        rcases hconsume c Hc hdomFull hdomFullType with
          ⟨consumedDom, Hdom⟩
        rcases Hdom.body Hc hbodyFull with
          ⟨consumedBody, hbodyConsumed, _hbodyEq⟩
        apply index.scopeWF (stats := stats) (nparams := nparams)
          (i := nparams) (nindices := nindices) (fuel := fuel)
          (k := k) (Q := Q) Hc (by omega) Hdom.consumed Hdom.isType
          hbodyConsumed
        intro normalized hbelow hnormalized
        let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
        have hdeps : dom.consumeTypeAnnotations.fvarsList ⊆ scope.fvars :=
          (fvarsIn_iff.mp
            (Expr.consumeTypeAnnotations_fvarsIn htypeFVars.1)).1
        rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
          ⟨domainLevel, hdomain⟩
        let Hruntime' : NarrowRuntimeScope Hc'.venv c.lparams
            ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotations.fvarsList),
              .vlam indexType) :: scope)
            Hc'.mlctx.vlctx :=
          Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
        have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
        have hopenedNarrow : TrExprS Hc'.venv c.lparams
            ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotations.fvarsList),
              .vlam indexType) :: scope)
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
          rw [Expr.instantiate1_eq]
          exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
        have hopenedFVars : FVarsIn
            (· ∈ VLCtx.fvars ((some (⟨c.ngen.curr⟩,
              dom.consumeTypeAnnotations.fvarsList),
              .vlam indexType) :: scope))
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) := by
          rw [Expr.instantiate1_eq]
          apply (htypeFVars.2.mono fun fv hfv => by
            rw [VLCtx.fvars_cons_some]
            exact List.mem_cons_of_mem _ hfv).instantiate1
          rw [VLCtx.fvars_cons_some]
          exact List.mem_cons_self
        have hnormalizedFVars := hbelow _ Hruntime'.upset hopenedFVars
        rcases hnormalized with
          ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
        have hnormalizedClosed : Closed normalized 0 := by
          have := hnormalizedFull.closed
          have hnoBV : Hc'.mlctx.vlctx.bvars = 0 := Hc'.mlctx.noBV
          rw [hnoBV] at this
          exact this
        rcases Hruntime'.restrictEq Hc'.checking.tr.wf
            hnormalizedFull hnormalizedClosed hnormalizedFVars with
          ⟨normalizedNarrow, hnormalizedNarrow, hnormalizedEq⟩
        have hopenedWeak : TrExprS Hc'.venv c.lparams Hruntime'.expanded
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
            (narrowBody.lift' Hruntime'.shift) := by
          simpa using hopenedNarrow.weakFV' Hc'.checking.tr.wf.ordered
            Hruntime'.lift Hruntime'.context.wf
        have hopenedFull := Hc.instantiateFresh
          (name := name) (bi := bi) Hdom.consumed Hdom.isType
          hbodyConsumed
        have hopenedEq := hopenedWeak.uniq Hc'.checking.tr.wf
          Hruntime'.context hopenedFull
        have hopenedEq' := hopenedEq.defeqDFC
          Hc'.checking.tr.wf.ordered Hruntime'.context.defeqCtx
        have hnormalizeU : Hc'.venv.IsDefEqU c.lparams.length
            Hc'.mlctx.vlctx.toCtx consumedBody normalizedFull :=
          hnormalizeEq.symm
        have hsourceNormalized := hopenedEq'.trans Hc'.checking.tr.wf
          Hc'.mlctx_wf.tr.wf.toCtx hnormalizeU
        have hfull : Hc'.venv.IsDefEqU c.lparams.length
            Hc'.mlctx.vlctx.toCtx
            (narrowBody.lift' Hruntime'.shift)
            (normalizedNarrow.lift' Hruntime'.shift) :=
          hsourceNormalized.trans Hc'.checking.tr.wf
            Hc'.mlctx_wf.tr.wf.toCtx hnormalizedEq
        have hexpanded := hfull.defeqDFC Hc'.checking.tr.wf.ordered
          (Hruntime'.context.defeqCtx.symm Hc'.checking.tr.wf.ordered)
        have hnarrow : Hc'.venv.IsDefEqU c.lparams.length
            (indexType :: scope.toCtx)
            narrowBody normalizedNarrow :=
          (VEnv.IsDefEqU.weak'_iff Hc'.checking.tr.wf
              Hruntime'.context.wf.toCtx Hruntime'.lift.toCtx).1 hexpanded
        have hdomainNarrow : ∃ sourceDom',
            TrExprS Hc'.venv c.lparams scope dom sourceDom' ∧
            Hc'.venv.IsDefEqU c.lparams.length scope.toCtx
              sourceDom' indexType :=
          ⟨_, hdomNarrow,
            ⟨.sort (Classical.choose hdomType),
              Classical.choose_spec hdomType⟩⟩
        have htransition : ∃ sourceBody' normalized',
            TrExprS Hc'.venv c.lparams
              ((none, .vlam indexType) :: scope)
              body sourceBody' ∧
            TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam indexType) :: scope)
              normalized normalized' ∧
            Hc'.venv.IsDefEqU c.lparams.length
              (indexType :: scope.toCtx)
              sourceBody' normalized' :=
          ⟨narrowBody, normalizedNarrow, hbodyNarrow,
            hnormalizedNarrow, hnarrow⟩
        rcases Hsynthesis.consumeIndex (name := name) (bi := bi)
            Hc'.checking.tr.wf
            (.forallE hdomType _hbodyType hdomNarrow hbodyNarrow)
            hscopeWF hdomainNarrow htransition with
          ⟨nextNarrow, hnextNarrow, Hsynthesis', hparamsPreserved⟩
        exact ih (fun Hc'' hlparams'' =>
            Hresult Hc'' (by simpa using hlparams'')) Hc'
          (by simpa [Nat.add_assoc] using
            Hcache.withIndex Hc Hdom.consumed Hdom.isType)
          (by simpa [Nat.add_assoc] using
            Hsuffix.withIndex Hc Hdom.consumed Hdom.isType)
          (by simpa [Nat.add_assoc] using
            (Hambient.withIndex Hdom.consumed Hdom.isType
              Hdom.source_defeq))
          (by change R Hc.venv; exact HR)
          Hsynthesis' (by
            rw [hparamsPreserved]
            change VEnv.IsDefEqCtx Hc.venv paramU []
              commonParams.reverse Hsynthesis.params.reverse
            exact Hparams) Hruntime' hnextNarrow
          hnormalizedFVars
          ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
    · exact Hresult Hc rfl hforall Hsynthesis Hruntime htypeNarrow
        htypeFVars htypeFull Hcache Hsuffix Hambient HR Hparams

end checkInductiveTypes.loopType

namespace checkInductiveTypes.loopInd

/-- At the first mutual header, the executable `whnf` result determines a
syntax-directed abstract normal form.  Independent translation of the source
header shows that this normal form is definitionally equal to the header in
`TrInductDecl`; the checked source type supplies the common typing witness. -/
theorem initialHeaderNormalization
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized' exprType,
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Hc.venv.IsDefEq c.lparams.length []
        target.type normalized' exprType := by
  rcases hnormalized with ⟨normalized', hnormalized', hnormalizedEq⟩
  have hsource : TrExprS Hc.venv c.lparams [] source.type sourceType := by
    simpa [hctx] using hchecked.2.1
  have htargetEq : Hc.venv.IsDefEqU c.lparams.length []
      target.type sourceType :=
    Htarget.header.type.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf (by trivial)) hsource
  have hsourceType : Hc.venv.HasType c.lparams.length []
      sourceType checkedType' := by
    simpa [hctx, VLCtx.toCtx] using hchecked.2.2.2
  have htargetType := hsourceType.defeqU_l Hc.checking.tr.wf
    (by trivial) htargetEq.symm
  have hnormalizedEq' : Hc.venv.IsDefEqU c.lparams.length []
      normalized' sourceType := by
    simpa [hctx, VLCtx.toCtx] using hnormalizedEq
  have htargetNormalized := htargetEq.trans Hc.checking.tr.wf
    (by trivial) hnormalizedEq'.symm
  exact ⟨normalized', checkedType', hnormalized',
    htargetNormalized.of_l Hc.checking.tr.wf (by trivial) htargetType⟩

/-- Package initial normalization with the empty executable telescope state.
This is the state consumed by the first parameter/index branch. -/
theorem initialHeaderState
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized' exprType,
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Hc.venv.IsDefEq c.lparams.length []
        target.type normalized' exprType ∧
      Nonempty (checkInductiveTypes.loopType.HeaderTelescopeLoopCertificate
        Hc normalized' normalized' 0 0) := by
  rcases initialHeaderNormalization Hc hctx Htarget hchecked hnormalized with
    ⟨normalized', exprType, hnormalized', hheader⟩
  have hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx := by
    simpa [hctx, VLCtx.toCtx] using
      (VEnv.IsDefEqCtx.refl (env := Hc.venv) (U := c.lparams.length)
        (by trivial : OnCtx ([] : List VExpr)
          (Hc.venv.IsType c.lparams.length)))
  exact ⟨normalized', exprType, hnormalized', hheader,
    ⟨checkInductiveTypes.loopType.HeaderTelescopeLoopCertificate.empty hctxEq⟩⟩

/-- Definitional synthesis state used by the complete first-header recursion. -/
theorem initialHeaderSynthesisState
    (Hc : ContextWF c) (hctx : Hc.mlctx.vlctx = [])
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx normalized normalized' ∧
      Nonempty (checkInductiveTypes.loopType.HeaderSynthesisCertificate
        Hc target normalized' 0 0) := by
  rcases initialHeaderNormalization Hc hctx Htarget hchecked hnormalized with
    ⟨normalized', exprType, hnormalized', hheader⟩
  have hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      [] Hc.mlctx.vlctx.toCtx := by
    simpa [hctx, VLCtx.toCtx] using
      (VEnv.IsDefEqCtx.refl (env := Hc.venv) (U := c.lparams.length)
        (by trivial : OnCtx ([] : List VExpr)
          (Hc.venv.IsType c.lparams.length)))
  have htargetType : Hc.venv.IsType c.lparams.length [] target.type := by
    have hwf := Htarget.header.wf
    change Hc.venv.IsType target.uvars [] target.type at hwf
    rw [Htarget.header.uvars] at hwf
    exact hwf
  have hcurrent : Hc.venv.IsType c.lparams.length [] normalized' :=
    htargetType.defeqU_l Hc.checking.tr.wf (by trivial) hheader.toU
  exact ⟨normalized', hnormalized',
    ⟨checkInductiveTypes.loopType.HeaderSynthesisCertificate.empty
      hctxEq hcurrent hheader⟩⟩

/-- A later source header is closed before cached parameters are substituted.
The outer `whnf` scope witness therefore initializes the narrow
later-parameter invariant at executable parameter zero. -/
noncomputable def initialLaterParameterScope
    (Hc : ContextWF c)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (hi : 0 < stats.params.size)
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hnormalized : FVarsBelow Hc.mlctx.vlctx source.type normalized) :
    checkInductiveTypes.loopType.LaterParameterScope
      Hsuffix 0 normalized := by
  have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
    Htarget.header.type.fvarsIn.mono fun fv hfv => by
      simpa [VLCtx.fvars] using hfv
  have hfalseUpSet : IsFVarUpSet (fun _ => False) Hc.mlctx.vlctx := by
    have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
      Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
    simpa [VLCtx.fvars] using hsuffix
  exact checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars hi
    (hnormalized _ hfalseUpSet hsourceNoFVars)

/-- Although a later header is normalized in the retained first-header local
context, both the source header and its initial normal form are closed.  The
normalization equality therefore descends to the empty abstract context,
where it can seed an independent later-header telescope certificate. -/
theorem initialLaterHeaderDefEq
    (Hc : ContextWF c)
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType)
    (hfvars : FVarsIn (fun _ => False) normalized) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams [] normalized normalized' ∧
      Hc.venv.IsDefEqU c.lparams.length [] target.type normalized' := by
  rcases hnormalized with ⟨normalizedFull, hnormalizedFull, hnormalizeEq⟩
  let W : VLCtx.FVLift [] Hc.mlctx.vlctx 0
      Hc.mlctx.vlctx.toCtx.length 0 :=
    VLCtx.FVLift.from_nil Hc.mlctx.noBV
  have hnormalizedClosed : Closed normalized 0 := by
    have := hnormalizedFull.closed
    simpa [Hc.mlctx.noBV] using this
  have hnormalizedNoFVars :
      FVarsIn (fun fv => fv ∈ VLCtx.fvars []) normalized := by
    simpa [VLCtx.fvars] using hfvars
  rcases hnormalizedFull.weakFV_inv Hc.checking.tr.wf W
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      hnormalizedClosed hnormalizedNoFVars with
    ⟨normalized', hnormalized'⟩
  have hsourceNoFVars : FVarsIn (fun _ => False) source.type :=
    Htarget.header.type.fvarsIn.mono fun fv hfv => by
      simpa [VLCtx.fvars] using hfv
  have hsourceClosed : Closed source.type 0 := by
    have := hchecked.2.1.closed
    simpa [Hc.mlctx.noBV] using this
  have hsourceNoFVars' :
      FVarsIn (fun fv => fv ∈ VLCtx.fvars []) source.type := by
    simpa [VLCtx.fvars] using hsourceNoFVars
  rcases hchecked.2.1.weakFV_inv Hc.checking.tr.wf W
      (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      hsourceClosed hsourceNoFVars' with
    ⟨sourceType', hsourceType'⟩
  have hnormalizedWeak := hnormalized'.weakFV Hc.checking.tr.wf.ordered
    W Hc.mlctx_wf.tr.wf
  have hsourceWeak := hsourceType'.weakFV Hc.checking.tr.wf.ordered
    W Hc.mlctx_wf.tr.wf
  have hnormalizedUniq := hnormalizedFull.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hnormalizedWeak
  have hsourceUniq := hchecked.2.1.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hsourceWeak
  have hfull : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
      (normalized'.liftN Hc.mlctx.vlctx.toCtx.length 0)
      (sourceType'.liftN Hc.mlctx.vlctx.toCtx.length 0) :=
    hnormalizedUniq.symm.trans Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx
      (hnormalizeEq.trans Hc.checking.tr.wf
        Hc.mlctx_wf.tr.wf.toCtx hsourceUniq)
  have hempty : Hc.venv.IsDefEqU c.lparams.length []
      normalized' sourceType' :=
    (VEnv.IsDefEqU.weakN_iff Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf.toCtx W.toCtx).1 hfull
  have htarget : Hc.venv.IsDefEqU c.lparams.length []
      target.type sourceType' :=
    Htarget.header.type.uniq Hc.checking.tr.wf
      (.refl Hc.checking.tr.wf (by trivial)) hsourceType'
  exact ⟨normalized', hnormalized',
    htarget.trans Hc.checking.tr.wf (by trivial) hempty.symm⟩

/-- Initialize the narrow later-header synthesis state in the empty consumed
scope. -/
theorem initialLaterHeaderSynthesisState
    (Hc : ContextWF c)
    (Htarget : TrInductiveTypeSkeleton Hc.venv envTypes
      c.lparams source target)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source.type checkedType sourceType checkedType')
    (hnormalized : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      normalized sourceType)
    (hfvars : FVarsIn (fun _ => False) normalized) :
    ∃ normalized',
      TrExprS Hc.venv c.lparams [] normalized normalized' ∧
      Nonempty (checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams target [] normalized' 0 0) := by
  rcases initialLaterHeaderDefEq Hc Htarget hchecked hnormalized hfvars with
    ⟨normalized', hnormalized', hheader⟩
  have htargetType : Hc.venv.IsType c.lparams.length [] target.type := by
    have hwf := Htarget.header.wf
    change Hc.venv.IsType target.uvars [] target.type at hwf
    rw [Htarget.header.uvars] at hwf
    exact hwf
  have hnormalizedType : Hc.venv.IsType c.lparams.length [] normalized' :=
    htargetType.defeqU_l Hc.checking.tr.wf (by trivial) hheader
  rcases htargetType with ⟨targetLevel, htargetType⟩
  have hheaderTyped := hheader.of_l Hc.checking.tr.wf (by trivial)
    htargetType
  exact ⟨normalized', hnormalized',
    ⟨checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.empty
      ⟨targetLevel, htargetType⟩ hnormalizedType hheaderTyped⟩⟩

private def updatedStats (stats : AddInductive.InductiveStats)
    (lctx : LocalContext) (resultLevel : Level) (setResult : Bool)
    (nindices : Nat) (indName : Name) : AddInductive.InductiveStats :=
  let stats := if setResult then
    { stats with
      lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
  else stats
  { stats with
    nindices := stats.nindices.push nindices
    indConsts := stats.indConsts.push (.const indName stats.levels) }

@[simp] theorem updatedStats_levels :
    (updatedStats stats lctx resultLevel setResult nindices indName).levels =
      stats.levels := by
  cases setResult <;> rfl

@[simp] theorem updatedStats_nindices_size :
    (updatedStats stats lctx resultLevel setResult nindices indName).nindices.size =
      stats.nindices.size + 1 := by
  cases setResult <;> simp [updatedStats]

@[simp] theorem updatedStats_nindices :
    (updatedStats stats lctx resultLevel setResult nindices indName).nindices =
      stats.nindices.push nindices := by
  cases setResult <;> rfl

@[simp] theorem updatedStats_indConsts_size :
    (updatedStats stats lctx resultLevel setResult nindices indName).indConsts.size =
      stats.indConsts.size + 1 := by
  cases setResult <;> simp [updatedStats]

@[simp] theorem updatedStats_indConsts :
    (updatedStats stats lctx resultLevel setResult nindices indName).indConsts =
      stats.indConsts.push (.const indName stats.levels) := by
  cases setResult <;> rfl

@[simp] theorem updatedStats_params :
    (updatedStats stats lctx resultLevel setResult nindices indName).params =
      stats.params := by
  cases setResult <;> rfl

/-- Initialize the loop certificate when the first header fixes the common
result universe. -/
def HeaderLoopCertificate.first
    {c : AddInductive.Context} {decl : VInductDecl} {params : List VExpr}
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderLoopCertificate env c.lparams decl params
      (updatedStats stats c.lctx resultSort true nindices indName) 1 := by
  subst target
  exact {
    resultLevel := decl.types[0].resultLevel
    commonLevel := by simpa [updatedStats] using hofLevel
    headerPrefix := HeaderPrefixCertificate.first hindex hshape }

/-- Extend the loop certificate for a later mutual header using precisely the
successful production `isEquiv` guard and sort-translation witness. -/
def HeaderLoopCertificate.later
    {c : AddInductive.Context} {decl : VInductDecl} {params : List VExpr}
    (H : HeaderLoopCertificate env c.lparams decl params stats dIdx)
    (hindex : dIdx < decl.types.length)
    (htarget : decl.types[dIdx] = target)
    (hguard : resultSort.isEquiv stats.resultLevel = true)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderLoopCertificate env c.lparams decl params
      (updatedStats stats stats.lctx resultSort false nindices indName)
      (dIdx + 1) := by
  subst target
  exact {
    resultLevel := H.resultLevel
    commonLevel := by simpa [updatedStats] using H.commonLevel
    headerPrefix := H.headerPrefix.pushOfIsEquiv hindex hguard hofLevel
      H.commonLevel hshape }

def HeaderLoopCertificate.complete
    (H : HeaderLoopCertificate env lparams decl params stats
      decl.types.length) : HeaderCertificate env decl :=
  H.headerPrefix.complete

/-- Post-telescope continuation for the first mutual header. -/
theorem firstResult.WF
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hrec : ∀ resultSort,
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx (.sort resultSort) type' →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  change ((monadLift (TypeChecker.ensureSort type) : AddInductive.M Expr) c >>=
    fun type => ((do
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) : AddInductive.M α) c).WF Q
  refine (ensureSortInContext.WF Hc htype).bind fun sorted hsorted => ?_
  rcases hsorted with ⟨hsorted, resultSort, rfl⟩
  rw [if_pos hempty]
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun c' h => ?_
  subst c'
  simpa [updatedStats, Expr.sortLevel!] using Hrec resultSort hsorted

/-- The first mutual header records its result universe and simultaneously
assembles the independent `TypeShape` certificate before continuing with the
remaining headers. -/
theorem firstResult.refines
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv params target →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  apply Hrec resultSort hofLevel
  exact TrExpr.typeShapeOfDefEqCtx Hc.checking.tr.wf Hc.mlctx_wf.tr.wf huvars
    hctxEq hheader hparamsTake hindicesTake hparams
    (hlevel resultSort) hsorted

/-- Canonical first-header specialization: choose the first header's own
parameter telescope as the block-wide parameter list.  Its `ParamsDefEq`
obligation is reflexive and follows from local-context well-formedness. -/
theorem firstResult.refinesCanonical
    {decl : VInductDecl} {target : VInductiveType}
    {ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv ownParams target →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  have hctxType : OnCtx (indices.reverse ++ ownParams.reverse)
      (Hc.venv.IsType decl.uvars) := by
    simpa [huvars] using hctxEq.isType
  exact firstResult.refines k Q Hc hempty htype huvars hctxEq hheader
    hparamsTake hindicesTake
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hlevel Hrec

/-- First-header result with the retained ambient-prefix invariant initialized
from the checked index telescope. -/
theorem firstResult.refinesRuntimeState
    {decl : VInductDecl} {target : VInductiveType}
    {ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv ownParams target →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc ownParams indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.refinesCanonical k Q Hc hempty htype huvars hctxEq
    hheader hparamsTake hindicesTake hlevel
  intro resultSort hofLevel hshape
  exact Hrec resultSort hofLevel hshape
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq hctxEq)

/-- First-header result specialized to the state accumulated by the actual
`loopType` parameter/index branches.  The source telescope supplies the
parameter split, index split, and context-conversion premises. -/
theorem firstResult.refinesTelescope
    {decl : VInductDecl} {target : VInductiveType}
    {normalized result translatedResult exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (Htelescope : checkInductiveTypes.loopType.HeaderTelescopeLoopCertificate
      Hc normalized result decl.nparams nindices)
    (hnindices : nindices = target.numIndices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type translatedResult)
    (hresultEq : Hc.venv.IsDefEqU c.lparams.length
      Hc.mlctx.vlctx.toCtx result translatedResult)
    (huvars : c.lparams.length = decl.uvars)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv Htelescope.params target →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Htelescope.params Htelescope.indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst nindices
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  have hctxType : OnCtx
      (Htelescope.indices.reverse ++ Htelescope.params.reverse)
      (Hc.venv.IsType decl.uvars) := by
    simpa [huvars] using Htelescope.telescope.context.isType
  have hshape := TrExpr.typeShapeOfDefEqCtxResult
    Hc.checking.tr.wf Hc.mlctx_wf.tr.wf huvars
    Htelescope.telescope.context hheader Htelescope.takeParameters
    Htelescope.takeIndices
    (VInductDecl.paramsDefEq_reflOfAppend hctxType) hresultEq
    (hlevel resultSort) hsorted
  exact Hrec resultSort hofLevel hshape
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
      Htelescope.telescope.context)

/-- Post-telescope first-header refinement using the definitional synthesis
state produced by `firstHeaderSynthesisWF`. -/
theorem firstResult.refinesSynthesis
    {decl : VInductDecl} {target : VInductiveType}
    {current : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc target.toSkeleton current decl.nparams nindices)
    (hnindices : nindices = target.numIndices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = decl.uvars)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv Hsynthesis.params target →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Hsynthesis.params Hsynthesis.indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst nindices
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  exact Hrec resultSort hofLevel
    (Hsynthesis.typeShape huvars (hlevel resultSort) hsorted)
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
      Hsynthesis.context)

/-- Metadata-synthesizing first-header continuation.  The executable index
counter and translated result sort are exported as data, together with a
declaration-independent shape proof; no pre-existing `VInductiveType`
metadata is assumed. -/
theorem firstResult.synthesizesHeader
    {source : VInductiveTypeSkeleton} {current : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc source current nparams nindices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = uvars)
    (Hrec : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeader Hc.venv uvars nparams
        Hsynthesis.params source nindices resultLevel →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Hsynthesis.params Hsynthesis.indices.length →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.WF k Q Hc hempty htype
  intro resultSort hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  exact Hrec resultSort resultLevel hofLevel
    (Hsynthesis.synthesizedHeader huvars hofLevel hsorted)
    (checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq
      Hsynthesis.context)

/-- Initialize the ordered mutual metadata prefix from the first successful
header result. -/
theorem firstResult.initializesPrefix
    {skeleton : VInductDeclSkeleton} {current : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hempty : stats.indConsts.isEmpty = true)
    (hindex : 0 < skeleton.types.length)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc skeleton.types[0] current skeleton.nparams nindices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = skeleton.uvars)
    (Hrec : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc.venv
        skeleton Hsynthesis.params resultLevel [(nindices, resultLevel)] 1 →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc Hsynthesis.params Hsynthesis.indices.length →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats c.lctx resultSort true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply firstResult.synthesizesHeader k Q Hc hempty Hsynthesis htype
    huvars
  intro resultSort resultLevel hofLevel Hheader Hambient
  exact Hrec resultSort resultLevel hofLevel
    (checkInductiveTypes.loopType.SynthesizedHeaderPrefix.first
      hindex Hheader) Hambient

/-- Post-telescope continuation for later mutual headers.  A mismatched result
universe throws; a successful path records the checked equivalence before
updating the per-type arrays. -/
theorem laterResult.WF
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx (.sort resultSort) type' →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  change ((monadLift (TypeChecker.ensureSort type) : AddInductive.M Expr) c >>=
    fun type => ((do
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) : AddInductive.M α) c).WF Q
  refine (ensureSortInContext.WF Hc htype).bind fun sorted hsorted => ?_
  rcases hsorted with ⟨hsorted, resultSort, rfl⟩
  rw [if_neg (by simp [hnonempty])]
  by_cases hequiv : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel = true
  · have hequiv' : resultSort.isEquiv stats.resultLevel = true := by
      simpa [Expr.sortLevel!] using hequiv
    simpa [updatedStats, Expr.sortLevel!, hequiv, hequiv'] using
      Hrec resultSort hequiv' hsorted
  · have hfalse : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel = false := by
      cases h : (Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel <;>
        simp_all
    have hnot : (!(Expr.sort resultSort).sortLevel!.isEquiv stats.resultLevel) = true := by
      simp [hfalse]
    rw [if_pos hnot]
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Every later mutual header produces the same independent `TypeShape`
certificate as the first header. The executable `isEquiv` guard is retained
as an explicit continuation premise; it is subsequently used to establish
the common-result-universe component of `FormationWF`. -/
theorem laterResult.refines
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      decl.TypeShape Hc.venv params target →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply laterResult.WF k Q Hc hnonempty htype
  intro resultSort hequiv hsorted
  rcases TrExpr.sort_source hsorted with ⟨resultLevel, hofLevel, _⟩
  have hresultLevel := hlevel resultSort resultLevel hofLevel
  subst resultLevel
  apply Hrec resultSort hequiv hofLevel
  exact TrExpr.typeShapeOfDefEqCtx Hc.checking.tr.wf Hc.mlctx_wf.tr.wf huvars
    hctxEq hheader hparamsTake hindicesTake hparams
    (hlevel resultSort) hsorted

/-- Metadata-synthesizing continuation for a later mutual header.  The
executable result-universe guard extends the ordered metadata prefix, while
the successful parameter comparisons let the independently synthesized
header use the common parameter telescope fixed by the first family member.

This theorem deliberately starts at the post-telescope boundary.  The
per-binder later-header recursion has a different runtime shape from the
first header (cached parameters are substituted rather than introduced), so
it is verified separately instead of being hidden behind the first-header
invariant. -/
theorem laterResult.extendsPrefix
    {skeleton : VInductDeclSkeleton} {source : VInductiveTypeSkeleton}
    {current : VExpr} {commonParams : List VExpr}
    {metadata : List (Nat × VLevel)} {commonLevel : VLevel}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (hindex : dIdx < skeleton.types.length)
    (hsource : skeleton.types[dIdx] = source)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hsynthesis : checkInductiveTypes.loopType.HeaderSynthesisCertificate
      Hc source current skeleton.nparams nindices)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type current)
    (huvars : c.lparams.length = skeleton.uvars)
    (hparams : VEnv.IsDefEqCtx Hc.venv skeleton.uvars []
      commonParams.reverse Hsynthesis.params.reverse)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (Hrec : ∀ resultSort resultLevel,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc.venv
        skeleton commonParams commonLevel
        (metadata ++ [(nindices, resultLevel)]) (dIdx + 1) →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName)
        k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other
          "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst source
  apply laterResult.WF k Q Hc hnonempty htype
  intro resultSort hguard hsorted
  rcases TrExpr.sort_source hsorted with
    ⟨resultLevel, hofLevel, _hresult⟩
  have hheader := Hsynthesis.synthesizedHeaderWithParams huvars hparams
    hofLevel hsorted
  have hlevel : resultLevel ≈ commonLevel :=
    Level.isEquiv_wf hguard hofLevel hcommon
  exact Hrec resultSort resultLevel hguard hofLevel
    (Hprefix.push hindex hheader hlevel)

/-- Later-header result continuation for the independent narrow telescope.
The executable sort check runs in the retained runtime context; `resultSort`
restricts its translation before the synthesized header is added to the
ordered metadata prefix. -/
theorem laterResult.extendsPrefixNarrow
    {skeleton : VInductDeclSkeleton} {source : VInductiveTypeSkeleton}
    {narrowCurrent fullCurrent : VExpr} {scope : VLCtx}
    {commonParams : List VExpr}
    {metadata : List (Nat × VLevel)} {commonLevel : VLevel}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c) (hnonempty : stats.indConsts.isEmpty = false)
    (hindex : dIdx < skeleton.types.length)
    (hsource : skeleton.types[dIdx] = source)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hsynthesis : checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      Hc.venv c.lparams source scope narrowCurrent
      skeleton.nparams nindices)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowCurrent)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type fullCurrent)
    (huvars : c.lparams.length = skeleton.uvars)
    (hparams : VEnv.IsDefEqCtx Hc.venv skeleton.uvars []
      commonParams.reverse Hsynthesis.params.reverse)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (Hrec : ∀ resultSort resultLevel,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc.venv
        skeleton commonParams commonLevel
        (metadata ++ [(nindices, resultLevel)]) (dIdx + 1) →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices indName)
        k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other
          "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  subst source
  rcases htypeFull with ⟨sourceFull, hsourceFull, _hsourceEq⟩
  apply laterResult.WF k Q Hc hnonempty hsourceFull
  intro resultSort hguard hsorted
  have hsourceFull' : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      type sourceFull :=
    hsourceFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
  have hsortedNarrow := Hruntime.resultSort Hc.checking.tr.wf
    htypeNarrow hsourceFull' hsorted
  rcases TrExpr.sort_source hsortedNarrow with
    ⟨resultLevel, hofLevel, _hresult⟩
  have hheader := Hsynthesis.synthesizedHeaderWithParams
    Hc.checking.tr.wf huvars hparams hofLevel hsortedNarrow
  have hlevel : resultLevel ≈ commonLevel :=
    Level.isEquiv_wf hguard hofLevel hcommon
  exact Hrec resultSort resultLevel hguard hofLevel
    (Hprefix.push hindex hheader hlevel)

/-- Base case of the mutual-header loop.  The executable assertions become
explicit invariants at the proof boundary instead of being silently erased. -/
theorem result.WF
    (hidx : ¬ dIdx < indTypes.size)
    (hlevels : stats.levels.length = c.lparams.length)
    (hindices : stats.nindices.size = indTypes.size)
    (hconsts : stats.indConsts.size = indTypes.size)
    (hparams : stats.params.size = nparams)
    (Hk : (k stats c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopInd]
  rw [dif_neg hidx]
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  simpa [hlevels, hindices, hconsts, hparams] using Hk

/-- Verified prefix of one mutual-header iteration: closed source checking and
WHNF are connected to the abstract translation before control enters the
already verified telescope loop.  The continuation owns the result-sort,
statistics update, and recursive mutual iteration invariants. -/
theorem stepPrefix.WF
    (Hc : ContextWF c) (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[dIdx].type checkedType type' checkedType' →
      ∀ normalized,
      FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
        c.fuel.inductiveFuel (fun type stats nindices => show AddInductive.M _ from do
          let type ← TypeChecker.ensureSort type
          let mut stats := stats
          let resultLevel := type.sortLevel!
          if stats.indConsts.isEmpty then
            let lctx := (← read).lctx
            stats := { stats with
              lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
          else if !resultLevel.isEquiv stats.resultLevel then
            throw <| .other "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd nparams indTypes
            (dIdx + 1) stats k) c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  rw [AddInductive.checkInductiveTypes.loopInd]
  rw [dif_pos hidx]
  change (AddInductive.checkClosedType indTypes[dIdx].name indTypes[dIdx].type c >>=
    fun _ => ((do
      let normalized ← TypeChecker.whnf indTypes[dIdx].type
      AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
        c.fuel.inductiveFuel (fun type stats nindices => show AddInductive.M _ from do
          let type ← TypeChecker.ensureSort type
          let mut stats := stats
          let resultLevel := type.sortLevel!
          if stats.indConsts.isEmpty then
            let lctx := (← read).lctx
            stats := { stats with
              lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
          else if !resultLevel.isEquiv stats.resultLevel then
            throw <| .other "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd nparams indTypes
            (dIdx + 1) stats k)) : AddInductive.M _) c).WF Q
  exact (checkClosedType.WF Hc).bind fun checkedType hchecked => by
    rcases hchecked with ⟨type', checkedType', hchecked⟩
    exact (whnfInContext.scopeWF Hc hchecked.2.1).bind
      fun normalized hnormalized =>
      Hloop checkedType type' checkedType' hchecked normalized
        hnormalized.1 hnormalized.2

/-- Metadata-free declaration-facing header step.  This is the entry point
used before `checkInductiveTypes` has recovered enough information to build a
`VInductDecl`. -/
theorem stepPrefix.refinesSkeleton
    {skeleton : VInductDeclSkeleton}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeleton Hc.venv c.lparams nparams
      indTypes.toList isUnsafe skeleton)
    (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[dIdx].type checkedType type' checkedType' →
      ∀ envTypes,
        Hc.venv.addConsts skeleton.typeConstants = some envTypes →
        ∀ target,
        skeleton.types[dIdx]? = some target →
        TrInductiveTypeSkeleton Hc.venv envTypes c.lparams
          indTypes[dIdx] target →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
          c.fuel.inductiveFuel (fun type stats nindices =>
            show AddInductive.M _ from do
            let type ← TypeChecker.ensureSort type
            let mut stats := stats
            let resultLevel := type.sortLevel!
            if stats.indConsts.isEmpty then
              let lctx := (← read).lctx
              stats := { stats with
                lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
            else if !resultLevel.isEquiv stats.resultLevel then
              throw <| .other
                "mutually inductive types must live in the same universe"
            stats := { stats with
              nindices := stats.nindices.push nindices
              indConsts := stats.indConsts.push
                (.const indTypes[dIdx].name stats.levels) }
            AddInductive.checkInductiveTypes.loopInd nparams indTypes
              (dIdx + 1) stats k) c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  have htarget : dIdx < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeleton.types_length Hdecl]
    simpa using hidx
  rcases Lean4Lean.VerifyInductive.TrInductDeclSkeleton.typeAt Hdecl dIdx
      (by simpa using hidx) htarget with
    ⟨envTypes, htypes, htargetTr⟩
  apply stepPrefix.WF (nparams := nparams) (stats := stats) (k := k)
    (Q := Q) Hc hidx
  intro checkedType type' checkedType' hchecked normalized hscope hnormalized
  exact Hloop checkedType type' checkedType' hchecked envTypes htypes
    skeleton.types[dIdx] (by simp [htarget]) (by simpa using htargetTr)
    normalized hscope hnormalized

/-- Complete first iteration of the executable mutual-header loop, from the
closed source check through initialization of the ordered synthesized
metadata prefix. -/
theorem firstStep.initializesPrefix
    {skeleton : VInductDeclSkeleton}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeleton Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton)
    (hctx : Hc.mlctx.vlctx = [])
    (hidx : 0 < indTypes.size)
    (hempty : stats.indConsts.isEmpty = true)
    (hparams : stats.params = #[])
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hrec : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {nindices : Nat}
      {resultSort : Level} {resultLevel : VLevel} {params : List VExpr},
      (Hc' : ContextWF c') →
      c'.lparams = c.lparams →
      stats'.levels = stats.levels →
      stats'.nindices = stats.nindices →
      stats'.indConsts = stats.indConsts →
      TrInductDeclSkeleton Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe skeleton →
      VLevel.ofLevel c'.lparams resultSort = some resultLevel →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx stats'
        skeleton.nparams nindices →
      checkInductiveTypes.loopType.ParameterContextSuffix
        Hc' stats' nindices →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc'.venv
        skeleton params resultLevel [(nindices, resultLevel)] 1 →
      checkInductiveTypes.loopType.AmbientParamContext
        Hc' params nindices →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 1
        (updatedStats stats' c'.lctx resultSort true nindices
          indTypes[0].name) k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 0
      stats k c).WF Q := by
  have hskeletonIdx : 0 < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeleton.types_length Hdecl]
    simpa using hidx
  apply stepPrefix.refinesSkeleton (k := k) (Q := Q) Hc Hdecl hidx
  intro checkedType type' checkedType' hchecked envTypes htypes
    target htarget Htarget normalized _hscope hnormalized
  have htargetEq : target = skeleton.types[0] := by
    symm
    simpa [List.getElem?_eq_getElem hskeletonIdx] using htarget
  subst target
  rcases initialHeaderSynthesisState Hc hctx Htarget hchecked hnormalized with
    ⟨normalized', hnormalized', ⟨Hsynthesis⟩⟩
  have Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats 0 0 :=
    checkInductiveTypes.loopType.ParameterCachePrefix.empty hparams
  have Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats 0 :=
    checkInductiveTypes.loopType.ParameterContextSuffix.empty Hc hctx hparams
  apply checkInductiveTypes.loopType.firstHeaderSynthesisWF
    (Us := c.lparams) (target := skeleton.types[0])
    (nparams := skeleton.nparams) (stats := stats)
    (type := normalized) (current := normalized') (i := 0)
    (nindices := 0) (c := c)
    (k := fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other
          "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push
          (.const indTypes[0].name stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 1
        stats k)
    (Q := Q) (hconsume := hconsume)
    (Hresult := by
      intro c' stats' type'' current'' i' nindices' Hc' hlparams'
        hempty' hlevels' hnindices' hconsts' Hdecl' hforall iEq Hcache'
        Hsuffix' Hsynthesis' htype'
      cases iEq
      apply firstResult.initializesPrefix k Q Hc' hempty' hskeletonIdx
        Hsynthesis' htype'
      · rw [hlparams', ← Hdecl.2.1]
      · intro resultSort resultLevel hofLevel Hprefix Hambient
        apply Hrec Hc' hlparams' hlevels' hnindices' hconsts'
          (by simpa [hlparams'] using Hdecl') hofLevel Hcache' Hsuffix'
          Hprefix
        simpa [Hsynthesis'.indexCount] using Hambient)
    (Hc := Hc) (hlparams := rfl) (hempty := hempty)
    (hlevelsStable := rfl) (hnindicesStable := rfl)
    (hconstsStable := rfl)
    (R := fun env => TrInductDeclSkeleton env c.lparams
      skeleton.nparams indTypes.toList isUnsafe skeleton)
    (HR := Hdecl)
    (Hcache := Hcache) (Hsuffix := Hsuffix) (Hsynthesis := Hsynthesis)
    (hphase := by
      intro _
      exact ⟨List.eq_nil_of_length_eq_zero Hsynthesis.indexCount, rfl⟩)
    (htype := hnormalized')

/-- Complete a noninitial mutual-header iteration.  Cached parameters are
consumed in an independent narrow telescope, later indices extend both the
runtime and outer-loop context certificates, and the result sort appends one
ordered metadata entry. -/
theorem laterStep.extendsPrefix
    {skeleton : VInductDeclSkeleton} {commonParams : List VExpr}
    {commonLevel : VLevel} {metadata : List (Nat × VLevel)}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeleton Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton)
    (hidx : dIdx < indTypes.size)
    (_hnoninitial : 0 < dIdx)
    (hnonempty : stats.indConsts.isEmpty = false)
    (hparams : stats.params.size = skeleton.nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats skeleton.nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hrec : ∀ {c' : AddInductive.Context} {nindices : Nat}
      {resultSort : Level} {resultLevel : VLevel},
      (Hc' : ContextWF c') →
      c'.lparams = c.lparams →
      TrInductDeclSkeleton Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe skeleton →
      checkInductiveTypes.loopType.ParameterCachePrefix
        Hc'.venv c'.lparams Hc'.mlctx.vlctx
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name)
        skeleton.nparams (depth + nindices) →
      checkInductiveTypes.loopType.ParameterContextSuffix Hc'
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name)
        (depth + nindices) →
      checkInductiveTypes.loopType.SynthesizedHeaderPrefix Hc'.venv
        skeleton commonParams commonLevel
        (metadata ++ [(nindices, resultLevel)]) (dIdx + 1) →
      checkInductiveTypes.loopType.AmbientParamContext Hc'
        commonParams (depth + nindices) →
      (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1)
        (updatedStats stats stats.lctx resultSort false nindices
          indTypes[dIdx].name) k c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
      dIdx stats k c).WF Q := by
  have hskeletonIdx : dIdx < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeleton.types_length Hdecl]
    simpa using hidx
  apply stepPrefix.refinesSkeleton (k := k) (Q := Q) Hc Hdecl hidx
  intro checkedType type' checkedType' hchecked envTypes htypes
    target htarget Htarget normalized hbelow hnormalized
  have htargetEq : target = skeleton.types[dIdx] := by
    symm
    simpa [List.getElem?_eq_getElem hskeletonIdx] using htarget
  subst target
  have hnormalizedNoFVars : FVarsIn (fun _ => False) normalized := by
    have hsourceNoFVars : FVarsIn (fun _ => False)
        indTypes[dIdx].type :=
      Htarget.header.type.fvarsIn.mono fun fv hfv => by
        simpa [VLCtx.fvars] using hfv
    have hfalseUpSet : IsFVarUpSet (fun _ => False)
        Hc.mlctx.vlctx := by
      have hsuffix := IsFVarUpSet.suffixFVars ([] : VLCtx)
        Hc.mlctx.vlctx (by simpa using Hc.mlctx_wf.tr.wf)
      simpa [VLCtx.fvars] using hsuffix
    exact hbelow _ hfalseUpSet hsourceNoFVars
  rcases initialLaterHeaderSynthesisState Hc Htarget hchecked
      hnormalized hnormalizedNoFVars with
    ⟨narrowCurrent, hnormalizedNarrow, ⟨Hsynthesis⟩⟩
  let Hscope : ∀ h : 0 < stats.params.size,
      checkInductiveTypes.loopType.LaterParameterScope Hsuffix 0
        normalized := fun h =>
    initialLaterParameterScope Hc Hsuffix h Htarget hbelow
  apply checkInductiveTypes.loopType.laterParameterSynthesisWF Hc
    (target := skeleton.types[dIdx])
    (k := fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other
          "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push
          (.const indTypes[dIdx].name stats.levels) }
      AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
        (dIdx + 1) stats k)
    (Q := Q) hnonempty Hsuffix
    (Hresult := by
      intro type'' narrow'' full'' scope'' i'' fuel'' hi'' Hsynthesis''
        hscope'' htypeNarrow'' htypeFVars'' htypeFull''
      cases hi''
      subst scope''
      let Hruntime :=
        checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
          Hc Hsuffix
      have hindices'' : Hsynthesis''.indices = [] :=
        List.eq_nil_of_length_eq_zero Hsynthesis''.indexCount
      have hparamScope : Hsuffix.parameterDecls.toCtx =
          Hsynthesis''.params.reverse := by
        simpa [hindices''] using Hsynthesis''.scopeCtx
      have hparamsBoundary := Hsuffix.paramsDefEq Hambient <|
        Hprefix.parameterCount.trans hparams.symm
      rw [hparamScope] at hparamsBoundary
      apply checkInductiveTypes.loopType.laterIndexSynthesisWF
        (depth := depth) (commonParams := commonParams)
        (paramU := c.lparams.length)
        (R := fun env =>
          checkInductiveTypes.loopType.SynthesizedHeaderPrefix env
              skeleton commonParams commonLevel metadata dIdx ∧
            TrInductDeclSkeleton env c.lparams skeleton.nparams
              indTypes.toList isUnsafe skeleton)
        (k := fun type stats nindices => show AddInductive.M α from do
          let type ← TypeChecker.ensureSort type
          let mut stats := stats
          let resultLevel := type.sortLevel!
          if stats.indConsts.isEmpty then
            let lctx := (← read).lctx
            stats := { stats with
              lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
          else if !resultLevel.isEquiv stats.resultLevel then
            throw <| .other
              "mutually inductive types must live in the same universe"
          stats := { stats with
            nindices := stats.nindices.push nindices
            indConsts := stats.indConsts.push
              (.const indTypes[dIdx].name stats.levels) }
          AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
            (dIdx + 1) stats k)
        (Q := Q)
        (Hresult := by
          intro c' Hc' hlparams' type''' narrow''' full''' scope'''
            nindices''' fuel''' hforall''' Hsynthesis''' Hruntime'''
            htypeNarrow''' _htypeFVars''' htypeFull''' Hcache'''
            Hsuffix''' Hambient''' HR''' hparams'''
          rcases HR''' with ⟨Hprefix''', Hdecl'''⟩
          apply checkInductiveTypes.loopType.result.WF
            (fuel := fuel''') (Q := Q) hforall''' rfl
          apply laterResult.extendsPrefixNarrow
            (indTypes := indTypes) (indName := indTypes[dIdx].name)
            (commonParams := commonParams) (metadata := metadata)
            (commonLevel := commonLevel) k Q Hc' hnonempty
            hskeletonIdx rfl Hprefix''' Hsynthesis'''
            Hruntime''' htypeNarrow''' htypeFull'''
          · rw [hlparams', ← Hdecl.2.1]
          · simpa [hlparams', ← Hdecl.2.1] using hparams'''
          · simpa [hlparams'] using hcommon
          · intro resultSort resultLevel hguard hofLevel Hprefix'
            apply Hrec Hc' hlparams'
            · simpa [hlparams'] using Hdecl'''
            · exact Hcache'''.reindex (by simp [updatedStats])
            · exact Hsuffix'''.reindex (by simp [updatedStats])
            · exact Hprefix'
            · exact Hambient''')
        hconsume Hc (by simpa using Hcache) (by simpa using Hsuffix)
        (by simpa using Hambient) ⟨Hprefix, Hdecl⟩ Hsynthesis''
        hparamsBoundary
        Hruntime
        htypeNarrow'' htypeFVars'' htypeFull'')
    hparams (by omega) Hscope
    (fun h => (Hscope h).older_eq_nil h |>.symm)
    (by
      intro hzero
      have hsize : stats.params.size = 0 := hparams.trans hzero.symm
      apply (List.eq_nil_of_length_eq_zero ?_).symm
      rw [Hsuffix.parameterDecls_length, hsize])
    Hsynthesis hnormalizedNarrow (by simpa [VLCtx.fvars] using
      hnormalizedNoFVars) hnormalized

/-- Concrete statistics recovered together with a materialized mutual header.
This is the early traversal-facing form of `ValidAppStatsWF`; it is kept here
because the latter also packages the derived name-search invariant used by
positivity, which is defined after the executable constructor interfaces. -/
structure MaterializedHeaderResult (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (stats : AddInductive.InductiveStats)
    (decl : VInductDecl) (depth : Nat) where
  headers : HeaderCertificate env decl
  levels : stats.levels.length = decl.uvars
  uvars : Us.length = decl.uvars
  consts : stats.indConsts =
    (decl.types.map fun type => .const type.name stats.levels).toArray
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv
  parameterScope : VLCtx
  ambientScope : VLCtx
  scopeDecomposition : Δ = ambientScope ++ parameterScope
  ambientLength : ambientScope.length = depth
  cachedScope : List.Forall₂
    checkInductiveTypes.loopType.CachedParameterDecl
    stats.params.toList.reverse parameterScope
  runtimeScope : checkInductiveTypes.loopType.NarrowRuntimeScope
    env Us parameterScope Δ
  paramsContext : VEnv.IsDefEqCtx env Us.length []
    headers.params.reverse parameterScope.toCtx
  narrowParams : List.Forall₂ (TrExprS env Us parameterScope)
    stats.params.toList (decl.paramVars 0)

private theorem forall₂_trExprS_mono {env env' : VEnv}
    (henv : env ≤ env') :
    ∀ {es : List Expr} {es' : List VExpr},
      List.Forall₂ (TrExprS env Us Δ) es es' →
      List.Forall₂ (TrExprS env' Us Δ) es es'
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons (h.mono henv)
      (forall₂_trExprS_mono henv hs)

def MaterializedHeaderResult.mono {env env' : VEnv}
    (henv : env ≤ env')
    (H : MaterializedHeaderResult env Us Δ stats decl depth) :
    MaterializedHeaderResult env' Us Δ stats decl depth where
  headers := H.headers.mono henv
  levels := H.levels
  uvars := H.uvars
  consts := H.consts
  indices := H.indices
  params := forall₂_trExprS_mono henv H.params
  paramFVars := H.paramFVars
  parameterScope := H.parameterScope
  ambientScope := H.ambientScope
  scopeDecomposition := H.scopeDecomposition
  ambientLength := H.ambientLength
  cachedScope := H.cachedScope
  runtimeScope := H.runtimeScope.mono henv
  paramsContext := H.paramsContext.mono henv
  narrowParams := forall₂_trExprS_mono henv H.narrowParams

/-- Fold the verified noninitial step over the remainder of the mutual block.
At exact coverage the executable length assertions are discharged and the
metadata-free declaration is materialized together with its header
certificate. -/
theorem laterSteps.materialize
    {skeleton : VInductDeclSkeleton} {commonParams : List VExpr}
    {commonLevel : VLevel} {metadata : List (Nat × VLevel)}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeleton Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton)
    (hdone : dIdx ≤ indTypes.size)
    (hpositive : 0 < dIdx)
    (hlevels : stats.levels.length = c.lparams.length)
    (hindices : stats.nindices.size = dIdx)
    (hconsts : stats.indConsts.size = dIdx)
    (hindicesExact : stats.nindices.toList = metadata.map Prod.fst)
    (hconstsExact : stats.indConsts =
      ((skeleton.types.take dIdx).map fun type =>
        .const type.name stats.levels).toArray)
    (hparams : stats.params.size = skeleton.nparams)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats skeleton.nparams depth)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hprefix : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
      Hc.venv skeleton commonParams commonLevel metadata dIdx)
    (Hambient : checkInductiveTypes.loopType.AmbientParamContext
      Hc commonParams depth)
    (hcommon : VLevel.ofLevel c.lparams stats.resultLevel =
      some commonLevel)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth' : Nat},
      (Hc' : ContextWF c') →
      TrInductDecl Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe decl →
      MaterializedHeaderResult Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' decl depth' →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
      dIdx stats k c).WF Q := by
  by_cases hidx : dIdx < indTypes.size
  · have hnonempty : stats.indConsts.isEmpty = false := by
      cases hempty : stats.indConsts.isEmpty
      · rfl
      · have hzero : stats.indConsts.size = 0 := by
          simpa [Array.isEmpty] using hempty
        omega
    have htargetIdx : dIdx < skeleton.types.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeleton.types_length Hdecl]
      simpa using hidx
    have hname := Lean4Lean.VerifyInductive.TrInductDeclSkeleton.typeNameAt
      Hdecl dIdx (by simpa using hidx) htargetIdx
    have hname' : indTypes[dIdx].name = skeleton.types[dIdx].name := by
      simpa using hname
    apply laterStep.extendsPrefix k Q Hc Hdecl hidx hpositive hnonempty
      hparams Hcache Hsuffix Hprefix Hambient hcommon hconsume
    intro c' nindices resultSort resultLevel Hc' hlparams' Hdecl'
      Hcache' Hsuffix' Hprefix' Hambient'
    apply laterSteps.materialize k Q Hc' Hdecl'
      (dIdx := dIdx + 1) (depth := depth + nindices)
      (stats := updatedStats stats stats.lctx resultSort false nindices
        indTypes[dIdx].name)
      (metadata := metadata ++ [(nindices, resultLevel)])
      (commonParams := commonParams) (commonLevel := commonLevel)
    · omega
    · omega
    · simpa [updatedStats, hlparams'] using hlevels
    · simp [updatedStats, hindices]
    · simp [updatedStats, hconsts]
    · simp [updatedStats, hindicesExact]
    · rw [List.take_succ_eq_append_getElem]
      · simp [updatedStats, hconstsExact, hname']
      · rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeleton.types_length Hdecl]
        simpa using hidx
    · simpa [updatedStats] using hparams
    · exact Hcache'
    · exact Hsuffix'
    · exact Hprefix'
    · exact Hambient'
    · simpa [updatedStats, hlparams'] using hcommon
    · exact hconsume
    · intro c'' stats'' decl depth'' Hc'' Hdecl'' Hresult
      exact Hfinish Hc'' Hdecl'' Hresult
  · have heq : dIdx = indTypes.size := by omega
    have htypes : skeleton.types.length = indTypes.size := by
      rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeleton.types_length Hdecl]
      simp
    have Hprefix' : checkInductiveTypes.loopType.SynthesizedHeaderPrefix
        Hc.venv skeleton commonParams commonLevel metadata
          skeleton.types.length := by
      simpa [heq, htypes] using Hprefix
    rcases Hprefix'.materializes with
      ⟨decl, hmaterialize, _⟩
    let Hheaders := Hprefix'.complete hmaterialize
    have hfields := VInductDeclSkeleton.materialize_fields hmaterialize
    have herase := VInductDeclSkeleton.materialize_toSkeleton hmaterialize
    have Hdecl' :=
      Lean4Lean.VerifyInductive.TrInductDeclSkeleton.materialized
        Hdecl hmaterialize
    apply checkInductiveTypes.loopInd.result.WF
      (k := k) (Q := Q) hidx hlevels
    · simpa [heq] using hindices
    · simpa [heq] using hconsts
    · exact hparams
    · apply Hfinish (depth' := depth) Hc Hdecl'
      refine {
        headers := Hheaders
        levels := ?_
        uvars := ?_
        consts := ?_
        indices := ?_
        params := ?_
        paramFVars := Hcache.paramFVars
        parameterScope := Hsuffix.parameterDecls
        ambientScope := Hsuffix.ambientDecls
        scopeDecomposition := Hsuffix.context
        ambientLength := Hsuffix.prefixLength
        cachedScope := Hsuffix.cached
        runtimeScope :=
          checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
            Hc Hsuffix
        paramsContext := ?_
        narrowParams := ?_ }
      · exact hlevels.trans (Hdecl.2.1.symm.trans hfields.1.symm)
      · exact Hdecl.2.1.symm.trans hfields.1.symm
      · have hconstMap :
            (decl.types.map fun type => Expr.const type.name stats.levels) =
              (skeleton.types.map fun type =>
                Expr.const type.name stats.levels) := by
          have := congrArg (fun d : VInductDeclSkeleton =>
            d.types.map fun type => Expr.const type.name stats.levels) herase
          simpa [VInductDecl.toSkeleton, VInductiveType.toSkeleton,
            Function.comp_def] using this
        calc
          stats.indConsts =
              (skeleton.types.map fun type =>
                .const type.name stats.levels).toArray := by
            have hd : dIdx = skeleton.types.length := heq.trans htypes.symm
            simpa [hd] using hconstsExact
          _ = (decl.types.map fun type =>
                .const type.name stats.levels).toArray := by
            rw [hconstMap]
      · have hmetadata : metadata.map Prod.fst =
            decl.types.map (·.numIndices) := by
          have zipIndices : ∀ (types : List VInductiveTypeSkeleton)
              (data : List (Nat × VLevel)), data.length = types.length →
              (List.zipWith (fun type datum =>
                type.toVInductiveType datum.1 datum.2) types data).map
                  (·.numIndices) = data.map Prod.fst := by
            intro types data hlength
            induction types generalizing data with
            | nil => simpa using hlength
            | cons type types ih =>
              cases data with
              | nil => simp at hlength
              | cons datum data =>
                simp only [List.length_cons] at hlength
                change datum.1 ::
                    (List.zipWith (fun type datum =>
                      type.toVInductiveType datum.1 datum.2)
                      types data).map (·.numIndices) =
                    datum.1 :: data.map Prod.fst
                exact congrArg (List.cons datum.1) (ih data (by omega))
          have hmetadataLength :=
            VInductDeclSkeleton.materialize_length hmaterialize
          simp only [VInductDeclSkeleton.materialize] at hmaterialize
          split at hmaterialize
          · simp only [Option.some.injEq] at hmaterialize
            subst decl
            exact (zipIndices skeleton.types metadata hmetadataLength).symm
          · contradiction
        exact hindicesExact.trans hmetadata
      · have Hcache' : checkInductiveTypes.loopType.ParameterCachePrefix
            Hc.venv c.lparams Hc.mlctx.vlctx stats decl.nparams depth := by
          rw [hfields.2.1]
          exact Hcache
        exact Hcache'.complete
      · apply Hsuffix.paramsDefEq Hambient
        exact Hprefix.parameterCount.trans hparams.symm
      · rw [← checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl]
        have hsize : stats.params.size = decl.nparams := by
          exact hparams.trans hfields.2.1.symm
        simpa [hsize] using Hsuffix.narrowParams
termination_by indTypes.size - dIdx

def MaterializedHeaderResult.parameterSuffix
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : MaterializedHeaderResult Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth) :
    checkInductiveTypes.loopType.ParameterContextSuffix Hc stats depth where
  ambientDecls := H.ambientScope
  parameterDecls := H.parameterScope
  context := H.scopeDecomposition
  prefixLength := H.ambientLength
  cached := H.cachedScope
  narrowParams := by
    have hsize : stats.params.size = decl.nparams := by
      have hlength :=
        Lean4Lean.VerifyInductive.List.Forall₂.length_eq' H.narrowParams
      simpa [VInductDecl.paramVars] using hlength
    rw [hsize,
      checkInductiveTypes.loopType.cachedParamVars_eq_paramVars decl]
    exact H.narrowParams

/-- Complete the whole nonempty mutual-header phase, including the special
first header that establishes the common parameters and result universe. -/
theorem firstStep.materialize
    {skeleton : VInductDeclSkeleton}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeleton Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton)
    (hctx : Hc.mlctx.vlctx = [])
    (hidx : 0 < indTypes.size)
    (hempty : stats.indConsts.isEmpty = true)
    (hlevels : stats.levels.length = c.lparams.length)
    (hnindices : stats.nindices = #[])
    (hconsts : stats.indConsts = #[])
    (hparams : stats.params = #[])
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth' : Nat},
      (Hc' : ContextWF c') →
      TrInductDecl Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe decl →
      MaterializedHeaderResult Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' decl depth' →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes 0
      stats k c).WF Q := by
  apply firstStep.initializesPrefix k Q Hc Hdecl hctx hidx hempty hparams
    hconsume
  intro c' stats' nindices resultSort resultLevel params Hc' hlparams'
    hlevels' hnindices' hconsts' Hdecl' hofLevel Hcache' Hsuffix'
    Hprefix' Hambient'
  let statsNext := updatedStats stats' c'.lctx resultSort true nindices
    indTypes[0].name
  have hparamSize : stats'.params.size = skeleton.nparams := by
    have hlength :=
      Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Hcache'.params
    simpa using hlength
  have hskeletonIdx : 0 < skeleton.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDeclSkeleton.types_length Hdecl']
    simpa using hidx
  have hname := Lean4Lean.VerifyInductive.TrInductDeclSkeleton.typeNameAt
    Hdecl' 0 (by simpa using hidx) hskeletonIdx
  have hname' : indTypes[0].name = skeleton.types[0].name := by
    simpa using hname
  apply laterSteps.materialize k Q Hc' Hdecl'
    (dIdx := 1) (depth := nindices) (stats := statsNext)
    (metadata := [(nindices, resultLevel)])
    (commonParams := params) (commonLevel := resultLevel)
  · omega
  · omega
  · simpa [statsNext, updatedStats, hlevels', hlparams'] using hlevels
  · simp [statsNext, updatedStats, hnindices', hnindices]
  · simp [statsNext, updatedStats, hconsts', hconsts]
  · simp [statsNext, updatedStats, hnindices', hnindices]
  · rw [List.take_succ_eq_append_getElem hskeletonIdx]
    simp [statsNext, updatedStats, hconsts', hconsts, hname']
  · simpa [statsNext, updatedStats] using hparamSize
  · exact Hcache'.reindex (by simp [statsNext, updatedStats])
  · exact Hsuffix'.reindex (by simp [statsNext, updatedStats])
  · exact Hprefix'
  · exact Hambient'
  · simpa [statsNext, updatedStats] using hofLevel
  · exact hconsume
  · exact Hfinish

/-- Public verifier for the executable mutual-header checker.  Successful
checking returns a materialized abstract declaration, its source translation,
and the independent header specification certificate to the continuation. -/
theorem checkInductiveTypes.materialize
    {skeleton : VInductDeclSkeleton}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDeclSkeleton Hc.venv c.lparams skeleton.nparams
      indTypes.toList isUnsafe skeleton)
    (hctx : Hc.mlctx.vlctx = [])
    (hnonempty : 0 < indTypes.size)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (Hfinish : ∀ {c' : AddInductive.Context}
      {stats' : AddInductive.InductiveStats} {decl : VInductDecl}
      {depth : Nat},
      (Hc' : ContextWF c') →
      TrInductDecl Hc'.venv c'.lparams skeleton.nparams
        indTypes.toList isUnsafe decl →
      MaterializedHeaderResult Hc'.venv c'.lparams Hc'.mlctx.vlctx
        stats' decl depth →
      (k stats' c').WF Q) :
    (AddInductive.checkInductiveTypes skeleton.nparams indTypes k c).WF Q := by
  change (AddInductive.checkInductiveTypes.loopInd skeleton.nparams indTypes
    0 { (default : AddInductive.InductiveStats) with
      levels := c.lparams.map .param } k c).WF Q
  apply firstStep.materialize k Q Hc Hdecl hctx hnonempty
  · rfl
  · simp
  · rfl
  · rfl
  · rfl
  · exact hconsume
  · exact Hfinish

/-- Indexed declaration-facing form of `stepPrefix.WF`.  Besides the checked
source translation, the continuation receives the exact corresponding
abstract mutual header and the environment obtained by installing all header
constants. -/
theorem stepPrefix.refinesTrInduct
    {decl : VInductDecl}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hc : ContextWF c)
    (Hdecl : TrInductDecl Hc.venv c.lparams nparams
      indTypes.toList isUnsafe decl)
    (hidx : dIdx < indTypes.size)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[dIdx].type checkedType type' checkedType' →
      ∀ envTypes,
        Hc.venv.addConsts decl.typeConstants = some envTypes →
        ∀ target,
        decl.types[dIdx]? = some target →
        TrInductiveType Hc.venv envTypes c.lparams
          indTypes[dIdx] target →
      ∀ normalized,
        FVarsBelow Hc.mlctx.vlctx indTypes[dIdx].type normalized →
        TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
        (AddInductive.checkInductiveTypes.loopType nparams stats normalized 0 0
          c.fuel.inductiveFuel (fun type stats nindices =>
            show AddInductive.M _ from do
            let type ← TypeChecker.ensureSort type
            let mut stats := stats
            let resultLevel := type.sortLevel!
            if stats.indConsts.isEmpty then
              let lctx := (← read).lctx
              stats := { stats with
                lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
            else if !resultLevel.isEquiv stats.resultLevel then
              throw <| .other
                "mutually inductive types must live in the same universe"
            stats := { stats with
              nindices := stats.nindices.push nindices
              indConsts := stats.indConsts.push
                (.const indTypes[dIdx].name stats.levels) }
            AddInductive.checkInductiveTypes.loopInd nparams indTypes
              (dIdx + 1) stats k) c).WF Q) :
    (AddInductive.checkInductiveTypes.loopInd nparams indTypes dIdx stats k c).WF Q := by
  have htarget : dIdx < decl.types.length := by
    rw [← Lean4Lean.VerifyInductive.TrInductDecl.types_length Hdecl]
    simpa using hidx
  rcases Lean4Lean.VerifyInductive.TrInductDecl.typeAt Hdecl dIdx
      (by simpa using hidx) htarget with
    ⟨envTypes, htypes, htargetTr⟩
  apply stepPrefix.WF (nparams := nparams) (stats := stats) (k := k)
    (Q := Q) Hc hidx
  intro checkedType type' checkedType' hchecked normalized hscope hnormalized
  exact Hloop checkedType type' checkedType' hchecked envTypes htypes
    decl.types[dIdx] (by simp [htarget]) (by simpa using htargetTr)
    normalized hscope hnormalized

end checkInductiveTypes.loopInd

namespace checkConstructors.loopCtors

theorem result.WF
    (hidx : ¬ ctorIdx < ctors.length) (hQ : Q ()) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtors, dif_neg hidx]
  exact Except.WF.pure hQ

/-- One constructor-loop iteration up to the already verified telescope
checker. The continuation receives the closed source translation before
choosing the public `CtorShape` refinement. -/
theorem stepPrefix.WF
    (Hc : ContextWF c) (hidx : ctorIdx < ctors.length)
    (hfresh : foundCtors.contains ctors[ctorIdx].name = false)
    (Hloop : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtors, dif_pos hidx]
  rw [if_neg (by simpa using hfresh)]
  exact (checkClosedType.WF Hc).bind fun _ hchecked => by
    rcases hchecked with ⟨type', checkedType', hchecked⟩
    change ((read : AddInductive.M AddInductive.Context) c >>= fun c' =>
      ((AddInductive.checkConstructors.loopCtor stats isUnsafe
          ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
          c'.fuel.inductiveFuel >>= fun _ =>
        AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
          (foundCtors.insert ctors[ctorIdx].name)) : AddInductive.M Unit) c).WF Q
    have hread : ((read : AddInductive.M AddInductive.Context) c).WF
        (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine hread.bind fun c' hc' => ?_
    subst c'
    exact (Hloop _ type' checkedType' hchecked).bind fun _ hnext => hnext

/-- Shape-producing constructor step. This is the interface used by the
flattened constructor-prefix accumulator; all telescope details remain local
to `Hshape`. -/
theorem stepShape.WF
    {decl : VInductDecl} {target : VInductiveType} {ctor' : VConstVal}
    {envTypes : VEnv} {params : List VExpr}
    (Hc : ContextWF c) (hidx : ctorIdx < ctors.length)
    (hfresh : foundCtors.contains ctors[ctorIdx].name = false)
    (Hshape : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
          decl.CtorShape envTypes params target ctor')
    (Hnext : decl.CtorShape envTypes params target ctor' →
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  apply stepPrefix.WF (stats := stats) (isUnsafe := isUnsafe)
    (targetIdx := targetIdx) (Q := Q) Hc hidx hfresh
  intro checkedType type' checkedType' hchecked
  exact (Hshape checkedType type' checkedType' hchecked).mono fun _ hshape =>
    Hnext hshape

theorem stepCertificate.WF
    {decl : VInductDecl} {target : VInductiveType} {ctor' : VConstVal}
    {envTypes : VEnv} {params : List VExpr} {done : Nat}
    (Hc : ContextWF c)
    (Hprefix : ConstructorPrefixCertificate Hc.venv decl envTypes params done)
    (hdone : done < decl.ownedConstructors.length)
    (howned : decl.ownedConstructors[done] = (target, ctor'))
    (hidx : ctorIdx < ctors.length)
    (hfresh : foundCtors.contains ctors[ctorIdx].name = false)
    (Hshape : ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        ctors[ctorIdx].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        ctors[ctorIdx].name targetIdx ctors[ctorIdx].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
          decl.CtorShape envTypes params target ctor')
    (Hnext : ConstructorPrefixCertificate Hc.venv decl envTypes params
        (done + 1) →
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        ctors (ctorIdx + 1)
        (foundCtors.insert ctors[ctorIdx].name) c).WF Q) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      ctors ctorIdx foundCtors c).WF Q := by
  apply stepShape.WF (decl := decl) (target := target) (ctor' := ctor')
    (stats := stats) (isUnsafe := isUnsafe) (targetIdx := targetIdx)
    (Q := Q) Hc hidx hfresh Hshape
  intro hshape
  have hshape' : decl.CtorShape envTypes params
      decl.ownedConstructors[done].1 decl.ownedConstructors[done].2 := by
    rw [howned]
    exact hshape
  exact Hnext (Hprefix.push hdone hshape')

/-- Complete the production constructor loop for one family.  Name-set
freshness is exposed against the exact reachable state, while semantic shape
checking is supplied one translated constructor at a time. -/
theorem refinesType
    {decl : VInductDecl} {target : VInductiveType}
    {sourceEnv envTypes : VEnv} {params : List VExpr}
    {source : InductiveType}
    (Q : Unit → Prop)
    (Hc : ContextWF c)
    (Htarget : TrInductiveType sourceEnv envTypes c.lparams source target)
    (Hnames : ConstructorNameState source.ctors ctorIdx foundCtors)
    (Hprefix : ConstructorTypePrefix envTypes decl params target ctorIdx)
    (Hfresh : ∀ {i found}, ConstructorNameState source.ctors i found →
      (hi : i < source.ctors.length) →
      found.contains source.ctors[i].name = false)
    (Hshape : ∀ i (hsource : i < source.ctors.length)
      (htarget : i < target.ctors.length),
      TrSourceConst envTypes c.lparams source.ctors[i].name
        source.ctors[i].type target.ctors[i] →
      ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        source.ctors[i].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        source.ctors[i].name targetIdx source.ctors[i].type 0
        c.fuel.inductiveFuel c).WF fun _ =>
          decl.CtorShape envTypes params target target.ctors[i])
    (Hfinish : ConstructorTypePrefix envTypes decl params target
        target.ctors.length →
      Q ()) :
    (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
      source.ctors ctorIdx foundCtors c).WF Q := by
  by_cases hidx : ctorIdx < source.ctors.length
  · have htarget : ctorIdx < target.ctors.length := by
      rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htarget]
      exact hidx
    have Hctor := Lean4Lean.VerifyInductive.TrInductiveType.ctorAt
      Htarget ctorIdx hidx htarget
    apply stepShape.WF (decl := decl) (target := target)
      (ctor' := target.ctors[ctorIdx]) (Q := Q) Hc hidx
      (Hfresh Hnames hidx)
    · intro checkedType type' checkedType' hchecked
      exact Hshape ctorIdx hidx htarget Hctor checkedType type'
        checkedType' hchecked
    · intro hshape
      exact refinesType Q Hc Htarget (.succ Hnames hidx)
        (Hprefix.push htarget hshape) Hfresh Hshape Hfinish
  · have heq : ctorIdx = source.ctors.length := by
      have := Hprefix.covered
      rw [← Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htarget]
        at this
      omega
    apply result.WF (Q := Q) hidx
    have Hcomplete : ConstructorTypePrefix envTypes decl params target
        target.ctors.length := by
      simpa [heq,
        Lean4Lean.VerifyInductive.TrInductiveType.ctors_length Htarget] using
          Hprefix
    exact Hfinish Hcomplete
termination_by source.ctors.length - ctorIdx

end checkConstructors.loopCtors

namespace checkConstructors.loopTypes

theorem result.WF
    (hidx : ¬ targetIdx < indTypes.size) (hQ : Q ()) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  rw [AddInductive.checkConstructors.loopTypes, dif_neg hidx]
  exact Except.WF.pure hQ

theorem step.WF
    (hidx : targetIdx < indTypes.size)
    (Hctors :
      (AddInductive.checkConstructors.loopCtors stats isUnsafe targetIdx
        indTypes[targetIdx].ctors 0 {} c).WF fun _ =>
      (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
        (targetIdx + 1) c).WF Q) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  rw [AddInductive.checkConstructors.loopTypes, dif_pos hidx]
  exact Hctors.bind fun _ hnext => hnext

/-- Fold the verified inner constructor traversal over every family in a
mutual block, retaining the same two-dimensional order as the source arrays. -/
theorem refinesBlock
    {decl : VInductDecl} {sourceEnv envTypes : VEnv}
    {params : List VExpr}
    (Q : Unit → Prop)
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveType sourceEnv envTypes c.lparams)
      indTypes.toList decl.types)
    (Hprefix : ConstructorTypesPrefix envTypes decl params targetIdx)
    (Hfresh : ∀ targetIdx (htarget : targetIdx < indTypes.size)
      {i found}, ConstructorNameState indTypes[targetIdx].ctors i found →
      (hi : i < indTypes[targetIdx].ctors.length) →
      found.contains indTypes[targetIdx].ctors[i].name = false)
    (Hshape : ∀ targetIdx (hsource : targetIdx < indTypes.size)
      (htarget : targetIdx < decl.types.length)
      i (hctorSource : i < indTypes[targetIdx].ctors.length)
      (hctorTarget : i < decl.types[targetIdx].ctors.length),
      TrSourceConst envTypes c.lparams indTypes[targetIdx].ctors[i].name
        indTypes[targetIdx].ctors[i].type decl.types[targetIdx].ctors[i] →
      ∀ checkedType type' checkedType',
      TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
        indTypes[targetIdx].ctors[i].type checkedType type' checkedType' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe
        indTypes[targetIdx].ctors[i].name targetIdx
        indTypes[targetIdx].ctors[i].type 0 c.fuel.inductiveFuel c).WF
        fun _ => decl.CtorShape envTypes params decl.types[targetIdx]
          decl.types[targetIdx].ctors[i])
    (Hfinish : ConstructorTypesPrefix envTypes decl params
        decl.types.length → Q ()) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
      targetIdx c).WF Q := by
  by_cases hidx : targetIdx < indTypes.size
  · have htarget : targetIdx < decl.types.length := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
      omega
    have Htarget : TrInductiveType sourceEnv envTypes c.lparams
        indTypes[targetIdx] decl.types[targetIdx] := by
      have Htarget' := Lean4Lean.VerifyInductive.List.Forall₂.getElem Htypes
        targetIdx (by simpa using hidx) htarget
      rw [Array.getElem_toList] at Htarget'
      exact Htarget'
    apply step.WF (Q := Q) hidx
    apply checkConstructors.loopCtors.refinesType
      (Q := fun _ =>
        (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe
          (targetIdx + 1) c).WF Q)
      Hc Htarget .zero
      (ConstructorTypePrefix.empty envTypes decl params decl.types[targetIdx])
      (Hfresh targetIdx hidx)
    · intro i hsource htarget' Hctor checkedType type' checkedType' hchecked
      exact Hshape targetIdx hidx htarget i hsource htarget' Hctor
        checkedType type' checkedType' hchecked
    · intro Htype
      exact refinesBlock Q Hc Htypes
        (Hprefix.push htarget Htype) Hfresh Hshape Hfinish
  · have heq : targetIdx = indTypes.size := by
      have hlength : indTypes.size = decl.types.length := by
        simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
      have := Hprefix.covered
      omega
    apply result.WF (Q := Q) hidx
    apply Hfinish
    have hlength : indTypes.size = decl.types.length := by
      simpa using Lean4Lean.VerifyInductive.List.Forall₂.length_eq' Htypes
    simpa [heq, hlength] using Hprefix
termination_by indTypes.size - targetIdx

end checkConstructors.loopTypes

namespace checkConstructors.loopCtor

theorem zero.WF :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i 0 c).WF Q := by
  intro _ h
  simp [AddInductive.checkConstructors.loopCtor] at h

/-- A constructor telescope ending in the checked target application returns
success; the separate application-refinement theorem will connect
`isValidIndAppIdx` to `VInductDecl.ValidIndAppAt`. -/
theorem result.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = true)
    (hQ : Q ()) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkConstructors.loopCtor]
  all_goals exact Except.WF.pure hQ

/-- An invalid non-forall constructor target is rejected. -/
theorem invalidResult.WF
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = false) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkConstructors.loopCtor]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Common-parameter branch of a constructor telescope.  The cached parameter
type comparison is converted directly into abstract body instantiation. -/
theorem parameter.sourceWF
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = some param)
    (hget : (AddInductive.getType param c).WF (fun ty => ty = paramTy))
    (hdom : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom dom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam dom') :: Hc.mlctx.vlctx) body body')
    (hparamTy : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx paramTy paramTy')
    (hparam : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx param param')
    (hparamType : Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
      param' paramTy')
    (Hrec : Hc.venv.IsDefEqU c.lparams.length Hc.mlctx.vlctx.toCtx
        dom' paramTy' →
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx
        (body.instantiate1 param) (body'.inst param') →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        (body.instantiate1 param) (i + 1) fuel c).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  change (AddInductive.getType param c >>= fun paramTy =>
    ((do
      unless ← TypeChecker.isDefEq dom paramTy do
        throw <| .other
          s!"arg #{i + 1} of '{ctor}' does not match inductive datatype parameters"
      AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        (body.instantiate1 param) (i + 1) fuel) : AddInductive.M _) c).WF Q
  refine hget.bind fun paramTy' hparamTyEq => ?_
  subst paramTy'
  refine (isDefEqInContext.WF Hc hdom hparamTy).bind fun equal hequal => ?_
  cases equal
  · change (Except.error _).WF Q
    exact Except.WF.throw
  · have heq := hequal rfl
    have hopened := Hc.instantiateDefEq hbody hparam hparamType heq
    exact Hrec heq hopened

/-- Safe constructor-field branch.  Successful field typing, the executable
universe bound, positivity, annotation transport, and fresh body opening are
all delivered to the recursive continuation. -/
theorem safeField.sourceWF
    {Pos : Prop}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hpos : (AddInductive.checkPositivity stats dom ctor i c).WF (fun _ => Pos))
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      Pos →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  refine (ensureTypeInContext.WF Hc Hdom.source).bind fun fieldSort hfield => ?_
  rcases hfield with ⟨fieldType', hfieldType, fieldLevel, fieldLevel', rfl,
    hfieldLevel, hfieldHasType⟩
  change ((do
    unless stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel! do
      throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
        is too big for the corresponding inductive datatype"
    if !false then
      AddInductive.checkPositivity stats dom ctor i
    withLocalDecl name bi dom.consumeTypeAnnotations fun arg =>
      AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
        (body.instantiate1 arg) (i + 1) fuel) : AddInductive.M Unit) c |>.WF Q
  by_cases hbound :
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true
  · rw [if_pos hbound]
    refine Hpos.bind fun _ hpos => ?_
    rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
    refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
      (k := fun arg =>
        AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 arg) (i + 1) fuel)
      Hc Hdom.consumed Hdom.isType ?_
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
      Hdom.consumed Hdom.isType
    have hopened := Hc.instantiateFresh (name := name) (bi := bi)
      Hdom.consumed Hdom.isType hbody''
    exact Hrec fieldType' fieldLevel fieldLevel' hfieldType hfieldLevel
      hfieldHasType hbound hpos body'' hbodyEq hopened
  · rw [if_neg hbound]
    change (Except.error _).WF Q
    exact Except.WF.throw

/-- Unsafe constructor-field branch: the same source typing, universe, and
annotation obligations apply, while positivity is intentionally skipped. -/
theorem unsafeField.sourceWF
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF Q := by
  rw [AddInductive.checkConstructors.loopCtor]
  rw [hparamAt]
  refine (ensureTypeInContext.WF Hc Hdom.source).bind fun fieldSort hfield => ?_
  rcases hfield with ⟨fieldType', hfieldType, fieldLevel, fieldLevel', rfl,
    hfieldLevel, hfieldHasType⟩
  change ((do
    unless stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel! do
      throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
        is too big for the corresponding inductive datatype"
    if !true then
      AddInductive.checkPositivity stats dom ctor i
    withLocalDecl name bi dom.consumeTypeAnnotations fun arg =>
      AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
        (body.instantiate1 arg) (i + 1) fuel) : AddInductive.M Unit) c |>.WF Q
  by_cases hbound :
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true
  · rw [if_pos hbound]
    rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
    refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
      (k := fun arg =>
        AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 arg) (i + 1) fuel)
      Hc Hdom.consumed Hdom.isType ?_
    let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
      Hdom.consumed Hdom.isType
    have hopened := Hc.instantiateFresh (name := name) (bi := bi)
      Hdom.consumed Hdom.isType hbody''
    exact Hrec fieldType' fieldLevel fieldLevel' hfieldType hfieldLevel
      hfieldHasType hbound body'' hbodyEq hopened
  · rw [if_neg hbound]
    change (Except.error _).WF Q
    exact Except.WF.throw

end checkConstructors.loopCtor

namespace checkPositivityStep

theorem hasIndOcc_eq_findAny :
    AddInductive.hasIndOcc indConsts type =
      type.findAny (fun
        | .const name _ => indConsts.any fun I => I.constName! == name
        | _ => false) := by
  unfold AddInductive.hasIndOcc
  exact Expr.find?_isSome_eq_findAny _ _

def IndConstNames (indConsts : Array Expr) (names : List Name) : Prop :=
  ∀ name, (indConsts.any fun I => I.constName! == name) = names.contains name

/-- The concrete array accumulated by header checking has exactly the abstract
mutual-family names, in declaration order.  Keeping this stronger structural
fact separate makes the weaker search correspondence above reusable by both
positivity and recursive-target validation. -/
structure IndConstArray (levels : List Level) (indConsts : Array Expr)
    (names : List Name) : Prop where
  exact : indConsts = (names.map fun name => .const name levels).toArray
  names : IndConstNames indConsts names

/-- The portion of the mutable header statistics needed to interpret a
recursive application in the independent declaration.  In particular, the
common parameters are related by expression translation rather than merely by
array position. -/
structure ValidAppStatsWF (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) : Prop where
  levels : stats.levels.length = decl.uvars
  uvars : Us.length = decl.uvars
  consts : IndConstArray stats.levels stats.indConsts
    (decl.types.map (·.name))
  indices : stats.nindices.toList = decl.types.map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

theorem forall₂_length_eq
    (H : List.Forall₂ R as bs) : as.length = bs.length := by
  induction H with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem List.mapM_some_length
    {xs : List α} {ys : List β} {f : α → Option β}
    (H : xs.mapM f = some ys) :
    xs.length = ys.length := by
  induction xs generalizing ys with
  | nil =>
    simp at H
    subst ys
    rfl
  | cons x xs ih =>
    cases hx : f x <;> simp [hx] at H
    rename_i y
    cases hxs : xs.mapM f <;> simp [hxs] at H
    rename_i ys'
    subst ys
    simp [ih hxs]

theorem forall₂_get?_eq_some
    {R : α → β → Prop} {as : List α} {bs : List β}
    {i : Nat} {a : α} {b : β}
    (H : List.Forall₂ R as bs)
    (ha : as[i]? = some a) (hb : bs[i]? = some b) : R a b := by
  induction H generalizing i with
  | nil => simp at ha
  | cons h _ ih =>
    cases i with
    | zero =>
      simp at ha hb
      subst a
      subst b
      exact h
    | succ i => exact ih (by simpa using ha) (by simpa using hb)

theorem ValidAppStatsWF.params_size
    (H : ValidAppStatsWF env Us Δ stats decl depth) :
    stats.params.size = decl.nparams := by
  have := forall₂_length_eq H.params
  simpa [VInductDecl.paramVars] using this

theorem ValidAppStatsWF.types_size
    (H : ValidAppStatsWF env Us Δ stats decl depth) :
    stats.indConsts.size = decl.types.length := by
  rw [H.consts.exact]
  simp

theorem ValidAppStatsWF.indConstAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < decl.types.length) :
    stats.indConsts[i]? = some (.const decl.types[i].name stats.levels) := by
  rw [H.consts.exact]
  simp [hi]

theorem ValidAppStatsWF.nindicesAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < decl.types.length) :
    stats.nindices[i]? = some decl.types[i].numIndices := by
  rw [← Array.getElem?_toList, H.indices]
  simp [hi]

theorem ValidAppStatsWF.paramAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < stats.params.size) :
    ∃ param', (decl.paramVars depth)[i]? = some param' ∧
      TrExprS env Us Δ stats.params[i] param' := by
  have hsource : stats.params.toList[i]? = some stats.params[i] := by
    simp [hi]
  have htarget : ∃ param', (decl.paramVars depth)[i]? = some param' := by
    have hi' : i < (decl.paramVars depth).length := by
      have hlen := forall₂_length_eq H.params
      simpa using hlen ▸ hi
    exact ⟨(decl.paramVars depth)[i], List.getElem?_eq_getElem hi'⟩
  rcases htarget with ⟨param', htarget⟩
  exact ⟨param', htarget,
    forall₂_get?_eq_some H.params hsource htarget⟩

theorem ValidAppStatsWF.paramFVarAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : i < stats.params.size) :
    ∃ fv, stats.params[i] = .fvar fv := by
  exact H.paramFVars _ (by simp)

theorem forall₂_map_right
    (H : List.Forall₂ R as bs)
    (hf : ∀ {a b}, R a b → S a (f b)) :
    List.Forall₂ S as (bs.map f) := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (hf h) ih

@[simp] theorem VInductDecl.paramVars_liftN
    {decl : VInductDecl} {depth : Nat} :
    (decl.paramVars depth).map (fun e => VExpr.liftN 1 e 0) =
      decl.paramVars (depth + 1) := by
  simp [VInductDecl.paramVars, VExpr.liftN]
  omega

theorem ValidAppStatsWF.withLocalDecl
    (Hc : ContextWF c)
    (H : ValidAppStatsWF Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ValidAppStatsWF
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats decl (depth + 1) := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  have W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 := by
    change VLCtx.FVLift Hc.mlctx.vlctx
      ((some (⟨c.ngen.curr⟩, ty.fvarsList), .vlam ty') ::
        Hc.mlctx.vlctx) 0 1 0
    exact .skip_fvar _ _ .refl
  have hparams := forall₂_map_right
    (f := fun e => VExpr.liftN 1 e 0)
    (S := TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
    H.params fun h =>
      h.weakFV Hc'.checking.tr.wf W Hc'.mlctx_wf.tr.wf
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := ?_
    paramFVars := H.paramFVars }
  change List.Forall₂ (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
    stats.params.toList (decl.paramVars (depth + 1))
  rw [← VInductDecl.paramVars_liftN]
  exact hparams

/-- Extend application statistics in an independently tracked semantic scope.
Unlike `withLocalDecl`, this theorem does not require the executable context
to be that scope; the already verified target-context extension is sufficient
for weakening the cached parameter translations. -/
theorem ValidAppStatsWF.withFVar
    (H : ValidAppStatsWF env Us scope stats decl depth)
    (henv : env.WF)
    (hscope' : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam fieldType) :: scope)) :
    ValidAppStatsWF env Us
      ((some (fv, deps), .vlam fieldType) :: scope)
      stats decl (depth + 1) := by
  let W : VLCtx.FVLift scope
      ((some (fv, deps), .vlam fieldType) :: scope) 0 1 0 :=
    .skip_fvar _ _ .refl
  have hparams := forall₂_map_right
    (f := fun e => VExpr.liftN 1 e 0)
    (S := TrExprS env Us
      ((some (fv, deps), .vlam fieldType) :: scope))
    H.params fun h => h.weakFV henv.ordered W hscope'
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := ?_
    paramFVars := H.paramFVars }
  rw [← VInductDecl.paramVars_liftN]
  exact hparams

theorem IndConstArray.empty (levels : List Level) :
    IndConstArray levels #[] [] where
  exact := rfl
  names := by simp [IndConstNames, Array.any]

theorem IndConstArray.push
    {levels : List Level} {indConsts : Array Expr} {names : List Name}
    (H : IndConstArray levels indConsts names) (newName : Name) :
    IndConstArray levels (indConsts.push (.const newName levels))
      (names ++ [newName]) where
  exact := by rw [H.exact]; simp
  names := by
    intro name
    rw [Array.any_push, H.names name]
    change (names.contains name || (newName == name)) =
      (names ++ [newName]).contains name
    rw [List.contains_append]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, List.contains_cons,
      List.contains_nil, Bool.or_false]
    exact eq_comm

theorem IndConstArray.ofExact
    {levels : List Level} {indConsts : Array Expr} {names : List Name}
    (h : indConsts = (names.map fun name => .const name levels).toArray) :
    IndConstArray levels indConsts names where
  exact := h
  names := by
    intro name
    apply Bool.eq_iff_iff.mpr
    simp [h]
    constructor
    · rintro ⟨source, hsource, hname⟩
      have : source = name := by
        simpa [Expr.constName!] using hname
      simpa [this] using hsource
    · intro hname
      exact ⟨name, hname, by simp [Expr.constName!]⟩

/-- Promote the exact traversal-facing statistics into the positivity-facing
application invariant. -/
def ValidAppStatsWF.ofMaterializedHeader
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      env Us Δ stats decl depth) :
    ValidAppStatsWF env Us Δ stats decl depth where
  levels := H.levels
  uvars := H.uvars
  consts := IndConstArray.ofExact (by
    simpa [List.map_map, Function.comp_def] using H.consts)
  indices := H.indices
  params := H.params
  paramFVars := H.paramFVars

def ValidAppStatsWF.ofMaterializedHeaderNarrow
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      env Us Δ stats decl depth) :
    ValidAppStatsWF env Us H.parameterScope stats decl 0 where
  levels := H.levels
  uvars := H.uvars
  consts := IndConstArray.ofExact (by
    simpa [List.map_map, Function.comp_def] using H.consts)
  indices := H.indices
  params := H.narrowParams
  paramFVars := H.paramFVars

theorem IndConstArray.updatedStats
    {stats : AddInductive.InductiveStats} {names : List Name}
    {lctx : LocalContext} {resultLevel : Level} {setResult : Bool}
    {nindices : Nat} {indName : Name}
    (H : IndConstArray stats.levels stats.indConsts names) :
    IndConstArray
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName).levels
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName).indConsts
      (names ++ [indName]) := by
  simpa using H.push indName

/-- Incremental form of `ValidAppStatsWF`, synchronized with the mutual-header
loop before all family members have been visited. -/
structure ValidAppStatsPrefix (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth done : Nat) : Prop where
  covered : done ≤ decl.types.length
  levels : stats.levels.length = decl.uvars
  uvars : Us.length = decl.uvars
  consts : IndConstArray stats.levels stats.indConsts
    ((decl.types.take done).map (·.name))
  indices : stats.nindices.toList =
    (decl.types.take done).map (·.numIndices)
  params : List.Forall₂ (TrExprS env Us Δ) stats.params.toList
    (decl.paramVars depth)
  paramFVars : ∀ param ∈ stats.params, ∃ fv, param = .fvar fv

/-- Convert the completed first-header telescope invariant into the initial
mutual-family statistics prefix, just before the first family constant and
index count are appended. -/
def ValidAppStatsPrefix.beforeFirst
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      env Us Δ stats decl.nparams depth)
    (hlevels : stats.levels.length = decl.uvars)
    (huvars : Us.length = decl.uvars)
    (hconsts : stats.indConsts = #[])
    (hindices : stats.nindices = #[]) :
    ValidAppStatsPrefix env Us Δ stats decl depth 0 where
  covered := Nat.zero_le _
  levels := hlevels
  uvars := huvars
  consts := by
    simpa [hconsts] using IndConstArray.empty stats.levels
  indices := by simp [hindices]
  params := Hcache.complete
  paramFVars := Hcache.paramFVars

theorem ValidAppStatsPrefix.withLocalDecl
    (Hc : ContextWF c)
    (H : ValidAppStatsPrefix Hc.venv c.lparams Hc.mlctx.vlctx
      stats decl depth done)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty') :
    ValidAppStatsPrefix
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).venv
      c.lparams
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty).mlctx.vlctx
      stats decl (depth + 1) done := by
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi) htr hty
  let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
    .skip_fvar _ _ .refl
  have hparams : List.Forall₂
      (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
      stats.params.toList (decl.paramVars (depth + 1)) := by
    rw [← VInductDecl.paramVars_liftN]
    exact forall₂_map_right H.params fun h =>
      h.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf
  exact {
    covered := H.covered
    levels := H.levels
    uvars := H.uvars
    consts := H.consts
    indices := H.indices
    params := hparams
    paramFVars := H.paramFVars }

theorem ValidAppStatsPrefix.push
    (H : ValidAppStatsPrefix env Us Δ stats decl depth done)
    (hindex : done < decl.types.length)
    (hname : indName = decl.types[done].name)
    (hnindices : nindices = decl.types[done].numIndices) :
    ValidAppStatsPrefix env Us Δ
      (checkInductiveTypes.loopInd.updatedStats stats lctx resultLevel
        setResult nindices indName)
      decl depth (done + 1) := by
  have htake : decl.types.take (done + 1) =
      decl.types.take done ++ [decl.types[done]] :=
    List.take_succ_eq_append_getElem hindex
  refine {
    covered := by omega
    levels := by simpa using H.levels
    uvars := H.uvars
    consts := ?_
    indices := ?_
    params := by simpa using H.params
    paramFVars := by simpa using H.paramFVars }
  · rw [htake, List.map_append]
    simpa [hname] using H.consts.updatedStats (lctx := lctx)
      (resultLevel := resultLevel) (setResult := setResult)
      (nindices := nindices) (indName := indName)
  · rw [htake, List.map_append]
    simp [H.indices, hnindices]

theorem ValidAppStatsPrefix.complete
    (H : ValidAppStatsPrefix env Us Δ stats decl depth decl.types.length) :
    ValidAppStatsWF env Us Δ stats decl depth := by
  refine {
    levels := H.levels
    uvars := H.uvars
    consts := ?_
    indices := ?_
    params := H.params
    paramFVars := H.paramFVars }
  · simpa using H.consts
  · simpa using H.indices

/-- The two independent invariants carried across the mutual-header loop.
`headers` follows the context used to check the current family header, while
`applicationStats` remains interpreted in the parameter context captured by
the first header.  Keeping the contexts separate reflects the executable
implementation: later family headers reuse the cached parameter free
variables without retaining their temporary index contexts. -/
structure HeaderTraversalCertificate (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (decl : VInductDecl) (params : List VExpr)
    (stats : AddInductive.InductiveStats) (depth done : Nat) where
  headers : HeaderLoopCertificate env Us decl params stats done
  applicationStats : ValidAppStatsPrefix env Us Δ stats decl depth done

structure HeaderTraversalResult (env : VEnv) (Us : List Name)
    (Δ : VLCtx) (decl : VInductDecl)
    (stats : AddInductive.InductiveStats) (depth : Nat) where
  headers : HeaderCertificate env decl
  applicationStats : ValidAppStatsWF env Us Δ stats decl depth

def HeaderTraversalResult.ofMaterialized
    (H : checkInductiveTypes.loopInd.MaterializedHeaderResult
      env Us Δ stats decl depth) :
    HeaderTraversalResult env Us Δ decl stats depth where
  headers := H.headers
  applicationStats := ValidAppStatsWF.ofMaterializedHeader H

/-- Executable header-loop state in the actual retained reader context. -/
structure HeaderRuntimeCertificate (Hc : ContextWF c)
    (decl : VInductDecl) (params : List VExpr)
    (stats : AddInductive.InductiveStats) (depth done : Nat) where
  headers : HeaderLoopCertificate Hc.venv c.lparams decl params stats done
  applicationStats : ValidAppStatsPrefix Hc.venv c.lparams
    Hc.mlctx.vlctx stats decl depth done
  ambient : checkInductiveTypes.loopType.AmbientParamContext Hc params depth

def HeaderRuntimeCertificate.withIndex
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderRuntimeCertificate Hc decl params stats depth done)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx ty ty')
    (hty : Hc.venv.IsType c.lparams.length Hc.mlctx.vlctx.toCtx ty')
    (hsource : ∃ u, Hc.venv.IsDefEq c.lparams.length
      Hc.mlctx.vlctx.toCtx sourceTy ty' (.sort u)) :
    HeaderRuntimeCertificate
      (Hc.withLocalDecl (name := name) (bi := bi) htr hty)
      decl params stats (depth + 1) done where
  headers := H.headers
  applicationStats := H.applicationStats.withLocalDecl Hc htr hty
  ambient := H.ambient.withIndex htr hty hsource

def HeaderRuntimeCertificate.first
    {c : AddInductive.Context} {Hc : ContextWF c}
    {indices params : List VExpr}
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl.nparams indices.length)
    (hlevels : stats.levels.length = decl.uvars)
    (huvars : c.lparams.length = decl.uvars)
    (hconsts : stats.indConsts = #[])
    (hindices : stats.nindices = #[])
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hname : indName = decl.types[0].name)
    (hnindices : nindices = decl.types[0].numIndices)
    (hofLevel : VLevel.ofLevel c.lparams resultSort = some target.resultLevel)
    (hctx : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx)
    (hshape : decl.TypeShape Hc.venv params target) :
    HeaderRuntimeCertificate Hc decl params
      (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
        true nindices indName)
      indices.length 1 where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.first
    hindex htarget hofLevel hshape
  applicationStats :=
    (ValidAppStatsPrefix.beforeFirst Hcache hlevels huvars hconsts hindices).push
      hindex hname hnindices
  ambient :=
    checkInductiveTypes.loopType.AmbientParamContext.ofFirstDefEq hctx

def HeaderRuntimeCertificate.later
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderRuntimeCertificate Hc decl params stats depth done)
    (hindex : done < decl.types.length)
    (htarget : decl.types[done] = target)
    (hname : indName = decl.types[done].name)
    (hnindices : nindices = decl.types[done].numIndices)
    (hguard : resultSort.isEquiv stats.resultLevel = true)
    (hofLevel : VLevel.ofLevel c.lparams resultSort = some target.resultLevel)
    (hshape : decl.TypeShape Hc.venv params target) :
    HeaderRuntimeCertificate Hc decl params
      (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
        false nindices indName)
      depth (done + 1) where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.later
    H.headers hindex htarget hguard hofLevel hshape
  applicationStats := H.applicationStats.push hindex hname hnindices
  ambient := H.ambient

theorem HeaderRuntimeCertificate.firstResultWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    {params indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (Hcache : checkInductiveTypes.loopType.ParameterCachePrefix
      Hc.venv c.lparams Hc.mlctx.vlctx stats decl.nparams indices.length)
    (hlevels : stats.levels.length = decl.uvars)
    (huvars : c.lparams.length = decl.uvars)
    (hconsts : stats.indConsts = #[])
    (hindices : stats.nindices = #[])
    (hempty : stats.indConsts.isEmpty = true)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ params.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (params, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hname : indName = decl.types[0].name)
    (hnindices : nindices = decl.types[0].numIndices)
    (Hrec : ∀ resultSort,
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      HeaderRuntimeCertificate Hc decl params
        (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
          true nindices indName)
        indices.length 1 →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes 1
        (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
          true nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes 1 stats k)
      type stats nindices c).WF Q := by
  apply checkInductiveTypes.loopInd.firstResult.refinesRuntimeState
    (dIdx := 0) k Q Hc hempty htype huvars hctxEq hheader hparamsTake
      hindicesTake hlevel
  intro resultSort hofLevel _hshape _hambient
  exact Hrec resultSort hofLevel
    (HeaderRuntimeCertificate.first Hcache hlevels huvars hconsts hindices
      hindex htarget hname hnindices hofLevel
      hctxEq _hshape)

theorem HeaderRuntimeCertificate.laterResultWF
    {c : AddInductive.Context} {Hc : ContextWF c}
    {decl : VInductDecl} {target : VInductiveType}
    {params ownParams indices : List VExpr}
    {normalized afterParams result exprType : VExpr}
    {α : Type} (k : AddInductive.InductiveStats → AddInductive.M α)
    (Q : α → Prop)
    (H : HeaderRuntimeCertificate Hc decl params stats depth dIdx)
    (hnonempty : stats.indConsts.isEmpty = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type result)
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : VEnv.IsDefEqCtx Hc.venv c.lparams.length []
      (indices.reverse ++ ownParams.reverse) Hc.mlctx.vlctx.toCtx)
    (hheader : Hc.venv.IsDefEq decl.uvars []
      target.type normalized exprType)
    (hparamsTake : normalized.takeForalls decl.nparams =
      some (ownParams, afterParams))
    (hindicesTake : afterParams.takeForalls target.numIndices =
      some (indices, result))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hlevel : ∀ resultSort resultLevel,
      VLevel.ofLevel c.lparams resultSort = some resultLevel →
      resultLevel = target.resultLevel)
    (hindex : dIdx < decl.types.length)
    (htarget : decl.types[dIdx] = target)
    (hname : indName = decl.types[dIdx].name)
    (hnindices : nindices = decl.types[dIdx].numIndices)
    (Hrec : ∀ resultSort,
      resultSort.isEquiv stats.resultLevel = true →
      VLevel.ofLevel c.lparams resultSort = some target.resultLevel →
      HeaderRuntimeCertificate Hc decl params
        (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
          false nindices indName)
        depth (dIdx + 1) →
      (AddInductive.checkInductiveTypes.loopInd nparams indTypes (dIdx + 1)
        (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
          false nindices indName) k c).WF Q) :
    ((fun type stats nindices => show AddInductive.M α from do
      let type ← TypeChecker.ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with
          lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indName stats.levels) }
      AddInductive.checkInductiveTypes.loopInd nparams indTypes
        (dIdx + 1) stats k) type stats nindices c).WF Q := by
  apply checkInductiveTypes.loopInd.laterResult.refines k Q Hc hnonempty
    htype huvars hctxEq hheader hparamsTake hindicesTake hparams hlevel
  intro resultSort hguard hofLevel hshape
  exact Hrec resultSort hguard hofLevel
    (H.later hindex htarget hname hnindices hguard hofLevel hshape)

def HeaderRuntimeCertificate.complete
    {c : AddInductive.Context} {Hc : ContextWF c}
    (H : HeaderRuntimeCertificate Hc decl params stats depth
      decl.types.length) :
    HeaderTraversalResult Hc.venv c.lparams Hc.mlctx.vlctx
      decl stats depth where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.complete H.headers
  applicationStats := H.applicationStats.complete

/-- Pair the first successfully checked header with the corresponding first
statistics update.  The application-statistics premise is deliberately about
the post-telescope parameter context, which is exactly the context saved in
`stats.lctx` by the executable first-header branch. -/
def HeaderTraversalCertificate.first
    {c : AddInductive.Context}
    (Hstats : ValidAppStatsPrefix env c.lparams Δ stats decl depth 0)
    (hindex : 0 < decl.types.length)
    (htarget : decl.types[0] = target)
    (hname : indName = decl.types[0].name)
    (hnindices : nindices = decl.types[0].numIndices)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderTraversalCertificate env c.lparams Δ decl params
      (checkInductiveTypes.loopInd.updatedStats stats c.lctx resultSort
        true nindices indName)
      depth 1 where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.first
    hindex htarget hofLevel hshape
  applicationStats := Hstats.push hindex hname hnindices

/-- Extend both mutual-header invariants after a later header passes the
common-universe guard. -/
def HeaderTraversalCertificate.later
    {c : AddInductive.Context}
    (H : HeaderTraversalCertificate env c.lparams Δ decl params stats
      depth done)
    (hindex : done < decl.types.length)
    (htarget : decl.types[done] = target)
    (hname : indName = decl.types[done].name)
    (hnindices : nindices = decl.types[done].numIndices)
    (hguard : resultSort.isEquiv stats.resultLevel = true)
    (hofLevel : VLevel.ofLevel c.lparams resultSort =
      some target.resultLevel)
    (hshape : decl.TypeShape env params target) :
    HeaderTraversalCertificate env c.lparams Δ decl params
      (checkInductiveTypes.loopInd.updatedStats stats stats.lctx resultSort
        false nindices indName)
      depth (done + 1) where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.later
    H.headers hindex htarget hguard hofLevel hshape
  applicationStats := H.applicationStats.push hindex hname hnindices

/-- At loop completion, expose exactly the two public certificates needed by
the constructor and formation stages. -/
def HeaderTraversalCertificate.complete
    (H : HeaderTraversalCertificate env Us Δ decl params stats depth
      decl.types.length) :
    HeaderTraversalResult env Us Δ decl stats depth where
  headers := checkInductiveTypes.loopInd.HeaderLoopCertificate.complete H.headers
  applicationStats := H.applicationStats.complete

/-- Joint output of header checking and the subsequent flattened constructor
traversal.  This is the formation-side payload eventually returned to
`Environment.addInductive`; application statistics remain available for
recursor and iota generation. -/
structure CheckedFormationResult (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (decl : VInductDecl) (stats : AddInductive.InductiveStats)
    (depth : Nat) where
  formation : FormationCertificate env decl
  applicationStats : ValidAppStatsWF env Us Δ stats decl depth

def HeaderTraversalResult.withConstructors
    (H : HeaderTraversalResult env Us Δ decl stats depth)
    (envTypes : VEnv)
    (htypes : env.addConsts decl.typeConstants = some envTypes)
    (Hctors : ConstructorPrefixCertificate env decl envTypes
      H.headers.params decl.ownedConstructors.length) :
    CheckedFormationResult env Us Δ decl stats depth where
  formation := {
    headers := H.headers
    envTypes := envTypes
    typesInstalled := htypes
    constructors := Hctors.complete }
  applicationStats := H.applicationStats

def HeaderTraversalResult.withConstructorTypes
    (H : HeaderTraversalResult env Us Δ decl stats depth)
    (envTypes : VEnv)
    (htypes : env.addConsts decl.typeConstants = some envTypes)
    (Hctors : ConstructorTypesPrefix envTypes decl H.headers.params
      decl.types.length) :
    CheckedFormationResult env Us Δ decl stats depth where
  formation := {
    headers := H.headers
    envTypes := envTypes
    typesInstalled := htypes
    constructors := Hctors.complete }
  applicationStats := H.applicationStats

def LiteralDisjoint (indConsts : Array Expr) : Prop :=
  ∀ literal : Literal,
    AddInductive.hasIndOcc indConsts literal.toConstructor = false

theorem forall₂_append {R : α → β → Prop}
    (H₁ : List.Forall₂ R as₁ bs₁) (H₂ : List.Forall₂ R as₂ bs₂) :
    List.Forall₂ R (as₁ ++ as₂) (bs₁ ++ bs₂) := by
  induction H₁ with
  | nil => exact H₂
  | cons h _ ih => exact .cons h ih

/-- Translation preserves a constant-headed application spine and the
left-to-right correspondence of all its arguments.  This is the syntax bridge
needed by both executable recursive-target checks. -/
theorem TrExprS.constAppSpine
    (H : TrExprS env Us Δ e e')
    (hhead : e.getAppFn = .const name levels) :
    ∃ levels' args',
      e'.getAppFnArgs = (.const name levels', args') ∧
      levels.mapM (VLevel.ofLevel Us) = some levels' ∧
      List.Forall₂ (TrExprS env Us Δ) e.getAppArgsList args' := by
  induction e generalizing e' with
  | const _ _ =>
    cases H with
    | const _ hlevels _ =>
      cases hhead
      exact ⟨_, [], rfl, hlevels, .nil⟩
  | app fn arg ihFn _ =>
    cases H
    rename_i f' _ _ arg' _ _ hfn harg
    rcases ihFn hfn hhead with ⟨levels', args', hspine, hlevels, hargs⟩
    have hargs' := forall₂_append hargs (.cons harg .nil)
    refine ⟨levels', args' ++ [arg'], ?_, hlevels, ?_⟩
    · simp [hspine]
    · simpa only [Expr.getAppArgsList_app] using hargs'
  | bvar _ | fvar _ | sort _ | lit _ => cases hhead
  | mvar _ => cases H
  | lam _ _ _ _ _ _ => cases hhead
  | forallE _ _ _ _ _ _ => cases hhead
  | letE _ _ _ _ _ _ _ _ => cases hhead
  | mdata _ _ _ => cases hhead
  | proj _ _ _ _ => cases hhead

theorem TrExprS.eqv_fvar_target
    (H₁ : TrExprS env Us Δ (.fvar fv) e₁')
    (H₂ : TrExprS env Us Δ e₂ e₂')
    (heq : ((.fvar fv : Expr) == e₂) = true) : e₁' = e₂' := by
  cases e₂ <;> simp [(· == ·), Expr.eqv'] at heq
  have hfv : fv = _ := beq_iff_eq.mp heq
  subst_vars
  cases H₁ with
  | fvar h₁ =>
    cases H₂ with
    | fvar h₂ =>
      rw [h₁] at h₂
      cases h₂
      rfl

theorem isValidIndAppIdx.head
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true) :
    (type.getAppFn == stats.indConsts[i]!) = true := by
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq] at hvalid
  split at hvalid
  · simp_all
  · simp_all

theorem isValidIndAppIdx.constHead
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hconst : stats.indConsts[i]? = some (.const name levels)) :
    type.getAppFn = .const name levels := by
  have hhead := isValidIndAppIdx.head hvalid
  have hget : stats.indConsts[i]! = .const name levels := by
    simp [Array.getElem!_eq_getD, hconst]
  rw [hget] at hhead
  exact Expr.eqv_const.mp hhead

theorem isValidIndAppIdx.arity
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true) :
    type.getAppArgs.size = stats.params.size + stats.nindices[i]! := by
  simp only [AddInductive.isValidIndAppIdx, Expr.withApp_eq] at hvalid
  split at hvalid
  · simp_all
  · simp_all

theorem isValidIndAppIdx.param
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hj : j < stats.params.size) :
    (stats.params[j] == type.getAppArgs[j]'(by
      have := isValidIndAppIdx.arity hvalid
      omega)) = true := by
  have hp :
      (stats.params == type.getAppArgs.extract 0 stats.params.size) = true := by
    cases hparams :
        (stats.params == type.getAppArgs.extract 0 stats.params.size) <;>
      simp_all [AddInductive.isValidIndAppIdx, Expr.withApp_eq]
  rw [Array.beq_eq_decide] at hp
  split at hp
  · rename_i hsize
    simp only [decide_eq_true_eq] at hp
    have helem := hp j hj
    simpa only [Array.getElem_extract, Nat.zero_add] using helem
  · simp_all

theorem isValidIndAppIdx.indexNoOccurrence
    (hvalid : AddInductive.isValidIndAppIdx stats type i = true)
    (hlower : stats.params.size ≤ j) (hupper : j < type.getAppArgs.size) :
    AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] = false := by
  have hall :
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).all
        (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) = true := by
    have harity := isValidIndAppIdx.arity hvalid
    rw [harity]
    cases hclean :
        (type.getAppArgs.extract stats.params.size
          (stats.params.size + stats.nindices[i]!)).all
          (fun arg => !AddInductive.hasIndOcc stats.indConsts arg) <;>
      simp_all [AddInductive.isValidIndAppIdx, Expr.withApp_eq]
  have hk : j - stats.params.size <
      (type.getAppArgs.extract stats.params.size type.getAppArgs.size).size := by
    simp only [Array.size_extract]
    omega
  have hclean := Array.all_eq_true.mp hall (j - stats.params.size) hk
  simp only [Array.getElem_extract] at hclean
  have hj : stats.params.size + (j - stats.params.size) = j := by omega
  simp only [hj] at hclean
  cases hocc : AddInductive.hasIndOcc stats.indConsts type.getAppArgs[j] <;>
    simp_all

theorem isValidIndAppFrom?_some
    (h : AddInductive.isValidIndAppFrom? stats type start fuel = some i) :
    start ≤ i ∧ i < start + fuel ∧
      AddInductive.isValidIndAppIdx stats type i = true := by
  induction fuel generalizing start with
  | zero => simp [AddInductive.isValidIndAppFrom?] at h
  | succ fuel ih =>
    rw [AddInductive.isValidIndAppFrom?] at h
    by_cases hvalid : AddInductive.isValidIndAppIdx stats type start = true
    · rw [if_pos hvalid] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, hvalid⟩
    · have hfalse : AddInductive.isValidIndAppIdx stats type start = false := by
        cases hv : AddInductive.isValidIndAppIdx stats type start
        · rfl
        · exact False.elim (hvalid hv)
      simp [hfalse] at h
      rcases ih h with ⟨hlower, hupper, hvalid⟩
      exact ⟨by omega, by omega, hvalid⟩

theorem isValidIndApp?_some
    (h : AddInductive.isValidIndApp? stats type = some i) :
    i < stats.indConsts.size ∧
      AddInductive.isValidIndAppIdx stats type i = true := by
  exact ⟨by simpa using (isValidIndAppFrom?_some h).2.1,
    (isValidIndAppFrom?_some h).2.2⟩

/-- Once the preceding validation has identified a family member,
`getIIndices` returns that same member. This isolates the partial `get!` in
the production helper. -/
theorem getIIndices.fst_eq_of_valid
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).1 = i := by
  simp only [AddInductive.getIIndices, h, Option.get!_eq_getD,
    Option.getD_some]

/-- The suffix returned by `getIIndices` has the declared index arity of the
selected mutual-family member. -/
theorem getIIndices.index_arity
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).2.size = stats.nindices[i]! := by
  rw [AddInductive.getIIndices]
  change (type.getAppArgs.toSubarray stats.params.size).toArray.size = _
  rw [Subarray.size_toArray, Subarray.size_eq]
  simp only [Array.stop_toSubarray, Array.start_toSubarray]
  have hvalid := (isValidIndApp?_some h).2
  have harity := isValidIndAppIdx.arity hvalid
  omega

theorem getIIndices.family_lt
    {decl : VInductDecl}
    (H : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).1 < decl.types.length := by
  rw [getIIndices.fst_eq_of_valid h]
  have hi := (isValidIndApp?_some h).1
  rw [H.consts.exact] at hi
  simpa using hi

/-- Together with the stats/declaration correspondence, the executable suffix
has the abstractly declared index arity. -/
theorem getIIndices.declared_index_arity
    {decl : VInductDecl}
    (H : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (h : AddInductive.isValidIndApp? stats type = some i) :
    (AddInductive.getIIndices stats type).2.size =
      (decl.types[i]'(by simpa [getIIndices.fst_eq_of_valid h] using
        getIIndices.family_lt H h)).numIndices := by
  rw [getIIndices.index_arity h]
  have hi : i < decl.types.length := by
    simpa [getIIndices.fst_eq_of_valid h] using getIIndices.family_lt H h
  have hlen : stats.nindices.size = decl.types.length := by
    have := congrArg List.length H.indices
    simpa using this
  have hget := congrArg (fun xs => xs[i]?) H.indices
  simpa [Array.getElem!_eq_getD, hi, hlen] using hget

namespace mkRecRules.loopU

/-- The iota RHS generator produces exactly one recursive-result term for
each field selected by `loopCtorArgs`. The contents of each term are verified
separately; this theorem fixes the cardinality and continuation boundary. -/
theorem resultCount
    (hi : i ≤ u.size) (hv : v.size = i)
    (Hk : ∀ v c, v.size = u.size → (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u i v k c).WF Q := by
  rw [AddInductive.mkRecRules.loopU.eq_1]
  by_cases hnext : i < u.size
  · rw [dif_pos hnext]
    have hval :
        ((AddInductive.mkRecInfos.loopUArgs u[i] (fun uiTy xs =>
          let (itIdx, itIndices) := AddInductive.getIIndices stats uiTy
          let val := Expr.const (Lean.mkRecName indTypes[itIdx]!.name) lvls
          let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params)
            motives) minors) itIndices
          return (← getLCtx).mkLambda xs <| val.app (mkAppN u[i] xs)) c).WF
          (fun _ => True)) := by
      intro _ _
      trivial
    refine hval.bind fun val _ => ?_
    exact resultCount (indTypes := indTypes) (stats := stats)
      (motives := motives) (minors := minors) (lvls := lvls)
      (u := u) (i := i + 1) (v := v.push val) (k := k) (c := c)
      (by omega) (by simp [hv]) Hk
  · rw [dif_neg hnext]
    apply Hk
    omega
termination_by u.size - i

end mkRecRules.loopU

theorem mkRecRules.loopU.resultCountFromEmpty
    (Hk : ∀ v c, v.size = u.size → (k v c).WF Q) :
    (AddInductive.mkRecRules.loopU indTypes stats motives minors lvls
      u 0 #[] k c).WF Q :=
  mkRecRules.loopU.resultCount (Nat.zero_le _) rfl Hk

/-- A validated concrete parameter argument translates to the corresponding
abstract de Bruijn parameter.  The fvar-shape invariant is what upgrades
structural `Expr` equality to exact syntax translation here. -/
theorem ValidAppStatsWF.translatedParam
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env Us Δ)
      type.getAppArgsList args')
    (hj : j < stats.params.size) :
    args'[j]? = (decl.paramVars depth)[j]? := by
  have harity := isValidIndAppIdx.arity hvalid
  have hjArgs : j < type.getAppArgs.size := by omega
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have hlen := forall₂_length_eq hargs
  have hjArgs' : j < args'.length := by
    rw [← hlen, ← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hjArgs'
  have harg := forall₂_get?_eq_some hargs hsource htarget
  rcases H.paramAt hj with ⟨param', hparamTarget, hparam⟩
  rcases H.paramFVarAt hj with ⟨fv, hfv⟩
  have heq := isValidIndAppIdx.param hvalid hj
  rw [hfv] at hparam heq
  have habstract := checkPositivityStep.TrExprS.eqv_fvar_target
    hparam harg heq
  rw [htarget, hparamTarget, ← habstract]

/-- Absence of a newly declared constant is preserved by syntax translation.
Literal expansion and projection translation are explicit side conditions:
literals introduce old primitive constants, while `TrProj` is still an
independent typing boundary in the existing model. -/
theorem TrExprS.noIndOcc
    (halign : IndConstNames indConsts names)
    (hlit : LiteralDisjoint indConsts)
    (hctx : VLCtx.NoIndConsts names Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst names = false →
      e''.containsAnyConst names = false)
    (H : TrExprS env Us Δ e e')
    (hno : AddInductive.hasIndOcc indConsts e = false) :
    e'.containsAnyConst names = false := by
  rw [hasIndOcc_eq_findAny] at hno
  induction H with
  | bvar hfind | fvar hfind => exact hctx hfind
  | sort _ => rfl
  | const _ _ _ =>
    simp only [Expr.findAny] at hno
    change names.contains _ = false
    rw [← halign]
    exact hno
  | app _ _ _ _ ihFn ihArg =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hfn, harg⟩
    exact Bool.or_eq_false_iff.mpr ⟨ihFn hctx hfn, ihArg hctx harg⟩
  | lam _ _ _ ihTy ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hty, hbody⟩
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx hty, ihBody ?_ hbody⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | forallE _ _ _ _ ihTy ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨hty, hbody⟩
    apply Bool.or_eq_false_iff.mpr
    refine ⟨ihTy hctx hty, ihBody ?_ hbody⟩
    exact VLCtx.NoIndConsts.cons hctx (by rfl)
  | letE _ _ _ _ ihTy ihValue ihBody =>
    simp only [Expr.findAny, Bool.false_or] at hno
    rcases Bool.or_eq_false_iff.mp hno with ⟨htyValue, hbody⟩
    rcases Bool.or_eq_false_iff.mp htyValue with ⟨hty, hvalue⟩
    have hvalue' := ihValue hctx hvalue
    exact ihBody (hctx.cons (d := .vlet _ _) (ofv := none) hvalue') hbody
  | lit _ _ ih =>
    apply ih hctx
    rw [← hasIndOcc_eq_findAny]
    exact hlit _
  | mdata _ ih =>
    simpa only [Expr.findAny, Bool.false_or] using ih hctx hno
  | proj _ Hproj ih =>
    simp only [Expr.findAny, Bool.false_or] at hno
    exact hproj Hproj (ih hctx hno)

theorem ValidAppStatsWF.translatedIndexNoOccurrence
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (hargs : List.Forall₂ (TrExprS env Us Δ)
      type.getAppArgsList args')
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hlower : stats.params.size ≤ j) (hupper : j < args'.length) :
    args'[j].containsAnyConst (decl.types.map (·.name)) = false := by
  have hlen := forall₂_length_eq hargs
  have hjArgs : j < type.getAppArgs.size := by
    have hsize : type.getAppArgs.size = type.getAppArgsList.length := by
      rw [← Expr.getAppArgs_toList]
      simp
    rw [hsize, hlen]
    exact hupper
  have hsource : type.getAppArgsList[j]? = some type.getAppArgs[j] := by
    rw [← Expr.getAppArgs_toList]
    simp [hjArgs]
  have htarget : args'[j]? = some args'[j] :=
    List.getElem?_eq_getElem hupper
  have harg := forall₂_get?_eq_some hargs hsource htarget
  have hno := isValidIndAppIdx.indexNoOccurrence hvalid hlower hjArgs
  exact TrExprS.noIndOcc H.consts.names hlit hctx hproj harg hno

theorem isValidIndAppIdx.validIndAppAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (hi : typeIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndAppIdx stats type typeIdx = true)
    (htarget : target = none ∨ target = some decl.types[typeIdx].name)
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    decl.ValidIndAppAt target depth type' := by
  have hconst := H.indConstAt hi
  have hhead := isValidIndAppIdx.constHead hvalid hconst
  rcases checkPositivityStep.TrExprS.constAppSpine htr hhead with
    ⟨levels', args', hspine, hlevels, hargs⟩
  have hlevelLen : levels'.length = decl.uvars := by
    have hlen := List.mapM_some_length hlevels
    have hstats := H.levels
    omega
  have hargsLen : args'.length =
      decl.nparams + decl.types[typeIdx].numIndices := by
    have htranslated := forall₂_length_eq hargs
    have hsource : type.getAppArgsList.length = type.getAppArgs.size := by
      rw [← Expr.getAppArgs_toList]
      simp
    have harity := isValidIndAppIdx.arity hvalid
    have hnindices : stats.nindices[typeIdx]! =
        decl.types[typeIdx].numIndices := by
      simp [Array.getElem!_eq_getD, H.nindicesAt hi]
    have hparamsSize := H.params_size
    omega
  have hparams : args'.take decl.nparams = decl.paramVars depth := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take]
    by_cases hj : j < decl.nparams
    · rw [if_pos hj]
      apply H.translatedParam hvalid hargs
      rw [H.params_size]
      exact hj
    · rw [if_neg hj]
      simp [VInductDecl.paramVars, hj]
  rw [VInductDecl.ValidIndAppAt, hspine]
  refine ⟨decl.types[typeIdx], List.getElem_mem hi, htarget,
    levels', rfl, hlevelLen, hargsLen, hparams, ?_⟩
  intro arg harg
  rcases List.mem_drop_iff_getElem.mp harg with ⟨j, hj, hargEq⟩
  subst arg
  exact H.translatedIndexNoOccurrence (j := decl.nparams + j)
    hvalid hargs hlit hctx hproj
    (by rw [H.params_size]; omega) (by simpa [Nat.add_comm] using hj)

theorem isValidIndApp?.validIndAppAt
    (H : ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hvalid : AddInductive.isValidIndApp? stats type = some typeIdx)
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false) :
    decl.ValidIndAppAt none depth type' := by
  rcases isValidIndApp?_some hvalid with ⟨hi, hvalidIdx⟩
  have hi' : typeIdx < decl.types.length := by
    rw [← H.types_size]
    exact hi
  exact isValidIndAppIdx.validIndAppAt H hi' htr hvalidIdx
    (Or.inl rfl) hlit hctx hproj

theorem noOccurrence.WF
    {type : Expr} {Q : Unit → Prop}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false)
    (hQ : Q ()) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  simp [AddInductive.checkPositivityStep, hocc]
  change (Except.ok ()).WF Q
  exact Except.WF.pure hQ

/-- The successful fast path of executable positivity establishes the
declarative nonrecursive case.  All non-syntactic correspondence assumptions
are named at the boundary: the accumulated mutual constants, local-variable
translation, literal expansion, and projection translation. -/
theorem noOccurrence.refines
    {decl : VInductDecl} {type' : VExpr} {depth : Nat} {ctx : List VExpr}
    (hconsts : IndConstArray stats.levels stats.indConsts
      (decl.types.map (·.name)))
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htr : TrExprS env Us Δ type type')
    (hocc : AddInductive.hasIndOcc stats.indConsts type = false) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  exact noOccurrence.WF
    (Q := fun _ => decl.SyntacticallyPositive env ctx depth type')
    hocc (.nonrecursive <|
      checkPositivityStep.TrExprS.noIndOcc hconsts.names hlit hctx hproj htr hocc)

theorem validApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hQ : Q ()) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals exact Except.WF.pure hQ

/-- Once the application-spine refinement supplies `ValidIndAppAt`, the final
executable success branch is exactly the declarative recursive positivity
constructor. -/
theorem validApplication.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr} {ctx : List VExpr}
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target)
    (hrefines : decl.ValidIndAppAt none depth type') :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  exact validApplication.WF hocc hforall hvalid (.recursive hrefines)

theorem validApplication.sourceRefines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr} {ctx : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (htr : TrExprS env Us Δ type type')
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = some target) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive env ctx depth type') := by
  apply validApplication.refines hocc hforall hvalid
  exact isValidIndApp?.validIndAppAt Hstats htr hvalid hlit hctx hproj

theorem invalidApplication.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts type = true)
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndApp? stats type = none) :
    (AddInductive.checkPositivityStep stats type ctor idx recur c).WF Q := by
  cases type <;>
    simp_all [AddInductive.checkPositivityStep]
  all_goals
    change (Except.error _).WF Q
    exact Except.WF.throw

theorem negativeDomain.WF
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF Q := by
  rw [AddInductive.checkPositivityStep]
  rw [if_neg (by simp [hocc]), if_pos hdomOcc]
  change (Except.error _).WF Q
  exact Except.WF.throw

/-- Positive higher-order branch after WHNF.  Source-domain annotation
transport is shared with header and constructor telescopes. -/
theorem forallE.sourceWF
    (Hc : ContextWF c)
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = false)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
      (recur (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }).WF Q) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF Q := by
  rw [AddInductive.checkPositivityStep]
  rw [if_neg (by simp [hocc]), if_neg (by simp [hdomOcc])]
  rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
  refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
    (k := fun arg => recur (body.instantiate1 arg))
    Hc Hdom.consumed Hdom.isType ?_
  let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
    Hdom.consumed Hdom.isType
  have hopened := Hc.instantiateFresh (name := name) (bi := bi)
    Hdom.consumed Hdom.isType hbody''
  exact Hrec body'' hbodyEq hopened

/-- The successful higher-order branch refines the declarative `forallE`
positivity rule.  The recursive checker runs in the consumed-annotation local
context, while its certificate is deliberately stated for the original
source-domain/body translation used by the independent specification. -/
theorem forallE.refines
    {decl : VInductDecl} {depth : Nat}
    (Hc : ContextWF c)
    (hconsts : IndConstArray stats.levels stats.indConsts
      (decl.types.map (·.name)))
    (hlit : LiteralDisjoint stats.indConsts)
    (hctx : VLCtx.NoIndConsts (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hocc : AddInductive.hasIndOcc stats.indConsts
      (.forallE name dom body bi) = true)
    (hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = false)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (huvars : c.lparams.length = decl.uvars)
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (Hrec : ∀ body'',
      Hc.venv.IsDefEqU c.lparams.length
        (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
      TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).venv c.lparams
        (Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType).mlctx.vlctx
        (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
      (recur (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))
        { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF
        (fun _ => decl.Positive Hc.venv
          (consumedDom' :: Hc.mlctx.vlctx.toCtx) (depth + 1) body'')) :
    (AddInductive.checkPositivityStep stats (.forallE name dom body bi)
      ctor idx recur c).WF
      (fun _ => decl.SyntacticallyPositive Hc.venv Hc.mlctx.vlctx.toCtx depth
        (.forallE sourceDom' sourceBody')) := by
  have hdomNo := checkPositivityStep.TrExprS.noIndOcc hconsts.names hlit
    hctx hproj Hdom.source hdomOcc
  refine forallE.sourceWF (Q := fun _ => decl.SyntacticallyPositive Hc.venv
      Hc.mlctx.vlctx.toCtx depth (.forallE sourceDom' sourceBody'))
      (recur := recur) (ctor := ctor)
      (idx := idx) Hc hocc hdomOcc Hdom hbody ?_
  intro body'' hbodyEq hopened
  exact (Hrec body'' hbodyEq hopened).mono fun _ hpositive => by
    rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
    rcases hbodyEq with ⟨bodyType, hbodyEq⟩
    exact .forallE hdomNo
      (by simpa [huvars] using hdomEq)
      (by simpa [huvars] using hbodyEq) hpositive

end checkPositivityStep

namespace checkConstructors.loopCtor

/-- The terminal constructor target check now discharges the declarative
`CtorTailWF.result` rule, rather than returning an unconstrained success. -/
theorem result.refines
    {decl : VInductDecl} {depth : Nat} {result type' exprType : VExpr}
    {ctorCtx : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF env Us Δ stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htr : TrExprS env Us Δ type type')
    (hforall : ¬ ∃ name dom body bi, type = .forallE name dom body bi)
    (hvalid : AddInductive.isValidIndAppIdx stats type targetIdx = true)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Δ)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hdefeq : env.IsDefEq decl.uvars ctorCtx result type' exprType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF env decl.types[targetIdx]
        ctorCtx depth result) := by
  exact checkConstructors.loopCtor.result.WF
    (Q := fun _ => decl.CtorTailWF env decl.types[targetIdx]
      ctorCtx depth result)
    hforall hvalid (.result
      (checkPositivityStep.isValidIndAppIdx.validIndAppAt
        Hstats hi htr hvalid (Or.inr rfl) hlit hctx hproj)
      hdefeq)

/-- Semantic wrapper for a safe constructor field.  The low-level traversal
supplies source typing and annotation transport; this theorem packages those
facts as the declarative `CtorTailWF.field` rule. -/
theorem safeField.refines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorCtx : List VExpr} {depth : Nat}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ctorCtx)
    (Hpos : (AddInductive.checkPositivity stats dom ctor i c).WF
      (fun _ => decl.Positive Hc.venv ctorCtx depth sourceDom'))
    (Hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      decl.Positive Hc.venv ctorCtx depth sourceDom' →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF
          (fun _ => decl.CtorTailWF Hc.venv target
            (consumedDom' :: ctorCtx) (depth + 1) body'')) :
    (AddInductive.checkConstructors.loopCtor stats false ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
        (.forallE sourceDom' sourceBody')) := by
  refine safeField.sourceWF
    (Q := fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
      (.forallE sourceDom' sourceBody'))
    (Pos := decl.Positive Hc.venv ctorCtx depth sourceDom')
    (targetIdx := targetIdx) (fuel := fuel) (name := name) (bi := bi)
    Hc hparamAt Hdom hbody Hpos ?_
  intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped hbound
    hpositive body'' hbodyEq hopened
  have hdomainEq := Hdom.source.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hfield
  have hsourceTyped := htyped.defeqU_l Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx hdomainEq.symm
  exact (Hrec fieldType' fieldLevel fieldLevel' hfield hlevel htyped
    hbound hpositive body'' hbodyEq hopened).mono fun _ htail =>
    by
      rcases Hdom.source_defeq with ⟨checkedLevel, hdomEq⟩
      rcases hbodyEq with ⟨bodyType, hbodyEq⟩
      exact .field (by simpa [huvars, hctxEq] using hsourceTyped)
        (Hbound fieldLevel fieldLevel' hlevel hbound)
        (Or.inr hpositive)
        (by simpa [huvars, hctxEq] using hdomEq)
        (by simpa [huvars, hctxEq] using hbodyEq) htail

theorem unsafeField.refines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorCtx : List VExpr} {depth : Nat}
    (Hc : ContextWF c) (hparamAt : stats.params[i]? = none)
    (Hdom : Hc.ConsumedDomain dom sourceDom' consumedDom')
    (hbody : TrExprS Hc.venv c.lparams
      ((none, .vlam sourceDom') :: Hc.mlctx.vlctx) body sourceBody')
    (huvars : c.lparams.length = decl.uvars)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ctorCtx)
    (hunsafe : decl.isUnsafe = true)
    (Hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (Hrec : ∀ fieldType' fieldLevel fieldLevel',
      TrExprS Hc.venv c.lparams Hc.mlctx.vlctx dom fieldType' →
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      Hc.venv.HasType c.lparams.length Hc.mlctx.vlctx.toCtx
        fieldType' (.sort fieldLevel') →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      ∀ body'',
        Hc.venv.IsDefEqU c.lparams.length
          (sourceDom' :: Hc.mlctx.vlctx.toCtx) sourceBody' body'' →
        TrExprS (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).venv c.lparams
          (Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType).mlctx.vlctx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) body'' →
        (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
          (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1) fuel
          { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }).WF
          (fun _ => decl.CtorTailWF Hc.venv target
            (consumedDom' :: ctorCtx) (depth + 1) body'')) :
    (AddInductive.checkConstructors.loopCtor stats true ctor targetIdx
      (.forallE name dom body bi) i (fuel + 1) c).WF
      (fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
        (.forallE sourceDom' sourceBody')) := by
  refine unsafeField.sourceWF
    (Q := fun _ => decl.CtorTailWF Hc.venv target ctorCtx depth
      (.forallE sourceDom' sourceBody'))
    (targetIdx := targetIdx) (fuel := fuel) (name := name) (bi := bi)
    Hc hparamAt Hdom hbody ?_
  intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped hbound
    body'' hbodyEq hopened
  have hdomainEq := Hdom.source.uniq Hc.checking.tr.wf
    (.refl Hc.checking.tr.wf Hc.mlctx_wf.tr.wf) hfield
  have hsourceTyped := htyped.defeqU_l Hc.checking.tr.wf
    Hc.mlctx_wf.tr.wf.toCtx hdomainEq.symm
  exact (Hrec fieldType' fieldLevel fieldLevel' hfield hlevel htyped
    hbound body'' hbodyEq hopened).mono fun _ htail =>
    by
      rcases Hdom.source_defeq with ⟨checkedLevel, hdomEq⟩
      rcases hbodyEq with ⟨bodyType, hbodyEq⟩
      exact .field (by simpa [huvars, hctxEq] using hsourceTyped)
        (Hbound fieldLevel fieldLevel' hlevel hbound)
        (Or.inl hunsafe)
        (by simpa [huvars, hctxEq] using hdomEq)
        (by simpa [huvars, hctxEq] using hbodyEq) htail

/-- Starting after the common constructor parameters, the complete executable
constructor-tail traversal builds `CtorTailWF`.  The remaining level-order
premise is isolated explicitly until `Level.geq` is connected to `VLevel.LE`. -/
theorem tailRefines
    {decl : VInductDecl} {target : VInductiveType}
    {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hpositivity : ∀ {c : AddInductive.Context} {depth posIdx : Nat}
      {type : Expr} {type' : VExpr} (Hc : ContextWF c),
      checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
        Hc.mlctx.vlctx stats decl depth →
      checkPositivityStep.VLCtx.NoIndConsts
        (decl.types.map (·.name)) Hc.mlctx.vlctx →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type' →
      (AddInductive.checkPositivity stats type ctor posIdx c).WF
        (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type'))
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorTailWF Hc.venv target Hc.mlctx.vlctx.toCtx
        depth type') := by
  induction fuel generalizing c type type' depth i with
  | zero => exact zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases htr with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        have hparamNext : stats.params[i + 1]? = none := by
          rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
          omega
        cases isUnsafe with
        | false =>
          have Hpos := hpositivity (posIdx := i) Hc Hstats hctx
            (hdom.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
          exact safeField.refines Hc hparamAt Hdom hbody Hstats.uvars rfl
            Hpos hbound fun _ _ _ _ _ _ _ _ body'' _ hopened => by
              let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
                Hdom.consumed Hdom.isType
              have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
                Hc Hdom.consumed Hdom.isType
              have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                  (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
                apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
                rfl
              exact ih Hc' Hstats' hparamNext hctx' hbound hopened
        | true =>
          exact unsafeField.refines Hc hparamAt Hdom hbody Hstats.uvars rfl
            (hunsafe rfl) hbound fun _ _ _ _ _ _ _ body'' _ hopened => by
              let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
                Hdom.consumed Hdom.isType
              have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
                Hc Hdom.consumed Hdom.isType
              have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                  (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
                apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
                rfl
              exact ih Hc' Hstats' hparamNext hctx' hbound hopened
    · cases hvalid : AddInductive.isValidIndAppIdx stats type targetIdx
      · exact invalidResult.WF hforall hvalid
      · rcases htr.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf with
          ⟨exprType, htype⟩
        subst target
        exact result.refines Hstats hi htr hforall hvalid hlit hctx hproj
          (by simpa [Hstats.uvars] using htype)

end checkConstructors.loopCtor

namespace checkPositivity.loop

theorem zero.WF :
    (AddInductive.checkPositivity.loop stats ctor idx type 0 c).WF Q := by
  intro _ h
  simp [AddInductive.checkPositivity.loop] at h

theorem succ.WF
    (Hc : ContextWF c)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hstep : ∀ normalized,
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      (AddInductive.checkPositivityStep stats normalized ctor idx
        (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
        c).WF Q) :
    (AddInductive.checkPositivity.loop stats ctor idx type (fuel + 1) c).WF Q := by
  rw [AddInductive.checkPositivity.loop]
  exact (whnfInContext.WF Hc htype).bind fun normalized hnormalized =>
    Hstep normalized hnormalized

/-- Positivity's WHNF step with the concrete free-variable preservation fact
retained for refinements whose semantic scope is narrower than the executable
local context. -/
theorem succ.scopeWF
    (Hc : ContextWF c)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type')
    (Hstep : ∀ normalized,
      FVarsBelow Hc.mlctx.vlctx type normalized →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx normalized type' →
      (AddInductive.checkPositivityStep stats normalized ctor idx
        (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
        c).WF Q) :
    (AddInductive.checkPositivity.loop stats ctor idx type (fuel + 1) c).WF Q := by
  rw [AddInductive.checkPositivity.loop]
  exact (whnfInContext.scopeWF Hc htype).bind
    fun normalized hnormalized => Hstep normalized hnormalized.1 hnormalized.2

/-- The complete recursive positivity traversal refines the independent
declarative judgment.  In particular, every recursive call under a higher-
order binder performs and records its own WHNF/definitional-equality step. -/
theorem refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkPositivity.loop stats ctor idx type fuel c).WF
      (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  induction fuel generalizing c type type' depth with
  | zero => exact zero.WF
  | succ fuel ih =>
    rcases htype with ⟨sourceSyntax, hsource, hsourceEq⟩
    refine succ.WF Hc hsource ?_
    intro normalized hnormalized
    rcases hnormalized with ⟨exposed, hexposed, hexposedEq⟩
    have hsourceExposed :=
      (hexposedEq.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
        hsourceEq).symm
    rcases hsourceExposed with ⟨exprType, hsourceExposed⟩
    have finish
        (Hstep : (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.SyntacticallyPositive Hc.venv Hc.mlctx.vlctx.toCtx
              depth exposed)) :
        (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') :=
      Hstep.mono fun _ hpositive =>
        .unfold (by simpa [Hstats.uvars] using hsourceExposed) hpositive
    by_cases hocc : AddInductive.hasIndOcc stats.indConsts normalized = false
    · exact finish <| checkPositivityStep.noOccurrence.refines
        Hstats.consts hlit hctx hproj hexposed hocc
    have hocc' : AddInductive.hasIndOcc stats.indConsts normalized = true := by
      cases h : AddInductive.hasIndOcc stats.indConsts normalized
      · exact False.elim (hocc h)
      · rfl
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      by_cases hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true
      · exact checkPositivityStep.negativeDomain.WF hocc' hdomOcc
      have hdomOcc' : AddInductive.hasIndOcc stats.indConsts dom = false := by
        cases h : AddInductive.hasIndOcc stats.indConsts dom
        · rfl
        · exact False.elim (hdomOcc h)
      cases hexposed with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        exact finish <| checkPositivityStep.forallE.refines Hc Hstats.consts
          hlit hctx hproj hocc' hdomOcc' Hdom Hstats.uvars hbody
          fun body'' hbodyEq hopened => by
            let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType
            have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
              Hc Hdom.consumed Hdom.isType
            have hctx' : checkPositivityStep.VLCtx.NoIndConsts
                (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
              apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
              rfl
            exact ih Hc' Hstats' hctx'
              (hopened.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
    ·
      cases hvalid : AddInductive.isValidIndApp? stats normalized with
      | none =>
        exact checkPositivityStep.invalidApplication.WF hocc' hforall hvalid
      | some target =>
        exact finish <| checkPositivityStep.validApplication.sourceRefines
          Hstats hexposed hlit hctx hproj hocc' hforall hvalid

/-- Positivity refinement for constructor checking after mutual headers have
left ambient declarations in the executable context.  The concrete checker
runs in `Hc.mlctx.vlctx`, while every declarative judgment is constructed in
the independent `scope`; runtime WHNF results are restricted before any
positivity rule is emitted. -/
theorem refinesNarrow
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity.loop stats ctor idx type fuel c).WF
      (fun _ => decl.Positive Hc.venv scope.toCtx depth narrowType) := by
  induction fuel generalizing c type scope narrowType fullType depth with
  | zero => exact zero.WF
  | succ fuel ih =>
    rcases htypeFull with ⟨sourceFull, hsourceFull, hsourceTarget⟩
    refine succ.scopeWF Hc hsourceFull ?_
    intro normalized hbelow hnormalized
    have hnormalizedFVars : FVarsIn (· ∈ scope.fvars) normalized :=
      hbelow _ Hruntime.upset htypeNarrow.fvarsIn
    rcases hnormalized with
      ⟨exposedFull, hexposedFull, hexposedTarget⟩
    have hnormalizedClosed : Closed normalized 0 := by
      have hclosed := hexposedFull.closed
      rw [Hc.mlctx.noBV] at hclosed
      exact hclosed
    have hnormalizedFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
        normalized fullType :=
      ⟨exposedFull, hexposedFull,
        hexposedTarget.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
          hsourceTarget⟩
    have hinputFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
        type fullType :=
      ⟨sourceFull, hsourceFull, hsourceTarget⟩
    rcases Hruntime.restrictTrExpr Hc.checking.tr.wf htypeNarrow
        hinputFull hnormalizedFull hnormalizedClosed hnormalizedFVars with
      ⟨exposed, hexposed, hexposedEq⟩
    rcases hexposedEq.symm with ⟨exprType, htypeExposed⟩
    have finish
        (Hstep : (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.SyntacticallyPositive Hc.venv scope.toCtx depth exposed)) :
        (AddInductive.checkPositivityStep stats normalized ctor idx
          (fun body => AddInductive.checkPositivity.loop stats ctor idx body fuel)
          c).WF (fun _ =>
            decl.Positive Hc.venv scope.toCtx depth narrowType) :=
      Hstep.mono fun _ hpositive =>
        .unfold (by simpa [Hstats.uvars] using htypeExposed) hpositive
    by_cases hocc : AddInductive.hasIndOcc stats.indConsts normalized = false
    · exact finish <| checkPositivityStep.noOccurrence.refines
        Hstats.consts hlit
        (Hruntime.noIndConsts (decl.types.map (·.name))) hproj hexposed hocc
    have hocc' : AddInductive.hasIndOcc stats.indConsts normalized = true := by
      cases h : AddInductive.hasIndOcc stats.indConsts normalized
      · exact False.elim (hocc h)
      · rfl
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      by_cases hdomOcc : AddInductive.hasIndOcc stats.indConsts dom = true
      · exact checkPositivityStep.negativeDomain.WF hocc' hdomOcc
      have hdomOcc' : AddInductive.hasIndOcc stats.indConsts dom = false := by
        cases h : AddInductive.hasIndOcc stats.indConsts dom
        · rfl
        · exact False.elim (hdomOcc h)
      cases hexposed with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hexposedFull with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          refine finish <| checkPositivityStep.forallE.sourceWF
            (Q := fun _ => decl.SyntacticallyPositive Hc.venv
              scope.toCtx depth (.forallE _ _))
            (recur := fun body =>
              AddInductive.checkPositivity.loop stats ctor idx body fuel)
            Hc hocc' hdomOcc' Hdom hbodyFull ?_
          intro bodyFull' _hbodyFullEq hopenedFull
          let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
            Hdom.consumed Hdom.isType
          have hdeps : dom.consumeTypeAnnotations.fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotations_fvarsIn hnormalizedFVars.1)).1
          rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
          let Hruntime' :
              checkInductiveTypes.loopType.NarrowRuntimeScope
                Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam narrowDom) :: scope)
                Hc'.mlctx.vlctx :=
            Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
          have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
          have hopenedNarrow : TrExprS Hc'.venv c.lparams
              ((some (⟨c.ngen.curr⟩,
                dom.consumeTypeAnnotations.fvarsList),
                .vlam narrowDom) :: scope)
              (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
            rw [Expr.instantiate1_eq]
            exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
          have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
          have Hrec := ih Hc' Hruntime' Hstats' hopenedNarrow
            (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
          exact Hrec.mono fun _ hpositive => by
            rcases hdomNarrowType with ⟨domLevel, hdomTyped⟩
            rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
            change Hc.venv.IsDefEq c.lparams.length scope.toCtx
              narrowDom narrowDom (.sort domLevel) at hdomTyped
            change Hc.venv.IsDefEq c.lparams.length
              (narrowDom :: scope.toCtx) narrowBody narrowBody
              (.sort bodyLevel) at hbodyTyped
            exact .forallE
              (checkPositivityStep.TrExprS.noIndOcc Hstats.consts.names
                hlit (Hruntime.noIndConsts (decl.types.map (·.name)))
                hproj hdomNarrow hdomOcc')
              (by simpa [Hstats.uvars] using hdomTyped)
              (by simpa [Hstats.uvars] using hbodyTyped)
              hpositive
    · cases hvalid : AddInductive.isValidIndApp? stats normalized with
      | none =>
        exact checkPositivityStep.invalidApplication.WF hocc' hforall hvalid
      | some target =>
        exact finish <| checkPositivityStep.validApplication.sourceRefines
          Hstats hexposed hlit
            (Hruntime.noIndConsts (decl.types.map (·.name)))
            hproj hocc' hforall hvalid

end checkPositivity.loop

theorem checkPositivity.WF
    (Hloop : (AddInductive.checkPositivity.loop stats ctor idx type
      c.fuel.inductiveFuel c).WF Q) :
    (AddInductive.checkPositivity stats type ctor idx c).WF Q := by
  unfold AddInductive.checkPositivity
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  exact Hloop

/-- Public positivity refinement, including the production fuel lookup. -/
theorem checkPositivity.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkPositivity stats type ctor idx c).WF
      (fun _ => decl.Positive Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  apply checkPositivity.WF
  exact checkPositivity.loop.refines Hc Hstats hconsume hlit hctx hproj htype

/-- Public narrow-scope positivity refinement, including the production fuel
lookup used by constructor checking. -/
theorem checkPositivity.refinesNarrow
    {decl : VInductDecl} {depth : Nat} {scope : VLCtx}
    {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkPositivity stats type ctor idx c).WF
      (fun _ => decl.Positive Hc.venv scope.toCtx depth narrowType) := by
  apply checkPositivity.WF
  exact checkPositivity.loop.refinesNarrow Hc Hruntime Hstats hconsume
    hlit hproj htypeNarrow htypeFull

namespace isRecArg.loop

/-- The recursive-argument classifier used by recursor generation refines the
independent `RecursiveArg` judgment whenever it returns a family index. -/
theorem refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.isRecArg.loop stats type fuel c).WF
      (fun result => ∀ target, result = some target →
        decl.RecursiveArg Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  induction fuel generalizing c type type' depth with
  | zero =>
    intro _ h
    simp [AddInductive.isRecArg.loop] at h
  | succ fuel ih =>
    rcases htype with ⟨sourceSyntax, hsource, hsourceEq⟩
    rw [AddInductive.isRecArg.loop]
    refine (whnfInContext.WF Hc hsource).bind fun normalized hnormalized => ?_
    rcases hnormalized with ⟨exposed, hexposed, hexposedEq⟩
    have hsourceExposed :=
      (hexposedEq.trans Hc.checking.tr.wf Hc.mlctx_wf.tr.wf.toCtx
        hsourceEq).symm
    rcases hsourceExposed with ⟨exprType, hsourceExposed⟩
    by_cases hforall : ∃ name dom body bi,
        normalized = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      cases hexposed with
      | forallE hdomType _ hdom hbody =>
        rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
        rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
        refine withLocalDecl.WF (name := name) (bi := bi)
          (Q := fun result => ∀ target, result = some target →
            decl.RecursiveArg Hc.venv Hc.mlctx.vlctx.toCtx depth type')
          Hc Hdom.consumed Hdom.isType ?_
        let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
          Hdom.consumed Hdom.isType
        have hopened := Hc.instantiateFresh (name := name) (bi := bi)
          Hdom.consumed Hdom.isType hbody''
        have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
          Hc Hdom.consumed Hdom.isType
        have hctx' : checkPositivityStep.VLCtx.NoIndConsts
            (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
          apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
          rfl
        have Hrec := ih Hc' Hstats' hctx'
          (hopened.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
        exact Hrec.mono fun result hrec target htarget => by
          rcases Hdom.source_defeq with ⟨domLevel, hdomEq⟩
          rcases hbodyEq with ⟨bodyType, hbodyEq⟩
          exact .forallE
            (by simpa [Hstats.uvars] using hsourceExposed)
            (by simpa [Hstats.uvars] using hdomEq)
            (by simpa [Hstats.uvars] using hbodyEq)
            (hrec target htarget)
    · cases normalized <;> try { simp at hforall }
      all_goals
        change (Except.ok (AddInductive.isValidIndApp? stats _)).WF _
        exact Except.WF.pure fun target htarget =>
          .direct (by simpa [Hstats.uvars] using hsourceExposed)
            (checkPositivityStep.isValidIndApp?.validIndAppAt Hstats hexposed
              htarget hlit hctx hproj)

end isRecArg.loop

theorem isRecArg.refines
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s i e' e''}, TrProj Δ.toCtx s i e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.isRecArg stats type c).WF
      (fun result => ∀ target, result = some target →
        decl.RecursiveArg Hc.venv Hc.mlctx.vlctx.toCtx depth type') := by
  unfold AddInductive.isRecArg
  have hread : ((read : AddInductive.M AddInductive.Context) c).WF
      (fun c' => c' = c) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  exact isRecArg.loop.refines Hc Hstats hconsume hlit hctx hproj htype

namespace mkRecInfos.loopCtorArgs.loop

/-- Independently of typing, the recursive-argument array accumulated by
recursor generation is an ordered sublist of the complete field array. This
is the executable source of `IotaRule.fieldPositions_ordered`. -/
theorem selectedSublist {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : α → Prop}
    (hselected : u.toList.Sublist bu.toList)
    (Hk : ∀ t bu u c, u.toList.Sublist bu.toList → (k t bu u c).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      cases hparam : stats.params[i]? with
      | some param =>
        change (AddInductive.mkRecInfos.loopCtorArgs.loop stats k
          (body.instantiate1 param) (i + 1) bu u fuel c).WF Q
        exact ih hselected
      | none =>
        change (Lean4Lean.withLocalDecl name bi dom.consumeTypeAnnotations
          (fun arg => do
            let bu := bu.push arg
            let u := if (← AddInductive.isRecArg stats dom).isSome then
              u.push arg else u
            AddInductive.mkRecInfos.loopCtorArgs.loop stats k
              (body.instantiate1 arg) (i + 1) bu u fuel) c).WF Q
        unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
          AddInductive.instMonadLocalNameGeneratorM
          AddInductive.instMonadWithReaderOfLocalContextM
        let c' : AddInductive.Context := { c with
          ngen := c.ngen.next
          lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
            dom.consumeTypeAnnotations bi }
        change (AddInductive.isRecArg stats dom c' >>= fun selected =>
          AddInductive.mkRecInfos.loopCtorArgs.loop stats
            k (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) (i + 1)
            (bu.push (.fvar ⟨c.ngen.curr⟩))
            (if selected.isSome then u.push (.fvar ⟨c.ngen.curr⟩) else u)
            fuel c') |>.WF Q
        have hclass : (AddInductive.isRecArg stats dom c').WF (fun _ => True) := by
          intro _ _
          trivial
        refine hclass.bind fun selected _ => ?_
        cases selected with
        | none =>
          apply ih
          simpa using hselected.trans
            (List.sublist_append_left bu.toList [.fvar ⟨c.ngen.curr⟩])
        | some target =>
          apply ih
          simpa using hselected.append_right [.fvar ⟨c.ngen.curr⟩]
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata | proj =>
      change (k _ bu u c).WF Q
      exact Hk _ _ _ _ hselected

end mkRecInfos.loopCtorArgs.loop

/-- Public structural invariant for constructor argument classification. -/
theorem mkRecInfos.loopCtorArgs.selectedSublist {α : Type}
    (stats : AddInductive.InductiveStats) (t : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    (c : AddInductive.Context) {Q : α → Prop}
    (Hk : ∀ t bu u c, u.toList.Sublist bu.toList → (k t bu u c).WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  unfold AddInductive.mkRecInfos.loopCtorArgs
  exact mkRecInfos.loopCtorArgs.loop.selectedSublist stats k .slnil Hk

/-- Proof-side metadata retained for every field selected by `isRecArg`.
The executable code stores only the field free variable; this record retains
the independent recursive-domain certificate needed by `IotaRule`. -/
structure RecursorRecursiveDomain (env : VEnv) (decl : VInductDecl) where
  fieldIndex : Nat
  ctx : List VExpr
  depth : Nat
  domain : VExpr
  recursive : decl.RecursiveArg env ctx depth domain

/-- Exact correspondence between the two arrays built by `loopCtorArgs` and
the proof-side recursive-domain certificates. Constructors preserve the
left-to-right field order and record the field ordinal at selection time. -/
inductive RecursorFieldSelections (env : VEnv) (decl : VInductDecl) :
    Array Expr → Array Expr → List (RecursorRecursiveDomain env decl) → Prop
  | nil : RecursorFieldSelections env decl #[] #[] []
  | nonrecursive : RecursorFieldSelections env decl bu u fields →
      RecursorFieldSelections env decl (bu.push arg) u fields
  | recursive : RecursorFieldSelections env decl bu u fields →
      cert.fieldIndex = bu.size →
      RecursorFieldSelections env decl (bu.push arg) (u.push arg)
        (fields ++ [cert])

theorem RecursorFieldSelections.selectedSublist
    (H : RecursorFieldSelections env decl bu u fields) :
    u.toList.Sublist bu.toList := by
  induction H with
  | nil => exact .slnil
  | nonrecursive _ ih =>
    simpa using ih.trans (List.sublist_append_left _ [_])
  | @recursive bu u fields arg cert _ _ ih =>
    simpa using ih.append_right [arg]

theorem RecursorFieldSelections.fields_length
    (H : RecursorFieldSelections env decl bu u fields) :
    fields.length = u.size := by
  induction H with
  | nil => rfl
  | nonrecursive _ ih => exact ih
  | recursive _ _ ih => simp [ih]

theorem RecursorFieldSelections.positions_lt
    (H : RecursorFieldSelections env decl bu u fields) :
    ∀ cert ∈ fields, cert.fieldIndex < bu.size := by
  induction H with
  | nil => simp
  | @nonrecursive bu u fields arg _ ih =>
    intro cert hmem
    have := ih cert hmem
    simp only [Array.size_push]
    omega
  | @recursive bu u fields arg cert _ hindex ih =>
    intro old hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · have := ih old hmem
      simp only [Array.size_push]
      omega
    · simp only [Array.size_push, hindex]
      omega

theorem RecursorFieldSelections.positions_ordered
    (H : RecursorFieldSelections env decl bu u fields) :
    (fields.map (·.fieldIndex)).Pairwise (· < ·) := by
  induction H with
  | nil => simp
  | nonrecursive _ ih => exact ih
  | @recursive bu u fields arg cert H hindex ih =>
    simp only [List.map_append, List.map_singleton]
    rw [List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro old hold _ hnew
    simp only [List.mem_singleton] at hnew
    subst hnew
    rw [hindex]
    rcases List.mem_map.mp hold with ⟨oldCert, hmem, rfl⟩
    exact H.positions_lt oldCert hmem

def RecursorRecursiveDomain.toRecursiveField
    (cert : RecursorRecursiveDomain env decl) (arg : VExpr) :
    decl.RecursiveField env where
  fieldIndex := cert.fieldIndex
  arg := arg
  ctx := cert.ctx
  depth := cert.depth
  domain := cert.domain
  recursive := cert.recursive

/-- Zips the proof-side domain certificates with their final translated field
arguments to obtain the public `RecursiveField` witnesses used by iota rules. -/
inductive RecursorFieldsMaterialize (env : VEnv) (decl : VInductDecl) :
    List (RecursorRecursiveDomain env decl) → List VExpr →
      List (decl.RecursiveField env) → Prop
  | nil : RecursorFieldsMaterialize env decl [] [] []
  | cons : RecursorFieldsMaterialize env decl certs args fields →
      RecursorFieldsMaterialize env decl (cert :: certs) (arg :: args)
        (cert.toRecursiveField arg :: fields)

theorem RecursorFieldsMaterialize.exists_of_length
    (h : certs.length = args.length) :
    ∃ fields, RecursorFieldsMaterialize env decl certs args fields := by
  induction certs generalizing args with
  | nil =>
    cases args <;> simp_all
    exact ⟨[], .nil⟩
  | cons cert certs ih =>
    cases args with
    | nil => simp at h
    | cons arg args =>
      have h' : certs.length = args.length := by
        simpa using Nat.succ.inj h
      rcases ih h' with ⟨fields, hfields⟩
      exact ⟨_, .cons hfields⟩

theorem RecursorFieldsMaterialize.args
    {env : VEnv} {decl : VInductDecl}
    {certs : List (RecursorRecursiveDomain env decl)}
    {translated : List VExpr} {fields : List (decl.RecursiveField env)}
    (H : RecursorFieldsMaterialize env decl certs translated fields) :
    fields.map (·.arg) = translated := by
  induction H with
  | nil => rfl
  | cons _ ih => simp [RecursorRecursiveDomain.toRecursiveField, ih]

theorem RecursorFieldsMaterialize.positions
    {env : VEnv} {decl : VInductDecl}
    {certs : List (RecursorRecursiveDomain env decl)} {translated : List VExpr}
    {fields : List (decl.RecursiveField env)}
    (H : RecursorFieldsMaterialize env decl certs translated fields) :
    fields.map (·.fieldIndex) = certs.map (·.fieldIndex) := by
  induction H with
  | nil => rfl
  | cons _ ih => simp [RecursorRecursiveDomain.toRecursiveField, ih]

theorem RecursorFieldSelections.exists_materialization
    (H : RecursorFieldSelections env decl bu u certs)
    (hargs : List.Forall₂ R u.toList args) :
    ∃ fields, RecursorFieldsMaterialize env decl certs args fields := by
  apply RecursorFieldsMaterialize.exists_of_length
  rw [H.fields_length]
  have hlen := checkPositivityStep.forall₂_length_eq hargs
  simpa using hlen

theorem RecursorFieldsMaterialize.positions_ordered
    {env : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain env decl)} {translated : List VExpr}
    {fields : List (decl.RecursiveField env)}
    (Hsel : RecursorFieldSelections env decl bu u certs)
    (Hmat : RecursorFieldsMaterialize env decl certs translated fields) :
    (fields.map (·.fieldIndex)).Pairwise (· < ·) := by
  rw [Hmat.positions]
  exact Hsel.positions_ordered

theorem RecursorFieldsMaterialize.positions_lt
    {env : VEnv} {decl : VInductDecl} {bu u : Array Expr}
    {certs : List (RecursorRecursiveDomain env decl)} {translated : List VExpr}
    {fields : List (decl.RecursiveField env)}
    (Hsel : RecursorFieldSelections env decl bu u certs)
    (Hmat : RecursorFieldsMaterialize env decl certs translated fields) :
    ∀ field ∈ fields, field.fieldIndex < bu.size := by
  intro field hmem
  have hpos : field.fieldIndex ∈ fields.map (·.fieldIndex) := by
    exact List.mem_map.mpr ⟨field, hmem, rfl⟩
  rw [Hmat.positions] at hpos
  rcases List.mem_map.mp hpos with ⟨cert, hcert, heq⟩
  rw [← heq]
  exact Hsel.positions_lt cert hcert

/-- Exact concrete common-parameter prefix consumed by recursor generation.
The relation is intentionally separate from field classification: agreement
of these substitutions with the abstract parameter telescope is established
during constructor checking. -/
inductive RecursorParamPrefix (stats : AddInductive.InductiveStats) :
    Nat → Expr → Expr → Prop
  | done : i = stats.params.size → RecursorParamPrefix stats i tail tail
  | step : stats.params[i]? = some param →
      RecursorParamPrefix stats (i + 1) (body.instantiate1 param) tail →
      RecursorParamPrefix stats i (.forallE name dom body bi) tail

namespace mkRecInfos.loopCtorArgs.loop

/-- `loopCtorArgs.loop` follows a certified common-parameter prefix without
changing either accumulator, then delegates to the supplied tail proof. Fuel
exhaustion is harmless because it cannot return successfully. -/
theorem followsParamPrefix {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {t tail : Expr} {i : Nat} {bu u : Array Expr}
    {c : AddInductive.Context} {Q : α → Prop}
    (hprefix : RecursorParamPrefix stats i t tail)
    (Htail : ∀ fuel,
      (AddInductive.mkRecInfos.loopCtorArgs.loop stats k tail
        stats.params.size bu u fuel c).WF Q) :
    ∀ fuel, (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  intro fuel
  induction fuel generalizing t i with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases hprefix with
    | done hi =>
      subst i
      exact Htail (fuel + 1)
    | @step i param body tail name dom bi hparam hprefix =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop, hparam]
      exact ih hprefix

/-- Typed refinement of the genuine-field suffix of `loopCtorArgs`. Common
parameters have already been exhausted, so every remaining forall binder is a
constructor field. Each successful recursive classification extends an exact
ordered list of independent `RecursiveArg` certificates. -/
theorem recursiveDomains {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    {decl : VInductDecl} {depth : Nat} {type' : VExpr}
    {t : Expr} {i : Nat} {bu u : Array Expr} {fuel : Nat}
    {c : AddInductive.Context} {Q : α → Prop}
    (Hc : ContextWF c)
    {fields : List (RecursorRecursiveDomain Hc.venv decl)}
    {args : List VExpr}
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hparams : stats.params.size ≤ i)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htype : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx t type')
    (hfields : RecursorFieldSelections Hc.venv decl bu u fields)
    (hargs : List.Forall₂
      (TrExprS Hc.venv c.lparams Hc.mlctx.vlctx) u.toList args)
    (Hk : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      {t' : Expr} {type'' : VExpr}
      {bu' u' : Array Expr}
      {fields' : List (RecursorRecursiveDomain Hc'.venv decl)} {args' : List VExpr},
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx t' type'' →
      RecursorFieldSelections Hc'.venv decl bu' u' fields' →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
        u'.toList args' →
      (k t' bu' u' c').WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs.loop stats k t i bu u fuel c).WF Q := by
  induction fuel generalizing c t i bu u depth type' fields args with
  | zero =>
    intro _ h
    simp [AddInductive.mkRecInfos.loopCtorArgs.loop] at h
  | succ fuel ih =>
    cases t with
    | forallE name dom body bi =>
      rw [AddInductive.mkRecInfos.loopCtorArgs.loop]
      have hparam : stats.params[i]? = none := by
        apply Array.getElem?_eq_none
        omega
      rw [hparam]
      have htypeTr := htype.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
      rcases TrExpr.forallE_source htypeTr with
        ⟨sourceDom', sourceBody', hdom, hbody, hdomType, _, _⟩
      rcases hconsume c Hc hdom hdomType with ⟨consumedDom', Hdom⟩
      rcases Hdom.body Hc hbody with ⟨body'', hbody'', hbodyEq⟩
      refine withLocalDecl.WF (name := name) (bi := bi) (Q := Q)
        Hc Hdom.consumed Hdom.isType ?_
      let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
        Hdom.consumed Hdom.isType
      have Hstats' := Hstats.withLocalDecl (name := name) (bi := bi)
        Hc Hdom.consumed Hdom.isType
      have hctx' : checkPositivityStep.VLCtx.NoIndConsts
          (decl.types.map (·.name)) Hc'.mlctx.vlctx := by
        apply checkPositivityStep.VLCtx.NoIndConsts.cons hctx
        rfl
      let W : VLCtx.FVLift Hc.mlctx.vlctx Hc'.mlctx.vlctx 0 1 0 :=
        .skip_fvar _ _ .refl
      have hdomWeak : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx dom
          (sourceDom'.liftN 1 0) := by
        apply Hdom.source.weakFV Hc.checking.tr.wf.ordered
          W
        exact Hc'.mlctx_wf.tr.wf
      have hargsWeak : List.Forall₂
          (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx) u.toList
          (args.map fun arg => arg.liftN 1 0) := by
        apply checkPositivityStep.forall₂_map_right hargs
        intro source arg harg
        exact harg.weakFV Hc.checking.tr.wf.ordered W Hc'.mlctx_wf.tr.wf
      have harg : TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx
          (.fvar ⟨c.ngen.curr⟩) (.bvar 0) := by
        exact TrExprS.fvar (A := consumedDom'.lift) (by
          change VLCtx.find? ((some (⟨c.ngen.curr⟩,
            dom.consumeTypeAnnotations.fvarsList), .vlam consumedDom') ::
              Hc.mlctx.vlctx) (Sum.inr ⟨c.ngen.curr⟩) = _
          simp only [VLCtx.find?, VLCtx.next, beq_self_eq_true, if_true,
            VLocalDecl.value, VLocalDecl.type])
      have hopened := Hc.instantiateFresh (name := name) (bi := bi)
        Hdom.consumed Hdom.isType hbody''
      have Hclass := isRecArg.refines Hc' Hstats' hconsume hlit hctx' hproj
        (hdomWeak.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
      refine Hclass.bind fun selected hselected => ?_
      cases selected with
      | none =>
        exact ih Hc' Hstats' (by omega) hctx' hopened
          (.nonrecursive hfields) hargsWeak
      | some target =>
        let cert : RecursorRecursiveDomain Hc'.venv decl := {
          fieldIndex := bu.size
          ctx := Hc'.mlctx.vlctx.toCtx
          depth := depth + 1
          domain := sourceDom'.liftN 1 0
          recursive := hselected target rfl }
        have hargs' : List.Forall₂
            (TrExprS Hc'.venv c.lparams Hc'.mlctx.vlctx)
            (u.push (.fvar ⟨c.ngen.curr⟩)).toList
            ((args.map fun arg => arg.liftN 1 0) ++ [.bvar 0]) := by
          simpa using checkPositivityStep.forall₂_append
            hargsWeak (.cons harg .nil)
        exact ih Hc' Hstats' (by omega) hctx' hopened
          (.recursive hfields (cert := cert) rfl) hargs'
    | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata | proj =>
      exact Hk Hc htype hfields hargs

end mkRecInfos.loopCtorArgs.loop

/-- Full constructor-argument refinement, composing exact common-parameter
substitution with typed recursive-field classification. -/
theorem mkRecInfos.loopCtorArgs.recursiveDomains {α : Type}
    (stats : AddInductive.InductiveStats) (t tail : Expr)
    (k : Expr → Array Expr → Array Expr → AddInductive.M α)
    (c : AddInductive.Context) {Q : α → Prop}
    {decl : VInductDecl} {tail' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl 0)
    (hprefix : RecursorParamPrefix stats 0 t tail)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (htail : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx tail tail')
    (Hk : ∀ {c' : AddInductive.Context} (Hc' : ContextWF c')
      {t' : Expr} {type'' : VExpr} {bu' u' : Array Expr}
      {fields' : List (RecursorRecursiveDomain Hc'.venv decl)} {args' : List VExpr},
      TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx t' type'' →
      RecursorFieldSelections Hc'.venv decl bu' u' fields' →
      List.Forall₂ (TrExprS Hc'.venv c'.lparams Hc'.mlctx.vlctx)
        u'.toList args' →
      (k t' bu' u' c').WF Q) :
    (AddInductive.mkRecInfos.loopCtorArgs stats t k c).WF Q := by
  let inputContext := c
  unfold AddInductive.mkRecInfos.loopCtorArgs
  have hread : ((read : AddInductive.M AddInductive.Context) inputContext).WF
      (fun c' => c' = inputContext) := by
    intro c' h
    cases h
    rfl
  refine hread.bind fun _ h => ?_
  subst h
  have Htail : ∀ fuel,
      (AddInductive.mkRecInfos.loopCtorArgs.loop stats k tail
        stats.params.size #[] #[] fuel inputContext).WF Q := by
    intro fuel
    exact mkRecInfos.loopCtorArgs.loop.recursiveDomains stats k Hc Hstats
      (Nat.le_refl _) hconsume hlit hctx hproj htail .nil .nil Hk
  exact mkRecInfos.loopCtorArgs.loop.followsParamPrefix stats k hprefix Htail
    inputContext.fuel.inductiveFuel

namespace mkRecInfos.loopArgs1

/-- `loopArgs1` cannot manufacture a successful result: after any sequence
of WHNF steps and local index binders it returns only through its supplied
continuation. This structural fact is the outer-loop interface used to count
one motive record per mutual family. -/
theorem continueWith {α : Type}
    (stats : AddInductive.InductiveStats)
    (k : Array Expr → AddInductive.M α)
    {Q : α → Prop}
    (Hk : ∀ indices c, (k indices c).WF Q) :
    ∀ type i indices fuel c,
      (AddInductive.mkRecInfos.loopArgs1 stats type i indices fuel k c).WF Q
  | _, _, _, 0, _ => by
      intro _ h
      simp [AddInductive.mkRecInfos.loopArgs1] at h
  | type, i, indices, fuel + 1, c => by
      cases type with
      | forallE name dom body bi =>
        rw [AddInductive.mkRecInfos.loopArgs1]
        by_cases hparam : i < stats.params.size
        · rw [if_pos hparam]
          have hwhnf :
              ((monadLift (TypeChecker.whnf
                (body.instantiate1 stats.params[i]!)) :
                AddInductive.M Expr) c).WF (fun _ => True) := by
            intro _ _
            trivial
          exact hwhnf.bind fun next _ =>
            continueWith stats k Hk next (i + 1) indices fuel c
        · rw [if_neg hparam]
          unfold Lean4Lean.withLocalDecl
            MonadLocalNameGenerator.withFreshId
            AddInductive.instMonadLocalNameGeneratorM
            AddInductive.instMonadWithReaderOfLocalContextM
          let c' : AddInductive.Context := { c with
            ngen := c.ngen.next
            lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name
              dom.consumeTypeAnnotations bi }
          change ((monadLift (TypeChecker.whnf
            (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
              AddInductive.M Expr) c' >>= fun next =>
              AddInductive.mkRecInfos.loopArgs1 stats next i
                (indices.push (.fvar ⟨c.ngen.curr⟩)) fuel k c').WF Q
          have hwhnf :
              ((monadLift (TypeChecker.whnf
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩))) :
                AddInductive.M Expr) c').WF (fun _ => True) := by
            intro _ _
            trivial
          exact hwhnf.bind fun next _ =>
            continueWith stats k Hk next i
              (indices.push (.fvar ⟨c.ngen.curr⟩)) fuel c'
      | bvar | fvar | mvar | sort | const | app | lam | letE | lit | mdata
        | proj =>
          simpa [AddInductive.mkRecInfos.loopArgs1] using Hk indices c

end mkRecInfos.loopArgs1

/-- Structural opening of a production local declaration when the proof only
needs to follow the continuation and does not yet claim typing for the new
domain. -/
theorem withLocalDecl.continueRaw
    {α : Type} {Q : α → Prop} {k : Expr → AddInductive.M α}
    {c : AddInductive.Context} {name : Name} {bi : BinderInfo} {ty : Expr}
    (H : (k (.fvar ⟨c.ngen.curr⟩) { c with
      ngen := c.ngen.next
      lctx := c.lctx.mkLocalDecl ⟨c.ngen.curr⟩ name ty bi }).WF Q) :
    (Lean4Lean.withLocalDecl name bi ty k c).WF Q := by
  unfold Lean4Lean.withLocalDecl MonadLocalNameGenerator.withFreshId
    AddInductive.instMonadLocalNameGeneratorM
    AddInductive.instMonadWithReaderOfLocalContextM
  exact H

/-- `Except.WF.bind` lifted across the reader layer used by the executable
inductive checker. Keeping the reader bind visible avoids repeatedly
unfolding `ReaderT` in structural traversal proofs. -/
theorem readerBind.WF
    {α β : Type} {Q : α → Prop} {R : β → Prop}
    {x : AddInductive.M α} {f : α → AddInductive.M β}
    {c : AddInductive.Context}
    (Hx : (x c).WF Q) (Hf : ∀ a, Q a → (f a c).WF R) :
    ((x >>= f) c).WF R := by
  exact Hx.bind Hf

namespace mkRecInfos.loopInd1

/-- The first recursor pass appends exactly one `RecInfo` (motive, indices,
major premise) for each mutual family. -/
theorem resultCount
    {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hdone : dIdx ≤ indTypes.size)
    (hsize : recInfos.size = dIdx)
    (hempty : ∀ r ∈ recInfos.toList, r.minors.isEmpty)
    (Hk : ∀ recInfos c, recInfos.size = indTypes.size →
      (∀ r ∈ recInfos.toList, r.minors.isEmpty) →
      (k recInfos c).WF Q) :
    (AddInductive.mkRecInfos.loopInd1 stats indTypes elimLevel dIdx
      recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd1]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    have hread : ((readThe AddInductive.Context :
        AddInductive.M AddInductive.Context) c).WF
        (fun c' => c' = c) := by
      intro c' h
      cases h
      rfl
    refine readerBind.WF (x := readThe AddInductive.Context) hread fun ctx hctx => ?_
    subst ctx
    have hwhnf :
        ((monadLift (TypeChecker.whnf indTypes[dIdx].type) :
          AddInductive.M Expr) c).WF (fun _ => True) := by
      intro _ _
      trivial
    refine hwhnf.bind fun type _ => ?_
    apply mkRecInfos.loopArgs1.continueWith stats
    intro indices cIndices
    apply withLocalDecl.continueRaw
    let cMajor : AddInductive.Context := { cIndices with
      ngen := cIndices.ngen.next
      lctx := cIndices.lctx.mkLocalDecl ⟨cIndices.ngen.curr⟩ `t
        (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices).consumeTypeAnnotations
        .default }
    have hget : ((getLCtx : AddInductive.M LocalContext) cMajor).WF
        (fun lctx => lctx = cMajor.lctx) := by
      intro lctx h
      cases h
      rfl
    refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
      hget fun lctx hlctx => ?_
    subst lctx
    apply withLocalDecl.continueRaw
    apply mkRecInfos.loopInd1.resultCount
      (stats := stats) (indTypes := indTypes) (elimLevel := elimLevel)
      (dIdx := dIdx + 1) (recInfos := recInfos.push {
        motive := .fvar ⟨cMajor.ngen.curr⟩, minors := #[], indices := indices,
        major := .fvar ⟨cIndices.ngen.curr⟩ }) (k := k)
      (Q := Q)
    · omega
    · simpa [hsize]
    · intro r hr
      simp only [Array.toList_push, List.mem_append, List.mem_cons,
        List.mem_singleton] at hr
      rcases hr with hr | hr
      · exact hempty r hr
      · rcases hr with rfl | hr
        · rfl
        · contradiction
    · exact Hk
  · rw [dif_neg hidx]
    apply Hk
    · omega
    · exact hempty
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd1

namespace mkRecInfos.loopU

/-- The induction-hypothesis loop returns only through its continuation.
Its generated local declarations affect the eventual minor type, but not the
`RecInfo` array whose cardinality is tracked by `loopCtors`. -/
theorem continueWith {α : Type}
    (stats : AddInductive.InductiveStats) (u : Array Expr)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array Expr → AddInductive.M α) {Q : α → Prop}
    (Hk : ∀ v c, (k v c).WF Q)
    (i : Nat) (v : Array Expr) (c : AddInductive.Context) :
    (AddInductive.mkRecInfos.loopU stats u recInfos i v k c).WF Q := by
      rw [AddInductive.mkRecInfos.loopU]
      by_cases hnext : i < u.size
      · rw [dif_pos hnext]
        have hviTy :
            ((AddInductive.mkRecInfos.loopUArgs u[i] fun uiTy xs => do
              let (itIdx, itIndices) := AddInductive.getIIndices stats uiTy
              let motiveApp := .app
                (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN u[i] xs)
              return (← getLCtx).mkForall xs motiveApp) c).WF
              (fun _ => True) := by
          intro _ _
          trivial
        refine hviTy.bind fun viTy _ => ?_
        have hget : ((getLCtx : AddInductive.M LocalContext) c).WF
            (fun lctx => lctx = c.lctx) := by
          intro lctx h
          cases h
          rfl
        refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
          hget fun lctx hlctx => ?_
        subst lctx
        apply withLocalDecl.continueRaw
        exact continueWith stats u recInfos k Hk (i + 1)
          (v.push (.fvar ⟨c.ngen.curr⟩)) _
      · rw [dif_neg hnext]
        exact Hk v c
termination_by u.size - i

end mkRecInfos.loopU

namespace mkRecInfos.loopCtors

theorem getElemBang_modify_ne {α : Type} [Inhabited α]
    (xs : Array α) (dIdx i : Nat) (f : α → α)
    (hi : i < xs.size) (hne : dIdx ≠ i) :
    (xs.modify dIdx f)[i]! = xs[i]! := by
  have hi' : i < (xs.modify dIdx f).size := by simpa using hi
  have heq : (xs.modify dIdx f)[i]'hi' = xs[i]'hi := by
    rw [Array.getElem_modify]
    simp [hne]
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

theorem getElemBang_modify_self {α : Type} [Inhabited α]
    (xs : Array α) (i : Nat) (f : α → α) (hi : i < xs.size) :
    (xs.modify i f)[i]! = f xs[i]! := by
  have hi' : i < (xs.modify i f).size := by simpa using hi
  have heq : (xs.modify i f)[i]'hi' = f (xs[i]'hi) :=
    Array.getElem_modify_self f hi'
  simp only [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos hi', dif_pos hi]
  exact heq

/-- Processing a constructor list preserves the number of family records and
appends exactly one minor premise per constructor to the selected owner. -/
theorem resultCount {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats) (indTypeName : Name)
    (dIdx : Nat) (recInfos : Array AddInductive.RecInfo)
    (ctors : List Constructor)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hidx : dIdx < recInfos.size)
    (Hk : ∀ out c,
      out.size = recInfos.size →
      out[dIdx]!.minors.size = recInfos[dIdx]!.minors.size + ctors.length →
      { out[dIdx]! with minors := #[] } = { recInfos[dIdx]! with minors := #[] } →
      (∀ i, i < recInfos.size → dIdx ≠ i → out[i]! = recInfos[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopCtors stats indTypeName dIdx recInfos ctors k c).WF Q := by
  induction ctors generalizing recInfos c with
  | nil =>
      simp only [AddInductive.mkRecInfos.loopCtors]
      apply Hk
      · rfl
      · simp
      · rfl
      · intros
        rfl
  | cons ctor ctors ih =>
      rw [AddInductive.mkRecInfos.loopCtors]
      apply mkRecInfos.loopCtorArgs.selectedSublist stats
      intro t bu u cArgs _
      apply mkRecInfos.loopU.continueWith stats u recInfos
      intro v cIH
      have hget : ((getLCtx : AddInductive.M LocalContext) cIH).WF
          (fun lctx => lctx = cIH.lctx) := by
        intro lctx h
        cases h
        rfl
      refine readerBind.WF (x := (getLCtx : AddInductive.M LocalContext))
        hget fun lctx hlctx => ?_
      subst lctx
      apply withLocalDecl.continueRaw
      let next := recInfos.modify dIdx fun s =>
        { s with minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩) }
      apply ih next _
      · simpa [next]
      · intro out cOut houtSize houtCount houtFrame
          houtOther
        apply Hk out cOut
        · simpa [next] using houtSize
        · rw [houtCount]
          dsimp [next]
          have hnextIdx : dIdx < (recInfos.modify dIdx fun s =>
              { s with minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩) }).size := by
            simpa using hidx
          have hbangModified :
              (recInfos.modify dIdx fun s =>
                { s with minors := s.minors.push (.fvar ⟨cIH.ngen.curr⟩) })[dIdx]! =
              { recInfos[dIdx]! with
                minors := recInfos[dIdx]!.minors.push (.fvar ⟨cIH.ngen.curr⟩) } := by
            simp only [Array.getElem!_eq_getD]
            unfold Array.getD
            rw [dif_pos hnextIdx, dif_pos hidx]
            exact Array.getElem_modify_self _ hnextIdx
          rw [hbangModified]
          simp
          omega
        · rw [houtFrame]
          dsimp [next]
          rw [getElemBang_modify_self recInfos dIdx _ hidx]
        · intro i hi hine
          rw [houtOther i (by simpa [next] using hi) hine]
          exact getElemBang_modify_ne recInfos dIdx i _ hi hine

end mkRecInfos.loopCtors

namespace mkRecInfos.loopInd2

def SameFrame (a b : AddInductive.RecInfo) : Prop :=
  { a with minors := #[] } = { b with minors := #[] }

theorem SameFrame.refl (a : AddInductive.RecInfo) : SameFrame a a := rfl

theorem SameFrame.trans (hab : SameFrame a b) (hbc : SameFrame b c) :
    SameFrame a c := Eq.trans hab hbc

/-- The second mutual pass finishes every family with exactly one minor per
owned constructor. The prefix/suffix formulation makes the mutation boundary
explicit and is directly initialized by `loopInd1`, whose minor arrays are
empty. -/
theorem resultCounts {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (origin : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hdone : dIdx ≤ indTypes.size)
    (hsize : recInfos.size = indTypes.size)
    (horiginSize : origin.size = recInfos.size)
    (hframes : ∀ i, i < recInfos.size → SameFrame recInfos[i]! origin[i]!)
    (hprefix : ∀ i, i < dIdx → i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length)
    (hsuffix : ∀ i, dIdx ≤ i → i < recInfos.size →
      recInfos[i]!.minors.size = 0)
    (Hk : ∀ out c, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      out.size = origin.size →
      (∀ i, i < out.size → SameFrame out[i]! origin[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    apply mkRecInfos.loopCtors.resultCount (Q := Q) stats indTypes[dIdx].name dIdx
      recInfos indTypes[dIdx].ctors
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes (dIdx + 1) out k)
      c (by simpa [hsize] using hidx)
    intro out cOut houtSize houtCount houtFrame houtOther
    apply mkRecInfos.loopInd2.resultCounts (Q := Q) stats indTypes (dIdx + 1)
      out origin k cOut
    · omega
    · simpa [hsize] using houtSize
    · omega
    · intro i hiout
      apply SameFrame.trans (b := recInfos[i]!)
      · by_cases heq : i = dIdx
        · subst i
          exact houtFrame
        · rw [houtOther i (by simpa [hsize, houtSize] using hiout) (Ne.symm heq)]
          exact SameFrame.refl _
      · exact hframes i (by simpa [houtSize] using hiout)
    · intro i hi hiout
      by_cases heq : i = dIdx
      · subst i
        rw [houtCount, hsuffix dIdx (by omega) (by simpa [hsize] using hidx)]
        simp [Array.getElem!_eq_getD, Array.getD, hidx]
      · rw [houtOther i (by simpa [hsize, houtSize] using hiout) (Ne.symm heq)]
        exact hprefix i (by omega) (by simpa [hsize, houtSize] using hiout)
    · intro i hi hiout
      rw [houtOther i (by simpa [hsize, houtSize] using hiout) (by omega)]
      exact hsuffix i (by omega) (by simpa [hsize, houtSize] using hiout)
    · exact Hk
  · rw [dif_neg hidx]
    apply Hk recInfos c hsize
    · intro i hi
      exact hprefix i (by omega) hi
    · omega
    · exact hframes
termination_by indTypes.size - dIdx

/-- `loopInd2` changes only the `minors` field of each `RecInfo`; motives,
indices, and major premises remain those constructed by `loopInd1`. -/
theorem resultFrames {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (dIdx : Nat)
    (recInfos : Array AddInductive.RecInfo)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (hdone : dIdx ≤ indTypes.size)
    (hsize : recInfos.size = indTypes.size)
    (Hk : ∀ out c, out.size = recInfos.size →
      (∀ i, i < recInfos.size → SameFrame out[i]! recInfos[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos.loopInd2 stats indTypes dIdx recInfos k c).WF Q := by
  rw [AddInductive.mkRecInfos.loopInd2]
  by_cases hidx : dIdx < indTypes.size
  · rw [dif_pos hidx]
    apply mkRecInfos.loopCtors.resultCount (Q := Q) stats indTypes[dIdx].name dIdx
      recInfos indTypes[dIdx].ctors
      (fun out => AddInductive.mkRecInfos.loopInd2 stats indTypes (dIdx + 1) out k)
      c (by simpa [hsize] using hidx)
    intro out cOut houtSize _ houtFrame houtOther
    apply mkRecInfos.loopInd2.resultFrames (Q := Q) stats indTypes (dIdx + 1)
      out k cOut
    · omega
    · simpa [hsize] using houtSize
    · intro final cFinal hfinalSize hfinalFrames
      apply Hk final cFinal
      · simpa [houtSize] using hfinalSize
      · intro i hi
        apply SameFrame.trans (hfinalFrames i (by simpa [houtSize] using hi))
        by_cases heq : i = dIdx
        · subst i
          exact houtFrame
        · have hsibling := houtOther i hi (Ne.symm heq)
          rw [hsibling]
          exact SameFrame.refl _
  · rw [dif_neg hidx]
    apply Hk recInfos c
    · rfl
    · intro i hi
      exact SameFrame.refl _
termination_by indTypes.size - dIdx

end mkRecInfos.loopInd2

/-- End-to-end structural cardinality theorem for production `mkRecInfos`:
one record per mutual family, initialized by the first pass and populated with
one minor per source constructor by the second pass. -/
theorem mkRecInfos.resultStructure {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (Hk : ∀ (initial out : Array AddInductive.RecInfo)
        (c : AddInductive.Context),
      initial.size = indTypes.size →
      (∀ r ∈ initial.toList, r.minors.isEmpty) →
      out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      (∀ i, i < out.size →
        mkRecInfos.loopInd2.SameFrame out[i]! initial[i]!) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  unfold AddInductive.mkRecInfos
  apply mkRecInfos.loopInd1.resultCount (Q := Q) stats indTypes elimLevel
    0 #[] (fun recInfos =>
      AddInductive.mkRecInfos.loopInd2 stats indTypes 0 recInfos k) c
  · omega
  · simp
  · simp
  · intro recInfos cRec hsize hempty
    apply mkRecInfos.loopInd2.resultCounts (Q := Q) stats indTypes 0
      recInfos recInfos k cRec
    · omega
    · exact hsize
    · rfl
    · intro i hi
      exact mkRecInfos.loopInd2.SameFrame.refl _
    · intro i hi
      omega
    · intro i _ hi
      have he := hempty (recInfos[i]'hi) (Array.getElem_mem_toList hi)
      rw [Array.isEmpty_iff_size_eq_zero] at he
      simpa [Array.getElem!_eq_getD, Array.getD, hi] using he
    · intro out cOut houtSize houtCounts _ houtFrames
      exact Hk recInfos out cOut hsize hempty houtSize houtCounts houtFrames

/-- Cardinality-only projection of `resultStructure`. -/
theorem mkRecInfos.resultCounts {α : Type} {Q : α → Prop}
    (stats : AddInductive.InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (k : Array AddInductive.RecInfo → AddInductive.M α)
    (c : AddInductive.Context)
    (Hk : ∀ out c, out.size = indTypes.size →
      (∀ i, i < out.size →
        out[i]!.minors.size = indTypes[i]!.ctors.length) →
      (k out c).WF Q) :
    (AddInductive.mkRecInfos stats indTypes elimLevel k c).WF Q := by
  apply mkRecInfos.resultStructure (Q := Q) stats indTypes elimLevel k c
  intro _ out cOut _ _ houtSize houtCounts _
  exact Hk out cOut houtSize houtCounts

/-- Per-family minor counts imply the corresponding flattened block count
used by production recursor types. -/
theorem mkRecInfos.flatMinors_size
    {recInfos : Array AddInductive.RecInfo}
    {indTypes : Array InductiveType}
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length) :
    (recInfos.flatMap (·.minors)).size =
      (indTypes.flatMap fun type => type.ctors.toArray).size := by
  rw [Array.size_flatMap, Array.size_flatMap]
  congr 1
  apply Array.ext
  · simp [hsize]
  · intro i hiLeft hiRight
    simp only [Array.getElem_map]
    have hiRec : i < recInfos.size := by simpa using hiLeft
    have hiInd : i < indTypes.size := by omega
    have hc := hcounts i hiRec
    simpa [Array.getElem!_eq_getD, Array.getD, hiRec, hiInd] using hc

theorem ownedConstructors_length_eq_flattened_size
    (indTypes : Array InductiveType) :
    (ownedConstructors indTypes.toList).length =
      (indTypes.flatMap fun type => type.ctors.toArray).size := by
  simp only [ownedConstructors, List.length_flatMap, List.length_map,
    Array.size_flatMap]
  rw [← Array.sum_toList, Array.toList_map]
  simp

theorem mkRecInfos.motives_size_of_translation
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    (Hdecl : TrInductDecl env lparams nparams indTypes.toList isUnsafe decl)
    (hsize : recInfos.size = indTypes.size) :
    (recInfos.map (·.motive)).size = decl.types.length := by
  simp only [Array.size_map]
  rw [hsize]
  simpa using Lean4Lean.VerifyInductive.TrInductDecl.types_length Hdecl

theorem mkRecInfos.flatMinors_size_of_translation
    {indTypes : Array InductiveType}
    {recInfos : Array AddInductive.RecInfo}
    (Hdecl : TrInductDecl env lparams nparams indTypes.toList isUnsafe decl)
    (hsize : recInfos.size = indTypes.size)
    (hcounts : ∀ i, i < recInfos.size →
      recInfos[i]!.minors.size = indTypes[i]!.ctors.length) :
    (recInfos.flatMap (·.minors)).size = decl.ownedConstructors.length := by
  rw [mkRecInfos.flatMinors_size hsize hcounts,
    ← ownedConstructors_length_eq_flattened_size]
  exact Lean4Lean.VerifyInductive.TrInductDecl.ownedConstructors_length Hdecl

/-- Constructor-tail refinement with the verified positivity traversal plugged
into every safe field. -/
theorem checkConstructors.loopCtor.tailRefinesFull
    {decl : VInductDecl} {target : VInductiveType}
    {depth : Nat} {type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorTailWF Hc.venv target Hc.mlctx.vlctx.toCtx
        depth type') := by
  apply checkConstructors.loopCtor.tailRefines Hc Hstats hi htarget
    hparamAt hconsume hlit hctx hproj hunsafe hbound
  · intro c' depth' posIdx type' type'' Hc' Hstats' hctx' htype'
    exact checkPositivity.refines Hc' Hstats' hconsume hlit hctx' hproj htype'
  · exact htr

/-- Regard a constructor constant as the root of a telescope synthesis.  The
existing narrow header certificate only uses the constant fields of its
`target`; the empty constructor list therefore lets the same, already proved
wrapping invariant serve constructor parameter prefixes without duplicating
it. -/
def constructorTelescopeTarget (ctorVal : VConstVal) :
    VInductiveTypeSkeleton where
  toVConstVal := ctorVal
  ctors := []

/-- Initialize constructor telescope synthesis from the independently
translated source constant. -/
noncomputable def ConstructorSynthesisState.initial
    (Hctor : TrSourceConst env Us ctor type ctorVal) :
    checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
      env Us (constructorTelescopeTarget ctorVal) [] ctorVal.type 0 0 := by
  have htype : env.IsType Us.length [] ctorVal.type := by
    have hwf := Hctor.wf
    change env.IsType ctorVal.uvars [] ctorVal.type at hwf
    rwa [Hctor.uvars] at hwf
  let level := Classical.choose htype
  have htyped := Classical.choose_spec htype
  exact checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.empty
    htype htype htyped

/-- A successful cached-parameter comparison advances the semantic
constructor telescope directly.  The executable loop performs no
normalization in this branch: after converting the binder context from the
source domain to the cached parameter type, opening the source body with the
cached free variable supplies the next residual verbatim. -/
theorem checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.consumeConstructorParameter
    (henv : env.WF)
    (H : NarrowHeaderSynthesisCertificate env Us target scope current i 0)
    (htype : TrExprS env Us scope (.forallE name dom body bi) current)
    (hscopeWF : VLCtx.WF env Us.length
      ((some (fv, deps), .vlam paramType) :: scope))
    (hdomain : ∃ sourceDom,
      TrExprS env Us scope dom sourceDom ∧
      env.IsDefEqU Us.length scope.toCtx sourceDom paramType) :
    ∃ next,
      TrExprS env Us ((some (fv, deps), .vlam paramType) :: scope)
        (body.instantiate1' (.fvar fv)) next ∧
      Nonempty (NarrowHeaderSynthesisCertificate env Us target
        ((some (fv, deps), .vlam paramType) :: scope) next (i + 1) 0) := by
  cases htype with
  | forallE hdomType _hbodyType hdom hbody =>
    rcases hdomain with ⟨sourceDom, hsourceDom, hsourceDomEq⟩
    have hscopeEq : VLCtx.IsDefEq env Us.length scope scope :=
      .refl henv H.scopeWF
    have hdomEq : env.IsDefEqU Us.length scope.toCtx _ paramType :=
      (hdom.uniq henv hscopeEq hsourceDom).trans henv H.scopeWF.toCtx
        hsourceDomEq
    have hdomTyped := hdomEq.of_l henv H.scopeWF.toCtx
      (Classical.choose_spec hdomType)
    have hbodyCtx : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: scope)
        ((none, .vlam paramType) :: scope) :=
      .cons hscopeEq nofun (.vlam hdomTyped)
    rcases hbody.defeqDFC henv hbodyCtx with ⟨next, hnext⟩
    have hopened : TrExprS env Us
        ((some (fv, deps), .vlam paramType) :: scope)
        (body.instantiate1' (.fvar fv)) next :=
      hnext.inst_fvar henv.ordered hscopeWF
    have hbodyWF : VLCtx.WF env Us.length
        ((none, .vlam paramType) :: scope) :=
      ⟨H.scopeWF, nofun, ⟨_, hdomTyped.hasType.2⟩⟩
    have hnextRefl : env.IsDefEqU Us.length
        (paramType :: scope.toCtx) next next :=
      hnext.wf henv.ordered hbodyWF
    have hindices : H.indices = [] :=
      List.eq_nil_of_length_eq_zero H.indexCount
    have htype' : TrExprS env Us scope
        (.forallE name dom body bi) (.forallE _ _) :=
      .forallE hdomType _hbodyType hdom hbody
    rcases H.consumeParameter (name := name) (bi := bi)
        henv hindices htype' hscopeWF
        ⟨sourceDom, hsourceDom, hsourceDomEq⟩
        ⟨next, next, hnext, hopened, hnextRefl⟩ with
      ⟨next', hopened', Hnext⟩
    exact ⟨next', hopened', Hnext⟩

/-- Traverse the executable constructor's common-parameter prefix while
building its independent semantic telescope.  The two callbacks isolate the
control-flow boundaries: exact parameter coverage hands the synthesized tail
to the field verifier, while an early non-forall is discharged separately by
the invalid-result argument. -/
theorem checkConstructors.loopCtor.parameterSynthesisWF
    {decl : VInductDecl} {ctorVal : VConstVal}
    (Hc : ContextWF c)
    {Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth}
    (Q : Unit → Prop)
    (Hresult : ∀ {source' : Expr}
        {current' fullCurrent' : VExpr} {fuel' : Nat},
      (Hsynthesis' :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
          Hsuffix.parameterDecls current' decl.nparams 0) →
      TrExprS Hc.venv c.lparams Hsuffix.parameterDecls source' current' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source' fullCurrent' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        source' decl.nparams (fuel' + 1) c).WF Q)
    (Hearly : ∀ {source' : Expr} {scope' : VLCtx}
        {current' fullCurrent' : VExpr} {i' fuel' : Nat},
      i' < decl.nparams →
      (¬ ∃ name dom body bi, source' = .forallE name dom body bi) →
      checkInductiveTypes.loopType.LaterParameterScope
        Hsuffix i' source' →
      (Hsynthesis' :
        checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
          Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
          scope' current' i' 0) →
      TrExprS Hc.venv c.lparams scope' source' current' →
      TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source' fullCurrent' →
      (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
        source' i' (fuel' + 1) c).WF Q)
    (hparams : stats.params.size = decl.nparams)
    (hbound : i ≤ decl.nparams)
    (Hscope : ∀ h : i < stats.params.size,
      checkInductiveTypes.loopType.LaterParameterScope Hsuffix i source)
    (hscopeEq : ∀ h : i < stats.params.size,
      scope = (Hscope h).older)
    (hcompleteScope : i = decl.nparams →
      scope = Hsuffix.parameterDecls)
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
        scope current i 0)
    (htypeNarrow : TrExprS Hc.venv c.lparams scope source current)
    (htypeFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx
      source fullCurrent) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source i fuel c).WF Q := by
  induction fuel generalizing source scope current fullCurrent i with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hi : i < decl.nparams
    · have histats : i < stats.params.size := by
        simpa [hparams] using hi
      by_cases hforall : ∃ name dom body bi,
          source = .forallE name dom body bi
      · rcases hforall with ⟨name, dom, body, bi, rfl⟩
        let Hcurrent := Hscope histats
        have hscope : scope = Hcurrent.older := hscopeEq histats
        subst scope
        cases htypeNarrow with
        | @forallE narrowDom narrowBody _ _ _ _ _
            hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
          rcases TrExpr.forallE_source htypeFull with
            ⟨fullDom, fullBody, hdomFull, hbodyFull,
              _hdomFullType, _hbodyFullType, _hfullCurrent⟩
          rcases Hcurrent.typing with
            ⟨paramTy, paramTy', param', hget, hparamTy,
              hparamTyEq, hparam, hparamType⟩
          have hparamAt : stats.params[i]? = some stats.params[i]! := by
            simp [Array.getElem!_eq_getD, histats]
          refine checkConstructors.loopCtor.parameter.sourceWF
            (Q := Q) Hc hparamAt hget hdomFull hbodyFull
              hparamTy hparam hparamType ?_
          intro heq hopenedFull
          rcases Hcurrent.domainDefEq hdomFull hparamTyEq heq with
            ⟨sourceDom, hsourceDom, hsourceDomEq⟩
          have hconsumedWF : VLCtx.WF Hc.venv c.lparams.length
              ((some (Hcurrent.fv, Hcurrent.deps),
                .vlam Hcurrent.paramType) :: Hcurrent.older) :=
            Hcurrent.lift.wf Hc.checking.tr.wf Hc.mlctx_wf.tr.wf
          have htypeNarrow' : TrExprS Hc.venv c.lparams Hcurrent.older
              (.forallE name dom body bi) (.forallE narrowDom narrowBody) :=
            .forallE hdomNarrowType hbodyNarrowType
              hdomNarrow hbodyNarrow
          rcases Hsynthesis.consumeConstructorParameter
              (name := name) (bi := bi)
              Hc.checking.tr.wf
              htypeNarrow'
              hconsumedWF
              ⟨sourceDom, hsourceDom, hsourceDomEq⟩ with
            ⟨next, hopenedNarrow, ⟨Hsynthesis'⟩⟩
          have hopenedNarrow' : TrExprS Hc.venv c.lparams
              ((some (Hcurrent.fv, Hcurrent.deps),
                .vlam Hcurrent.paramType) :: Hcurrent.older)
              (body.instantiate1 stats.params[i]!) next := by
            simpa [Expr.instantiate1_eq, Hcurrent.parameter] using
              hopenedNarrow
          let Hbody :
              checkInductiveTypes.loopType.LaterParameterScope
                Hsuffix i body :=
            { Hcurrent with fvars := Hcurrent.fvars.2 }
          exact ih (i := i + 1)
            (scope := (some (Hcurrent.fv, Hcurrent.deps),
              .vlam Hcurrent.paramType) :: Hcurrent.older)
            (current := next) (fullCurrent := fullBody.inst param')
            (hbound := by omega)
            (Hscope := fun hlt => Hbody.next hlt (fun _ _ h => h))
            (hscopeEq := fun hlt =>
              Hbody.nextOlder (Hbody.next hlt (fun _ _ h => h)) hlt)
            (hcompleteScope := fun heq => by
              have hdone : i + 1 = stats.params.size := by
                rw [hparams]
                exact heq
              exact Hbody.completedScope hdone)
            Hsynthesis' hopenedNarrow'
            (hopenedFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
      · exact Hearly hi hforall (Hscope histats)
          Hsynthesis htypeNarrow htypeFull
    · have hieq : i = decl.nparams := by omega
      subst i
      have hscope := hcompleteScope rfl
      subst scope
      exact Hresult Hsynthesis htypeNarrow htypeFull

theorem _root_.Lean4Lean.FVarsIn.getAppArgsList
    (H : FVarsIn P e) (ha : a ∈ e.getAppArgsList) : FVarsIn P a := by
  have H' : FVarsIn P
      (e.getAppFn.mkAppRevList e.getAppArgsRevList) := by
    rw [Expr.mkAppRevList_getAppArgsRevList]
    exact H
  have ha' : a ∈ e.getAppArgsRevList := by
    simpa [← Expr.getAppArgsList_reverse] using ha
  exact (FVarsIn.appRevList.mp H').2 a ha'

theorem _root_.Lean4Lean.Expr.eqv_fvar_eq
    (H : (((.fvar fv : Expr) == e)) = true) : e = .fvar fv := by
  cases e <;> simp [(· == ·), Expr.eqv'] at H
  rename_i fv'
  have : fv = fv' := beq_iff_eq.mp H
  cases this
  rfl

/-- A constructor cannot reach its result before consuming every cached
parameter.  A valid result application would contain the current cached free
variable as argument `i`, whereas `LaterParameterScope` proves that the tail
can mention only the strictly older cached parameters. -/
theorem checkConstructors.loopCtor.earlyParameterResult.WF
    (Hc : ContextWF c)
    {Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth}
    (Hscope : checkInductiveTypes.loopType.LaterParameterScope
      Hsuffix i source)
    (hi : i < stats.params.size)
    (hforall : ¬ ∃ name dom body bi,
      source = .forallE name dom body bi) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source i (fuel + 1) c).WF Q := by
  cases hvalid : AddInductive.isValidIndAppIdx stats source targetIdx
  · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
  · have harity := checkPositivityStep.isValidIndAppIdx.arity hvalid
    have hiArgs : i < source.getAppArgs.size := by omega
    have hparam : stats.params[i] = .fvar Hscope.fv := by
      have hparam' := Hscope.parameter
      simpa [hi] using hparam'
    have hargEq := checkPositivityStep.isValidIndAppIdx.param hvalid hi
    rw [hparam] at hargEq
    have harg : source.getAppArgs[i] = .fvar Hscope.fv :=
      Expr.eqv_fvar_eq hargEq
    have hsourceArg : source.getAppArgsList[i]? =
        some source.getAppArgs[i] := by
      rw [← Expr.getAppArgs_toList]
      simp [hiArgs]
    have hmem : source.getAppArgs[i] ∈ source.getAppArgsList :=
      List.mem_of_getElem? hsourceArg
    have hargScope := Hscope.fvars.getAppArgsList hmem
    rw [harg] at hargScope
    have hsuffixWF := Hscope.lift.wf Hc.checking.tr.wf
      Hc.mlctx_wf.tr.wf
    have hfresh : Hscope.fv ∉ Hscope.older.fvars :=
      (hsuffixWF.2.1 Hscope.fv Hscope.deps rfl).1
    exact False.elim (hfresh hargScope)

/-- Constructor-tail refinement in the independent parameter/field scope.
The executable traversal remains in the retained mutual-header context, but
the resulting `CtorTailWF` never mentions those ambient declarations. -/
theorem checkConstructors.loopCtor.tailRefinesNarrow
    {decl : VInductDecl} {target : VInductiveType}
    {scope : VLCtx} {depth : Nat} {narrowType fullType : VExpr}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl depth)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorTailWF Hc.venv target scope.toCtx
        depth narrowType) := by
  induction fuel generalizing c type scope narrowType fullType depth i with
  | zero => exact checkConstructors.loopCtor.zero.WF
  | succ fuel ih =>
    by_cases hforall : ∃ name dom body bi,
        type = .forallE name dom body bi
    · rcases hforall with ⟨name, dom, body, bi, rfl⟩
      rcases htrFull with ⟨fullForall, hfullForall, hfullTarget⟩
      cases htrNarrow with
      | @forallE narrowDom narrowBody _ _ _ _ _
          hdomNarrowType hbodyNarrowType hdomNarrow hbodyNarrow =>
        cases hfullForall with
        | @forallE fullDom fullBody _ _ _ _ _
            hdomFullType _ hdomFull hbodyFull =>
          rcases hconsume c Hc hdomFull hdomFullType with
            ⟨consumedDom, Hdom⟩
          have hparamNext : stats.params[i + 1]? = none := by
            rw [Array.getElem?_eq_none_iff] at hparamAt ⊢
            omega
          have hdeps : dom.consumeTypeAnnotations.fvarsList ⊆ scope.fvars :=
            (fvarsIn_iff.mp
              (Expr.consumeTypeAnnotations_fvarsIn hdomNarrow.fvarsIn)).1
          rcases Hruntime.consumedDomain Hc Hdom hdomNarrow with
            ⟨domainLevel, hdomain⟩
          cases isUnsafe with
          | false =>
            have Hpos := checkPositivity.refinesNarrow
              (ctor := ctor) (idx := i) Hc Hruntime Hstats
              hconsume hlit hproj hdomNarrow
              (hdomFull.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)
            refine checkConstructors.loopCtor.safeField.sourceWF
              (Q := fun _ => decl.CtorTailWF Hc.venv target scope.toCtx
                depth (.forallE narrowDom narrowBody))
              Hc hparamAt Hdom hbodyFull Hpos ?_
            intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped
              hfieldBound hpositive bodyFull' _hbodyFullEq hopenedFull
            let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType
            let Hruntime' :
                checkInductiveTypes.loopType.NarrowRuntimeScope
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    dom.consumeTypeAnnotations.fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
            have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            have Htail := ih Hc' Hruntime' Hstats' hparamNext hbound
              hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
            exact Htail.mono fun _ htail => by
              have hfieldNarrow := Hruntime.hasTypeOfFull
                Hc.checking.tr.wf hdomNarrow hfield htyped
              have hfieldEq := hfieldNarrow
              change Hc.venv.IsDefEq c.lparams.length scope.toCtx
                narrowDom narrowDom (.sort fieldLevel') at hfieldEq
              rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
              change Hc.venv.IsDefEq c.lparams.length
                (narrowDom :: scope.toCtx) narrowBody narrowBody
                (.sort bodyLevel) at hbodyTyped
              exact .field
                (by simpa [Hstats.uvars] using hfieldNarrow)
                (hbound fieldLevel fieldLevel' hlevel hfieldBound)
                (Or.inr hpositive)
                (by simpa [Hstats.uvars] using hfieldEq)
                (by simpa [Hstats.uvars] using hbodyTyped)
                htail
          | true =>
            refine checkConstructors.loopCtor.unsafeField.sourceWF
              (Q := fun _ => decl.CtorTailWF Hc.venv target scope.toCtx
                depth (.forallE narrowDom narrowBody))
              Hc hparamAt Hdom hbodyFull ?_
            intro fieldType' fieldLevel fieldLevel' hfield hlevel htyped
              hfieldBound bodyFull' _hbodyFullEq hopenedFull
            let Hc' := Hc.withLocalDecl (name := name) (bi := bi)
              Hdom.consumed Hdom.isType
            let Hruntime' :
                checkInductiveTypes.loopType.NarrowRuntimeScope
                  Hc'.venv c.lparams
                  ((some (⟨c.ngen.curr⟩,
                    dom.consumeTypeAnnotations.fvarsList),
                    .vlam narrowDom) :: scope)
                  Hc'.mlctx.vlctx :=
              Hruntime.withIndex Hc'.mlctx_wf.tr.wf hdeps hdomain
            have hscopeWF := Hruntime'.scopeWF Hc'.checking.tr.wf
            have hopenedNarrow : TrExprS Hc'.venv c.lparams
                ((some (⟨c.ngen.curr⟩,
                  dom.consumeTypeAnnotations.fvarsList),
                  .vlam narrowDom) :: scope)
                (body.instantiate1 (.fvar ⟨c.ngen.curr⟩)) narrowBody := by
              rw [Expr.instantiate1_eq]
              exact hbodyNarrow.inst_fvar Hc.checking.tr.wf.ordered hscopeWF
            have Hstats' := Hstats.withFVar Hc'.checking.tr.wf hscopeWF
            have Htail := ih Hc' Hruntime' Hstats' hparamNext hbound
              hopenedNarrow
              (hopenedFull.trExpr Hc'.checking.tr.wf Hc'.mlctx_wf.tr.wf)
            exact Htail.mono fun _ htail => by
              have hfieldNarrow := Hruntime.hasTypeOfFull
                Hc.checking.tr.wf hdomNarrow hfield htyped
              have hfieldEq := hfieldNarrow
              change Hc.venv.IsDefEq c.lparams.length scope.toCtx
                narrowDom narrowDom (.sort fieldLevel') at hfieldEq
              rcases hbodyNarrowType with ⟨bodyLevel, hbodyTyped⟩
              change Hc.venv.IsDefEq c.lparams.length
                (narrowDom :: scope.toCtx) narrowBody narrowBody
                (.sort bodyLevel) at hbodyTyped
              exact .field
                (by simpa [Hstats.uvars] using hfieldNarrow)
                (hbound fieldLevel fieldLevel' hlevel hfieldBound)
                (Or.inl (hunsafe rfl))
                (by simpa [Hstats.uvars] using hfieldEq)
                (by simpa [Hstats.uvars] using hbodyTyped)
                htail
    · cases hvalid : AddInductive.isValidIndAppIdx stats type targetIdx
      · exact checkConstructors.loopCtor.invalidResult.WF hforall hvalid
      · rcases htrNarrow.wf Hc.checking.tr.wf
          (Hruntime.scopeWF Hc.checking.tr.wf) with ⟨exprType, htype⟩
        subst target
        exact checkConstructors.loopCtor.result.refines Hstats hi htrNarrow
          hforall hvalid hlit
          (Hruntime.noIndConsts (decl.types.map (·.name))) hproj
          (by simpa [Hstats.uvars] using htype)

/-- Aggregation boundary for constructors: once the common-parameter prefix
has supplied its independent `takeForalls` and parameter-conversion facts, the
verified executable tail establishes the public `CtorShape` judgment. -/
theorem checkConstructors.loopCtor.ctorShapeRefines
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params ownParams : List VExpr}
    {normalized tail exprType type' : VExpr}
    (Hc : ContextWF c)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hc.mlctx.vlctx stats decl 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hctx : checkPositivityStep.VLCtx.NoIndConsts
      (decl.types.map (·.name)) Hc.mlctx.vlctx)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hctor : Hc.venv.IsDefEq decl.uvars [] ctorVal.type normalized exprType)
    (htake : normalized.takeForalls decl.nparams = some (ownParams, tail))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (hctxEq : Hc.mlctx.vlctx.toCtx = ownParams.reverse)
    (htailEq : type' = tail)
    (htr : TrExprS Hc.venv c.lparams Hc.mlctx.vlctx type type') :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal) := by
  have Htail := checkConstructors.loopCtor.tailRefinesFull
    (ctor := ctor) (fuel := fuel) Hc Hstats hi
    htarget hparamAt hconsume hlit hctx hproj hunsafe hbound htr
  exact Htail.mono fun _ htail => by
    subst type'
    have hctxRefl : VEnv.IsDefEqCtx Hc.venv decl.uvars []
        Hc.mlctx.vlctx.toCtx Hc.mlctx.vlctx.toCtx :=
      .refl (by simpa [Hstats.uvars] using Hc.mlctx_wf.tr.wf.toCtx)
    exact ⟨normalized, ownParams, tail, exprType,
      Hc.mlctx.vlctx.toCtx, hctor, htake, hparams,
      by rw [← hctxEq]; exact hctxRefl, htail⟩

/-- Public constructor-shape refinement from the independent cached-parameter
scope.  `tailCtx` is allowed to be definitionally equal to the normalized
constructor parameters, which is the semantic relation supplied by mutual
header materialization. -/
theorem checkConstructors.loopCtor.ctorShapeRefinesNarrow
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params ownParams : List VExpr}
    {normalized tail exprType narrowType fullType : VExpr}
    {scope : VLCtx}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[i]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hctor : Hc.venv.IsDefEq decl.uvars [] ctorVal.type normalized exprType)
    (htake : normalized.takeForalls decl.nparams = some (ownParams, tail))
    (hparams : decl.ParamsDefEq Hc.venv params ownParams)
    (htailCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      ownParams.reverse scope.toCtx)
    (htailEq : narrowType = tail)
    (htrNarrow : TrExprS Hc.venv c.lparams scope type narrowType)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx type fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      type i fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal) := by
  have Htail := checkConstructors.loopCtor.tailRefinesNarrow
    (ctor := ctor) (fuel := fuel) Hc Hruntime Hstats hi htarget hparamAt
    hconsume hlit hproj hunsafe hbound htrNarrow htrFull
  exact Htail.mono fun _ htail => by
    subst narrowType
    exact ⟨normalized, ownParams, tail, exprType, scope.toCtx,
      hctor, htake, hparams, htailCtx, htail⟩

/-- Close a completely consumed constructor-parameter synthesis directly
against the verified field tail.  In particular, the normalized constructor
type and its `takeForalls` decomposition are outputs of the synthesis
certificate rather than assumptions reconstructed by the caller. -/
theorem checkConstructors.loopCtor.ctorShapeRefinesOfSynthesis
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params : List VExpr}
    {source : Expr} {current fullType : VExpr} {scope : VLCtx}
    (Hc : ContextWF c)
    (Hruntime : checkInductiveTypes.loopType.NarrowRuntimeScope
      Hc.venv c.lparams scope Hc.mlctx.vlctx)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      scope stats decl 0)
    (Hsynthesis :
      checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate
        Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
        scope current decl.nparams 0)
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hparamAt : stats.params[decl.nparams]? = none)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel)
    (hparams : decl.ParamsDefEq Hc.venv params Hsynthesis.params)
    (htrNarrow : TrExprS Hc.venv c.lparams scope source current)
    (htrFull : TrExpr Hc.venv c.lparams Hc.mlctx.vlctx source fullType) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source decl.nparams fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal) := by
  have hindices : Hsynthesis.indices = [] :=
    List.eq_nil_of_length_eq_zero Hsynthesis.indexCount
  have htake :
      (VExpr.wrapForalls Hsynthesis.params current).takeForalls decl.nparams =
        some (Hsynthesis.params, current) := by
    simpa [Hsynthesis.parameterCount] using
      VExpr.takeForalls_wrapForalls Hsynthesis.params current
  have htailCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      Hsynthesis.params.reverse scope.toCtx := by
    have hrefl : VEnv.IsDefEqCtx Hc.venv decl.uvars []
        scope.toCtx scope.toCtx :=
      .refl (by simpa [Hstats.uvars] using Hsynthesis.scopeWF.toCtx)
    simpa [Hsynthesis.scopeCtx, hindices] using hrefl
  apply checkConstructors.loopCtor.ctorShapeRefinesNarrow
    (ctor := ctor) (fuel := fuel) Hc Hruntime Hstats hi htarget
    hparamAt hconsume hlit hproj hunsafe hbound
    (normalized := VExpr.wrapForalls Hsynthesis.params current)
    (tail := current) (exprType := Hsynthesis.exprType)
    (ownParams := Hsynthesis.params)
  · simpa [constructorTelescopeTarget, hindices, Hstats.uvars] using
      Hsynthesis.header
  · exact htake
  · exact hparams
  · exact htailCtx
  · rfl
  · exact htrNarrow
  · exact htrFull

/-- End-to-end constructor telescope refinement in a single verifier
environment.  The source constructor is independently translated in the
empty scope; the executable closed-type result supplies its retained-runtime
translation.  Cached common parameters are consumed by
`parameterSynthesisWF`, and all remaining binders are checked by the narrow
positivity refinement. -/
theorem checkConstructors.loopCtor.refinesCtorShape
    {decl : VInductDecl} {target : VInductiveType}
    {ctorVal : VConstVal} {params : List VExpr}
    (Hc : ContextWF c)
    (Hsuffix : checkInductiveTypes.loopType.ParameterContextSuffix
      Hc stats depth)
    (Hstats : checkPositivityStep.ValidAppStatsWF Hc.venv c.lparams
      Hsuffix.parameterDecls stats decl 0)
    (hparamsCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hsuffix.parameterDecls.toCtx)
    (Hctor : TrSourceConst Hc.venv c.lparams ctor source ctorVal)
    (hchecked : TrTyping Hc.venv c.lparams Hc.mlctx.vlctx
      source checkedType fullType checkedType')
    (hi : targetIdx < decl.types.length)
    (htarget : decl.types[targetIdx] = target)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      target.resultLevel = .zero ∨ fieldLevel' ≤ target.resultLevel) :
    (AddInductive.checkConstructors.loopCtor stats isUnsafe ctor targetIdx
      source 0 fuel c).WF
      (fun _ => decl.CtorShape Hc.venv params target ctorVal) := by
  have hnoFVars : FVarsIn (fun _ => False) source := by
    simpa [VLCtx.fvars] using Hctor.type.fvarsIn
  let Hinitial := ConstructorSynthesisState.initial Hctor
  apply checkConstructors.loopCtor.parameterSynthesisWF
    (decl := decl) (ctorVal := ctorVal) Hc
    (Q := fun _ => decl.CtorShape Hc.venv params target ctorVal)
    (Hresult := by
      intro source' current' fullCurrent' fuel'
        Hsynthesis' htrNarrow htrFull
      have hindices : Hsynthesis'.indices = [] :=
        List.eq_nil_of_length_eq_zero Hsynthesis'.indexCount
      have hscopeCtx : Hsuffix.parameterDecls.toCtx =
          Hsynthesis'.indices.reverse ++ Hsynthesis'.params.reverse :=
        @checkInductiveTypes.loopType.NarrowHeaderSynthesisCertificate.scopeCtx
          Hc.venv c.lparams (constructorTelescopeTarget ctorVal)
          Hsuffix.parameterDecls current' decl.nparams 0 Hsynthesis'
      have hparams : decl.ParamsDefEq Hc.venv
          params Hsynthesis'.params := by
        change VEnv.IsDefEqCtx Hc.venv decl.uvars []
          params.reverse Hsynthesis'.params.reverse
        simpa [hscopeCtx, hindices] using hparamsCtx
      have hparamAt : stats.params[decl.nparams]? = none := by
        rw [Array.getElem?_eq_none_iff]
        exact Nat.le_of_eq Hstats.params_size
      exact checkConstructors.loopCtor.ctorShapeRefinesOfSynthesis
        (ctor := ctor) (fuel := fuel' + 1) Hc
        (checkInductiveTypes.loopType.NarrowRuntimeScope.ofParameterSuffix
          Hc Hsuffix)
        Hstats Hsynthesis' hi htarget hparamAt hconsume hlit hproj
        hunsafe hbound hparams htrNarrow htrFull)
    (Hearly := by
      intro source' scope' current' fullCurrent' i' fuel' hi'
        hforall Hscope' _Hsynthesis' _htrNarrow _htrFull
      exact checkConstructors.loopCtor.earlyParameterResult.WF
        (fuel := fuel') Hc Hscope'
        (by simpa [Hstats.params_size] using hi') hforall)
    Hstats.params_size (by omega)
    (fun h =>
      checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars h hnoFVars)
    (fun h =>
      (checkInductiveTypes.loopType.LaterParameterScope.ofNoFVars
        h hnoFVars).older_eq_nil h |>.symm)
    (by
      intro hzero
      have hlength := Hsuffix.parameterDecls_length
      have hempty : Hsuffix.parameterDecls = [] :=
        List.eq_nil_of_length_eq_zero (by
          rw [hlength, Hstats.params_size, hzero])
      exact hempty.symm)
    Hinitial Hctor.type
    (hchecked.2.1.trExpr Hc.checking.tr.wf Hc.mlctx_wf.tr.wf)

/-- Fold the end-to-end constructor theorem over the production's nested
family/constructor loops.  This is the constructor-formation result consumed
by `FormationCertificate`; environment installation is intentionally a
separate staging obligation. -/
theorem checkConstructors.loopTypes.refinesMaterialized
    {decl : VInductDecl} {sourceEnv : VEnv}
    {params : List VExpr}
    (Hc : ContextWF c)
    (Htypes : List.Forall₂
      (TrInductiveType sourceEnv Hc.venv c.lparams)
      indTypes.toList decl.types)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hparams : Hmaterialized.headers.params = params)
    (Hfresh : ∀ targetIdx (htarget : targetIdx < indTypes.size)
      {i found}, ConstructorNameState indTypes[targetIdx].ctors i found →
      (hi : i < indTypes[targetIdx].ctors.length) →
      found.contains indTypes[targetIdx].ctors[i].name = false)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel = .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel) :
    (AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0 c).WF
      (fun _ => ConstructorCertificate sourceEnv decl Hc.venv params) := by
  let Hsuffix := Hmaterialized.parameterSuffix
  let Hstats :=
    checkPositivityStep.ValidAppStatsWF.ofMaterializedHeaderNarrow
      Hmaterialized
  have hparamsCtx : VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hsuffix.parameterDecls.toCtx := by
    change VEnv.IsDefEqCtx Hc.venv decl.uvars []
      params.reverse Hmaterialized.parameterScope.toCtx
    subst params
    simpa [Hmaterialized.uvars] using Hmaterialized.paramsContext
  apply checkConstructors.loopTypes.refinesBlock
    (Q := fun _ => ConstructorCertificate sourceEnv decl Hc.venv params)
    Hc Htypes (ConstructorTypesPrefix.empty Hc.venv decl params)
    Hfresh
  · intro targetIdx hsource htarget ctorIdx hctorSource hctorTarget
      Hctor checkedType fullType checkedType' hchecked
    apply checkConstructors.loopCtor.refinesCtorShape
      (fuel := c.fuel.inductiveFuel) Hc Hsuffix Hstats hparamsCtx
      Hctor hchecked htarget rfl hconsume hlit hproj hunsafe
    exact hbound targetIdx htarget
  · intro Hcomplete
    exact Hcomplete.complete (env := sourceEnv)

@[simp] theorem VInductDecl.recursorName_eq_mkRecName
    (decl : VInductDecl) (type : VInductiveType) :
    decl.recursorName type = Lean.mkRecName type.name := rfl

/-- The production choice of an extra eliminator universe has exactly the two
universe arities admitted by `RecursorShape`. -/
theorem AddInductive.getRecLevelParams_length :
    (AddInductive.getRecLevelParams elimLevel lparams).length = lparams.length ∨
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length + 1 := by
  cases elimLevel with
  | param u => simp [AddInductive.getRecLevelParams]
  | _ => simp [AddInductive.getRecLevelParams]

theorem AddInductive.getRecLevelParams_length_of_param
    (h : elimLevel.isParam = true) :
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length + 1 := by
  cases elimLevel <;> simp_all [AddInductive.getRecLevelParams, Level.isParam]

theorem AddInductive.getRecLevelParams_length_of_not_param
    (h : elimLevel.isParam = false) :
    (AddInductive.getRecLevelParams elimLevel lparams).length =
      lparams.length := by
  cases elimLevel <;> simp_all [AddInductive.getRecLevelParams, Level.isParam]

/-- Abstract domains introduced by `MLCtx.mkForall'`, in outermost-to-
innermost order. Local lets are discharged by `mkForall'` and contribute no
domain. -/
def MLCtxForallDomains (c : TypeChecker.MLCtx) :
    (n : Nat) → n ≤ c.length → List VExpr
  | 0, _ => []
  | n + 1, h =>
    match c with
    | .vlam _ _ _ type' _ c =>
      MLCtxForallDomains c n (Nat.le_of_succ_le_succ h) ++ [type']
    | .vlet _ _ _ _ _ _ c =>
      MLCtxForallDomains c n (Nat.le_of_succ_le_succ h)

theorem TypeChecker.MLCtx.mkForall'_eq_wrapForalls
    (c : TypeChecker.MLCtx) (n : Nat) (hn : n ≤ c.length) (body : VExpr) :
    c.mkForall' n hn body = VExpr.wrapForalls (MLCtxForallDomains c n hn) body := by
  induction n generalizing c body with
  | zero => simp [TypeChecker.MLCtx.mkForall', MLCtxForallDomains,
      VExpr.wrapForalls]
  | succ n ih =>
    cases c with
    | nil => simp at hn
    | vlam fv name type type' bi c =>
      simp only [TypeChecker.MLCtx.mkForall', MLCtxForallDomains]
      rw [ih, VExpr.wrapForalls_append]
      rfl
    | vlet fv name type value type' value' c =>
      simp only [TypeChecker.MLCtx.mkForall', MLCtxForallDomains]
      exact ih c (Nat.le_of_succ_le_succ hn) body

/-- Exact certificate for a suffix of local declarations introduced by
`withLocalDecl`; its domains are recorded in the same outermost-to-innermost
order used by generated recursor telescopes. -/
inductive MLCtxLamPrefix : TypeChecker.MLCtx → Nat → List VExpr → Prop
  | nil (c : TypeChecker.MLCtx) : MLCtxLamPrefix c 0 []
  | cons : MLCtxLamPrefix c n domains →
      MLCtxLamPrefix (.vlam fv name type type' bi c) (n + 1)
        (domains ++ [type'])

theorem MLCtxLamPrefix.le
    (H : MLCtxLamPrefix c n domains) : n ≤ c.length := by
  induction H with
  | nil => simp
  | cons _ ih => simpa using Nat.succ_le_succ ih

theorem MLCtxLamPrefix.forallDomains
    (H : MLCtxLamPrefix c n domains) :
    MLCtxForallDomains c n H.le = domains := by
  induction H with
  | nil => simp [MLCtxForallDomains]
  | cons H ih =>
    simp only [MLCtxForallDomains]
    change MLCtxForallDomains _ _ H.le ++ [_] = _
    rw [ih]

theorem MLCtxLamPrefix.mkForall'
    (H : MLCtxLamPrefix c n domains) (body : VExpr) :
    c.mkForall' n H.le body = VExpr.wrapForalls domains body := by
  rw [TypeChecker.MLCtx.mkForall'_eq_wrapForalls, H.forallDomains]

/-- Production-side installation of a list of kernel constants. This small
reference function is used only to state the staging invariant; the executable
inductive checker continues to build the same environments directly. -/
def addConstants : Environment → List ConstantInfo → Environment
  | env, [] => env
  | env, ci :: cis => addConstants (env.add ci) cis

/-- A certificate that a list of production constants and abstract constants
are installed in lockstep. Each translation and typing premise is stated in
the environment at the exact point where that constant is introduced. -/
inductive AddConstants (safety : DefinitionSafety) :
    Environment → VEnv → List (ConstantInfo × VConstVal) →
      Environment → VEnv → Prop
  | nil : AddConstants safety env venv [] env venv
  | cons :
    env.find? ci.name = none →
    ¬ Kernel.Environment.primitives.contains ci.name →
    TrConstVal safety venv ci ci' →
    ci'.toVConstant.WF venv →
    venv.addConst ci.name ci'.toVConstant = some venv' →
    ci.deltaValue? = none →
    AddConstants safety (env.add ci) venv' rest outEnv outVEnv →
    AddConstants safety env venv ((ci, ci') :: rest) outEnv outVEnv

/-- A successful executable installation fold yields the lockstep production
/ abstract staging certificate. Translation and typing may be proved in an
earlier environment and are transported through the already installed
prefix. -/
theorem AddConstants.ofDeclareInductiveTypeInfos
    (Hvalid : CheckingEnv.Valid safety env venv)
    (Hentries : List.Forall₂
      (fun info ci' =>
        TrConstVal safety sourceEnv (.inductInfo info) ci' ∧
          ci'.toVConstant.WF sourceEnv)
      infos values)
    (hle : sourceEnv ≤ venv)
    (hadd : venv.addConsts values = some outVEnv)
    (hnprim : ∀ info ∈ infos,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypeInfos allowPrimitive infos env).WF
      fun outEnv =>
        AddConstants safety env venv
          (List.zip (infos.map (fun info => .inductInfo info)) values)
          outEnv outVEnv := by
  induction Hentries generalizing env venv with
  | nil =>
    simp [AddInductive.declareInductiveTypeInfos, VEnv.addConsts] at hadd ⊢
    subst outVEnv
    exact Except.WF.pure .nil
  | @cons info ci' infos values Hentry _ ih =>
    have hname : info.name = ci'.name := Hentry.1.2
    cases hnext : venv.addConst ci'.name ci'.toVConstant with
    | none => simp [VEnv.addConsts, hnext] at hadd
    | some nextVEnv =>
      have hrest : nextVEnv.addConsts values = some outVEnv := by
        simpa [VEnv.addConsts, hnext] using hadd
      have hnprimHead := hnprim info (by simp)
      have hnprimTail : ∀ info ∈ infos,
          ¬ Kernel.Environment.primitives.contains info.name := by
        intro info hinfo
        exact hnprim info (by simp [hinfo])
      rw [AddInductive.declareInductiveTypeInfos]
      exact (checkName.WF Hvalid.tr.map_wf info.name allowPrimitive).bind
        fun _ hchecked => by
          have hn : env.find? info.name = none := hchecked.1
          have htr : TrConstVal safety venv (.inductInfo info) ci' :=
            Hentry.1.mono hle
          have hwf : ci'.toVConstant.WF venv := Hentry.2.mono hle
          have haddHead :
              venv.addConst info.name ci'.toVConstant = some nextVEnv := by
            simpa [hname] using hnext
          have HnextValid : CheckingEnv.Valid safety
              (env.add (.inductInfo info)) nextVEnv :=
            Hvalid.add hn hnprimHead htr.1 hwf haddHead rfl
          have hnextLe : sourceEnv ≤ nextVEnv :=
            hle.trans (VEnv.addConst_le haddHead)
          exact (ih HnextValid hnextLe hrest hnprimTail).mono fun outEnv Hrest => by
            simpa using AddConstants.cons (ci := .inductInfo info)
              (ci' := ci') hn hnprimHead htr hwf haddHead rfl Hrest

theorem AddConstants.valid
    (H : AddConstants safety env venv entries outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety outEnv outVEnv := by
  induction H with
  | nil => exact hvalid
  | cons hn hnprim htr hwf hadd hdelta _ ih =>
    exact ih (hvalid.add hn hnprim htr.1 hwf hadd hdelta)

theorem AddConstants.production
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    addConstants env (entries.map Prod.fst) = outEnv := by
  induction H with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simpa [addConstants] using ih

theorem AddConstants.abstract
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv.addConsts (entries.map Prod.snd) = some outVEnv := by
  induction H with
  | nil => simp [VEnv.addConsts]
  | cons _ _ htr _ hadd _ _ ih =>
    rw [List.map_cons, VEnv.addConsts, ← htr.2, hadd]
    exact ih

theorem AddConstants.le
    (H : AddConstants safety env venv entries outEnv outVEnv) :
    venv ≤ outVEnv :=
  VEnv.addConsts_le H.abstract

/-- Verified boundary after installing all mutual type constants and before
checking any constructor. The executable and abstract environments are
aligned, while the original source-to-constructor translation already points
at this exact abstract header environment. -/
structure DeclaredTypesResult (c : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (decl : VInductDecl)
    (depth : Nat) (sourceEnv : VEnv)
    (indTypes : Array InductiveType) (outEnv : Environment) where
  entries : List (ConstantInfo × VConstVal)
  context : ContextWF { c with env := outEnv }
  headers : HeaderCertificate sourceEnv decl
  typesInstalled : sourceEnv.addConsts decl.typeConstants = some context.venv
  sourceTypes : List.Forall₂
    (TrInductiveType sourceEnv context.venv c.lparams)
    indTypes.toList decl.types
  installed : AddConstants c.safety c.env sourceEnv entries outEnv context.venv
  materialized : checkInductiveTypes.loopInd.MaterializedHeaderResult
    context.venv c.lparams context.mlctx.vlctx stats decl depth
  headerParams : materialized.headers.params = headers.params

/-- End-to-end refinement of `declareInductiveTypes`: a successful executable
fold installs precisely the independently specified mutual headers and
transports the materialized header certificate into that environment. -/
theorem AddInductive.declareInductiveTypes.WF
    (Hc : ContextWF c)
    (Hdecl : TrInductDecl Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name) :
    (AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe c).WF fun outEnv =>
        ∃ _ : DeclaredTypesResult c stats decl depth Hc.venv
          indTypes outEnv, True := by
  rcases Hdecl with
    ⟨hsource, huvars, hnparams, hunsafe, envTypes, envCtors,
      htypesAdded, hctorsAdded, Htypes⟩
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
  have Hinstall := AddConstants.ofDeclareInductiveTypeInfos
    (allowPrimitive := c.allowPrimitive)
    Hc.checking Hentries VEnv.LE.rfl htypesAdded (by
      simpa [infos] using hnprim)
  change (AddInductive.declareInductiveTypeInfos c.allowPrimitive
    infos.toList c.env).WF _
  exact Hinstall.mono fun outEnv Hinstalled => by
    refine ⟨{
      entries := List.zip
        (infos.toList.map (fun info => .inductInfo info)) decl.typeConstants
      context := Hc.withEnv (Hinstalled.valid Hc.checking) Hinstalled.le
      headers := Hmaterialized.headers
      typesInstalled := htypesAdded
      sourceTypes := Htypes
      installed := Hinstalled
      materialized := Hmaterialized.mono Hinstalled.le
      headerParams := rfl }, trivial⟩

def DeclaredTypesResult.formation
    (H : DeclaredTypesResult c stats decl depth sourceEnv indTypes outEnv)
    (Hconstructors : ConstructorCertificate sourceEnv decl H.context.venv
      H.headers.params) :
    FormationCertificate sourceEnv decl where
  headers := H.headers
  envTypes := H.context.venv
  typesInstalled := H.typesInstalled
  constructors := Hconstructors

theorem AddInductive.checkConstructors.WF
    (H : DeclaredTypesResult c stats decl depth sourceEnv indTypes outEnv)
    (Hfresh : ∀ targetIdx (htarget : targetIdx < indTypes.size)
      {i found}, ConstructorNameState indTypes[targetIdx].ctors i found →
      (hi : i < indTypes[targetIdx].ctors.length) →
      found.contains indTypes[targetIdx].ctors[i].name = false)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel = .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel) :
    (AddInductive.checkConstructors indTypes stats isUnsafe
      { c with env := outEnv }).WF fun _ =>
        ConstructorCertificate sourceEnv decl H.context.venv H.headers.params := by
  have Hloops := checkConstructors.loopTypes.refinesMaterialized
    H.context H.sourceTypes H.materialized H.headerParams Hfresh hconsume
    hlit hproj hunsafe hbound
  rw [AddInductive.checkConstructors]
  change (((liftM TypeChecker.getEnv : AddInductive.M _) >>= fun _ =>
    AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0)
      { c with env := outEnv }).WF _
  change (((liftM TypeChecker.getEnv : AddInductive.M _)
    { c with env := outEnv } >>= fun _ =>
      AddInductive.checkConstructors.loopTypes indTypes stats isUnsafe 0
        { c with env := outEnv }).WF _)
  rw [show (liftM TypeChecker.getEnv : AddInductive.M _)
    { c with env := outEnv } = .ok outEnv from rfl]
  exact Hloops

/-- The exact executable prefix used by `AddInductive.run`, through mutual
header installation and constructor checking, refines `FormationWF`. -/
theorem AddInductive.formationPrefix.WF
    (Hc : ContextWF c)
    (Hdecl : TrInductDecl Hc.venv c.lparams numParams
      indTypes.toList isUnsafe decl)
    (Hmaterialized :
      checkInductiveTypes.loopInd.MaterializedHeaderResult
        Hc.venv c.lparams Hc.mlctx.vlctx stats decl depth)
    (hvisible : c.safety ≤
      (if isUnsafe then DefinitionSafety.unsafe else .safe))
    (hnprim : ∀ info ∈
      (AddInductive.inductiveTypeInfos stats numParams indTypes numNested
        isUnsafe c.lparams).toList,
      ¬ Kernel.Environment.primitives.contains info.name)
    (Hfresh : ∀ targetIdx (htarget : targetIdx < indTypes.size)
      {i found}, ConstructorNameState indTypes[targetIdx].ctors i found →
      (hi : i < indTypes[targetIdx].ctors.length) →
      found.contains indTypes[targetIdx].ctors[i].name = false)
    (hconsume : ConsumeTypeAnnotationsCompat)
    (hlit : checkPositivityStep.LiteralDisjoint stats.indConsts)
    (hproj : ∀ {Δ : VLCtx} {s j e' e''}, TrProj Δ.toCtx s j e' e'' →
      e'.containsAnyConst (decl.types.map (·.name)) = false →
      e''.containsAnyConst (decl.types.map (·.name)) = false)
    (hunsafe : isUnsafe = true → decl.isUnsafe = true)
    (hbound : ∀ targetIdx (hi : targetIdx < decl.types.length)
      fieldLevel fieldLevel',
      VLevel.ofLevel c.lparams fieldLevel = some fieldLevel' →
      (stats.resultLevel.isAlwaysZero ||
        stats.resultLevel.geq (Expr.sort fieldLevel).sortLevel!) = true →
      decl.types[targetIdx].resultLevel = .zero ∨
        fieldLevel' ≤ decl.types[targetIdx].resultLevel) :
    ((AddInductive.declareInductiveTypes stats numParams indTypes numNested
      isUnsafe >>= fun outEnv =>
        AddInductive.withEnv outEnv
          (AddInductive.checkConstructors indTypes stats isUnsafe)) c).WF
      fun _ => Nonempty (FormationCertificate Hc.venv decl) := by
  have Htypes := AddInductive.declareInductiveTypes.WF Hc Hdecl Hmaterialized
    hvisible hnprim
  exact Htypes.bind fun outEnv hresult => by
    rcases hresult with ⟨Hstaged, _⟩
    have Hconstructors := AddInductive.checkConstructors.WF Hstaged Hfresh
      hconsume hlit hproj hunsafe hbound
    exact Hconstructors.mono fun _ Hctors => ⟨Hstaged.formation Hctors⟩

/-- Three-stage installation certificate matching the executable order:
mutual headers, constructors, then recursors. Reduction equations are not
included here because their validity depends on the independent iota schema. -/
structure StagedBlock (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (outEnv : Environment) (outVEnv : VEnv) where
  envTypes : Environment
  venvTypes : VEnv
  envCtors : Environment
  venvCtors : VEnv
  typesAdded : AddConstants safety env venv types envTypes venvTypes
  ctorsAdded : AddConstants safety envTypes venvTypes ctors envCtors venvCtors
  recursorsAdded : AddConstants safety envCtors venvCtors recursors outEnv outVEnv

theorem StagedBlock.valid
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv)
    (hvalid : CheckingEnv.Valid safety env venv) :
    CheckingEnv.Valid safety outEnv outVEnv :=
  H.recursorsAdded.valid (H.ctorsAdded.valid (H.typesAdded.valid hvalid))

theorem StagedBlock.abstract_types
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    venv.addConsts (types.map Prod.snd) = some H.venvTypes :=
  H.typesAdded.abstract

theorem StagedBlock.abstract_ctors
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    H.venvTypes.addConsts (ctors.map Prod.snd) = some H.venvCtors :=
  H.ctorsAdded.abstract

theorem StagedBlock.abstract_recursors
    (H : StagedBlock safety env venv types ctors recursors outEnv outVEnv) :
    H.venvCtors.addConsts (recursors.map Prod.snd) = some outVEnv :=
  H.recursorsAdded.abstract

/-- The complete semantic certificate for the block assembled by the three
executable installation stages. `AddConstants` records the per-step checking
environment; the three `*WF` fields deliberately record the stronger
stage-wide facts required by the independent `VInductBlock.WF` specification.
This distinction matters for mutual declarations: typing a later header only
after installing an earlier sibling would not establish formation of the
mutual block. -/
structure BlockCertificate (safety : DefinitionSafety)
    (env : Environment) (venv : VEnv)
    (types ctors recursors : List (ConstantInfo × VConstVal))
    (rules : List VDefEq) (outEnv : Environment) (outVEnv : VEnv) where
  staged : StagedBlock safety env venv types ctors recursors outEnv outVEnv
  typesWF : ∀ ci ∈ types.map Prod.snd, ci.toVConstant.WF venv
  ctorsWF : ∀ ci ∈ ctors.map Prod.snd,
    ci.toVConstant.WF staged.venvTypes
  recursorsWF : ∀ ci ∈ recursors.map Prod.snd,
    ci.toVConstant.WF staged.venvCtors
  rulesWF : ∀ df ∈ rules, df.WF outVEnv

def BlockCertificate.block
    (_H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) : VInductBlock where
  types := types.map Prod.snd
  ctors := ctors.map Prod.snd
  recursors := recursors.map Prod.snd
  rules := rules

/-- A completed executable staging certificate directly discharges the
independent semantic well-formedness judgment. -/
theorem BlockCertificate.wf
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.WF venv := by
  exact ⟨H.staged.venvTypes, H.staged.venvCtors, outVEnv,
    H.staged.abstract_types, H.staged.abstract_ctors,
    H.staged.abstract_recursors, H.typesWF, H.ctorsWF, H.recursorsWF,
    H.rulesWF⟩

/-- The abstract installation result is fixed by the executable staging
certificate; reduction rules are installed only after every recursor. -/
theorem BlockCertificate.install
    (H : BlockCertificate safety env venv types ctors recursors
      rules outEnv outVEnv) :
    H.block.install venv = some (outVEnv.addDefEqs rules) := by
  simp [BlockCertificate.block, VInductBlock.install,
    H.staged.abstract_types, H.staged.abstract_ctors,
    H.staged.abstract_recursors]

/-- Final assembly point for the implementation-refinement boundary. Once
the executable traversals have supplied source formation, compilation shape,
staged typing, and production-map conservation, no further semantic facts are
hidden in `AddInduct`. -/
theorem BlockCertificate.addInduct
    (H : BlockCertificate checkSafety prodEnv venv types ctors recursors
      rules outEnv outVEnv)
    (hdecl : decl.WF venv)
    (hcompile : decl.CompilesTo venv H.block)
    (haligned : ∀ safety, Aligned safety C venv →
      Aligned safety C' (outVEnv.addDefEqs rules))
    (hdelta : ∀ {name ci}, C'.find? name = some ci →
      ci.deltaValue?.isSome → C.find? name = some ci)
    (heq : ∀ info, C'.find? ``Eq = some (.inductInfo info) →
      (outVEnv.addDefEqs rules).constants ``Eq = some eqConst) :
    AddInduct C venv decl C' (outVEnv.addDefEqs rules) :=
  .intro H.block hdecl hcompile H.wf H.install haligned hdelta heq

/-- The first executable check on every source inductive header is an ordinary
type-checker run. At an empty local context its successful result already
provides both the source translation and the abstract typing derivation; later
stages must transport the same statement through the common-parameter local
context. -/
theorem checkType_closed.WF
    (hvalid : CheckingEnv.Valid safety env venv)
    (hclosed : e.FVarsIn fun _ => False) :
    (TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType e)).WF
      fun ty => ∃ e' ty', TrTyping venv lparams [] e ty e' ty' := by
  have hfvars : e.FVarsIn fun fv => fv ∈ VLCtx.fvars ([] : VLCtx) :=
    hclosed.mono fun _ h => False.elim h
  exact TypeChecker.M.WF.runCheckingValid
    (wf := hvalid) (lparams := lparams) (fuel := fuel)
    (TypeChecker.checkType.WF hfvars)

/-- Reference formulation of the executable header-checking prefix. Keeping
the closure check in the statement is important: it is what turns the
type-checker's context-relative result into a source declaration judgment. -/
def checkHeader (env : Environment) (safety : DefinitionSafety)
    (lparams : List Name) (fuel : FuelConfig) (name : Name) (type : Expr) :
    Except Exception Expr := do
  env.checkNoMVarNoFVar name type
  TypeChecker.M.run env safety {} lparams fuel (TypeChecker.checkType type)

theorem checkHeader.WF
    (hvalid : CheckingEnv.Valid safety env venv) :
    (checkHeader env safety lparams fuel name type).WF (fun checkedType =>
      ∃ type' checkedType',
        TrTyping venv lparams [] type checkedType type' checkedType') := by
  unfold checkHeader
  have hno : (env.checkNoMVarNoFVar name type).WF
      (fun _ => type.FVarsIn fun _ => False) := by
    intro _ h
    exact checkNoMVarNoFVar.closed (env := env) (name := name) h
  exact hno.bind fun _ hclosed =>
    checkType_closed.WF (lparams := lparams) (fuel := fuel) hvalid hclosed

end VerifyInductive
end Lean4Lean
