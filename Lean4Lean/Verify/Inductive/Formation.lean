import Lean4Lean.Verify.Inductive.Basic
import Lean4Lean.Theory.Inductive.Normalization

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel
open scoped _root_.List

/-! # Formation certificates and source translations

The certificates that the header and constructor phases of section 3.2 of the design notes
assemble (`HeaderCertificate`, `ConstructorCertificate` and their prefix invariants,
`FormationCertificate`, which yields `VInductDecl.OrdinaryFormationWF`), and the source
translation of a declaration (`TrInductDeclCore`, wave 1B's `Verify/Environment/Basic.lean`):
its passage from the two checking phases and the well-formedness facts it carries
(`TrInductDeclCore.sourceWF`).

Wave 2 scaffold: the certificate structures are the interface (frozen); the proofs that are
not mechanical are named stubs owned by the `Header/`+`Context/`+`Formation` agent. -/

namespace VerifyInductive

/-- Output of the mutual-header traversal: a common parameter telescope and result level,
and the type shape of every family. -/
structure HeaderCertificate (env : VEnv) (decl : VInductDecl) where
  params : List VExpr
  resultLevel : VLevel
  commonLevels : ∀ type ∈ decl.types, type.resultLevel ≈ resultLevel
  typeShapes : ∀ type ∈ decl.types, decl.TypeShape env params type

def HeaderCertificate.mono {env env' : VEnv} (henv : env ≤ env')
    (H : HeaderCertificate env decl) : HeaderCertificate env' decl where
  params := H.params
  resultLevel := H.resultLevel
  commonLevels := H.commonLevels
  typeShapes type htype := (H.typeShapes type htype).mono henv

/-- Prefix invariant threaded through `checkInductiveTypes.loopInd`. -/
structure HeaderPrefixCertificate (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (resultLevel : VLevel) (done : Nat) : Prop where
  commonLevels : ∀ i, i < done → (hi : i < decl.types.length) →
    decl.types[i].resultLevel ≈ resultLevel
  typeShapes : ∀ i, i < done → (hi : i < decl.types.length) →
    decl.TypeShape env params decl.types[i]

theorem HeaderPrefixCertificate.empty (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (resultLevel : VLevel) :
    HeaderPrefixCertificate env decl params resultLevel 0 where
  commonLevels _ h := by omega
  typeShapes _ h := by omega

/-- Output of the flattened constructor traversal: the shape of every owned constructor. -/
structure ConstructorCertificate (env : VEnv) (decl : VInductDecl)
    (envTypes : VEnv) (params : List VExpr) : Prop where
  shapes : ∀ owned ∈ decl.ownedConstructors,
    decl.CtorShape envTypes params owned.1 owned.2

/-- Raw common-parameter shapes retained separately from normalized
constructor formation. -/
structure ConstructorParameterCertificate (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) : Prop where
  shapes : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
    decl.CtorParameterShape env params ctor

theorem ConstructorParameterCertificate.ctorParameterShape
    (H : ConstructorParameterCertificate env decl params)
    (htype : type ∈ decl.types) (hctor : ctor ∈ type.ctors) :
    decl.CtorParameterShape env params ctor :=
  H.shapes type htype ctor hctor

/-- Constructor-tail formation together with the typing fact recovered by
fully applying the checked inductive header. `classes` is the field
classification returned by the executable's positivity check. -/
structure ConstructorTailCertificate (env : VEnv) (decl : VInductDecl)
    (target : VInductiveType) (ctx : List VExpr) (depth : Nat)
    (tail : VExpr) (classes : List Bool) : Prop where
  shape : decl.CtorTailWF env target ctx depth tail
  isType : env.IsType decl.uvars ctx tail
  /-- The executable check walks syntactic binders and then requires a valid
  application of the target family at the block's universe parameters, so the
  translated tail is literally a forall telescope over such a codomain. -/
  raw : ∃ doms result,
    tail = VExpr.wrapForalls doms result ∧
    decl.ValidIndAppAt (some target.name) (depth + doms.length) result ∧
    result.getAppFnArgs.1 = .const target.name (VLevel.params decl.uvars)
  /-- Actual source-field domains and contexts carry the uniform recursive
  normal forms checked before introducing the eliminator universe. -/
  uniform : decl.UniformCtorTail env target (VLevel.params decl.uvars) ctx depth tail classes

structure CheckedConstructorCertificate (env : VEnv) (decl : VInductDecl)
    (envTypes : VEnv) (params : List VExpr) : Prop where
  formation : ConstructorCertificate env decl envTypes params
  types : ∀ ctor ∈ decl.constructorConstants,
    envTypes.IsType decl.uvars [] ctor.type

theorem ConstructorCertificate.ctorShape
    (H : ConstructorCertificate env decl envTypes params)
    (htype : type ∈ decl.types) (hctor : ctor ∈ type.ctors) :
    decl.CtorShape envTypes params type ctor := by
  apply H.shapes (type, ctor)
  simp [VInductDecl.ownedConstructors, htype, hctor]

/-- What the constructor loop establishes for one constructor `ctor` of `target`: its shape
and the typing of its type in the header environment. -/
def CtorTypeChecked (envTypes : VEnv) (decl : VInductDecl) (params : List VExpr)
    (target : VInductiveType) (ctor : VConstVal) : Prop :=
  decl.CtorShape envTypes params target ctor ∧ envTypes.IsType decl.uvars [] ctor.type

theorem ConstructorCertificate.ofCtorTypesChecked
    (H : ∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
      CtorTypeChecked envTypes decl params decl.types[i] decl.types[i].ctors[j]) :
    ConstructorCertificate env decl envTypes params where
  shapes owned howned := by
    rcases List.mem_flatMap.1 howned with ⟨target, htarget, hctor⟩
    rcases List.mem_iff_getElem.1 htarget with ⟨i, hi, rfl⟩
    simp only [List.mem_map] at hctor
    rcases hctor with ⟨ctor, hctor, hpair⟩
    cases hpair
    rcases List.mem_iff_getElem.1 hctor with ⟨j, hj, hctorEq⟩
    cases hctorEq
    simpa using (H i hi j hj).1

theorem CheckedConstructorCertificate.ofCtorTypesChecked
    (H : ∀ i (hi : i < decl.types.length) j (hj : j < decl.types[i].ctors.length),
      CtorTypeChecked envTypes decl params decl.types[i] decl.types[i].ctors[j]) :
    CheckedConstructorCertificate env decl envTypes params where
  formation := .ofCtorTypesChecked H
  types ctor hctor := by
    simp only [VInductDecl.constructorConstants] at hctor
    rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
    rcases List.mem_iff_getElem.1 htarget with ⟨i, hi, rfl⟩
    rcases List.mem_iff_getElem.1 hctor with ⟨j, hj, rfl⟩
    exact (H i hi j hj).2

/-- Fielded aggregation target for the executable header and constructor
traversals. The public specification remains `VInductDecl.OrdinaryFormationWF`; this
certificate gives the refinement proof stable, named obligations instead of
repeatedly unpacking a large existential. -/
structure FormationCertificate (env : VEnv) (decl : VInductDecl) where
  headers : HeaderCertificate env decl
  envTypes : VEnv
  typesInstalled : env.addConstVals decl.typeConstants = some envTypes
  constructorParameters : ConstructorParameterCertificate envTypes decl
    headers.params
  constructors : ConstructorCertificate env decl envTypes headers.params
  /-- Raw syntactic shape of every source constructor, derived from the
  executable binder walk and its final `isValidIndAppIdx` check. -/
  rawShapes : ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
    decl.RawCtorShape type ctor

theorem FormationCertificate.formationWF
    (H : FormationCertificate env decl) : decl.OrdinaryFormationWF env :=
  ⟨H.headers.params, H.headers.resultLevel, H.envTypes, H.typesInstalled,
    fun type htype => ⟨H.headers.commonLevels type htype,
      H.headers.typeShapes type htype⟩,
    fun type htype ctor hctor =>
      ⟨H.constructorParameters.ctorParameterShape htype hctor,
        H.constructors.ctorShape htype hctor⟩,
    H.rawShapes⟩

/-- The recursor half of `VInductDecl.WF`: everything but `source` and `formation`. The
recursor and rule phases deliver it (`RecursorCheck`, `RuleTranslations`); together with a
formation certificate and the source judgment it gives `decl.WF env`
(`FormationCertificate.wf`). -/
structure RecursorsWF (env : VEnv) (decl : VInductDecl) : Prop where
  recsCompiled : decl.RecsCompiled env
  recs_wf : ∀ envP, decl.addTypesCtorsProjs env = some envP →
    ∀ r ∈ decl.recs, r.toVConstVal.toVConstant.WF envP
  rec_shape : ∀ r ∈ decl.recs, r.type.RecShape r.numParams r.numMotives r.numMinors r.numIndices
  rules_nodup : ∀ r ∈ decl.recs, (r.rules.map (·.ctor)).Nodup
  rules_ctor : ∀ envC, decl.addTypesCtors env = some envC → ∀ r ∈ decl.recs, ∀ ru ∈ r.rules,
    ∃ ci, envC.constants ru.ctor = some ci ∧ ci.type.CtorShape (ru.ctorParams + ru.nfields)
  rule_shape : ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∃ j < r.numMinors, ∃ A,
    r.type.piBinders[r.numParams + r.numMotives + j]? = some A ∧ A.MinorFor ru.ctor ∧
    ru.nfields ≤ A.piArity ∧
    ru.rhs.RuleShape r.numParams r.numMotives r.numMinors ru.nfields (A.piArity - ru.nfields) j
  rules_wf : ∀ envR, decl.addTypesCtorsProjsRecs env = some envR →
    ∀ r ∈ decl.recs, ∀ ru ∈ r.rules, ∀ hc : ru.rhs.Closed,
    envR.PatTyped
      (SimplePattern.iota r.name r.getMajorIdx ru.ctor (ru.ctorParams + ru.nfields)).toPattern
      (SimplePattern.iotaRHS r.name ru.ctor
        r.numParams r.numMotives r.numMinors r.numIndices ru.ctorParams ru.nfields ru.rhs hc,
        .true)

theorem VInductDecl.WF.recursorsWF {env : VEnv} {decl : VInductDecl} (H : decl.WF env) :
    RecursorsWF env decl :=
  ⟨H.recsCompiled, H.recs_wf, H.rec_shape, H.rules_nodup, H.rules_ctor, H.rule_shape, H.rules_wf⟩

/-- The declaration judgment from a formation certificate, the source judgment and the
recursor half. -/
theorem FormationCertificate.wf
    (H : FormationCertificate env decl) (hsource : decl.SourceWF env)
    (hrecs : RecursorsWF env decl) : decl.WF env where
  source := hsource
  formation := .ordinary H.formationWF
  recsCompiled := hrecs.recsCompiled
  recs_wf := hrecs.recs_wf
  rec_shape := hrecs.rec_shape
  rules_nodup := hrecs.rules_nodup
  rules_ctor := hrecs.rules_ctor
  rule_shape := hrecs.rule_shape
  rules_wf := hrecs.rules_wf

/-! ## The source translation (`TrInductDeclCore`) -/

/-- The installed names of a core translation are distinct: both `addConstVals` stages
succeeded. -/
theorem TrInductDeclCore.sourceNames_nodup
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    decl.sourceNames.Nodup := by
  -- WAVE 2 STUB (Header/Context/Formation): `VEnv.addConstVals_append` of the source branch
  have := H; sorry

/-- The two executable checking phases jointly recover the pointwise core
translation, without assuming aggregate source well-formedness. -/
theorem TrInductDeclCore.ofPhases
    (Hheaders : TrInductDeclHeaders env lparams nparams types isUnsafe decl
      envTypes)
    (Hctors : TrInductDeclConstructors envTypes lparams types decl envCtors) :
    TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors := by
  have combine : ∀ {sources targets},
      List.Forall₂ (TrInductiveTypeHeaders env envTypes lparams)
        sources targets →
      List.Forall₂
        (fun source target => List.Forall₂
          (fun ctor ctor' =>
            TrSourceConst envTypes lparams ctor.name ctor.type ctor')
          source.ctors target.ctors)
        sources targets →
      List.Forall₂ (TrInductiveType env envTypes lparams)
        sources targets := by
    intro sources targets hheaders hctors
    induction hheaders with
    | nil =>
      cases hctors
      exact .nil
    | cons hheader _ ih =>
      cases hctors with
      | cons hctor hctors =>
        exact .cons ⟨hheader.header, hctor⟩ (ih hctors)
  exact {
    uvars := Hheaders.uvars
    nparams := Hheaders.nparams
    isUnsafe := Hheaders.isUnsafe
    typesAdded := Hheaders.typesAdded
    ctorsAdded := Hctors.ctorsAdded
    types := combine Hheaders.types Hctors.types }

/-- The source family headers are well formed in the source environment. -/
theorem TrInductDeclCore.typeHeadersWF
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl envTypes envCtors) :
    ∀ type ∈ decl.types, type.toVConstant.WF env := by
  intro type member
  obtain ⟨source, _, translated⟩ := List.Forall₂.forall_exists_r H.types type member
  exact translated.header.wf

/-- The aggregate source judgment adds only nonemptiness and global name uniqueness to the
pointwise translation. -/
theorem TrInductDeclCore.sourceWF
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ [])
    (hnames : decl.sourceNames.Nodup) :
    decl.SourceWF env := by
  have hproperties : ∀ target ∈ decl.types,
      target.uvars = decl.uvars ∧
      target.toVConstant.WF env ∧
      ∀ ctor ∈ target.ctors,
        ctor.uvars = decl.uvars ∧
        ctor.toVConstant.WF envTypes := by
    intro target htarget
    rcases List.Forall₂.forall_exists_r H.types target htarget with
      ⟨source, _, Htarget⟩
    refine ⟨Htarget.header.uvars.trans H.uvars.symm,
      Htarget.header.wf, ?_⟩
    intro ctor hctor
    rcases List.Forall₂.forall_exists_r Htarget.ctors ctor hctor with
      ⟨sourceCtor, _, Hctor⟩
    exact ⟨Hctor.uvars.trans H.uvars.symm, Hctor.wf⟩
  refine ⟨hnonempty, hnames, ?_, ?_, envTypes, envCtors,
    H.typesAdded, H.ctorsAdded, ?_, ?_⟩
  · intro target htarget
    exact (hproperties target htarget).1
  · intro ctor hctor
    simp only [VInductDecl.constructorConstants] at hctor
    rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
    exact (hproperties target htarget).2.2 ctor hctor |>.1
  · intro target htarget
    exact (hproperties target htarget).2.1
  · intro ctor hctor
    simp only [VInductDecl.constructorConstants] at hctor
    rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
    exact (hproperties target htarget).2.2 ctor hctor |>.2

/-- Constructor universe arities are already fixed by the pointwise source
translation. -/
theorem TrInductDeclCore.constructorUvars
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars := by
  intro ctor hctor
  simp only [VInductDecl.constructorConstants] at hctor
  rcases List.mem_flatMap.mp hctor with ⟨target, htarget, hctor⟩
  rcases List.Forall₂.forall_exists_r H.types target htarget with
    ⟨source, _hsource, Htarget⟩
  rcases List.Forall₂.forall_exists_r Htarget.ctors ctor hctor with
    ⟨sourceCtor, _hsourceCtor, Hctor⟩
  exact Hctor.uvars.trans H.uvars.symm

theorem TrInductDeclCore.toTrInductDecl
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ [])
    (hnames : decl.sourceNames.Nodup) :
    TrInductDecl env lparams nparams types isUnsafe decl :=
  ⟨TrInductDeclCore.sourceWF H hnonempty hnames,
    H.uvars, H.nparams, H.isUnsafe,
    envTypes, envCtors, H.typesAdded, H.ctorsAdded, H.types⟩

theorem TrInductDeclCore.sourceWF_ofNonempty
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ []) :
    decl.SourceWF env :=
  TrInductDeclCore.sourceWF H hnonempty (TrInductDeclCore.sourceNames_nodup H)

theorem TrInductDeclCore.toTrInductDeclOfNonempty
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hnonempty : decl.types ≠ []) :
    TrInductDecl env lparams nparams types isUnsafe decl :=
  TrInductDeclCore.toTrInductDecl H hnonempty (TrInductDeclCore.sourceNames_nodup H)

theorem TrInductDeclCore.nonempty
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors)
    (hsource : types ≠ []) :
    decl.types ≠ [] := by
  intro htarget
  have hlength := List.Forall₂.length_eq H.types
  rw [htarget] at hlength
  exact hsource (List.eq_nil_of_length_eq_zero hlength)

theorem TrInductDeclCore.types_length
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    types.length = decl.types.length :=
  List.Forall₂.length_eq H.types

theorem TrInductiveType.ctors_length
    (H : TrInductiveType env envTypes lparams type target) :
    type.ctors.length = target.ctors.length :=
  List.Forall₂.length_eq H.ctors

/-- The source constructors with their owning families, in block order. -/
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

theorem TrInductDeclCore.ownedConstructors
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    List.Forall₂ (TrOwnedConstructor env envTypes lparams)
      (VerifyInductive.ownedConstructors types) decl.ownedConstructors := by
  have aux : ∀ {types targets},
      List.Forall₂ (TrInductiveType env envTypes lparams) types targets →
      List.Forall₂ (TrOwnedConstructor env envTypes lparams)
        (VerifyInductive.ownedConstructors types)
        (targets.flatMap fun target => target.ctors.map (target, ·)) := by
    intro types targets htypes
    induction htypes with
    | nil => exact .nil
    | cons h _ ih =>
      simpa [VerifyInductive.ownedConstructors] using
        List.Forall₂.append (TrInductiveType.ownedConstructors h) ih
  simpa [VInductDecl.ownedConstructors] using aux H.types

theorem TrInductDeclCore.ownedConstructors_length
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl
      envTypes envCtors) :
    (VerifyInductive.ownedConstructors types).length = decl.ownedConstructors.length :=
  List.Forall₂.length_eq (TrInductDeclCore.ownedConstructors H)


/-! ## Transport along `VInductDecl.withRecs`

The source fields of `decl.withRecs recs` are those of `decl`, so every judgment that reads only
them transports by reassembling its fields. -/

theorem TrInductDeclCore.withRecs
    (H : TrInductDeclCore env lparams nparams types isUnsafe decl envTypes envCtors)
    (recs : List VRecursor) :
    TrInductDeclCore env lparams nparams types isUnsafe (decl.withRecs recs) envTypes envCtors :=
  ⟨H.uvars, H.nparams, H.isUnsafe, H.typesAdded, H.ctorsAdded, H.types⟩

def HeaderCertificate.withRecs (H : HeaderCertificate env decl) (recs : List VRecursor) :
    HeaderCertificate env (decl.withRecs recs) where
  params := H.params
  resultLevel := H.resultLevel
  commonLevels := H.commonLevels
  typeShapes := H.typeShapes

theorem ConstructorCertificate.withRecs (H : ConstructorCertificate env decl envTypes params)
    (recs : List VRecursor) : ConstructorCertificate env (decl.withRecs recs) envTypes params := by
  -- WAVE 2 STUB (Install): `VInductDecl.CtorTailWF` is an inductive indexed by the
  -- declaration; it reads only the source fields (transport by induction).
  have := H; sorry

theorem ConstructorParameterCertificate.withRecs
    (H : ConstructorParameterCertificate env decl params) (recs : List VRecursor) :
    ConstructorParameterCertificate env (decl.withRecs recs) params :=
  ⟨H.shapes⟩

def FormationCertificate.withRecs (H : FormationCertificate env decl) (recs : List VRecursor) :
    FormationCertificate env (decl.withRecs recs) where
  headers := H.headers.withRecs recs
  envTypes := H.envTypes
  typesInstalled := H.typesInstalled
  constructorParameters := H.constructorParameters.withRecs recs
  constructors := H.constructors.withRecs recs
  rawShapes := H.rawShapes

theorem VInductDecl.SourceWF.withRecs {env : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env) (recs : List VRecursor) : (decl.withRecs recs).SourceWF env := H

end VerifyInductive
end Lean4Lean
