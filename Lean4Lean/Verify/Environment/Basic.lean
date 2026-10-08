import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Declaration
import Lean4Lean.Inductive.Add
import Lean4Lean.Std.SMap
import Lean4Lean.Verify.Environment.RecursorAlignment
import Lean4Lean.Theory.Inductive.NativeIotaRestoration

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- Environment evidence for the members named by `InductiveVal.all`, kept
in the same order as the production metadata.  This lives at the generic
environment layer because nested-inductive recognition needs it before the
inductive checker itself starts. -/
inductive InductiveMemberInfos (env : Environment) : List Name → Prop
  | nil : InductiveMemberInfos env []
  | cons : env.find? name = some (.inductInfo info) →
      InductiveMemberInfos env names →
      InductiveMemberInfos env (name :: names)

theorem InductiveMemberInfos.find
    (H : InductiveMemberInfos env names)
    (hname : name ∈ names) :
    ∃ info, env.find? name = some (.inductInfo info) := by
  induction H with
  | nil => simp at hname
  | @cons head info tail hhead _ ih =>
    simp only [List.mem_cons] at hname
    rcases hname with rfl | htail
    · exact ⟨info, hhead⟩
    · exact ih htail

/-- One production inductive header has a complete, duplicate-free mutual
family, including the header through which it was discovered. -/
structure MutualInductiveClosure
    (env : Environment) (targetName : Name) (value : InductiveVal) : Prop where
  members : InductiveMemberInfos env value.all
  target : targetName ∈ value.all
  names : value.all.Nodup
  /-- Every header in the producer-owned mutual block was emitted with the
  same common-parameter count. -/
  parameters : ∀ member info, member ∈ value.all →
    env.find? member = some (.inductInfo info) →
    info.numParams = value.numParams

/-- Every production inductive header has complete mutual-family metadata.
Nested lowering follows `InductiveVal.all`, so this is part of the persistent
production-environment contract rather than a per-declaration callback. -/
def MutualInductivesClosed (env : Environment) : Prop :=
  ∀ targetName value, env.find? targetName = some (.inductInfo value) →
    MutualInductiveClosure env targetName value

/-- Production environments do not contain dangling constructor metadata:
every constructor's recorded inductive owner is itself present.  This is a
persistent production-environment invariant, not a nested-lowering premise. -/
def ConstructorOwnersPresent (env : Environment) : Prop :=
  ∀ name info, env.find? name = some (.ctorInfo info) →
    ∃ owner, env.find? info.induct = some (.inductInfo owner)

/-- Constructor-owner presence depends only on production constant lookup. -/
theorem ConstructorOwnersPresent.mapEnvironmentEq
    {source target : Environment}
    (H : ConstructorOwnersPresent source)
    (heq : ∀ name, source.find? name = target.find? name) :
    ConstructorOwnersPresent target := by
  intro name info hctor
  have hsource : source.find? name = some (.ctorInfo info) := by
    rw [heq name]
    exact hctor
  rcases H name info hsource with ⟨owner, howner⟩
  exact ⟨owner, by rw [← heq info.induct]; exact howner⟩

/-- Mutual-member evidence depends only on production constant lookup. -/
theorem InductiveMemberInfos.mapEnvironmentEq
    {source targetEnv : Environment}
    (H : InductiveMemberInfos source names)
    (heq : ∀ name, source.find? name = targetEnv.find? name) :
    InductiveMemberInfos targetEnv names := by
  induction H with
  | nil => exact .nil
  | @cons name info names hfind _ ih =>
    exact .cons (by rw [← heq name]; exact hfind) ih

/-- One closed mutual family transports across extensionally equal production
constant maps. -/
theorem MutualInductiveClosure.mapEnvironmentEq
    {source targetEnv : Environment}
    (H : MutualInductiveClosure source targetName value)
    (heq : ∀ name, source.find? name = targetEnv.find? name) :
    MutualInductiveClosure targetEnv targetName value where
  members := H.members.mapEnvironmentEq heq
  target := H.target
  names := H.names
  parameters := by
    intro member info hmember hfind
    exact H.parameters member info hmember (by
      rw [heq member]
      exact hfind)

/-- Closure of every mutual family is invariant under extensional equality of
production constant lookup. -/
theorem MutualInductivesClosed.mapEnvironmentEq
    {source targetEnv : Environment}
    (H : MutualInductivesClosed source)
    (heq : ∀ name, source.find? name = targetEnv.find? name) :
    MutualInductivesClosed targetEnv := by
  intro targetName value htarget
  have hsource : source.find? targetName = some (.inductInfo value) := by
    rw [heq targetName]
    exact htarget
  exact (H targetName value hsource).mapEnvironmentEq heq

/-- The production metadata for one constructor listed by an inductive
header agrees with that header at every field needed to specialize the
constructor at the family's common parameters. -/
structure InductiveConstructorCoherenceAt
    (env : Environment) (familyName : Name) (familyInfo : InductiveVal)
    (i : Nat) (hi : i < familyInfo.ctors.length) where
  info : ConstructorVal
  lookup : env.find? familyInfo.ctors[i] = some (.ctorInfo info)
  induct : info.induct = familyName
  cidx : info.cidx = i
  numParams : info.numParams = familyInfo.numParams
  levelParams : info.levelParams = familyInfo.levelParams
  isUnsafe : info.isUnsafe = familyInfo.isUnsafe

/-- Every constructor name listed by a production inductive header resolves
to coherent constructor metadata. -/
def InductiveConstructorsCoherent (env : Environment) : Prop :=
  ∀ familyName familyInfo,
    env.find? familyName = some (.inductInfo familyInfo) →
    ∀ i (hi : i < familyInfo.ctors.length),
      Nonempty (InductiveConstructorCoherenceAt env familyName familyInfo i hi)

/-- Semantic common-parameter coherence for one visible production
constructor.  Concrete parameter domains need only be definitionally equal;
the independently translated family and constructor types are normalized in
the shared abstract environment before their parameter contexts are compared. -/
structure InductiveConstructorSemanticCoherenceAt
    (env : Environment) (venv : VEnv)
    (familyName : Name) (familyInfo : InductiveVal)
    (i : Nat) (hi : i < familyInfo.ctors.length)
    extends InductiveConstructorCoherenceAt env familyName familyInfo i hi where
  familyTarget : VConstant
  constructorTarget : VConstant
  familyLookup : venv.constants familyName = some familyTarget
  constructorLookup : venv.constants familyInfo.ctors[i] = some constructorTarget
  familyUvars : familyTarget.uvars = familyInfo.levelParams.length
  constructorUvars : constructorTarget.uvars = familyInfo.levelParams.length
  familyNormalized : VExpr
  constructorNormalized : VExpr
  familyDomains : List VExpr
  constructorDomains : List VExpr
  familyTail : VExpr
  constructorTail : VExpr
  familyType : VExpr
  constructorType : VExpr
  familyDefEq : venv.IsDefEq familyInfo.levelParams.length []
    familyTarget.type familyNormalized familyType
  constructorDefEq : venv.IsDefEq familyInfo.levelParams.length []
    constructorTarget.type constructorNormalized constructorType
  familyParams : familyNormalized.takeForalls familyInfo.numParams =
    some (familyDomains, familyTail)
  constructorParams : constructorNormalized.takeForalls familyInfo.numParams =
    some (constructorDomains, constructorTail)
  parameterDomains : venv.IsDefEqCtx familyInfo.levelParams.length []
    familyDomains.reverse constructorDomains.reverse

/-- Every constructor visible in one safety-indexed abstract environment has
production metadata and definitionally equal translated common parameters. -/
def InductiveConstructorsSemanticallyCoherent
    (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  ∀ familyName familyInfo,
    env.find? familyName = some (.inductInfo familyInfo) →
    safety ≤ (if familyInfo.isUnsafe then .unsafe else .safe) →
    ∀ i (hi : i < familyInfo.ctors.length),
      Nonempty (InductiveConstructorSemanticCoherenceAt
        env venv familyName familyInfo i hi)

end VerifyInductive

theorem ConstantInfo.hasValue_eq (ci : ConstantInfo) : ci.hasValue = ci.value?.isSome := by
  cases ci <;> rfl

theorem ConstantInfo.value!_eq (ci : ConstantInfo) : ci.value! = ci.value?.get! := by
  cases ci <;> simp [ConstantInfo.value?, ConstantInfo.value!]

/-- Operational production-side contract for a unary type-annotation wrapper.

The executable `Expr.consumeTypeAnnotations` recognizes these wrappers by
name alone.  Recording the actual environment lookup and delta body prevents a
hostile declaration at the reserved name from being silently treated as an
identity wrapper. -/
structure UnaryTypeAnnotationWrapper (env : Environment) (name : Name) : Prop where
  operational : ∃ info value,
    env.find? name = some info ∧
    info.safety = .safe ∧
    info.deltaValue? = some value ∧
    ∀ (levels : List Level) {arg : Expr}, arg.Closed →
      BetaReduce
        (.app (value.instantiateLevelParams info.levelParams levels) arg) arg

/-- Operational production-side contract for a binary type-annotation
wrapper whose result is its first argument. -/
structure BinaryTypeAnnotationWrapper (env : Environment) (name : Name) : Prop where
  operational : ∃ info value,
    env.find? name = some info ∧
    info.safety = .safe ∧
    info.deltaValue? = some value ∧
    ∀ (levels : List Level) {first second : Expr},
      first.Closed → second.Closed →
      BetaReduce
        (.app (.app (value.instantiateLevelParams info.levelParams levels)
          first) second) first

/-- The four Prelude declarations whose names receive special operational
treatment from `Expr.consumeTypeAnnotations` have their real, identity-like
delta bodies in the production environment. -/
structure TypeAnnotationWrappers (env : Environment) : Prop where
  optParam : BinaryTypeAnnotationWrapper env ``optParam
  autoParam : BinaryTypeAnnotationWrapper env ``autoParam
  outParam : UnaryTypeAnnotationWrapper env ``outParam
  semiOutParam : UnaryTypeAnnotationWrapper env ``semiOutParam

theorem UnaryTypeAnnotationWrapper.rebase
    (H : UnaryTypeAnnotationWrapper source name)
    (hpreserves : ∀ {n ci}, source.find? n = some ci →
      target.find? n = some ci) :
    UnaryTypeAnnotationWrapper target name := by
  rcases H.operational with ⟨info, value, hlookup, hsafe, hdelta, hreduces⟩
  exact ⟨⟨info, value, hpreserves hlookup, hsafe, hdelta, hreduces⟩⟩

theorem BinaryTypeAnnotationWrapper.rebase
    (H : BinaryTypeAnnotationWrapper source name)
    (hpreserves : ∀ {n ci}, source.find? n = some ci →
      target.find? n = some ci) :
    BinaryTypeAnnotationWrapper target name := by
  rcases H.operational with ⟨info, value, hlookup, hsafe, hdelta, hreduces⟩
  exact ⟨⟨info, value, hpreserves hlookup, hsafe, hdelta, hreduces⟩⟩

theorem TypeAnnotationWrappers.rebase
    (H : TypeAnnotationWrappers source)
    (hpreserves : ∀ {n ci}, source.find? n = some ci →
      target.find? n = some ci) :
    TypeAnnotationWrappers target where
  optParam := H.optParam.rebase hpreserves
  autoParam := H.autoParam.rebase hpreserves
  outParam := H.outParam.rebase hpreserves
  semiOutParam := H.semiOutParam.rebase hpreserves

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstant (ci : ConstantInfo) (ci' : VConstant) : Prop :=
  safety ≤ ci.safety ∧ ci.levelParams.length = ci'.uvars ∧
  TrExprS env ci.levelParams [] ci.type ci'.type

variable (safety : DefinitionSafety) (env : VEnv) in
def TrConstVal (ci : ConstantInfo) (ci' : VConstVal) : Prop :=
  TrConstant safety env ci ci'.toVConstant ∧ ci.name = ci'.name

variable (safety : DefinitionSafety) (env : VEnv) in
def TrDefVal (ci : ConstantInfo) (ci' : VDefVal) : Prop :=
  TrConstVal safety env ci ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] (ci.value! (allowOpaque := true)) ci'.value

/-- Translation of a source constant before the kernel has assigned it a
`ConstantInfo` variant. This is used for inductive headers and constructors,
whose types are translated at different environment stages. -/
structure TrSourceConst (env : VEnv) (lparams : List Name)
    (name : Name) (type : Expr) (ci' : VConstVal) : Prop where
  uvars : ci'.uvars = lparams.length
  name : ci'.name = name
  type : TrExprS env lparams [] type ci'.type
  wf : ci'.toVConstant.WF env

/-- Syntactic source-constant translation before its type has been checked in
the appropriate staged environment. -/
structure TrSourceConstRaw (env : VEnv) (lparams : List Name)
    (name : Name) (type : Expr) (ci' : VConstVal) : Prop where
  uvars : ci'.uvars = lparams.length
  name : ci'.name = name
  type : TrExprS env lparams [] type ci'.type

theorem TrSourceConst.raw
    {env : VEnv} {lparams : List Name} {constName : Name}
    {type : Expr} {ci' : VConstVal}
    (H : TrSourceConst env lparams constName type ci') :
    TrSourceConstRaw env lparams constName type ci' :=
  ⟨H.uvars, H.name, H.type⟩

/-- Translation of an inductive family before header checking has recovered
the semantic arity and result universe.  Those two fields are deliberately
absent: they are outputs of `checkInductiveTypes`, not assumptions supplied by
the source-translation relation. -/
structure VInductiveTypeSkeleton extends VConstVal where
  ctors : List VConstVal

/-- Metadata-free translation of a complete source inductive declaration. -/
structure VInductDeclSkeleton where
  uvars : Nat
  nparams : Nat
  types : List VInductiveTypeSkeleton
  isUnsafe : Bool

def VInductiveTypeSkeleton.toVInductiveType
    (type : VInductiveTypeSkeleton) (numIndices : Nat)
    (resultLevel : VLevel) : VInductiveType where
  toVConstVal := type.toVConstVal
  numIndices := numIndices
  resultLevel := resultLevel
  ctors := type.ctors

def VInductiveType.toSkeleton
    (type : VInductiveType) : VInductiveTypeSkeleton where
  toVConstVal := type.toVConstVal
  ctors := type.ctors

def VInductDecl.toSkeleton (decl : VInductDecl) : VInductDeclSkeleton where
  uvars := decl.uvars
  nparams := decl.nparams
  types := decl.types.map VInductiveType.toSkeleton
  isUnsafe := decl.isUnsafe

/-- Assemble the abstract declaration from source translations and the
metadata recovered by the executable header traversal.  Requiring an exact
metadata length prevents `List.zipWith` from silently dropping a family
member. -/
def VInductDeclSkeleton.materialize (decl : VInductDeclSkeleton)
    (metadata : List (Nat × VLevel)) : Option VInductDecl :=
  if metadata.length = decl.types.length then
    some {
      uvars := decl.uvars
      nparams := decl.nparams
      types := List.zipWith (fun type data =>
        type.toVInductiveType data.1 data.2) decl.types metadata
      isUnsafe := decl.isUnsafe }
  else none

@[simp] theorem VInductiveTypeSkeleton.toVInductiveType_toSkeleton
    (type : VInductiveTypeSkeleton) (numIndices : Nat)
    (resultLevel : VLevel) :
    (type.toVInductiveType numIndices resultLevel).toSkeleton = type := by
  cases type
  rfl

@[simp] theorem VInductiveType.toSkeleton_toVInductiveType
    (type : VInductiveType) :
    type.toSkeleton.toVInductiveType type.numIndices type.resultLevel = type := by
  cases type
  rfl

@[simp] theorem VInductDeclSkeleton.materialize_erased
    (decl : VInductDecl) :
    decl.toSkeleton.materialize
      (decl.types.map fun type => (type.numIndices, type.resultLevel)) =
      some decl := by
  simp [VInductDecl.toSkeleton, VInductDeclSkeleton.materialize]

theorem VInductDeclSkeleton.materialize_length
    {decl : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {materialized : VInductDecl}
    (H : decl.materialize metadata = some materialized) :
    metadata.length = decl.types.length := by
  simp only [VInductDeclSkeleton.materialize] at H
  split at H
  · assumption
  · contradiction

theorem VInductDeclSkeleton.materialize_fields
    {decl : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {materialized : VInductDecl}
    (H : decl.materialize metadata = some materialized) :
    materialized.uvars = decl.uvars ∧
    materialized.nparams = decl.nparams ∧
    materialized.isUnsafe = decl.isUnsafe ∧
    materialized.types.length = decl.types.length := by
  simp only [VInductDeclSkeleton.materialize] at H
  split at H
  · next hlength =>
    simp only [Option.some.injEq] at H
    subst materialized
    simp [hlength]
  · contradiction

theorem VInductDeclSkeleton.materialize_toSkeleton
    {decl : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {materialized : VInductDecl}
    (H : decl.materialize metadata = some materialized) :
    materialized.toSkeleton = decl := by
  have zipErase : ∀ (types : List VInductiveTypeSkeleton)
      (metadata : List (Nat × VLevel)),
      metadata.length = types.length →
      List.zipWith (fun type data =>
        (type.toVInductiveType data.1 data.2).toSkeleton)
        types metadata = types := by
    intro types metadata hlength
    induction types generalizing metadata with
    | nil => simpa using hlength
    | cons type types ih =>
      cases metadata with
      | nil => simp at hlength
      | cons data metadata =>
        have hlength' : metadata.length = types.length := by
          simp only [List.length_cons] at hlength
          omega
        simp only [List.zipWith_cons_cons,
          VInductiveTypeSkeleton.toVInductiveType_toSkeleton]
        congr 1
        simpa only [VInductiveTypeSkeleton.toVInductiveType_toSkeleton]
          using ih metadata hlength'
  simp only [VInductDeclSkeleton.materialize] at H
  split at H
  · next hlength =>
    simp only [Option.some.injEq] at H
    subst materialized
    cases decl
    simp only [VInductDecl.toSkeleton, List.map_zipWith]
    rw [zipErase _ _ (by simpa using hlength)]
  · simp at H

theorem VInductDeclSkeleton.materialize_typeAt
    {decl : VInductDeclSkeleton} {metadata : List (Nat × VLevel)}
    {materialized : VInductDecl}
    (H : decl.materialize metadata = some materialized)
    (hi : i < decl.types.length) :
    ∃ data,
      metadata[i]? = some data ∧
      materialized.types[i]? = some
        (decl.types[i].toVInductiveType data.1 data.2) := by
  have hlength := VInductDeclSkeleton.materialize_length H
  have himetadata : i < metadata.length := by omega
  refine ⟨metadata[i], by simp [himetadata], ?_⟩
  simp only [VInductDeclSkeleton.materialize] at H
  split at H
  · simp only [Option.some.injEq] at H
    subst materialized
    rw [List.getElem?_zipWith]
    simp [hi, himetadata]
  · contradiction

structure TrInductiveTypeSkeleton (env envTypes : VEnv)
    (lparams : List Name) (type : InductiveType)
    (type' : VInductiveTypeSkeleton) : Prop where
  header : TrSourceConst env lparams type.name type.type type'.toVConstVal
  ctors : List.Forall₂
    (fun ctor ctor' => TrSourceConst envTypes lparams ctor.name ctor.type ctor')
    type.ctors type'.ctors

/-- Header checking retains raw constructor correspondence, but deliberately
does not claim constructor well-formedness before the mutual headers have
been installed. -/
structure TrInductiveTypeSkeletonHeaders (env envTypes : VEnv)
    (lparams : List Name) (type : InductiveType)
    (type' : VInductiveTypeSkeleton) : Prop where
  header : TrSourceConst env lparams type.name type.type type'.toVConstVal
  ctors : List.Forall₂
    (fun ctor ctor' =>
      TrSourceConstRaw envTypes lparams ctor.name ctor.type ctor')
    type.ctors type'.ctors

def VInductDeclSkeleton.typeConstants
    (decl : VInductDeclSkeleton) : List VConstVal :=
  decl.types.map VInductiveTypeSkeleton.toVConstVal

def VInductDeclSkeleton.constructorConstants
    (decl : VInductDeclSkeleton) : List VConstVal :=
  decl.types.flatMap VInductiveTypeSkeleton.ctors

def VInductDeclSkeleton.sourceNames
    (decl : VInductDeclSkeleton) : List Name :=
  decl.typeConstants.map VConstVal.name ++
    decl.constructorConstants.map VConstVal.name

@[simp] theorem VInductDecl.toSkeleton_typeConstants
    (decl : VInductDecl) :
    decl.toSkeleton.typeConstants = decl.typeConstants := by
  simp [VInductDecl.toSkeleton, VInductDeclSkeleton.typeConstants,
    VInductDecl.typeConstants, VInductiveType.toSkeleton]

@[simp] theorem VInductDecl.toSkeleton_constructorConstants
    (decl : VInductDecl) :
    decl.toSkeleton.constructorConstants = decl.constructorConstants := by
  cases decl with
  | mk uvars nparams types isUnsafe =>
    induction types with
    | nil => rfl
    | cons type types ih =>
      have ih' :
          List.flatMap VInductiveTypeSkeleton.ctors
              (List.map VInductiveType.toSkeleton types) =
            List.flatMap VInductiveType.ctors types := by
        simpa [VInductDecl.toSkeleton,
          VInductDeclSkeleton.constructorConstants,
          VInductDecl.constructorConstants] using ih
      simp [VInductDecl.toSkeleton,
        VInductDeclSkeleton.constructorConstants,
        VInductDecl.constructorConstants, VInductiveType.toSkeleton, ih']

/-- Source well-formedness is metadata-parametric: every exact materialization
has the same translated constants, hence the same source typing obligations.
This formulation keeps recovered header metadata out of the source relation. -/
def VInductDeclSkeleton.SourceWF
    (env : VEnv) (decl : VInductDeclSkeleton) : Prop :=
  ∀ metadata materialized,
    decl.materialize metadata = some materialized →
    materialized.SourceWF env

/-- Translation of the original declaration without presupposing the two
semantic header fields recovered by the executable checker. -/
def TrInductDeclSkeleton (env : VEnv) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool)
    (decl : VInductDeclSkeleton) : Prop :=
  decl.SourceWF env ∧
  decl.uvars = lparams.length ∧
  decl.nparams = nparams ∧
  decl.isUnsafe = isUnsafe ∧
  ∃ envTypes envCtors,
    env.addConstVals decl.typeConstants = some envTypes ∧
    envTypes.addConstVals decl.constructorConstants = some envCtors ∧
    List.Forall₂ (TrInductiveTypeSkeleton env envTypes lparams)
      types decl.types

/-- Metadata-free source translation before aggregate block checks have been
recovered. As in `TrInductDeclCore`, all pointwise source typing is retained;
only nonemptiness and global source-name uniqueness are omitted. -/
structure TrInductDeclSkeletonCore (env : VEnv) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (decl : VInductDeclSkeleton) (envTypes envCtors : VEnv) : Prop where
  uvars : decl.uvars = lparams.length
  nparams : decl.nparams = nparams
  isUnsafe : decl.isUnsafe = isUnsafe
  typesAdded : env.addConstVals decl.typeConstants = some envTypes
  ctorsAdded : envTypes.addConstVals decl.constructorConstants = some envCtors
  types : List.Forall₂ (TrInductiveTypeSkeleton env envTypes lparams)
    types decl.types

/-- Metadata-free header translation used while `checkInductiveTypes` is
still recovering index counts and result universes. -/
structure TrInductDeclSkeletonHeaders (env : VEnv) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (decl : VInductDeclSkeleton) (envTypes : VEnv) : Prop where
  uvars : decl.uvars = lparams.length
  nparams : decl.nparams = nparams
  isUnsafe : decl.isUnsafe = isUnsafe
  typesAdded : env.addConstVals decl.typeConstants = some envTypes
  types : List.Forall₂
    (TrInductiveTypeSkeletonHeaders env envTypes lparams) types decl.types

theorem TrInductDeclSkeleton.core
    (H : TrInductDeclSkeleton env lparams nparams types isUnsafe decl) :
    ∃ envTypes envCtors,
      TrInductDeclSkeletonCore env lparams nparams types isUnsafe decl
        envTypes envCtors := by
  rcases H with ⟨_, huvars, hnparams, hunsafe, envTypes, envCtors,
    htypes, hctors, Htypes⟩
  exact ⟨envTypes, envCtors, huvars, hnparams, hunsafe, htypes, hctors,
    Htypes⟩

structure TrInductiveType (env envTypes : VEnv) (lparams : List Name)
    (type : InductiveType) (type' : VInductiveType) : Prop where
  header : TrSourceConst env lparams type.name type.type type'.toVConstVal
  ctors : List.Forall₂
    (fun ctor ctor' => TrSourceConst envTypes lparams ctor.name ctor.type ctor')
    type.ctors type'.ctors

structure TrInductiveTypeHeaders (env envTypes : VEnv) (lparams : List Name)
    (type : InductiveType) (type' : VInductiveType) : Prop where
  header : TrSourceConst env lparams type.name type.type type'.toVConstVal
  ctors : List.Forall₂
    (fun ctor ctor' =>
      TrSourceConstRaw envTypes lparams ctor.name ctor.type ctor')
    type.ctors type'.ctors

theorem TrInductiveType.toSkeleton
    (H : TrInductiveType env envTypes lparams type type') :
    TrInductiveTypeSkeleton env envTypes lparams type type'.toSkeleton where
  header := H.header
  ctors := H.ctors

/-- Translation of the original, pre-lowering inductive declaration. The
constructor relation deliberately uses `envTypes`, obtained by installing all
translated mutual headers, so an ill-typed nested parameter cannot disappear
behind auxiliary declarations. -/
def TrInductDecl (env : VEnv) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool) (decl : VInductDecl) : Prop :=
  decl.SourceWF env ∧
  decl.uvars = lparams.length ∧
  decl.nparams = nparams ∧
  decl.isUnsafe = isUnsafe ∧
  ∃ envTypes envCtors,
    env.addConstVals decl.typeConstants = some envTypes ∧
    envTypes.addConstVals decl.constructorConstants = some envCtors ∧
    List.Forall₂ (TrInductiveType env envTypes lparams) types decl.types

/-- Source translation without assuming the aggregate `SourceWF` judgment.
The pointwise `TrSourceConst` witnesses still retain the independently checked
typing of every original header and constructor; only block nonemptiness and
global name uniqueness are intentionally absent. -/
structure TrInductDeclCore (env : VEnv) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe : Bool)
    (decl : VInductDecl) (envTypes envCtors : VEnv) : Prop where
  uvars : decl.uvars = lparams.length
  nparams : decl.nparams = nparams
  isUnsafe : decl.isUnsafe = isUnsafe
  typesAdded : env.addConstVals decl.typeConstants = some envTypes
  ctorsAdded : envTypes.addConstVals decl.constructorConstants = some envCtors
  types : List.Forall₂ (TrInductiveType env envTypes lparams)
    types decl.types

/-- Header-phase translation in the exact form available after
`checkInductiveTypes` and mutual header installation. Constructor translation
is intentionally absent until `checkConstructors` has run in `envTypes`. -/
structure TrInductDeclHeaders (env : VEnv) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    (decl : VInductDecl) (envTypes : VEnv) : Prop where
  uvars : decl.uvars = lparams.length
  nparams : decl.nparams = nparams
  isUnsafe : decl.isUnsafe = isUnsafe
  typesAdded : env.addConstVals decl.typeConstants = some envTypes
  types : List.Forall₂ (TrInductiveTypeHeaders env envTypes lparams)
    types decl.types

/-- Constructor-phase translation produced after all mutual headers are
installed. It records both pointwise source typing and the exact abstract
constructor environment. -/
structure TrInductDeclConstructors (envTypes : VEnv) (lparams : List Name)
    (types : List InductiveType) (decl : VInductDecl)
    (envCtors : VEnv) : Prop where
  ctorsAdded : envTypes.addConstVals decl.constructorConstants = some envCtors
  types : List.Forall₂
    (fun source target => List.Forall₂
      (fun ctor ctor' =>
        TrSourceConst envTypes lparams ctor.name ctor.type ctor')
      source.ctors target.ctors)
    types decl.types

theorem TrInductDecl.core
    (H : TrInductDecl env lparams nparams types isUnsafe decl) :
    ∃ envTypes envCtors,
      TrInductDeclCore env lparams nparams types isUnsafe decl
        envTypes envCtors := by
  rcases H with ⟨_, huvars, hnparams, hunsafe, envTypes, envCtors,
    htypes, hctors, Htypes⟩
  exact ⟨envTypes, envCtors, huvars, hnparams, hunsafe, htypes, hctors,
    Htypes⟩

theorem TrInductDecl.sourceWF
    (H : TrInductDecl env lparams nparams types isUnsafe decl) : decl.SourceWF env :=
  H.1

/-- The step an abstract environment takes when `ci`, modelled by `ci'`, is added.

At safety levels where the declaration is visible the constant is added; where it is not, the
environment is unchanged, matching `TrEnv'.ignore`. Stating this rather than just `venv ≤ venv'`
is what lets a caller see *which* constant a step added. -/
def VEnv.AddConst (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VConstant) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    TrConstant safety venv ci ci' ∧ ci'.WF venv ∧ venv.addConst ci.name ci' = some venv'
  else
    venv' = venv

theorem VEnv.AddConst.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddConst venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddConst at H; split at H
  · exact addConst_le H.2.2
  · exact H ▸ VEnv.LE.rfl

/-- As `VEnv.AddConst`, for a definition: the constant is added and then its defining equation,
matching `TrEnv'.defn`. -/
def VEnv.AddDef (venv : VEnv) (safety : DefinitionSafety) (ci : ConstantInfo)
    (ci' : VDefVal) (venv' : VEnv) : Prop :=
  if safety ≤ ci.safety then
    ∃ base, TrDefVal safety venv ci ci' ∧ ci'.WF venv ∧
      venv.addConst ci.name ci'.toVConstant = some base ∧
      venv' = base.addDefEq ci'.toDefEq
  else
    venv' = venv

theorem VEnv.AddDef.le {venv venv' : VEnv} {ci ci'}
    (H : VEnv.AddDef venv safety ci ci' venv') : venv ≤ venv' := by
  unfold VEnv.AddDef at H; split at H
  · obtain ⟨base, _, _, hadd, rfl⟩ := H
    exact (addConst_le hadd).trans (VEnv.addDefEq_le ..)
  · exact H ▸ VEnv.LE.rfl

def AddQuot1 (name : Name) (kind : QuotKind) (ci' : VConstant) (P : ConstMap → VEnv → Prop)
    (m : ConstMap) (env : VEnv) : Prop :=
  ∃ levelParams type env',
    let ci := .quotInfo { name, kind, levelParams, type }
    TrConstant .safe env ci ci' ∧
    m.find? name = none ∧
    env.addConst name ci' = some env' ∧
    P (m.insert name ci) env'

theorem AddQuot1.to_addQuot
    (H1 : ∀ m env, P m env → f env = some env')
    (m env) (H : AddQuot1 name kind ci' P m env) :
    env.addConst name ci' >>= f = some env' := by
  let ⟨_, _, _, h1, _, h2, h3⟩ := H
  simpa using ⟨_, h2, H1 _ _ h3⟩

theorem AddQuot1.le
    (H1 : ∀ m env, P m env → env ≤ env₀)
    (m env) (H : AddQuot1 name kind ci' P m env) : env ≤ env₀ :=
  let ⟨_, _, _, _, _, h2, h3⟩ := H
  .trans (VEnv.addConst_le h2) (H1 _ _ h3)

def AddQuot (m₁ m₂ : ConstMap) (env₁ env₂ : VEnv) : Prop :=
  AddQuot1 ``Quot .type quotConst (m := m₁) (env := env₁) <|
  AddQuot1 ``Quot.mk .ctor quotMkConst <|
  AddQuot1 ``Quot.lift .lift quotLiftConst <|
  AddQuot1 ``Quot.ind .ind quotIndConst (· = m₂ ∧ ·.addDefEq quotDefEq = env₂)

nonrec theorem AddQuot.to_addQuot (H : AddQuot m₁ m₂ env₁ env₂) : env₁.addQuot = some env₂ :=
  open AddQuot1 in (to_addQuot <| to_addQuot <| to_addQuot <| to_addQuot (by simp)) _ _ H

nonrec theorem AddQuot.le (H : AddQuot m₁ m₂ env₁ env₂) : env₁ ≤ env₂ :=
  open AddQuot1 in (le <| le <| le <| le fun _ _ h => h.2 ▸ VEnv.addDefEq_le) _ _ H


/-- Exact production metadata for one constructor in an abstract inductive
family installed by the current declaration.  This prevents a flat constant
lookup from being mistaken for inductive-declaration provenance. -/
structure ProductionConstructorAlignment
    (C : ConstMap) (decl : VInductDecl) (familyIdx ctorIdx : Nat)
    (familyInfo : InductiveVal) where
  familyIdx_lt : familyIdx < decl.types.length
  ctorIdx_lt : ctorIdx < decl.types[familyIdx].ctors.length
  familyInfo_ctorIdx_lt : ctorIdx < familyInfo.ctors.length
  info : ConstructorVal
  name : familyInfo.ctors[ctorIdx] =
    decl.types[familyIdx].ctors[ctorIdx].name
  lookup : C.find? familyInfo.ctors[ctorIdx] = some (.ctorInfo info)
  induct : info.induct = familyInfo.name
  cidx : info.cidx = ctorIdx
  numParams : info.numParams = decl.nparams
  /-- The projection field count is the exact executable telescope arity
  after removing the independently aligned common parameters. -/
  numFields : info.numFields =
    AddInductive.constructorArity info.type - decl.nparams
  /-- The executable field count agrees with the syntactic forall arity of the
  abstract constructor type: the constructor check walks syntactic binders and
  requires a constant-headed codomain, which translation preserves. -/
  numFields_forallArity : info.numFields =
    (decl.types[familyIdx].ctors[ctorIdx]).type.forallArity - decl.nparams
  levelParamsExact : info.levelParams = familyInfo.levelParams
  levelParams : info.levelParams.length = decl.uvars
  isUnsafe : info.isUnsafe = decl.isUnsafe

/-- Exact mutual-family metadata installed by one abstract declaration. -/
structure ProductionFamilyAlignment
    (C : ConstMap) (decl : VInductDecl) (familyIdx : Nat)
    (familyInfo : InductiveVal) : Prop where
  familyIdx_lt : familyIdx < decl.types.length
  name : familyInfo.name = decl.types[familyIdx].name
  lookup : C.find? familyInfo.name = some (.inductInfo familyInfo)
  all : familyInfo.all = decl.types.map (fun family => family.name)
  levelParams : familyInfo.levelParams.length = decl.uvars
  numParams : familyInfo.numParams = decl.nparams
  numIndices : familyInfo.numIndices = decl.types[familyIdx].numIndices
  constructors : familyInfo.ctors.length =
    decl.types[familyIdx].ctors.length
  isUnsafe : familyInfo.isUnsafe = decl.isUnsafe
  constructor : ∀ ctorIdx
    (_hctor : ctorIdx < decl.types[familyIdx].ctors.length),
    Nonempty (ProductionConstructorAlignment C decl familyIdx ctorIdx
      familyInfo)

/-- Every inductive header visible after an inductive installation either
already existed or is one exact family of the declaration just installed. -/
def ProductionInductiveOrigins
    (source target : ConstMap) (decl : VInductDecl) : Prop :=
  ∀ familyName familyInfo,
    target.find? familyName = some (.inductInfo familyInfo) →
    source.find? familyName = some (.inductInfo familyInfo) ∨
      ∃ familyIdx, familyName = familyInfo.name ∧
        Nonempty (ProductionFamilyAlignment target decl familyIdx familyInfo)

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)
  | projections : Aligned C venv → Aligned C (venv.addProjections entries)
  /-- Abstract case symbols are absent from the native constant map. Their
  independent certification is carried by the checking environment's WF trace. -/
  | eliminators : Aligned C venv → Aligned C (venv.addEliminator block schema)
  /-- Production constant maps are implementation maps rather than ordered
  declaration lists.  A bulk declaration such as nested restoration may
  insert fresh entries in a different order from the dependency order used
  to type their abstract counterparts.  Exact lookup equivalence, together
  with well-formedness of the target representation, permits transport
  between those insertion histories without changing their semantics. -/
  | mapExt : Aligned C venv → C'.WF →
      (∀ name, C.find? name = C'.find? name) → Aligned C' venv

/-- Constructive implementation boundary for an inductive extension at one
observer safety. Besides the independent compilation and installation
witnesses, it records exact production-map alignment at that safety, and the
alignment of the recursors it installs with the stored iota equations
(`InductiveRecursorProvenance`). -/
inductive AddInduct (safety : DefinitionSafety)
    (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop where
  | intro (_block : VInductBlock) :
    decl.WF env₁ →
    VInductDecl.CompilesTo env₁ decl _block →
    VInductBlock.WF env₁ _block →
    VInductBlock.install env₁ _block = some env₂ →
    ProductionInductiveOrigins m₁ m₂ decl →
    (∀ {name ci}, m₁.find? name = some ci → m₂.find? name = some ci) →
    (Aligned safety m₁ env₁ → Aligned safety m₂ env₂) →
    (∀ {name ci}, m₂.find? name = some ci → ci.deltaValue?.isSome →
      m₁.find? name = some ci) →
    InductiveRecursorProvenance safety m₁ env₁ m₂ env₂ →
    VInductBlock.EliminatorsWF env₁ decl _block →
    AddInduct safety m₁ env₁ decl m₂ env₂

theorem AddInduct.toVEnv
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    VEnv.AddInduct env₁ decl env₂ :=
  match H with
  | .intro _ hdecl hcompile hblock hinstall _ _ _ _ _ helim =>
    .intro hdecl hcompile hblock helim hinstall

theorem AddInduct.declWF
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) : decl.WF env₁ := by
  cases H with
  | intro _ hdecl => exact hdecl

theorem AddInduct.le
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) : env₁ ≤ env₂ := by
  cases H with
  | intro _ _ _ _ hinstall => exact VInductBlock.install_le hinstall

theorem AddInduct.productionOrigins
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    ProductionInductiveOrigins m₁ m₂ decl := by
  cases H with
  | intro _ _ _ _ _ horigins => exact horigins

theorem AddInduct.preservesSourceFind
    (H : AddInduct safety m₁ env₁ decl m₂ env₂)
    (hfind : m₁.find? name = some ci) : m₂.find? name = some ci := by
  cases H with
  | intro _ _ _ _ _ _ hpreserves => exact hpreserves hfind

theorem AddInduct.aligned
    (H : AddInduct safety m₁ env₁ decl m₂ env₂)
    (haligned : Aligned safety m₁ env₁) : Aligned safety m₂ env₂ := by
  cases H with
  | intro _ _ _ _ _ _ _ hpreserves => exact hpreserves haligned

theorem AddInduct.recursorProvenance
    (H : AddInduct safety m₁ env₁ decl m₂ env₂) :
    InductiveRecursorProvenance safety m₁ env₁ m₂ env₂ := by
  cases H with
  | intro _ _ _ _ _ _ _ _ _ hrecursors => exact hrecursors

def ProductionConstructorAlignment.rebase
    (H : ProductionConstructorAlignment source decl familyIdx ctorIdx
      familyInfo)
    (hpreserves : ∀ {name ci}, source.find? name = some ci →
      target.find? name = some ci) :
    ProductionConstructorAlignment target decl familyIdx ctorIdx familyInfo :=
  { H with lookup := hpreserves H.lookup }

theorem ProductionFamilyAlignment.rebase
    (H : ProductionFamilyAlignment source decl familyIdx familyInfo)
    (hfamily : target.find? familyInfo.name = some (.inductInfo familyInfo))
    (hpreserves : ∀ {name ci}, source.find? name = some ci →
      target.find? name = some ci) :
    ProductionFamilyAlignment target decl familyIdx familyInfo where
  familyIdx_lt := H.familyIdx_lt
  name := H.name
  lookup := hfamily
  all := H.all
  levelParams := H.levelParams
  numParams := H.numParams
  numIndices := H.numIndices
  constructors := H.constructors
  isUnsafe := H.isUnsafe
  constructor ctorIdx hctor := by
    rcases H.constructor ctorIdx hctor with ⟨C⟩
    exact ⟨C.rebase hpreserves⟩

/-- Persistent, declaration-level provenance for one visible production
inductive family in one abstract environment. -/
structure InstalledInductiveFamilyProvenanceAt
    (C : ConstMap) (env : VEnv) (familyName : Name)
    (familyInfo : InductiveVal) where
  decl : VInductDecl
  familyIdx : Nat
  name : familyName = familyInfo.name
  alignment : ProductionFamilyAlignment C decl familyIdx familyInfo
  installed : VEnv.InstalledInductCertificate env decl

/-- A singleton production family with installed provenance has the exact
abstract projection entry derived from its source declaration.  The
singleton premise is the executable metadata check performed by
`inferProj`; the conclusion is obtained from the installation certificate,
not postulated as a separate readiness hypothesis. -/
theorem InstalledInductiveFamilyProvenanceAt.projectionOfSingle
    (H : InstalledInductiveFamilyProvenanceAt C env familyName familyInfo)
    (hsingle : familyInfo.ctors = [constructorName]) :
    ∃ owner constructor,
      owner = H.decl.types[H.familyIdx]'H.alignment.familyIdx_lt ∧
      owner.ctors = [constructor] ∧
      familyName = owner.name ∧
      env.projections familyName {
        uvars := H.decl.uvars
        nparams := H.decl.nparams
        nindices := owner.numIndices
        resultLevel := owner.resultLevel
        ctorName := constructor.name
        ctorType := constructor.type } := by
  let owner := H.decl.types[H.familyIdx]'H.alignment.familyIdx_lt
  have hlength : owner.ctors.length = 1 := by
    change (H.decl.types[H.familyIdx]'H.alignment.familyIdx_lt).ctors.length = 1
    rw [← H.alignment.constructors, hsingle]
    rfl
  cases hctors : owner.ctors with
  | nil => simp [hctors] at hlength
  | cons constructor tail =>
    cases tail with
    | cons next rest => simp [hctors] at hlength
    | nil =>
      have howner : owner ∈ H.decl.types :=
        List.getElem_mem H.alignment.familyIdx_lt
      have hentry : ({
          typeName := owner.name
          info := {
            uvars := H.decl.uvars
            nparams := H.decl.nparams
            nindices := owner.numIndices
            resultLevel := owner.resultLevel
            ctorName := constructor.name
            ctorType := constructor.type } } : VProjectionEntry) ∈
          H.decl.projectionEntries := by
        rw [VInductDecl.projectionEntries, List.mem_filterMap]
        exact ⟨owner, howner, by simp [hctors]⟩
      have hname : familyName = owner.name :=
        H.name.trans H.alignment.name
      refine ⟨owner, constructor, rfl, hctors, hname, ?_⟩
      simpa [hname] using H.installed.projection hentry

/-- Exact agreement between a concrete singleton inductive family and the
primitive-projection entry available in its abstract checking environment.
This is the persistent invariant consumed by projection inference: it records
precisely the executable metadata read by `inferProj` and `reduceProjCore`
(parameter and index counts, universe arity, the constructor's identity and
field count) against the registered abstract entry, and the abstract
constants named by that entry. -/
structure ProjectionRegistryAlignmentAt
    (C : ConstMap) (env : VEnv) (familyName : Name)
    (familyInfo : InductiveVal) (constructorName : Name) where
  info : VProjectionInfo
  projection : env.projections familyName info
  ctorName : info.ctorName = constructorName
  uvars : familyInfo.levelParams.length = info.uvars
  nparams : familyInfo.numParams = info.nparams
  nindices : familyInfo.numIndices = info.nindices
  constructorInfo : ConstructorVal
  constructor_lookup : C.find? constructorName = some (.ctorInfo constructorInfo)
  constructor_induct : constructorInfo.induct = familyName
  constructor_levelParams : constructorInfo.levelParams = familyInfo.levelParams
  constructor_numParams : constructorInfo.numParams = familyInfo.numParams
  constructor_isUnsafe : constructorInfo.isUnsafe = familyInfo.isUnsafe
  constructor_numFields : constructorInfo.numFields = info.numFields
  familyType : VExpr
  family_lookup : env.constants familyName = some ⟨info.uvars, familyType⟩
  constructor_abstract :
    env.constants constructorName = some ⟨info.uvars, info.ctorType⟩

/-- Every executable singleton-family lookup that is visible at this safety
level, whose listed constructor is present and names the family as its
owner, has matching primitive-projection metadata in the abstract model. -/
def ProjectionRegistryCoherent
    (safety : DefinitionSafety) (C : ConstMap) (env : VEnv) : Prop :=
  ∀ familyName familyInfo constructorName constructorInfo,
    C.find? familyName = some (.inductInfo familyInfo) →
    safety ≤ (ConstantInfo.inductInfo familyInfo).safety →
    familyInfo.ctors = [constructorName] →
    C.find? constructorName = some (.ctorInfo constructorInfo) →
    constructorInfo.induct = familyName →
    Nonempty (ProjectionRegistryAlignmentAt C env familyName familyInfo
      constructorName)

/-- Projection-registry alignment is preserved by monotone abstract
environment extension. -/
def ProjectionRegistryAlignmentAt.monoEnv
    (H : ProjectionRegistryAlignmentAt C env familyName familyInfo
      constructorName)
    (henv : env ≤ env') :
    ProjectionRegistryAlignmentAt C env' familyName familyInfo
      constructorName where
  info := H.info
  projection := henv.projections H.projection
  ctorName := H.ctorName
  uvars := H.uvars
  nparams := H.nparams
  nindices := H.nindices
  constructorInfo := H.constructorInfo
  constructor_lookup := H.constructor_lookup
  constructor_induct := H.constructor_induct
  constructor_levelParams := H.constructor_levelParams
  constructor_numParams := H.constructor_numParams
  constructor_isUnsafe := H.constructor_isUnsafe
  constructor_numFields := H.constructor_numFields
  familyType := H.familyType
  family_lookup := henv.constants H.family_lookup
  constructor_abstract := henv.constants H.constructor_abstract

/-- Transport an alignment across a production constant map that preserves
every existing lookup and a monotone abstract extension. -/
def ProjectionRegistryAlignmentAt.rebase
    (H : ProjectionRegistryAlignmentAt source env familyName familyInfo
      constructorName)
    (hpreserves : ∀ {name ci}, source.find? name = some ci →
      target.find? name = some ci)
    (henv : env ≤ env') :
    ProjectionRegistryAlignmentAt target env' familyName familyInfo
      constructorName where
  info := H.info
  projection := henv.projections H.projection
  ctorName := H.ctorName
  uvars := H.uvars
  nparams := H.nparams
  nindices := H.nindices
  constructorInfo := H.constructorInfo
  constructor_lookup := hpreserves H.constructor_lookup
  constructor_induct := H.constructor_induct
  constructor_levelParams := H.constructor_levelParams
  constructor_numParams := H.constructor_numParams
  constructor_isUnsafe := H.constructor_isUnsafe
  constructor_numFields := H.constructor_numFields
  familyType := H.familyType
  family_lookup := henv.constants H.family_lookup
  constructor_abstract := henv.constants H.constructor_abstract

theorem ProjectionRegistryCoherent.monoEnv
    (H : ProjectionRegistryCoherent safety C env)
    (henv : env ≤ env') :
    ProjectionRegistryCoherent safety C env' := by
  intro familyName familyInfo constructorName constructorInfo hfind hvisible
    hsingle hconstructor hinduct
  rcases H familyName familyInfo constructorName constructorInfo hfind hvisible
    hsingle hconstructor hinduct with ⟨P⟩
  exact ⟨P.monoEnv henv⟩

/-- Registry coherence depends on the production constant map only through
lookup. -/
theorem ProjectionRegistryCoherent.mapExt
    (H : ProjectionRegistryCoherent safety source env)
    (heq : ∀ name, source.find? name = target.find? name) :
    ProjectionRegistryCoherent safety target env := by
  intro familyName familyInfo constructorName constructorInfo hfind hvisible
    hsingle hconstructor hinduct
  rw [← heq] at hfind hconstructor
  rcases H familyName familyInfo constructorName constructorInfo hfind hvisible
    hsingle hconstructor hinduct with ⟨P⟩
  exact ⟨P.rebase (fun {name ci} h => by rw [← heq]; exact h) .rfl⟩

/-- Constructor-owner presence stated on a production constant map. -/
def ConstructorOwnersPresentMap (C : ConstMap) : Prop :=
  ∀ name info, C.find? name = some (.ctorInfo info) →
    ∃ owner, C.find? info.induct = some (.inductInfo owner)

/-- Per-constant side condition under which inserting `ci` preserves
projection-registry coherence.  Only constructors carry an obligation: their
owner must already be present, and if they complete a singleton family the
registry must align with that family in the extended abstract environment. -/
def ProjectionRegistryStep (C : ConstMap) (env' : VEnv) : ConstantInfo → Prop
  | .ctorInfo info =>
    (∃ owner, C.find? info.induct = some (.inductInfo owner)) ∧
    ∀ owner, C.find? info.induct = some (.inductInfo owner) →
      owner.ctors = [info.name] →
      Nonempty (ProjectionRegistryAlignmentAt
        (C.insert info.name (.ctorInfo info)) env' info.induct owner info.name)
  | _ => True

theorem ProjectionRegistryStep.monoEnv
    (H : ProjectionRegistryStep C env ci) (henv : env ≤ env') :
    ProjectionRegistryStep C env' ci := by
  cases ci with
  | ctorInfo info =>
    rcases H with ⟨howner, halign⟩
    refine ⟨howner, fun owner hfind hsingle => ?_⟩
    rcases halign owner hfind hsingle with ⟨P⟩
    exact ⟨P.monoEnv henv⟩
  | _ => trivial

theorem ProjectionRegistryStep.of_not_ctor
    (hnctor : ∀ info, ci ≠ .ctorInfo info) :
    ProjectionRegistryStep C env ci := by
  cases ci with
  | ctorInfo info => exact absurd rfl (hnctor info)
  | _ => trivial

/-- Adding concrete metadata that is neither an inductive header nor a
constructor preserves projection-registry coherence across any monotone
abstract extension. -/
theorem ProjectionRegistryCoherent.insertNonInductive
    (H : ProjectionRegistryCoherent safety C env)
    (hwf : C.WF) (hfresh : C.find? ci.name = none)
    (hnind : ∀ familyInfo, ci ≠ .inductInfo familyInfo)
    (hnctor : ∀ constructorInfo, ci ≠ .ctorInfo constructorInfo)
    (henv : env ≤ env') :
    ProjectionRegistryCoherent safety (C.insert ci.name ci) env' := by
  have hpreserves : ∀ {name found}, C.find? name = some found →
      (C.insert ci.name ci).find? name = some found := by
    intro name found hfind
    rw [hwf.find?_insert]
    split
    · rename_i heq
      have hname : ci.name = name := LawfulBEq.eq_of_beq heq
      subst name
      rw [hfind] at hfresh
      contradiction
    · exact hfind
  intro familyName familyInfo constructorName constructorInfo hfamily
    hvisible hsingle hconstructor hinduct
  have holdFamily : C.find? familyName = some (.inductInfo familyInfo) := by
    rw [hwf.find?_insert] at hfamily
    split at hfamily
    · exact False.elim (hnind familyInfo (Option.some.inj hfamily))
    · exact hfamily
  have holdConstructor : C.find? constructorName =
      some (.ctorInfo constructorInfo) := by
    rw [hwf.find?_insert] at hconstructor
    split at hconstructor
    · exact False.elim (hnctor constructorInfo
        (Option.some.inj hconstructor))
    · exact hconstructor
  rcases H familyName familyInfo constructorName constructorInfo holdFamily
      hvisible hsingle holdConstructor hinduct with ⟨P⟩
  exact ⟨P.rebase hpreserves henv⟩

/-- Installing an inductive header preserves projection-registry coherence
whenever every present constructor already has a present owner: no present
constructor can name the fresh header as its owner, so the new header cannot
activate the invariant until one of its constructors is installed. -/
theorem ProjectionRegistryCoherent.insertInductiveHeader
    (H : ProjectionRegistryCoherent safety C env)
    (hwf : C.WF)
    (howners : ConstructorOwnersPresentMap C)
    (hfresh : C.find? familyInfo.name = none)
    (henv : env ≤ env') :
    ProjectionRegistryCoherent safety
      (C.insert familyInfo.name (.inductInfo familyInfo)) env' := by
  have hpreserves : ∀ {name found}, C.find? name = some found →
      (C.insert familyInfo.name (.inductInfo familyInfo)).find? name =
        some found := by
    intro name found hfind
    rw [hwf.find?_insert]
    split
    · rename_i heq
      have hname : familyInfo.name = name := LawfulBEq.eq_of_beq heq
      subst name
      rw [hfind] at hfresh
      contradiction
    · exact hfind
  intro familyName foundFamily constructorName constructorInfo hfamily
    hvisible hsingle hconstructor hinduct
  have holdConstructor : C.find? constructorName =
      some (.ctorInfo constructorInfo) := by
    rw [hwf.find?_insert] at hconstructor
    split at hconstructor
    · cases hconstructor
    · exact hconstructor
  rw [hwf.find?_insert] at hfamily
  split at hfamily
  · rename_i heq
    have hfamilyName : familyInfo.name = familyName :=
      LawfulBEq.eq_of_beq heq
    rcases howners constructorName constructorInfo holdConstructor with
      ⟨owner, howner⟩
    rw [hinduct, ← hfamilyName, hfresh] at howner
    contradiction
  · rename_i hnotNew
    rcases H familyName foundFamily constructorName constructorInfo
        hfamily hvisible hsingle holdConstructor hinduct with ⟨P⟩
    exact ⟨P.rebase hpreserves henv⟩

/-- Installing a constructor preserves registry coherence under its step
condition: the owner is present and, if the constructor completes a singleton
family, exact projection alignment has been established for that family.
Existing completed families are transported unchanged. -/
theorem ProjectionRegistryCoherent.insertConstructor
    (H : ProjectionRegistryCoherent safety C env)
    (hwf : C.WF)
    (hfresh : C.find? constructorInfo.name = none)
    (henv : env ≤ env')
    (hstep : ProjectionRegistryStep C env' (.ctorInfo constructorInfo)) :
    ProjectionRegistryCoherent safety
      (C.insert constructorInfo.name (.ctorInfo constructorInfo)) env' := by
  have hpreserves : ∀ {name found}, C.find? name = some found →
      (C.insert constructorInfo.name (.ctorInfo constructorInfo)).find? name =
        some found := by
    intro name found hfind
    rw [hwf.find?_insert]
    split
    · rename_i heq
      have hname : constructorInfo.name = name := LawfulBEq.eq_of_beq heq
      subst name
      rw [hfind] at hfresh
      contradiction
    · exact hfind
  intro familyName familyInfo constructorName foundConstructor hfamily
    hvisible hsingle hconstructor hinduct
  have holdFamily : C.find? familyName =
      some (.inductInfo familyInfo) := by
    rw [hwf.find?_insert] at hfamily
    split at hfamily
    · cases hfamily
    · exact hfamily
  rw [hwf.find?_insert] at hconstructor
  split at hconstructor
  · rename_i heq
    have hconstructorName : constructorInfo.name = constructorName :=
      LawfulBEq.eq_of_beq heq
    cases hconstructor
    subst constructorName
    subst hinduct
    exact hstep.2 familyInfo holdFamily hsingle
  · rename_i hnotNew
    rcases H familyName familyInfo constructorName foundConstructor holdFamily
        hvisible hsingle hconstructor hinduct with ⟨P⟩
    exact ⟨P.rebase hpreserves henv⟩

/-- Inserting a constant into a map with present constructor owners keeps
owners present, provided a constructor names a present owner. -/
theorem ConstructorOwnersPresentMap.insert
    (H : ConstructorOwnersPresentMap C) (hwf : C.WF)
    (hfresh : C.find? ci.name = none)
    (howner : ∀ info, ci = .ctorInfo info →
      ∃ owner, C.find? info.induct = some (.inductInfo owner)) :
    ConstructorOwnersPresentMap (C.insert ci.name ci) := by
  have hpreserves : ∀ {name found}, C.find? name = some found →
      (C.insert ci.name ci).find? name = some found := by
    intro name found hfind
    rw [hwf.find?_insert]
    split
    · rename_i heq
      have hname : ci.name = name := LawfulBEq.eq_of_beq heq
      subst name
      rw [hfind] at hfresh
      contradiction
    · exact hfind
  intro name info hfind
  rw [hwf.find?_insert] at hfind
  split at hfind
  · rcases howner info (Option.some.inj hfind) with ⟨owner, howner⟩
    exact ⟨owner, hpreserves howner⟩
  · rcases H name info hfind with ⟨owner, howner⟩
    exact ⟨owner, hpreserves howner⟩

theorem ConstructorOwnersPresentMap.mapExt
    (H : ConstructorOwnersPresentMap source)
    (heq : ∀ name, source.find? name = target.find? name) :
    ConstructorOwnersPresentMap target := by
  intro name info hfind
  rw [← heq] at hfind
  rcases H name info hfind with ⟨owner, howner⟩
  exact ⟨owner, by rw [← heq]; exact howner⟩

/-- Registry coherence survives a batch that adds no singleton family: every
new family has a constructor count other than one, and every new constructor
belongs to a family absent from the source.  Old families keep their aligned
registry entries by monotonicity. -/
theorem ProjectionRegistryCoherent.extendNonSingleton
    (H : ProjectionRegistryCoherent safety sourceC sourceEnv)
    (hpreserves : ∀ {name ci}, sourceC.find? name = some ci →
      targetC.find? name = some ci)
    (hfamilies : ∀ {name info}, targetC.find? name = some (.inductInfo info) →
      sourceC.find? name = some (.inductInfo info) ∨ info.ctors.length ≠ 1)
    (hreflect : ∀ {name info}, targetC.find? name = some (.ctorInfo info) →
      sourceC.find? name = some (.ctorInfo info) ∨
        sourceC.find? info.induct = none)
    (henv : sourceEnv ≤ targetEnv) :
    ProjectionRegistryCoherent safety targetC targetEnv := by
  intro familyName familyInfo constructorName constructorInfo hfamily hvisible
    hsingle hconstructor hinduct
  rcases hfamilies hfamily with hold | hlength
  · rcases hreflect hconstructor with holdConstructor | hnone
    · rcases H familyName familyInfo constructorName constructorInfo hold
        hvisible hsingle holdConstructor hinduct with ⟨P⟩
      exact ⟨P.rebase hpreserves henv⟩
    · rw [hinduct, hold] at hnone
      contradiction
  · exact absurd (by simp [hsingle]) hlength

/-- Complete a constructor-stage registry from the positional production
alignment of a whole declaration.  Old families are rebased through the
concrete and abstract extension; every new constructor names a new family as
its owner, so an old singleton family can only be completed by its own old
constructor.  New singleton families are reconstructed from their positional
production alignment, the exact abstract constant spines, and the registered
projection entries. -/
theorem ProjectionRegistryCoherent.extendInductive
    (H : ProjectionRegistryCoherent safety sourceC sourceEnv)
    (horigins : ProductionInductiveOrigins sourceC targetC decl)
    (hpreserves : ∀ {name ci}, sourceC.find? name = some ci →
      targetC.find? name = some ci)
    (hreflect : ∀ {name info}, targetC.find? name = some (.ctorInfo info) →
      sourceC.find? name = some (.ctorInfo info) ∨
        sourceC.find? info.induct = none)
    (htypeUvars : ∀ type ∈ decl.types, type.uvars = decl.uvars)
    (hctorUvars : ∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars)
    (htypes : sourceEnv.addConstVals decl.typeConstants = some envTypes)
    (hctors : envTypes.addConstVals decl.constructorConstants = some envCtors)
    (henv : envCtors ≤ targetEnv)
    (hentries : ∀ entry ∈ decl.projectionEntries,
      targetEnv.projections entry.typeName entry.info) :
    ProjectionRegistryCoherent safety targetC targetEnv := by
  have hsourceLe : sourceEnv ≤ targetEnv :=
    (VEnv.addConstVals_le htypes).trans ((VEnv.addConstVals_le hctors).trans henv)
  intro familyName familyInfo constructorName constructorInfo hfamily hvisible
    hsingle hconstructor hinduct
  rcases horigins familyName familyInfo hfamily with hold | hnew
  · rcases hreflect hconstructor with holdConstructor | hnone
    · rcases H familyName familyInfo constructorName constructorInfo hold
        hvisible hsingle holdConstructor hinduct with ⟨P⟩
      exact ⟨P.rebase hpreserves hsourceLe⟩
    · rw [hinduct, hold] at hnone
      contradiction
  · rcases hnew with ⟨familyIdx, hname, ⟨A⟩⟩
    let owner := decl.types[familyIdx]'A.familyIdx_lt
    have hownerLength : owner.ctors.length = 1 := by
      change (decl.types[familyIdx]'A.familyIdx_lt).ctors.length = 1
      rw [← A.constructors, hsingle]
      rfl
    cases hownerCtors : owner.ctors with
    | nil => simp [hownerCtors] at hownerLength
    | cons constructor tail =>
      cases tail with
      | cons next rest => simp [hownerCtors] at hownerLength
      | nil =>
        have hctorIdx : 0 <
            (decl.types[familyIdx]'A.familyIdx_lt).ctors.length := by
          change 0 < owner.ctors.length
          rw [hownerCtors]
          simp
        rcases A.constructor 0 hctorIdx with ⟨C⟩
        have hctorEq :
            (decl.types[familyIdx]'A.familyIdx_lt).ctors[0]'hctorIdx =
              constructor := by
          change owner.ctors[0]'_ = constructor
          simp [hownerCtors]
        have hconstructorName : constructorName = constructor.name := by
          simpa [hsingle, hctorEq] using C.name
        have hinfoEq : C.info = constructorInfo := by
          have hlookup := C.lookup
          simp only [hsingle, List.getElem_cons_zero] at hlookup
          exact ConstantInfo.ctorInfo.inj
            (Option.some.inj (hlookup.symm.trans hconstructor))
        have hownerMem : owner ∈ decl.types := List.getElem_mem A.familyIdx_lt
        have hconstructorMem : constructor ∈ decl.constructorConstants := by
          simp only [VInductDecl.constructorConstants, List.mem_flatMap]
          exact ⟨owner, hownerMem, by simp [hownerCtors]⟩
        have hfamilyLookupRaw := VEnv.addConstVals_get htypes
          (show owner.toVConstVal ∈ decl.typeConstants by
            exact List.mem_map.mpr ⟨owner, hownerMem, rfl⟩)
        have hconstructorLookupRaw := VEnv.addConstVals_get hctors hconstructorMem
        have hownerUvars : owner.uvars = decl.uvars := htypeUvars owner hownerMem
        have hconstructorUvars : constructor.uvars = decl.uvars :=
          hctorUvars constructor hconstructorMem
        have hentry : ({
            typeName := owner.name
            info := {
              uvars := decl.uvars
              nparams := decl.nparams
              nindices := owner.numIndices
              resultLevel := owner.resultLevel
              ctorName := constructor.name
              ctorType := constructor.type } } : VProjectionEntry) ∈
            decl.projectionEntries := by
          rw [VInductDecl.projectionEntries, List.mem_filterMap]
          exact ⟨owner, hownerMem, by simp [hownerCtors]⟩
        have hfamilyName : familyName = owner.name := hname.trans A.name
        refine ⟨{
          info := {
            uvars := decl.uvars
            nparams := decl.nparams
            nindices := owner.numIndices
            resultLevel := owner.resultLevel
            ctorName := constructor.name
            ctorType := constructor.type }
          projection := by
            rw [hfamilyName]
            exact hentries _ hentry
          ctorName := hconstructorName.symm
          uvars := A.levelParams
          nparams := A.numParams
          nindices := A.numIndices
          constructorInfo := constructorInfo
          constructor_lookup := hconstructor
          constructor_induct := hinduct
          constructor_levelParams := by rw [← hinfoEq]; exact C.levelParamsExact
          constructor_numParams := by
            rw [← hinfoEq, C.numParams, A.numParams]
          constructor_isUnsafe := by
            rw [← hinfoEq, C.isUnsafe, A.isUnsafe]
          constructor_numFields := by
            rw [← hinfoEq, C.numFields_forallArity, hctorEq]
            rfl
          familyType := owner.type
          family_lookup := by
            have h : owner.toVConstant = ⟨decl.uvars, owner.type⟩ := by
              rw [← hownerUvars]
            rw [hfamilyName, ← h]
            exact henv.constants ((VEnv.addConstVals_le hctors).constants
              hfamilyLookupRaw)
          constructor_abstract := by
            have h : constructor.toVConstant = ⟨decl.uvars, constructor.type⟩ := by
              rw [← hconstructorUvars]
            rw [hconstructorName, ← h]
            exact henv.constants hconstructorLookupRaw }⟩

/-- Every production inductive visible to this observer comes from a prior,
finitely well-formed abstract inductive installation. -/
def InstalledInductiveProvenance
    (safety : DefinitionSafety) (C : ConstMap) (env : VEnv) : Prop :=
  ∀ familyName familyInfo,
    C.find? familyName = some (.inductInfo familyInfo) →
    safety ≤ (ConstantInfo.inductInfo familyInfo).safety →
    Nonempty (InstalledInductiveFamilyProvenanceAt C env familyName familyInfo)

/-- Completed declaration provenance entails the projection-specific
invariant, but users of projection inference need only the latter. -/
theorem InstalledInductiveProvenance.projectionRegistryCoherent
    (H : InstalledInductiveProvenance safety C env) :
    ProjectionRegistryCoherent safety C env := by
  intro familyName familyInfo constructorName constructorInfo hfind hvisible
    hsingle hconstructor hinduct
  rcases H familyName familyInfo hfind hvisible with ⟨P⟩
  rcases P.projectionOfSingle hsingle with
    ⟨owner, constructor, howner, hctors, hfamily, hprojection⟩
  have hownerLength : 0 <
      (P.decl.types[P.familyIdx]'P.alignment.familyIdx_lt).ctors.length := by
    rw [← howner, hctors]
    simp
  rcases P.alignment.constructor 0 hownerLength with ⟨A⟩
  have habstract :
      (P.decl.types[P.familyIdx]'P.alignment.familyIdx_lt).ctors =
        [constructor] := by
    rw [← howner]
    exact hctors
  have hconstructorName : constructorName = constructor.name := by
    simpa [hsingle, habstract] using A.name
  have hinfoEq : A.info = constructorInfo := by
    have hlookup := A.lookup
    simp only [hsingle, List.getElem_cons_zero] at hlookup
    exact ConstantInfo.ctorInfo.inj
      (Option.some.inj (hlookup.symm.trans hconstructor))
  have hfamilyLookup :=
    P.installed.familyConstant P.familyIdx P.alignment.familyIdx_lt
  rw [← howner] at hfamilyLookup
  have hconstructorLookup :=
    P.installed.constructorConstant P.familyIdx 0
      P.alignment.familyIdx_lt hownerLength
  simp [habstract] at hconstructorLookup
  have hownerMem : owner ∈ P.decl.types := by
    rw [howner]
    exact List.getElem_mem P.alignment.familyIdx_lt
  have hconstructorMem : constructor ∈ P.decl.constructorConstants := by
    simp only [VInductDecl.constructorConstants, List.mem_flatMap]
    exact ⟨owner, hownerMem, by simp [hctors]⟩
  have hownerUvars : owner.uvars = P.decl.uvars :=
    P.installed.typeUvars owner hownerMem
  have hconstructorUvars : constructor.uvars = P.decl.uvars :=
    P.installed.constructorUvars constructor hconstructorMem
  exact ⟨{
    info := {
      uvars := P.decl.uvars
      nparams := P.decl.nparams
      nindices := owner.numIndices
      resultLevel := owner.resultLevel
      ctorName := constructor.name
      ctorType := constructor.type }
    projection := hprojection
    ctorName := hconstructorName.symm
    uvars := P.alignment.levelParams
    nparams := P.alignment.numParams
    nindices := by rw [P.alignment.numIndices, ← howner]
    constructorInfo := constructorInfo
    constructor_lookup := hconstructor
    constructor_induct := hinduct
    constructor_levelParams := by rw [← hinfoEq]; exact A.levelParamsExact
    constructor_numParams := by
      rw [← hinfoEq, A.numParams, P.alignment.numParams]
    constructor_isUnsafe := by
      rw [← hinfoEq, A.isUnsafe, P.alignment.isUnsafe]
    constructor_numFields := by
      rw [← hinfoEq, A.numFields_forallArity]
      have hctor0 : (P.decl.types[P.familyIdx]'P.alignment.familyIdx_lt).ctors[0]'
          A.ctorIdx_lt = constructor := by
        simp [habstract]
      rw [hctor0]
      rfl
    familyType := owner.type
    family_lookup := by
      have h : owner.toVConstant = ⟨P.decl.uvars, owner.type⟩ := by
        rw [← hownerUvars]
      have this := hfamilyLookup
      rw [← hfamily, h] at this
      exact this
    constructor_abstract := by
      have h : constructor.toVConstant = ⟨P.decl.uvars, constructor.type⟩ := by
        rw [← hconstructorUvars]
      rw [hconstructorName, ← h]
      exact hconstructorLookup }⟩

def InstalledInductiveFamilyProvenanceAt.mono
    (H : InstalledInductiveFamilyProvenanceAt source env familyName familyInfo)
    (hfind : target.find? familyInfo.name = some (.inductInfo familyInfo))
    (hpreserves : ∀ {name ci}, source.find? name = some ci →
      target.find? name = some ci)
    (henv : env ≤ env') :
    InstalledInductiveFamilyProvenanceAt target env' familyName familyInfo where
  decl := H.decl
  familyIdx := H.familyIdx
  name := H.name
  alignment := H.alignment.rebase hfind hpreserves
  installed := H.installed.mono henv

theorem InstalledInductiveProvenance.monoEnv
    (H : InstalledInductiveProvenance safety C env)
    (henv : env ≤ env') :
    InstalledInductiveProvenance safety C env' := by
  intro familyName familyInfo hfind hvisible
  rcases H familyName familyInfo hfind hvisible with ⟨P⟩
  exact ⟨P.mono (by simpa [P.name] using hfind) (fun h => h) henv⟩

/-- A fresh non-inductive production entry preserves declaration-level
inductive provenance across any monotone abstract extension. -/
theorem InstalledInductiveProvenance.insertNonInductive
    (H : InstalledInductiveProvenance safety C env)
    (hwf : C.WF) (hfresh : C.find? ci.name = none)
    (hnind : ∀ familyInfo, ci ≠ .inductInfo familyInfo)
    (henv : env ≤ env') :
    InstalledInductiveProvenance safety (C.insert ci.name ci) env' := by
  have hpreserves : ∀ {name found}, C.find? name = some found →
      (C.insert ci.name ci).find? name = some found := by
    intro name found hfind
    rw [hwf.find?_insert]
    split
    · rename_i heq
      have hname : ci.name = name := LawfulBEq.eq_of_beq heq
      subst name
      rw [hfind] at hfresh
      contradiction
    · exact hfind
  intro familyName familyInfo hfind hvisible
  have hold : C.find? familyName = some (.inductInfo familyInfo) := by
    rw [hwf.find?_insert] at hfind
    split at hfind
    · exact False.elim (hnind familyInfo (Option.some.inj hfind))
    · exact hfind
  rcases H familyName familyInfo hold hvisible with ⟨P⟩
  exact ⟨P.mono (by simpa [P.name] using hfind) hpreserves henv⟩

theorem AddInduct.installedCertificate
    (H : AddInduct safety source base decl target installed) :
    VEnv.InstalledInductCertificate installed decl := by
  cases H with
  | intro block hdecl hcompile hblock hinstall =>
    exact .intro hdecl.1 hdecl.2 hcompile hblock hinstall VEnv.LE.rfl

theorem InstalledInductiveProvenance.addInduct
    (Hsource : InstalledInductiveProvenance safety source base)
    (H : AddInduct safety source base decl target installed) :
    InstalledInductiveProvenance safety target installed := by
  intro familyName familyInfo hfind hvisible
  rcases H.productionOrigins familyName familyInfo hfind with hold | hnew
  · rcases Hsource familyName familyInfo hold hvisible with ⟨P⟩
    exact ⟨P.mono (by simpa [P.name] using hfind)
      H.preservesSourceFind H.le⟩
  · rcases hnew with ⟨familyIdx, hname, ⟨Halignment⟩⟩
    exact ⟨{
      decl := decl
      familyIdx := familyIdx
      name := hname
      alignment := Halignment
      installed := H.installedCertificate }⟩

/-- Insert a whole block of definitions into the constant map. -/
def insertDefs (C : ConstMap) (cis : List DefinitionVal) : ConstMap :=
  cis.foldl (fun C ci => C.insert ci.name (.defnInfo ci)) C

variable (safety : DefinitionSafety) (env env' : VEnv) in
/-- Translation data for a mutual block: the headers are translated against the environment
before the block is added, the values against the environment that already has every constant
of the block, mirroring the kernel adding them all as axioms first. -/
def TrDefBlock (cis : List DefinitionVal) (cis' : List VDefVal) : Prop :=
  List.Forall₂ (fun ci ci' =>
    TrConstVal safety env (.defnInfo ci) ci'.toVConstVal ∧
    TrExprS env' ci.levelParams [] ci.value ci'.value) cis cis'

variable (safety : DefinitionSafety) in
inductive TrEnv' : ConstMap → Bool → VEnv → Prop where
  | empty : TrEnv' {} false .empty
  | ignore :
    C.find? ci.name = none → ¬safety ≤ ci.safety →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name ci) Q env
  | axiom :
    TrConstant safety env (.axiomInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci' = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.axiomInfo ci)) Q env'
  | defn {ci' : VDefVal} :
    TrDefVal safety env (.defnInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.defnInfo ci)) Q (env'.addDefEq ci'.toDefEq)
  /-- A mutual block, and an unsafe definition as the one-element case. -/
  | mutualDef {cis : List DefinitionVal} {cis' : List VDefVal} :
    TrDefBlock safety env env' cis cis' →
    -- the block's names are distinct; `addMutual` checks this, as does lean4#14632
    (cis.map (·.name)).Nodup →
    (∀ ci ∈ cis, C.find? ci.name = none) →
    (∀ ci' ∈ cis', ci'.toVConstant.WF env) →
    env.addConsts cis' = some env' →
    (∀ ci' ∈ cis', ci'.WF env') →
    TrEnv' C Q env →
    TrEnv' (insertDefs C cis) Q (env'.addDefEqs cis')
  | thm {ci' : VDefVal} :
    TrDefVal safety env (.thmInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.HasType ci'.uvars [] ci'.type (.sort .zero) →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.thmInfo ci)) Q env'
  | opaque {ci' : VDefVal} :
    TrDefVal safety env (.opaqueInfo ci) ci' →
    C.find? ci.name = none → ci'.WF env →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.opaqueInfo ci)) Q env'
  | quot :
    env.QuotReady →
    AddQuot C C' env env' →
    TrEnv' C false env →
    TrEnv' C' true env'
  | induct :
    decl.WF env →
    AddInduct safety C env decl C' env' →
    TrEnv' C Q env →
    TrEnv' C' Q env'

def TrEnv (safety : DefinitionSafety) (env : Environment) (venv : VEnv) : Prop :=
  TrEnv' safety env.constants env.quotInit venv

theorem TrEnv'.wf (H : TrEnv' safety C Q venv) : venv.WF := by
  induction H with
  | empty => exact ⟨_, .empty⟩
  | ignore _ _ _ ih => exact ih
  | «axiom» _ _ h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .axiom (ci := ⟨_, _⟩) h1 h2⟩
  | defn h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .def h2 (this ▸ h3)⟩
  | mutualDef _ _ _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .mutualDef h2 h3 h4⟩
  | thm h1 _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    have hn := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    exact ⟨_, (H.decl (.example h2)).decl (.axiom ⟨_, h3⟩ (hn ▸ h4))⟩
  | «opaque» h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .opaque h2 (this ▸ h3)⟩
  | quot h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2.to_addQuot⟩
  | induct h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .induct h1 h2.toVEnv⟩
