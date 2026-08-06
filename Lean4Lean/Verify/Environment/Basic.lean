import Lean4Lean.Verify.LocalContext
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Declaration

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem ConstantInfo.hasValue_eq (ci : ConstantInfo) : ci.hasValue = ci.value?.isSome := by
  cases ci <;> rfl

theorem ConstantInfo.value!_eq (ci : ConstantInfo) : ci.value! = ci.value?.get! := by
  cases ci <;> simp [ConstantInfo.value?, ConstantInfo.value!]

def _root_.Lean.ConstantInfo.safety (ci : ConstantInfo) : DefinitionSafety :=
  if ci.isUnsafe then .unsafe else if ci.isPartial then .partial else .safe

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
  TrExprS env ci.levelParams [] ci.value! ci'.value

/-- Translation of a source constant before the kernel has assigned it a
`ConstantInfo` variant. This is used for inductive headers and constructors,
whose types are translated at different environment stages. -/
structure TrSourceConst (env : VEnv) (lparams : List Name)
    (name : Name) (type : Expr) (ci' : VConstVal) : Prop where
  uvars : ci'.uvars = lparams.length
  name : ci'.name = name
  type : TrExprS env lparams [] type ci'.type
  wf : ci'.toVConstant.WF env

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
    env.addConsts decl.typeConstants = some envTypes ∧
    envTypes.addConsts decl.constructorConstants = some envCtors ∧
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
  typesAdded : env.addConsts decl.typeConstants = some envTypes
  ctorsAdded : envTypes.addConsts decl.constructorConstants = some envCtors
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
  typesAdded : env.addConsts decl.typeConstants = some envTypes
  types : List.Forall₂
    (fun source target => TrSourceConst env lparams source.name source.type
      target.toVConstVal)
    types decl.types

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
    env.addConsts decl.typeConstants = some envTypes ∧
    envTypes.addConsts decl.constructorConstants = some envCtors ∧
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
  typesAdded : env.addConsts decl.typeConstants = some envTypes
  ctorsAdded : envTypes.addConsts decl.constructorConstants = some envCtors
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
  typesAdded : env.addConsts decl.typeConstants = some envTypes
  types : List.Forall₂
    (fun source target => TrSourceConst env lparams source.name source.type
      target.toVConstVal)
    types decl.types

/-- Constructor-phase translation produced after all mutual headers are
installed. It records both pointwise source typing and the exact abstract
constructor environment. -/
structure TrInductDeclConstructors (envTypes : VEnv) (lparams : List Name)
    (types : List InductiveType) (decl : VInductDecl)
    (envCtors : VEnv) : Prop where
  ctorsAdded : envTypes.addConsts decl.constructorConstants = some envCtors
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

variable (safety : DefinitionSafety) (env : VEnv) in
def TrThmVal (ci : TheoremVal) (ci' : VDefVal) : Prop :=
  TrConstVal safety env (.thmInfo ci) ci'.toVConstVal ∧
  TrExprS env ci.levelParams [] ci.value ci'.value

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

theorem VInductBlock.install_le
    (H : VInductBlock.install env block = some env') : env ≤ env' := by
  unfold VInductBlock.install at H
  cases htypes : env.addConsts block.types with
  | none => simp [htypes] at H
  | some envTypes =>
    cases hctors : envTypes.addConsts block.ctors with
    | none => simp [htypes, hctors] at H
    | some envCtors =>
      cases hrecursors : envCtors.addConsts block.recursors with
      | none => simp [htypes, hctors, hrecursors] at H
      | some envRecursors =>
        simp [htypes, hctors, hrecursors] at H
        subst env'
        exact (VEnv.addConsts_le htypes).trans <|
          (VEnv.addConsts_le hctors).trans <|
            (VEnv.addConsts_le hrecursors).trans VEnv.addDefEqs_le

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)

/-- Constructive implementation boundary for an inductive extension. Besides
the independent compilation and installation witnesses, it records the exact
production-map alignment proof that the executable `addInductive` verifier
must eventually construct. The `Eq` clause is the canonicality fact consumed
by quotient initialization. -/
inductive AddInduct (m₁ : ConstMap) (env₁ : VEnv) (decl : VInductDecl)
    (m₂ : ConstMap) (env₂ : VEnv) : Prop where
  | intro (_block : VInductBlock) :
    decl.WF env₁ →
    VInductDecl.CompilesTo env₁ decl _block →
    VInductBlock.WF env₁ _block →
    VInductBlock.install env₁ _block = some env₂ →
    (∀ safety, Aligned safety m₁ env₁ → Aligned safety m₂ env₂) →
    (∀ {name ci}, m₂.find? name = some ci → ci.deltaValue?.isSome →
      m₁.find? name = some ci) →
    (∀ info, m₂.find? ``Eq = some (.inductInfo info) →
      env₂.constants ``Eq = some eqConst) →
    AddInduct m₁ env₁ decl m₂ env₂

theorem AddInduct.toVEnv
    (H : AddInduct m₁ env₁ decl m₂ env₂) : VEnv.AddInduct env₁ decl env₂ :=
  match H with
  | .intro _ hdecl hcompile hblock hinstall _ _ _ =>
    .intro hdecl hcompile hblock hinstall

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
  | thm {ci' : VDefVal} :
    TrThmVal safety env ci ci' →
    C.find? ci.name = none → ci'.WF env →
    env.HasType ci'.uvars [] ci'.type (.sort .zero) →
    env.addConst ci.name ci'.toVConstant = some env' →
    TrEnv' C Q env →
    TrEnv' (C.insert ci.name (.thmInfo ci)) Q env'
  /-- Opaque bodies do not contribute definitional equalities, so `TrEnv'` retains only
  the checked header. Soundness of the opaque-body checker is not represented here. -/
  | opaque {ci' : VConstVal} :
    TrConstVal safety env (.opaqueInfo ci) ci' →
    C.find? ci.name = none → ci'.toVConstant.WF env →
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
    AddInduct C env decl C' env' →
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
  | thm h1 _ h2 h3 h4 _ ih =>
    have ⟨_, H⟩ := ih
    have hn := h1.1.2
    dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at hn
    exact ⟨_, (H.decl (.example h2)).decl (.axiom ⟨_, h3⟩ (hn ▸ h4))⟩
  | «opaque» h1 _ h2 h3 _ ih =>
    have ⟨_, H⟩ := ih
    have := h1.2; dsimp [ConstantInfo.name, ConstantInfo.toConstantVal] at this
    exact ⟨_, H.decl <| .axiom h2 (this ▸ h3)⟩
  | quot h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .quot h1 h2.to_addQuot⟩
  | induct h1 h2 _ ih =>
    have ⟨_, H⟩ := ih
    exact ⟨_, H.decl <| .induct h1 h2.toVEnv⟩
