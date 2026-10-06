import Lean4Lean.Theory.Typing.ShapeModel.EnvSigSchema
import Lean4Lean.Theory.Typing.ShapeModel.Sound.Ctor
import Lean4Lean.Theory.Typing.SchemaStructCompat

/-!
# The semantic signature of a well-formed environment (M4b)

`envSig env : SemSig` reads the shape model's semantic signature off a well-formed environment.
-/

namespace Lean4Lean.ShapeModel
open InductiveSignature

noncomputable section
open Classical

variable (env : VEnv)

/-- The parameter count of `c` as a registered structure constructor, `0` if it is none. -/
def structNp (c : Name) : Nat :=
  if h : ∃ info : VProjectionInfo, (∃ s, env.projections s info) ∧ info.ctorName = c then
    (Classical.choose h).nparams
  else 0

/-- `c` is the major constructor of a generic equation of a registered eliminator schema. -/
def SchemaMajor (c : Name) : Prop :=
  ∃ (key : Name) (schema : CaseSchema), env.eliminators key schema ∧
    ∃ (owner : Fin schema.signature.families.size) (rules : List VDefEq) (df : VDefEq) (fn : VExpr)
      (ls : List VLevel) (args : List VExpr),
      schema.genericEquations key owner = some rules ∧ df ∈ rules ∧
      df.lhs.stripLams = .app fn (VExpr.mkApps (.const c ls) args)

/-- The constructors of the signature: the constructor table of the first registrations
(native installations including container constructors, structure registrations, eliminator
registrations, `Quot.mk`) and the majors of all generic eliminator equations. -/
def IsCtor (c : Name) : Prop := ctorOf env c ≠ none ∨ SchemaMajor env c

/-- The constructor data of the signature. -/
def sigCtor (c : Name) : Option CtorInfo :=
  if IsCtor env c then
    (env.constants c).bind fun ci => (familyOfType ci.type).map fun F =>
      ⟨F, structNp env c, ci.type.forallArity - structNp env c⟩
  else none

/-- Remove duplicates (keeping last occurrences). -/
def dedupNames : List Name → List Name
  | [] => []
  | x :: xs => if x ∈ dedupNames xs then dedupNames xs else x :: dedupNames xs

/-- A list of all declared constants. -/
def constNames : List Name := if h : ∃ L, ConstList env L then Classical.choose h else []

/-- The constructors of a family. -/
def sigFamCtors (I : Name) : List Name :=
  dedupNames ((constNames env).filter fun c => decide (∃ ci, sigCtor env c = some ci ∧ ci.family = I))

/-- The result level of a family, from its first registration. -/
def sigFamLevel (I : Name) : Option VLevel := (famOf env I).map (·.resultLevel)

/-- Structure constructors with eta: constructors of registered structures without indices. -/
def sigIsStruct (c : Name) : Bool :=
  decide (∃ s info, env.projections s info ∧ info.ctorName = c ∧ info.nindices = 0)

/-- The constructor of a registered structure. -/
def sigStructCtor (s : Name) : Option Name :=
  if h : ∃ info, env.projections s info then some (Classical.choose h).ctorName else none

/-- The generic type of an eliminator slot. -/
def sigElimType (b : Name) (o : Nat) : Option VExpr :=
  if h : ∃ (schema : CaseSchema) (T : VExpr), env.eliminators b schema ∧
      ∃ ho : o < schema.signature.families.size, schema.genericType ⟨o, ho⟩ = some T then
    some (Classical.choose (Classical.choose_spec h))
  else none

/-- The field count of a generic eliminator equation: the number of arguments of its right body
(a minor applied to the fields). -/
def schemaNf (df : VDefEq) : Nat := (dropLams (lamDoms df.lhs).length df.rhs).getAppFnArgs.2.length

/-- The rules of the signature. -/
def EnvRule (r : Rule) : Prop :=
  (∃ v : VDefVal, env.defeqs v.toDefEq ∧ (envTables env).defs v.name = some v ∧ r = defRule v) ∨
  (env.defeqs quotDefEq ∧ (envTables env).quot = true ∧
    r = majorRule (structNp env) (.const ``Quot.lift) quotDefEq.uvars quotDefEq 1) ∨
  (∃ df, env.defeqs df ∧ ∃ data : NativeRecursorData, (envTables env).natives data.name = some data ∧
    ∃ index : Fin data.schema.signature.constructors.size,
      data.schema.signature.constructors[index].owner = data.owner ∧ data.equation index = some df ∧
      r = majorRule (structNp env) (.const data.name) df.uvars df
        data.schema.signature.constructors[index].fields.length) ∨
  (∃ (key : Name) (schema : CaseSchema), env.eliminators key schema ∧
    ∃ (owner : Fin schema.signature.families.size) (rules : List VDefEq) (df : VDefEq),
      schema.genericEquations key owner = some rules ∧ df ∈ rules ∧
      r = majorRule (structNp env) (.elim key owner.val) schema.genericUvars df (schemaNf df))

/-- The semantic signature of an environment. -/
@[instance_reducible] def envSig : SemSig where
  ctor := sigCtor env
  famLevel := sigFamLevel env
  famCtors := sigFamCtors env
  isStruct := sigIsStruct env
  rules := EnvRule env
  elimType := sigElimType env
  structCtor := sigStructCtor env

end

end Lean4Lean.ShapeModel
