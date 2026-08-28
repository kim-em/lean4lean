import Batteries.Data.List.Basic
import Lean4Lean.Environment.Basic
import Lean4Lean.TypeChecker

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace AddInductive
open TypeChecker

structure RecCallBlueprint where
  major : Expr
  args : Array Expr
  /-- The producer context containing the temporary higher-order binders in
  `args`.  These binders are out of scope by final recursor installation, so
  rule construction must not consult the final ambient context for them. -/
  lctx : LocalContext
  targetTypeIdx : Nat
  targetIndices : Array Expr
  /-- The complete call closed over its temporary higher-order binders, with
  one outer de Bruijn placeholder for the final recursor application.  It is
  produced before those temporary identifiers leave scope, so later outer
  binders cannot be confused with them even if the reader-local name
  generator reuses an identifier. -/
  template : Expr
  deriving Inhabited

structure RecRuleBlueprint where
  ctor : Name
  fields : Array Expr
  /-- The producer context containing the temporary constructor fields. -/
  lctx : LocalContext
  recursiveCalls : Array RecCallBlueprint
  targetTypeIdx : Nat
  targetIndices : Array Expr
  minor : Expr
  deriving Inhabited

structure RecInfo where
  motive : Expr
  minors : Array Expr
  indices : Array Expr
  major : Expr
  ruleBlueprints : Array RecRuleBlueprint := #[]
  deriving Inhabited

structure InductiveStats where
  lctx : LocalContext := {}
  levels : List Level
  resultLevel : Level
  nindices : Array Nat := #[]
  indConsts : Array Expr
  params : Array Expr
  isNotZero : Bool
  deriving Inhabited

structure Context where
  env : Environment
  lctx : LocalContext := {}
  lparams : List Name
  /-- Universe parameters used by embedded typechecker calls.  Inductive
  declarations normally use `lparams`; generated large-elimination recursors
  temporarily prepend their fresh result-universe parameter. -/
  typeCheckerLParams : Option (List Name) := none
  ngen : NameGenerator := { namePrefix := `_ind_fresh }
  safety : DefinitionSafety
  allowPrimitive : Bool
  fuel : FuelConfig := {}

abbrev M := ReaderT Context <| Except Exception

instance : MonadLocalNameGenerator M where
  withFreshId f c := f c.ngen.curr { c with ngen := c.ngen.next }

instance (priority := low) : MonadLift TypeChecker.M M where
  monadLift x c := x.run c.env c.safety c.lctx
    (c.typeCheckerLParams.getD c.lparams) (fuel := c.fuel)

instance (priority := low+1) : MonadWithReaderOf LocalContext M where
  withReader f x := withReader (fun c => { c with lctx := f c.lctx }) x

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

@[inline] def withEnv (env : Environment) (x : M α) : M α :=
  withReader (fun c => { c with env }) x

/-- Run embedded typechecker calls under the universe parameters of a
generated recursor while preserving every other inductive-checker reader
field. -/
@[inline] def withTypeCheckerLParams (lparams : List Name) (x : M α) : M α :=
  withReader (fun c => { c with typeCheckerLParams := some lparams }) x

def getType (fvar : Expr) : M Expr :=
  return ((← getLCtx).get! fvar.fvarId!).type

def checkClosedType (name : Name) (type : Expr) : M Expr := do
  let env := (← read).env
  env.checkNoMVarNoFVar name type
  checkType type

namespace checkInductiveTypes

def loopType (nparams : Nat) (stats : InductiveStats) (type : Expr)
    (i nindices fuel : Nat) (k : Expr → InductiveStats → Nat → M α) : M α :=
  match fuel with
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := type then
      if i < nparams then
        if stats.indConsts.isEmpty then
          withLocalDecl name bi dom.consumeTypeAnnotationsVerified fun param => do
            let stats := { stats with params := stats.params.push param }
            let type := body.instantiate1 param
            loopType nparams stats (← whnf type) (i + 1) nindices fuel k
        else
          let param := stats.params[i]!
          unless ← isDefEq dom (← getType param) do
            throw <| .other "parameters of all inductive datatypes must match"
          let type := body.instantiate1 param
          loopType nparams stats (← whnf type) (i + 1) nindices fuel k
      else
        withLocalDecl name bi dom.consumeTypeAnnotationsVerified fun arg => do
          let type := body.instantiate1 arg
          loopType nparams stats (← whnf type) i (nindices + 1) fuel k
    else
      if i != nparams then
        throw <| .other "number of parameters mismatch in inductive datatype declaration"
      k type stats nindices

def loopInd (nparams : Nat) (indTypes : Array InductiveType)
    (dIdx : Nat) (stats : InductiveStats) (k : InductiveStats → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let indType := indTypes[dIdx]
    let type := indType.type
    _ ← checkClosedType indType.name type
    let fuel := (← readThe Context).fuel.inductiveFuel
    loopType nparams stats (← whnf type) 0 0 fuel fun type stats nindices => show M α from do
    let type ← ensureSort type
    let mut stats := stats
    let resultLevel := type.sortLevel!
    if stats.indConsts.isEmpty then
      let lctx := (← read).lctx
      stats := { stats with lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
    else if !resultLevel.isEquiv stats.resultLevel then
      throw <| .other "mutually inductive types must live in the same universe"
    stats := { stats with
      nindices := stats.nindices.push nindices
      indConsts := stats.indConsts.push (.const indType.name stats.levels) }
    loopInd nparams indTypes (dIdx + 1) stats k
  else
    k <|
      assert! stats.levels.length == (← read).lparams.length
      assert! stats.nindices.size == indTypes.size
      assert! stats.indConsts.size == indTypes.size
      assert! stats.params.size == nparams
      stats
termination_by indTypes.size - dIdx

end checkInductiveTypes

def checkInductiveTypes
    (nparams : Nat) (indTypes : Array InductiveType)
    (k : InductiveStats → M α) : M α := do
  checkInductiveTypes.loopInd nparams indTypes 0
    { (default : InductiveStats) with levels := (← read).lparams.map .param } k

def hasIndOcc (indConsts : Array Expr) (t : Expr) : Bool :=
  t.findAny fun
    | .const e _ => indConsts.any fun I => I.constName! == e
    | _ => false

/-- Return true if declaration is recursive -/
def isRec (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

/-- Return true if the given declaration is reflexive.

Remark: We say an inductive type `T` is reflexive if it
contains at least one constructor that takes as an argument a
function returning `T'` where `T'` is another inductive datatype (possibly equal to `T`)
in the same mutual declaration. -/
def isReflexive (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => dom.isForall && hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

/-- Production `ConstantInfo` payloads for the mutually declared type
constants. Kept as a named function so verification can relate the metadata-
enriched kernel entries to the independently translated source headers. -/
def inductiveTypeInfos (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (lparams : List Name) : Array InductiveVal :=
  let all := indTypes.map (·.name) |>.toList
  indTypes.zipWith (bs := stats.nindices) fun indType numIndices =>
    { indType with
      numParams, numIndices, all, numNested, isUnsafe
      levelParams := lparams
      ctors := indType.ctors.map (·.name)
      isRec := isRec indTypes stats.indConsts
      isReflexive := isReflexive indTypes stats.indConsts }

/-- Public name for the private kernel environment insertion primitive used by
the executable declaration fold.  Naming this boundary lets verification state
and prove its lookup-preservation contract directly. -/
def addConstant (env : Environment) (info : ConstantInfo) : Environment :=
  env.add info

def declareInductiveTypeInfos (allowPrimitive : Bool) :
    List InductiveVal → Environment → Except Exception Environment
  | [], env => pure env
  | info :: infos, env => do
    env.checkName info.name allowPrimitive
    declareInductiveTypeInfos allowPrimitive infos
      (addConstant env (.inductInfo info))

def declareInductiveTypes (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) : M Environment :=
  fun c =>
  let infos := inductiveTypeInfos stats numParams indTypes numNested
    isUnsafe c.lparams
  declareInductiveTypeInfos c.allowPrimitive infos.toList c.env

def isValidIndAppIdx (stats : InductiveStats) (t : Expr) (i : Nat) : Bool :=
  t.withApp fun I args => Id.run do
  unless I == stats.indConsts[i]! && args.size == stats.params.size + stats.nindices[i]! do
    return false
  unless stats.params == args.extract 0 stats.params.size do
    return false
  unless (args.extract stats.params.size args.size).all fun arg =>
      !hasIndOcc stats.indConsts arg do
    return false
  true

def isValidIndAppFrom? (stats : InductiveStats) (t : Expr) (start : Nat) :
    Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if isValidIndAppIdx stats t start then some start
    else isValidIndAppFrom? stats t (start + 1) fuel

def isValidIndApp? (stats : InductiveStats) (t : Expr) : Option Nat :=
  isValidIndAppFrom? stats t 0 stats.indConsts.size

def isRecArg (stats : InductiveStats) (t : Expr) : M (Option Nat) := do
  loop t (← readThe Context).fuel.inductiveFuel
where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    let .forallE name dom body bi := t | return isValidIndApp? stats t
    withLocalDecl name bi dom.consumeTypeAnnotationsVerified fun arg => do
    loop (body.instantiate1 arg) fuel

def checkPositivityStep (stats : InductiveStats) (t : Expr)
    (ctor : Name) (idx : Nat) (recur : Expr → M Unit) : M Unit := do
  if !hasIndOcc stats.indConsts t then return
  if let .forallE name dom body bi := t then
    if hasIndOcc stats.indConsts dom then
      throw <| .other s!"arg #{idx + 1} of '{ctor}' \
        has a non positive occurrence of the datatypes being declared"
    withLocalDecl name bi dom.consumeTypeAnnotationsVerified fun arg => do
      recur (body.instantiate1 arg)
  else if let none := isValidIndApp? stats t then
    throw <| .other s!"arg #{idx + 1} of '{ctor}' \
      has a non valid occurrence of the datatypes being declared"

def checkPositivity (stats : InductiveStats) (t : Expr) (ctor : Name) (idx : Nat) :
    M Unit := do loop t (← readThe Context).fuel.inductiveFuel where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    checkPositivityStep stats t ctor idx fun body => loop body fuel

namespace checkConstructors

def loopCtor (stats : InductiveStats) (isUnsafe : Bool) (ctor : Name)
    (targetIdx : Nat) (t : Expr) (i fuel : Nat) : M Unit :=
  match fuel with
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        unless ← isDefEq dom (← getType param) do
          throw <| .other
            s!"arg #{i + 1} of '{ctor}' does not match inductive datatype parameters"
        loopCtor stats isUnsafe ctor targetIdx
          (body.instantiate1 param) (i + 1) fuel
      else
        let s ← ensureType dom
        unless stats.resultLevel.isAlwaysZero || stats.resultLevel.geq' s.sortLevel! do
          throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{ctor}' \
            is too big for the corresponding inductive datatype"
        if !isUnsafe then
          checkPositivity stats dom ctor i
        withLocalDecl name bi dom.consumeTypeAnnotationsVerified fun arg => do
          loopCtor stats isUnsafe ctor targetIdx
            (body.instantiate1 arg) (i + 1) fuel
    else if !isValidIndAppIdx stats t targetIdx then
      throw <| .other s!"invalid return type for '{ctor}'"

end checkConstructors

namespace checkConstructors

def loopCtors (stats : InductiveStats) (isUnsafe : Bool)
    (targetIdx : Nat) (ctors : List Constructor) (ctorIdx : Nat)
    (foundCtors : NameSet) : M Unit := do
  if h : ctorIdx < ctors.length then
    let ctor := ctors[ctorIdx]
    let n := ctor.name
    if foundCtors.contains n then
      throw <| .other s!"duplicate constructor name '{n}'"
    let foundCtors := foundCtors.insert n
    let t := ctor.type
    _ ← checkClosedType n t
    checkConstructors.loopCtor stats isUnsafe n targetIdx t 0
      (← readThe Context).fuel.inductiveFuel
    loopCtors stats isUnsafe targetIdx ctors (ctorIdx + 1) foundCtors
  else
    pure ()
termination_by ctors.length - ctorIdx

def loopTypes (indTypes : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) (targetIdx : Nat) : M Unit := do
  if h : targetIdx < indTypes.size then
    loopCtors stats isUnsafe targetIdx indTypes[targetIdx].ctors 0 {}
    loopTypes indTypes stats isUnsafe (targetIdx + 1)
  else
    pure ()
termination_by indTypes.size - targetIdx

end checkConstructors

def checkConstructors (indTypes : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) : M Unit := do
  let _ ← getEnv
  checkConstructors.loopTypes indTypes stats isUnsafe 0

/-- Number of binders in a constructor's complete source telescope.  Keeping
this calculation named makes the production `numFields` entry available to
the projection refinement without duplicating the executable traversal. -/
def constructorArity : Expr → Nat
  | .forallE _ _ body _ => constructorArity body + 1
  | _ => 0

/-- Production metadata for one constructor. Keeping this record construction
named lets verification retain the exact source-aligned entry, rather than
only its translated type. -/
def constructorInfo (stats : InductiveStats) (lparams : List Name)
    (isUnsafe : Bool) (indType : InductiveType) (cidx : Nat)
    (ctor : Constructor) : ConstructorVal :=
  let type := ctor.type
  let arity := constructorArity type
  {
    type, cidx, isUnsafe
    levelParams := lparams
    name := ctor.name
    induct := indType.name
    numParams := stats.params.size
    numFields := assert! arity ≥ stats.params.size
      arity - stats.params.size
  }

@[simp] theorem constructorInfo_numFields
    (stats : InductiveStats) (lparams : List Name)
    (isUnsafe : Bool) (indType : InductiveType) (cidx : Nat)
    (ctor : Constructor) :
    (constructorInfo stats lparams isUnsafe indType cidx ctor).numFields =
      constructorArity ctor.type - stats.params.size := by
  simp [constructorInfo]
  omega

def declareConstructors (stats : InductiveStats)
    (indTypes : Array InductiveType) (isUnsafe : Bool) : M Environment :=
  fun c => indTypes.foldlM (init := c.env) fun env indType => do
    let (_, env) ← indType.ctors.foldlM (init := (0, env)) fun (cidx, env) ctor => do
      env.checkName ctor.name c.allowPrimitive
      pure (cidx + 1, addConstant env <| .ctorInfo
        (constructorInfo stats c.lparams isUnsafe indType cidx ctor))
    pure env

/-- Return true if recursor can map into any universe -/
def isLargeEliminator (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  if stats.isNotZero then return true
  let #[indType] := indTypes | return false
  match indType.ctors with
  | [] => return true
  | [ctor] =>
    let rec loop type i toCheck
    | 0 => throw .deepRecursion
    | fuel+1 => do
      if let .forallE name dom body bi := type then
        withLocalDecl name bi dom.consumeTypeAnnotationsVerified fun arg => do
          let mut toCheck := toCheck
          if i ≥ stats.params.size then
            if !(← ensureType dom).sortLevel!.isAlwaysZero then
              toCheck := toCheck.push arg
          loop (body.instantiate1 arg) (i + 1) toCheck fuel
      else
        return toCheck.all type.getAppArgs.contains
    loop ctor.type 0 #[] (← readThe Context).fuel.inductiveFuel
  | _ => return false

def getElimLevel (stats : InductiveStats) (indTypes : Array InductiveType) :
    M Level := do
  unless ← isLargeEliminator stats indTypes do return .zero
  let {lparams, ..} ← read
  let rec loop u i
    | 0 => throw <| .other "failed to select a fresh recursor universe parameter"
    | fuel + 1 => do
      unless lparams.contains u do return .param u
      loop ((`u).appendIndexAfter i) (i + 1) fuel
  loop `u 1 (lparams.length + 1)

def isKTarget (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  let #[indType] := indTypes | return false
  unless stats.resultLevel.isAlwaysZero do return false
  let [ctor] := indType.ctors | return false
  let rec loop i
    | .forallE _ _ body _ => i < stats.params.size && loop (i + 1) body
    | _ => true
  return loop 0 ctor.type

@[inline] def getIIndices (stats : InductiveStats) (t : Expr) : Nat × Array Expr :=
  ((isValidIndApp? stats t).get!, t.getAppArgs[stats.params.size:])

-- FIXME: The function below has been exploded into nested loops as standalone functions
-- because I couldn't get them all to compile together as `let rec`s.
namespace mkRecInfos

def loopArgs1 (stats : InductiveStats) (type : Expr) (i : Nat) (indices : Array Expr)
    (fuel : Nat) (k : Array Expr → M α) : M α := match fuel with
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := type then
      if i < stats.params.size then
        loopArgs1 stats (← whnf <| body.instantiate1 stats.params[i]!) (i + 1) indices fuel k
      else
        withLocalDecl name bi dom.consumeTypeAnnotationsVerified fun arg => do
        loopArgs1 stats (← whnf <| body.instantiate1 arg) i (indices.push arg) fuel k
    else
      if i < stats.params.size then
        throw <| .other "recursor parameter arity does not match checked inductive header"
      else
        k indices

variable (stats : InductiveStats) (indTypes : Array InductiveType) (elimLevel : Level) in
def loopInd1 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let ctx ← readThe Context
    loopArgs1 stats (← whnf indTypes[dIdx].type) 0 #[] ctx.fuel.inductiveFuel fun indices => do
    unless indices.size == stats.nindices[dIdx]! do
      throw <| .other "recursor index arity does not match checked inductive header"
    let tTy := mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices
    withLocalDecl `t .default tTy.consumeTypeAnnotationsVerified fun major => do
    let lctx ← getLCtx
    let motiveTy := lctx.mkForall indices <| lctx.mkForall #[major] <| .sort elimLevel
    let name := if indTypes.size > 1 then (`motive).appendIndexAfter (dIdx+1) else `motive
    withLocalDecl name .default motiveTy.consumeTypeAnnotationsVerified fun motive => do
    loopInd1 (dIdx + 1) (recInfos.push {
      motive, minors := #[], indices, major, ruleBlueprints := #[] }) k
  else
    k recInfos
termination_by indTypes.size - dIdx

variable (stats : InductiveStats) in
def loopCtorArgs (t : Expr) (k : Expr → Array Expr → Array Expr → M α) : M α := do
  loop t 0 #[] #[] (← readThe Context).fuel.inductiveFuel
where
  loop t i bu u
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        loop (body.instantiate1 param) (i + 1) bu u fuel
      else
        withLocalDecl name bi dom.consumeTypeAnnotationsVerified fun arg => do
        let bu := bu.push arg
        let u := if (← isRecArg stats dom).isSome then u.push arg else u
        loop (body.instantiate1 arg) (i + 1) bu u fuel
    else k t bu u

def loopUArgs (ui : Expr) (k : Expr → Array Expr → M α) : M α := do
  loop (← whnf (← inferType ui)) #[] (← readThe Context).fuel.inductiveFuel
where
  loop uiTy xs
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := uiTy then
      withLocalDecl name bi dom.consumeTypeAnnotationsVerified fun arg => do
      loop (← whnf <| body.instantiate1 arg) (xs.push arg) fuel
    else
      k uiTy xs

variable (stats : InductiveStats) (u : Array Expr) (recInfos : Array RecInfo) in
def loopU (i : Nat) (v : Array Expr) (k : Array Expr → M α) : M α := do
  if _h : i < u.size then
    let ui := u[i]
    let viTy ← loopUArgs ui fun uiTy xs => do
      let some itIdx := isValidIndApp? stats uiTy
        | throw (.other
          "recursive constructor field lost its inductive result type")
      let itIndices := uiTy.getAppArgs[stats.params.size:]
      return (← getLCtx).mkForall xs <|
        .app (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN ui xs)
    let vName := ((← getLCtx).get! ui.fvarId!).userName.appendAfter "_ih"
    withLocalDecl vName .default viTy.consumeTypeAnnotationsVerified fun vi => do
    loopU (i + 1) (v.push vi) k
  else
    k v
termination_by u.size - i

variable (stats : InductiveStats) (u : Array Expr) (recInfos : Array RecInfo) in
def loopUBlueprints (i : Nat) (v : Array Expr)
    (calls : Array RecCallBlueprint)
    (k : Array Expr → Array RecCallBlueprint → M α) : M α := do
  if _h : i < u.size then
    let ui := u[i]
    let (viTy, call) ← loopUArgs ui fun uiTy xs => do
      let some itIdx := isValidIndApp? stats uiTy
        | throw (.other
          "recursive constructor field lost its inductive result type")
      let itIndices := uiTy.getAppArgs[stats.params.size:]
      let lctx ← getLCtx
      let viTy := lctx.mkForall xs <|
        .app (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN ui xs)
      return (viTy, ({
        major := ui
        args := xs
        lctx := lctx
        targetTypeIdx := itIdx
        targetIndices := itIndices
        template := lctx.mkLambda xs <|
          (mkAppN (.bvar 0) itIndices).app (mkAppN ui xs) } :
            RecCallBlueprint))
    let vName := ((← getLCtx).get! ui.fvarId!).userName.appendAfter "_ih"
    withLocalDecl vName .default viTy.consumeTypeAnnotationsVerified fun vi => do
    loopUBlueprints (i + 1) (v.push vi)
      (calls.push call) k
  else
    k v calls
termination_by u.size - i

variable (stats : InductiveStats) (indTypeName : Name) (dIdx : Nat) in
def loopCtors (recInfos : Array RecInfo)
    (ctors : List Constructor) (k : Array RecInfo → M α) : M α := match ctors with
  | ctor::ctors =>
    loopCtorArgs stats ctor.type fun t bu u => do
    let (itIdx, itIndices) := getIIndices stats t
    let introApp := mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) bu
    let motiveApp := Expr.app (mkAppN recInfos[itIdx]!.motive itIndices) introApp
    loopUBlueprints stats u recInfos 0 #[] #[] fun v calls => do
    let lctx ← getLCtx
    let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    withLocalDecl minorName .default minorTy.consumeTypeAnnotationsVerified fun minor => do
    let blueprint : RecRuleBlueprint := {
      ctor := ctor.name
      fields := bu
      lctx := lctx
      recursiveCalls := calls
      targetTypeIdx := itIdx
      targetIndices := itIndices
      minor := minor }
    let recInfos := recInfos.modify dIdx fun s => {
      s with
      minors := s.minors.push minor
      ruleBlueprints := s.ruleBlueprints.push blueprint }
    loopCtors recInfos ctors k
  | [] => k recInfos

variable (stats : InductiveStats) (indTypes : Array InductiveType) in
def loopInd2 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let indType := indTypes[dIdx]
    let indTypeName := indType.name
    loopCtors stats indTypeName dIdx recInfos indType.ctors fun recInfos =>
    loopInd2 (dIdx + 1) recInfos k
  else
    k recInfos
termination_by indTypes.size - dIdx

end mkRecInfos

def mkRecInfos (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Array RecInfo → M α) : M α :=
  mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[] fun recInfos =>
  mkRecInfos.loopInd2 stats indTypes 0 recInfos k

def getRecLevels (elimLevel : Level) (levels : List Level) : List Level :=
  if elimLevel.isParam then elimLevel :: levels else levels

def getRecLevelParams (elimLevel : Level) (lparams : List Name) : List Name :=
  if let .param u := elimLevel then u :: lparams else lparams

namespace mkRecRules

def loopU (indTypes : Array InductiveType) (stats : InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) (u : Array Expr)
    (i : Nat) (v : Array Expr) (k : Array Expr → M α) : M α := do
  if _h : i < u.size then
    let ui := u[i]
    let val ← mkRecInfos.loopUArgs ui fun uiTy xs => do
      let some itIdx := isValidIndApp? stats uiTy
        | throw (.other
          "recursive constructor field lost its inductive result type")
      let itIndices := uiTy.getAppArgs[stats.params.size:]
      let val := .const (mkRecName indTypes[itIdx]!.name) lvls
      let val := mkAppN (mkAppN (mkAppN val stats.params) motives) minors
      let lctx ← getLCtx
      return (lctx.mkLambda xs <|
        (mkAppN (.bvar 0) itIndices).app (mkAppN ui xs)).instantiate1
          val
    loopU indTypes stats motives minors lvls u (i + 1) (v.push val) k
  else
    k v
termination_by u.size - i

end mkRecRules

namespace mkRecRules

def loopCtors (indTypes : Array InductiveType) (stats : InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (ctors : List Constructor) (rules : Array RecursorRule) :
    StateT Nat M (List RecursorRule)
  | minorIdx => match ctors with
  | [] => pure (rules.toList, minorIdx)
  | ctor :: ctors => do
    let (rule, nextMinorIdx) ←
      (fun minorIdx => mkRecInfos.loopCtorArgs stats ctor.type fun _ bu u =>
      mkRecRules.loopU indTypes stats motives minors lvls u 0 #[] fun v => do
      let lctx ← getLCtx
      let rule := {
        ctor := ctor.name
        nfields := bu.size
        rhs := lctx.mkLambda stats.params <| lctx.mkLambda motives <|
          lctx.mkLambda minors <| lctx.mkLambda bu <|
          mkAppN (mkAppN minors[minorIdx]! bu) v
      }
      return (rule, minorIdx + 1)) minorIdx
    loopCtors indTypes stats motives minors lvls ctors (rules.push rule)
      nextMinorIdx

end mkRecRules

def mkRecRules (indTypes : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (dIdx : Nat) (motives : Array Expr) (minors : Array Expr) :
    StateT Nat M (List RecursorRule) :=
  mkRecRules.loopCtors indTypes stats motives minors
    (getRecLevels elimLevel stats.levels) indTypes[dIdx]!.ctors #[]

def RecCallBlueprint.build (blueprint : RecCallBlueprint)
    (indTypes : Array InductiveType) (stats : InductiveStats)
    (motives minors : Array Expr) (lvls : List Level) : Expr :=
  let value := .const (mkRecName indTypes[blueprint.targetTypeIdx]!.name) lvls
  let value := mkAppN (mkAppN (mkAppN value stats.params) motives) minors
  blueprint.template.instantiate1 value

def RecRuleBlueprint.build (blueprint : RecRuleBlueprint)
    (indTypes : Array InductiveType) (stats : InductiveStats)
    (motives minors : Array Expr) (lvls : List Level)
    (outerLCtx : LocalContext) : RecursorRule :=
  let recursiveValues := blueprint.recursiveCalls.map fun call =>
    call.build indTypes stats motives minors lvls
  {
    ctor := blueprint.ctor
    nfields := blueprint.fields.size
    rhs := outerLCtx.mkLambda stats.params <| outerLCtx.mkLambda motives <|
      outerLCtx.mkLambda minors <| blueprint.lctx.mkLambda blueprint.fields <|
      mkAppN (mkAppN blueprint.minor blueprint.fields) recursiveValues
  }

/-- Build recursor rules from the exact first-pass field and higher-order
recursive-call choices retained by `mkRecInfos`.  This deliberately performs
no second constructor traversal, classification, inference, or WHNF. -/
def mkRecRulesFromBlueprints (indTypes : Array InductiveType)
    (elimLevel : Level) (stats : InductiveStats) (recInfos : Array RecInfo)
    (dIdx : Nat) (motives minors : Array Expr) : M (List RecursorRule) := do
  let lctx ← getLCtx
  let lvls := getRecLevels elimLevel stats.levels
  return recInfos[dIdx]!.ruleBlueprints.toList.map fun blueprint =>
    blueprint.build indTypes stats motives minors lvls lctx

namespace declareRecursors

def recursorType (stats : InductiveStats)
    (recInfos : Array RecInfo) (lctx : LocalContext) (dIdx : Nat) : Expr :=
  lctx.mkForall stats.params <|
  lctx.mkForall (recInfos.map (·.motive)) <|
  lctx.mkForall (recInfos.flatMap (·.minors)) <|
  lctx.mkForall recInfos[dIdx]!.indices <|
  lctx.mkForall #[recInfos[dIdx]!.major] <|
  .app (mkAppN recInfos[dIdx]!.motive recInfos[dIdx]!.indices)
    recInfos[dIdx]!.major

def recursorInfo (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (numMinors numMotives : Nat)
    (all : List Name) (lctx : LocalContext) (k isUnsafe : Bool)
    (lparams : List Name) (dIdx : Nat)
    (rules : List RecursorRule) : RecursorVal where
  levelParams := getRecLevelParams elimLevel lparams
  type := (recursorType stats recInfos lctx dIdx).inferImplicit 1000 false
  numParams := stats.params.size
  numIndices := stats.nindices[dIdx]!
  name := mkRecName indTypes[dIdx]!.name
  all := all
  numMotives := numMotives
  numMinors := numMinors
  rules := rules
  k := k
  isUnsafe := isUnsafe

/-- Independently validate the fully closed generated recursor type before
installing its kernel metadata. The recursor may carry one fresh eliminator
universe, so this deliberately uses `info.levelParams` and an empty local
context rather than the surrounding declaration context. -/
def checkRecursorType (info : RecursorVal) : M Expr := fun c => do
  c.env.checkNoMVarNoFVar info.name info.type
  TypeChecker.M.run c.env c.safety {} info.levelParams c.fuel do
    let type ← TypeChecker.checkType info.type
    _ ← TypeChecker.ensureSort type info.type
    return type

def checkRecursorTypes (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (numMinors numMotives : Nat)
    (all : List Name) (lctx : LocalContext) (k isUnsafe : Bool)
    (lparams : List Name) (dIdx : Nat) : M Unit := do
  if h : dIdx < indTypes.size then
    let info := recursorInfo stats indTypes elimLevel recInfos numMinors
      numMotives all lctx k isUnsafe lparams dIdx []
    _ ← checkRecursorType info
    checkRecursorTypes stats indTypes elimLevel recInfos numMinors numMotives
      all lctx k isUnsafe lparams (dIdx + 1)
termination_by indTypes.size - dIdx

def loop (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (recInfos : Array RecInfo)
    (motives minors : Array Expr) (numMinors numMotives : Nat)
    (all : List Name) (lctx : LocalContext) (k isUnsafe : Bool)
    (lparams : List Name) (allowPrimitive : Bool)
    (dIdx : Nat) (env : Environment) : StateT Nat M Environment := do
  if h : dIdx < indTypes.size then
    let rules ← mkRecRulesFromBlueprints indTypes elimLevel stats recInfos
      dIdx motives minors
    modify (· + indTypes[dIdx]!.ctors.length)
    let info := recursorInfo stats indTypes elimLevel recInfos numMinors
      numMotives all lctx k isUnsafe lparams dIdx rules
    let name := info.name
    env.checkName name allowPrimitive
    let env := addConstant env (.recInfo info)
    loop stats indTypes elimLevel recInfos motives minors numMinors
      numMotives all lctx k isUnsafe lparams allowPrimitive (dIdx + 1) env
  else
    pure env
termination_by indTypes.size - dIdx

end declareRecursors

def declareRecursors (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (k : Bool)
    (declarationLParams : List Name) : M Environment := do
  let motives := recInfos.map (·.motive)
  let minors := recInfos.flatMap (·.minors)
  let numMinors := minors.size
  let numMotives := motives.size
  let all := indTypes.map (·.name) |>.toList
  let lctx ← getLCtx
  let {safety, ..} ← read
  let isUnsafe := safety != .safe
  AddInductive.declareRecursors.checkRecursorTypes stats indTypes elimLevel
    recInfos numMinors numMotives all lctx k isUnsafe declarationLParams 0
  StateT.run' (s := 0) do
  let env ← getEnv
  let {allowPrimitive, ..} ← read
  declareRecursors.loop stats indTypes elimLevel recInfos motives minors
    numMinors numMotives all lctx k isUnsafe declarationLParams
      allowPrimitive 0 env

def runWithStats (stats : InductiveStats) (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat)
    (isUnsafe : Bool) : M Environment := do
  let ctorEnv ←
    declareInductiveTypes stats nparams indTypes numNested isUnsafe >>= fun headerEnv =>
      withEnv headerEnv do
        checkConstructors indTypes stats isUnsafe
        declareConstructors stats indTypes isUnsafe
  fun c =>
    (getElimLevel stats indTypes >>= fun elimLevel =>
      withTypeCheckerLParams (getRecLevelParams elimLevel c.lparams) do
        let k ← isKTarget stats indTypes
        mkRecInfos stats indTypes elimLevel fun recInfos =>
          declareRecursors stats indTypes elimLevel recInfos k c.lparams)
      { c with env := ctorEnv }

def run (nparams : Nat) (types : List InductiveType) (numNested : Nat) :
    M Environment := fun c => do
  let isUnsafe := c.safety != .safe
  let indTypes := types.toArray
  Environment.checkDuplicatedUnivParams c.lparams
  checkInductiveTypes nparams indTypes (fun stats =>
    runWithStats stats nparams indTypes numNested isUnsafe) c

end AddInductive

namespace ElimNestedInductive

structure Result where
  ngen : NameGenerator
  nparams : Nat
  lctx : LocalContext
  params : Array Expr -- the fvars declared in `lctx`
  aux2nested : NameMap Expr -- exprs are open over `params`, like the C++ `m_aux2nested`
  types : List InductiveType

instance [MonadStateOf NameGenerator m] : MonadNameGenerator m where
  getNGen := get
  setNGen := set

namespace Result

def getNestedIfAuxCtor (r : Result) (env' : Environment) (c : Name) : Option (Expr × Name) := do
  let .ctorInfo { induct, .. } ← env'.find? c | none
  return (← r.aux2nested.find? induct, induct)

def restoreCtorName (r : Result) (env' : Environment) (c : Name) : Name := Id.run do
  let (e, name) := (r.getNestedIfAuxCtor env' c).get!
  let .const I _ := e.getAppFn | unreachable!
  c.replacePrefix name I

def restoreNestedNode (r : Result) (env' : Environment) (As : Array Expr)
    (auxRec : NameMap Name) (t : Expr) : Option Expr := do
  if let .const c ls := t then
    if let some recName := auxRec.find? c then
      return .const recName ls
  let .const c _ := t.getAppFn | none
  if let some nested := r.aux2nested.find? c then
    let args := t.getAppArgs
    assert! args.size ≥ r.nparams
    return mkAppRange ((nested.abstract r.params).instantiateRev As)
      r.nparams args.size args
  let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
  let args := t.getAppArgs
  assert! args.size ≥ r.nparams
  let nested' := (nested.abstract r.params).instantiateRev As
  nested'.withApp fun I I_args => do
  let .const I_c I_ls := I | unreachable!
  let c' := .const (c.replacePrefix auxI_name I_c) I_ls
  return mkAppRange (mkAppN c' I_args) r.nparams args.size args

def openRestoreParams : Nat → LocalContext → Array Expr → Expr →
    StateM NameGenerator (LocalContext × Array Expr × Expr)
  | 0, lctx, As, e => pure (lctx, As, e)
  | n + 1, lctx, As, e => do
    let (name, dom, body, bi) := match e with
      | .forallE name dom body bi | .lam name dom body bi =>
        (name, dom, body, bi)
      | _ => unreachable!
    let id := ⟨← mkFreshId⟩
    let lctx := lctx.mkLocalDecl id name dom bi
    let arg := .fvar id
    openRestoreParams n lctx (As.push arg) (body.instantiate1 arg)

def restoreNested (r : Result) (env' : Environment) (e : Expr)
    (auxRec : NameMap Name := {}) : Expr :=
  let pi := e.isForall
  let ((lctx, As, e), _) := openRestoreParams r.nparams {} #[] e
    { namePrefix := `_nested_fresh }
  let e := e.replace (r.restoreNestedNode env' As auxRec)
  if pi then lctx.mkForall As e else lctx.mkLambda As e

def restoreRule (r : Result) (env' : Environment) (auxRec : NameMap Name)
    (oldRecName newRecName : Name) (rule : RecursorRule) : RecursorRule :=
  { rule with
    ctor := if newRecName == oldRecName then rule.ctor
      else r.restoreCtorName env' rule.ctor
    rhs := r.restoreNested env' rule.rhs auxRec }

def restoreRecursor (r : Result) (env' : Environment)
    (auxRec : NameMap Name) (allIndNames : List Name)
    (oldRecName newRecName : Name) (recInfo : RecursorVal) : RecursorVal :=
  { recInfo with
    name := newRecName
    type := r.restoreNested env' recInfo.type auxRec
    all := allIndNames
    rules := recInfo.rules.map
      (r.restoreRule env' auxRec oldRecName newRecName) }

end Result

structure State where
  ngen : NameGenerator := { namePrefix := `_nested_fresh }
  nestedAux : Array (Expr × Name) := {}
  lvls : List Level
  newTypes : Array InductiveType
  nextIdx : Nat := 1
  deriving Inhabited

abbrev M := ReaderT Environment <| StateT State <| Except Exception

instance : MonadNameGenerator M where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

def findUniqueName (env : Environment) (n : Name) (i : Nat) :
    Nat → Except Exception (Name × Nat)
  | 0 => throw <| .other "failed to select a fresh nested-inductive name"
  | fuel + 1 =>
    let r := Name.mkNum n i
    if env.contains r then
      findUniqueName env n (i + 1) fuel
    else
      pure (r, i + 1)

def mkUniqueName (n : Name) : M Name := fun env state => do
  let (name, nextIdx) ←
    findUniqueName env n state.nextIdx (env.constants.toList.length + 1)
  return (name, { state with nextIdx })

def illFormed : Exception :=
  .other "invalid nested inductive datatype, ill-formed declaration"

def replaceParamsCore (params : Array Expr) (e : Expr) (As : Array Expr) :
    Except Exception Expr := do
  assert! As.size == params.size
  return (e.abstract As).instantiateRev params

def replaceParams (params : Array Expr) (e : Expr) (As : Array Expr) : M Expr :=
  fun _ state => (fun result => (result, state)) <$> replaceParamsCore params e As

/-- IF `e` is of the form `I Ds is` where
  1) `I` is a nested inductive datatype (i.e., a previously declared inductive datatype),
  2) the parametric arguments `Ds` do not contain loose bound variables, and do contain inductive datatypes in `m_new_types`
THEN return the `inductive_val` in the `constant_info` associated with `I`.
Otherwise, return none. -/
def mentionsNestedNewType (newTypes : Array InductiveType) (e : Expr) : Bool :=
  e.findAny fun
    | .const t _ => newTypes.any fun ty => t == ty.name
    | _ => false

def nestedParamFlags (newTypes : Array InductiveType) (args : Array Expr) :
    Nat → Bool × Bool
  | 0 => (false, false)
  | n + 1 =>
    let flags := nestedParamFlags newTypes args n
    (flags.1 || mentionsNestedNewType newTypes args[n]!,
      flags.2 || args[n]!.hasLooseBVars)

def isNestedInductiveAppConst? (e : Expr) (fn : Name) : M (Option InductiveVal) :=
    fun env state => do
  let some (.inductInfo ci) := env.find? fn | return (none, state)
  let args := e.getAppArgs
  if ci.numParams > args.size then return (none, state)
  let flags := nestedParamFlags state.newTypes args ci.numParams
  if !flags.1 then return (none, state)
  if flags.2 then
    throw <| .other s!"invalid nested inductive datatype '{fn}', \
      nested inductive datatypes parameters cannot contain local variables."
  return (some ci, state)

def isNestedInductiveApp? (e : Expr) : M (Option InductiveVal) := do
  if !e.isApp then return none
  let .const fn _ := e.getAppFn | return none
  isNestedInductiveAppConst? e fn

def instantiateForallParams (e : Expr) (hi : Nat) (params : Array Expr) :
    Except Exception Expr := do
  let mut e := e
  for _ in [:hi] do
    let .forallE _ _ body _ := e | throw illFormed
    e := body
  return e.instantiateRevRange 0 hi params

def findCachedAux? (nestedAux : Array (Expr × Name)) (nested : Expr) :
    Option Name :=
  nestedAux.findSome? fun (e, n) =>
    if e == nested then some n else none

structure AuxiliaryData where
  nested : Expr
  type : InductiveType

def buildAuxiliary (env : Environment) (lctx : LocalContext)
    (params As : Array Expr) (I_lvls : List Level) (I_nparams : Nat)
    (args : Array Expr) (J_name auxJ_name : Name) : Except Exception AuxiliaryData := do
  let info ← env.get J_name
  let J_info := match info with
    | .inductInfo J_info => J_info
    | _ => unreachable!
  let J := .const J_name I_lvls
  let JAs := mkAppRange J 0 I_nparams args
  let auxJ_type := J_info.type.instantiateLevelParams J_info.levelParams I_lvls
  let auxJ_type := lctx.mkForall As <|
    ← instantiateForallParams auxJ_type I_nparams args
  let JAs' ← replaceParamsCore params JAs As
  let auxJ_ctors ← J_info.ctors.mapM fun J_ctor_name => do
    let J_ctor_info ← env.get J_ctor_name
    -- auxJ_cnstr_type still has references to `J`, this will be fixed later when we process it.
    let auxJ_ctor_name := J_ctor_name.replacePrefix J_name auxJ_name
    let auxJ_ctor_type := J_ctor_info.type.instantiateLevelParams
      J_ctor_info.levelParams I_lvls
    let auxJ_ctor_type ← instantiateForallParams auxJ_ctor_type I_nparams args
    return { name := auxJ_ctor_name, type := lctx.mkForall As auxJ_ctor_type }
  return {
    nested := JAs'
    type := { name := auxJ_name, type := auxJ_type, ctors := auxJ_ctors } }

def generateAuxiliary (lctx : LocalContext) (params As : Array Expr)
    (I_name : Name) (I_lvls : List Level) (I_nparams : Nat)
    (args : Array Expr) (J_name : Name) : M (Option Expr) := do
  let env ← read
  let auxJ_name ← mkUniqueName `_nested
  let data ← buildAuxiliary env lctx params As I_lvls I_nparams args J_name auxJ_name
  modify fun st => { st with nestedAux := st.nestedAux.push (data.nested, auxJ_name) }
  let result ← if J_name == I_name then
    pure <| some <| mkAppRange
      (mkAppN (.const auxJ_name (← get).lvls) As) I_nparams args.size args
  else
    pure none
  modify fun st => { st with newTypes := st.newTypes.push data.type }
  return result

def generateAuxiliaries (lctx : LocalContext) (params As : Array Expr)
    (I_name : Name) (I_lvls : List Level) (I_nparams : Nat)
    (args : Array Expr) (I_val : InductiveVal) : M (Option Expr) :=
  loop none I_val.all
where
  loop (result : Option Expr) : List Name → M (Option Expr)
    | [] => do
      assert! result.isSome
      return result
    | J_name :: names => do
      let found ← generateAuxiliary lctx params As I_name I_lvls I_nparams args J_name
      loop (found.or result) names

def replaceRecognizedNested (lctx : LocalContext) (params As : Array Expr)
    (fn : Expr) (args : Array Expr) (I_val : InductiveVal) : M (Option Expr) := do
  let .const I_name I_lvls := fn | unreachable!
  let I_nparams := I_val.numParams
  assert! I_nparams ≤ args.size
  let IAs := mkAppRange fn 0 I_nparams args -- `I As`
  let Iparams ← replaceParams params IAs As
  let st ← get
  if let some auxI_name := findCachedAux? st.nestedAux Iparams then
    return mkAppRange (mkAppN (.const auxI_name st.lvls) As) I_nparams args.size args
  generateAuxiliaries lctx params As I_name I_lvls I_nparams args I_val

/-- If `e` is a nested occurrence `I Ds is`, return `Iaux As is` -/
def replaceIfNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M (Option Expr) := do
  let some I_val ← isNestedInductiveApp? e | return none
  e.withApp fun fn args =>
    replaceRecognizedNested lctx params As fn args I_val

def replaceAllNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M Expr := e.replaceM (replaceIfNested lctx params As)

def withParams (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr → M α) : M α := loop {} type #[] nparams where
  loop lctx type params
  | 0 => k lctx type params
  | i+1 => do
    let .forallE name dom body bi := type
      | throw <| .other "invalid inductive datatype declaration, incorrect number of parameters"
    let id := ⟨← mkFreshId⟩
    let lctx := lctx.mkLocalDecl id name dom bi
    let arg := .fvar id
    loop lctx (body.instantiate1 arg) (params.push arg) i

def lowerConstructor (params : Array Expr) (nparams : Nat)
    (ctor : Constructor) : M Constructor := do
  withParams ctor.type nparams fun lctx ctorType As => do
  assert! As.size == nparams
  return { ctor with
    type := lctx.mkForall As (← replaceAllNested lctx params As ctorType) }

def lowerInductive (params : Array Expr) (nparams : Nat)
    (indType : InductiveType) : M InductiveType := do
  let ctors ← indType.ctors.mapM (lowerConstructor params nparams)
  return { indType with ctors }

def lowerNext (params : Array Expr) (nparams i : Nat) :
    M (Option InductiveType) := do
  let s ← get
  if _h : i < s.newTypes.size then
    let source := s.newTypes[i]
    let target ← lowerInductive params nparams source
    modify fun s => { s with newTypes := s.newTypes.set! i target }
    return some source
  else
    return none

def run (fuel nparams : Nat) (types : List InductiveType) : M Result := do
  let I :: _ := types
    | throw <| .other s!"invalid empty (mutual) inductive datatype declaration, \
        it must contain at least one inductive type."
  withParams I.type nparams fun lctx _ params => do
  let rec loop i
  | 0 => throw <| .other "deep recursion: ElimNestedInductive.run.loop"
  | fuel+1 => do
    match ← lowerNext params nparams i with
    | some _ => loop (i+1) fuel
    | none =>
      let s ← get
      let aux2nested := s.nestedAux.foldl (fun m (e, n) => m.insert n e) {}
      return { s with nparams := params.size, lctx, params, aux2nested, types := s.newTypes.toList }
  loop 0 fuel
end ElimNestedInductive

def mkAuxRecNameMap (env' : Environment) (types : List InductiveType) :
    List Name × NameMap Name := Id.run do
  let mainType :: _ := types | unreachable!
  let ntypes := types.length
  let mainName := mainType.name
  let some (.inductInfo mainInfo) := env'.find? mainName | unreachable!
  let allNames := mainInfo.all
  assert! allNames.length > ntypes
  let mut oldRecNames := #[]
  let mut recMap : NameMap Name := {}
  let mut nextIdx := 1
  for indName in allNames.drop ntypes do
    let oldRecName := mkRecName indName
    let newRecName := (mkRecName mainName).appendIndexAfter nextIdx
    nextIdx := nextIdx + 1
    recMap := recMap.insert oldRecName newRecName
    oldRecNames := oldRecNames.push oldRecName
  return (oldRecNames.toList, recMap)

def checkNoNestedAux (n : Name) (e : Expr) : Except Exception Unit := do
  if e.findAny fun
      | .const c _ => (`_nested).isPrefixOf c
      | .proj s _ _ => (`_nested).isPrefixOf s
      | _ => false then
    throw <| .other s!"invalid declaration '{n}', it uses the reserved prefix '_nested'"

def checkConstructorSources (env : Environment) :
    List Constructor → Except Exception Unit
  | [] => pure ()
  | ctor :: ctors => do
    env.checkNoMVarNoFVar ctor.name ctor.type
    checkNoNestedAux ctor.name ctor.type
    checkConstructorSources env ctors

def checkInductiveSources (env : Environment) :
    List InductiveType → Except Exception Unit
  | [] => pure ()
  | indType :: types => do
    env.checkNoMVarNoFVar indType.name indType.type
    checkConstructorSources env indType.ctors
    checkInductiveSources env types

/-- Restore and install one recursor emitted for the lowered nested block. -/
def restoreRecursorDecl (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (recNameMap : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool) (recName : Name) :
    StateT Environment (Except Exception) Unit := fun sourceEnv =>
  let newRecName := recNameMap.getD recName recName
  match loweredEnv.find? recName with
  | some (.recInfo recInfo) => do
    sourceEnv.checkName newRecName allowPrimitive
    return ((), sourceEnv.add <| .recInfo <|
      res.restoreRecursor loweredEnv recNameMap allIndNames recName newRecName
        recInfo)
  | _ => .error <| .other s!"missing lowered recursor '{recName}'"

/-- Restore and install one constructor emitted for the lowered nested block. -/
def restoreConstructorDecl (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (allowPrimitive : Bool) (ctorName : Name) :
    StateT Environment (Except Exception) Unit := fun sourceEnv =>
  match loweredEnv.find? ctorName with
  | some (.ctorInfo ctor) => do
    let newType := res.restoreNested loweredEnv ctor.type
    sourceEnv.checkName ctor.name allowPrimitive
    return ((), sourceEnv.add <| .ctorInfo { ctor with type := newType })
  | _ => .error <| .other s!"missing lowered constructor '{ctorName}'"

/-- Restore and install one source inductive header by replacing the lowered
mutual-family metadata with the source family names. -/
def restoreInductiveHeaderDecl (loweredEnv : Environment)
    (allIndNames : List Name) (allowPrimitive : Bool) (indName : Name) :
    StateT Environment (Except Exception) Unit := fun sourceEnv =>
  match loweredEnv.find? indName with
  | some (.inductInfo ind) => do
    sourceEnv.checkName ind.name allowPrimitive
    return ((), sourceEnv.add <| .inductInfo { ind with all := allIndNames })
  | _ => .error <| .other s!"missing lowered inductive '{indName}'"

/-- Restore and install one source inductive family member, its constructors,
and its primary recursor. -/
def restoreInductiveDecl (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (recNameMap : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (indType : InductiveType) :
    StateT Environment (Except Exception) Unit := do
  let some (.inductInfo ind) := loweredEnv.find? indType.name | unreachable!
  restoreInductiveHeaderDecl loweredEnv allIndNames allowPrimitive indType.name
  ind.ctors.forM fun ctorName =>
    restoreConstructorDecl res loweredEnv allowPrimitive ctorName
  restoreRecursorDecl res loweredEnv recNameMap allIndNames allowPrimitive
    (mkRecName indType.name)

/-- Restore only the source family headers and constructors.  This side
environment is used to validate original constructor parameters at the exact
post-constructor boundary, before restored recursors can become dependencies. -/
def restoreInductiveConstructors (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (indType : InductiveType) :
    StateT Environment (Except Exception) Unit := do
  let some (.inductInfo ind) := loweredEnv.find? indType.name | unreachable!
  restoreInductiveHeaderDecl loweredEnv allIndNames allowPrimitive indType.name
  ind.ctors.forM fun ctorName =>
    restoreConstructorDecl res loweredEnv allowPrimitive ctorName

/-- Restore the constructors of one source family after every mutual header
has already been installed in the side validation environment. -/
def restoreInductiveConstructorsOnly (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (allowPrimitive : Bool)
    (indType : InductiveType) :
    StateT Environment (Except Exception) Unit := do
  let some (.inductInfo ind) := loweredEnv.find? indType.name | unreachable!
  ind.ctors.forM fun ctorName =>
    restoreConstructorDecl res loweredEnv allowPrimitive ctorName

/-- Restore the source header/constructor prefix without installing any
recursors.  The ordinary returned restoration still uses
`restoreNestedDeclarations`; this is a proof-oriented validation boundary. -/
def restoreNestedConstructors (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (allIndNames : List Name)
    (allowPrimitive : Bool) (types : List InductiveType) :
    StateT Environment (Except Exception) Unit := do
  -- Constructors of one mutual family may mention a later sibling, so the
  -- validation environment uses the canonical dependency order.
  types.forM fun indType =>
    restoreInductiveHeaderDecl loweredEnv allIndNames allowPrimitive
      indType.name
  types.forM fun indType =>
    restoreInductiveConstructorsOnly res loweredEnv allowPrimitive indType

/-- The complete declaration-restoration loop for a lowered nested block.
Kept separate from `Environment.addInductive` so its state transition can be
verified compositionally. -/
def restoreNestedDeclarations (res : ElimNestedInductive.Result)
    (loweredEnv : Environment) (recNameMap : NameMap Name)
    (allIndNames : List Name) (allowPrimitive : Bool)
    (types : List InductiveType) (auxRecNames : List Name) :
    StateT Environment (Except Exception) Unit := do
  types.forM fun indType =>
    restoreInductiveDecl res loweredEnv recNameMap allIndNames
      allowPrimitive indType
  auxRecNames.forM fun recName =>
    restoreRecursorDecl res loweredEnv recNameMap allIndNames
      allowPrimitive recName

namespace validateRestoredConstructorParameters

/-- Recheck exactly the common-parameter prefix of one original constructor
against the parameter free variables retained by nested lowering.  This pass
deliberately stops before constructor fields: those may contain the nested
occurrences handled by lowering and must not be sent back through the ordinary
positivity checker. -/
def loop (env : Environment) (lparams : List Name)
    (safety : DefinitionSafety) (typeCheckerFuel : FuelConfig)
    (fullLCtx currentLCtx : LocalContext) (ctorName : Name)
    (params : Array Expr) (type : Expr)
    (i fuel : Nat) : Except Exception Unit :=
  match fuel with
  | 0 => throw .deepRecursion
  | fuel + 1 => do
    if hi : i < params.size then
      let .forallE _ dom body _ := type
        | throw <| .other s!"number of parameters mismatch in constructor '{ctorName}'"
      let .cdecl _ fv paramName paramType bi kind :=
          fullLCtx.get! params[i].fvarId!
        | throw <| .other s!"invalid retained parameter context for '{ctorName}'"
      unless ← TypeChecker.M.run env (safety := safety)
          (lctx := currentLCtx) (lparams := lparams)
          (fuel := typeCheckerFuel) (TypeChecker.isDefEq dom paramType) do
        throw <| .other
          s!"arg #{i + 1} of '{ctorName}' does not match inductive datatype parameters"
      loop env lparams safety typeCheckerFuel fullLCtx
        (currentLCtx.mkLocalDecl fv paramName paramType bi kind)
        ctorName params (body.instantiate1 params[i]) (i + 1) fuel
    else
      pure ()

/-- Recheck every original constructor type and its common-parameter prefix
in the source-shaped restored environment.  The local context and parameter
free variables are exact producer data retained by nested lowering, so this
does not reconstruct them in an environment already containing the restored
declarations.

This is an intentionally conservative post-restoration validation pass: it
can reject through the type-checker's ordinary recursion fuel in addition to
the lowering/production checks that have already succeeded. -/
def run (env : Environment) (lparams : List Name) (safety : DefinitionSafety)
    (fuel : FuelConfig) (types : List InductiveType)
    (res : ElimNestedInductive.Result) : Except Exception Unit := do
  types.forM fun type =>
    type.ctors.forM fun ctor => do
      _ ← TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := lparams) (fuel := fuel)
        (TypeChecker.checkType ctor.type)
      loop env lparams safety fuel res.lctx {} ctor.name res.params
        ctor.type 0 fuel.inductiveFuel

end validateRestoredConstructorParameters

/-- Validate every generated auxiliary witness in the restored local
parameter context. -/
def validateNestedAuxiliaries (env : Environment) (lparams : List Name)
    (safety : DefinitionSafety) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) : Except Exception Unit :=
  TypeChecker.M.run env (safety := safety) (lctx := res.lctx)
      (lparams := lparams) (fuel := fuel) do
    res.aux2nested.forM fun _ e => do
      let type ← TypeChecker.checkType e
      _ ← TypeChecker.ensureSort type e

/-- Restore a successfully installed lowered block and validate the generated
auxiliary witnesses before returning the source-shaped environment. -/
def Environment.restoreNestedAfterInstall (env loweredEnv : Environment)
    (lparams : List Name) (types : List InductiveType)
    (safety : DefinitionSafety) (allowPrimitive : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) : Except Exception Environment := do
  let allIndNames := types.map (·.name)
  let (recNames', recNameMap') := mkAuxRecNameMap loweredEnv types
  let restoredEnv ← (·.2) <$> StateT.run (s := env)
    (restoreNestedDeclarations res loweredEnv recNameMap' allIndNames
      allowPrimitive types recNames')
  let validationEnv ← (·.2) <$> StateT.run (s := env)
    (restoreNestedConstructors res loweredEnv allIndNames allowPrimitive types)
  validateRestoredConstructorParameters.run validationEnv lparams safety
    fuel types res
  validateNestedAuxiliaries restoredEnv lparams safety fuel res
  return restoredEnv

/-- Complete production pipeline after nested lowering has produced its
result: install the lowered block, then either return it directly or restore
the source declarations and validate every generated auxiliary witness. -/
def Environment.addInductiveAfterLowering (env : Environment)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (res : ElimNestedInductive.Result) : Except Exception Environment := do
  let numNested := res.aux2nested.size
  let safety := if isUnsafe then .unsafe else .safe
  let env' ← AddInductive.run nparams res.types numNested
    { env, allowPrimitive, lparams, fuel, safety }
  if numNested = 0 then return env'
  Environment.restoreNestedAfterInstall env env' lparams types safety
    allowPrimitive fuel res

def Environment.addInductive (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  checkInductiveSources env types
  let res ← ElimNestedInductive.run fuel.inductiveFuel nparams types env
    |>.run' { lvls := lparams.map .param, newTypes := types.toArray }
  Environment.addInductiveAfterLowering env lparams nparams types isUnsafe
    allowPrimitive fuel res
