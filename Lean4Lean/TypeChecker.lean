import Lean4Lean.Declaration
import Lean4Lean.Level
import Lean4Lean.Quot
import Lean4Lean.Inductive.Reduce
import Lean4Lean.Instantiate
import Lean4Lean.ForEachExprV
import Lean4Lean.EquivManager
import Lean4Lean.FuelConfig

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

abbrev InferCache := ExprMap Expr

structure TypeChecker.State where
  ngen : NameGenerator := { namePrefix := `_kernel_fresh, idx := 0 }
  inferTypeI : InferCache := {}
  inferTypeC : InferCache := {}
  whnfCoreCache : ExprMap Expr := {}
  whnfCache : ExprMap Expr := {}
  eqvManager : EquivManager := {}
  failure : Std.HashSet (Expr × Expr) := {}
  unfold : ExprMap Expr := {}

structure TypeChecker.Context where
  env : Environment
  lctx : LocalContext := {}
  safety : DefinitionSafety := .safe
  eagerReduce := false
  lparams : List Name := []
  fuel : FuelConfig := {}

namespace TypeChecker

abbrev M := ReaderT Context <| StateT State <| Except Exception

def M.run (env : Environment) (safety : DefinitionSafety := .safe)
    (lctx : LocalContext := {}) (lparams : List Name := []) (fuel : FuelConfig := {})
    (x : M α) : Except Exception α :=
  x { env, safety, lctx, lparams, fuel } |>.run' {}

def M.runTermElab (m : M α) (safety := DefinitionSafety.safe) : Elab.Term.TermElabM α := do
  ofExceptKernelException <| m.run (env := (← getEnv).toKernelEnv)
    (lctx := ← getLCtx) (safety := safety) (lparams := (← get).levelNames)

instance : MonadLift M Elab.Term.TermElabM := ⟨M.runTermElab⟩

def getEnv : M Environment := return (← read).env

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

instance [Monad m] : MonadNameGenerator (StateT State m) where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

instance : MonadLocalNameGenerator M where
  withFreshId x := do x (← mkFreshId)

instance (priority := low) : MonadWithReaderOf LocalContext M where
  withReader f := withReader fun s => { s with lctx := f s.lctx }

structure Methods where
  protected isDefEqCore : Expr → Expr → M Bool
  protected whnfCore (e : Expr) (cheapProj := false) : M Expr
  protected whnf (e : Expr) : M Expr
  protected inferType (e : Expr) (inferOnly : Bool) : M Expr

abbrev RecM := ReaderT Methods M

inductive ReductionStatus where
  | continue (tn sn : Expr)
  | unknown (tn sn : Expr)
  | true
  | false (tn sn : Expr)

def ReductionStatus.bool (tn sn : Expr) : Bool → ReductionStatus
  | .true => .true
  | .false => .false tn sn

namespace Inner

/-- Reduces `e` to its weak-head normal form. -/
def whnf (e : Expr) : RecM Expr := fun m => m.whnf e

@[inline] def withLCtx [MonadWithReaderOf LocalContext m] (lctx : LocalContext) (x : m α) : m α :=
  withReader (fun _ => lctx) x

/-- Ensures that `e` is defeq to some `e' := .sort ..`, returning `e'`. If not, throws an error with
`s` (the expression required to be a sort). -/
def ensureSortCore (e s : Expr) : RecM Expr := do
  if e.isSort then return e
  let e ← whnf e
  if e.isSort then return e
  throw <| .typeExpected (← getEnv) (← getLCtx) s

/-- Ensures that `e` is defeq to some `e' := .forallE ..`, returning `e'`. If not, throws an error
with `s := f a` (the application requiring `f` to be of function type). -/
def ensureForallCore (e s : Expr) : RecM Expr := do
  if e.isForall then return e
  let e ← whnf e
  if e.isForall then return e
  throw <| .funExpected (← getEnv) (← getLCtx) s

/-- Checks that `l` does not contain any level parameters not found in the context `tc`. -/
def checkLevel (tc : Context) (l : Level) : Except Exception Unit := do
  if let some n2 := l.getUndefParam tc.lparams then
    throw <| .other s!"invalid reference to undefined universe level parameter '{n2}'"

def inferFVar (tc : Context) (name : FVarId) : Except Exception Expr := do
  if let some decl := tc.lctx.find? name then
    return decl.type
  throw <| .other "unknown free variable"

/-- Infers the type of `.const name ls`. -/
def inferConstant (tc : Context) (name : Name) (ls : List Level) (inferOnly : Bool) :
    Except Exception Expr := do
  let e := Expr.const name ls
  let info ← tc.env.get name
  let ps := info.levelParams
  if ps.length != ls.length then
    throw <| .other s!"incorrect number of universe levels parameters for '{e
      }', #{ps.length} expected, #{ls.length} provided"
  if !inferOnly then
    if info.isUnsafe && tc.safety != .unsafe then
      throw <| .other s!"invalid declaration, it uses unsafe declaration '{e}'"
    if let .defnInfo v := info then
      if v.safety == .partial && tc.safety == .safe then
        throw <| .other
          s!"invalid declaration, safe declaration must not contain partial declaration '{e}'"
    for l in ls do
      checkLevel tc l
  return info.instantiateTypeLevelParams ls

/-- Infers the type of expression `e`. If `inferOnly := false`, this function throws an error
whenever `e` is not typeable according to Lean's algorithmic typing judgment (barring resource
exhaustion: it may also throw `.deterministicTimeout` or `.deepRecursion` on a typeable term).
Setting `inferOnly := true` optimizes to avoid unnecessary checks in the case that `e` is already
known to be well-typed. -/
def inferType (e : Expr) (inferOnly := true) : RecM Expr := fun m => m.inferType e inferOnly

/-- Infers the type of lambda expression `e`. -/
def inferLambda (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] e where
  loop fvars : Expr → RecM Expr
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    if !inferOnly then
      _ ← ensureSortCore (← inferType d inferOnly) d
    withLocalDecl name bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    return (← getLCtx).mkForall fvars r

/-- Infers the type of for-all expression `e`. -/
def inferForall (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] #[] e where
  loop fvars us : Expr → RecM Expr
  | .forallE name dom body bi => do
    let d := dom.instantiateRev fvars
    let t1 ← ensureSortCore (← inferType d inferOnly) d
    let us := us.push t1.sortLevel!
    withLocalDecl name bi d fun fv =>
      loop (fvars.push fv) us body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let s ← ensureSortCore r e
    return .sort <| us.foldr mkLevelIMax' s.sortLevel!

/-- Returns whether `t` and `s` are definitionally equal according to Lean's algorithmic
definitional equality judgment.

NOTE: This function does not do any typechecking of its own on `t` and `s`. So, when this is used as
part of a typechecking routine, it is expected that they are already well-typed (that is, that
`checkType t` and `checkType s` did not/would not throw an error). This is what justifies the
internal uses of `inferType` at its default `inferOnly := true`: on a well-typed subterm the fast
path returns the same type the checking path would have. -/
def isDefEqCore (t s : Expr) : RecM Bool := fun m => m.isDefEqCore t s

@[inherit_doc isDefEqCore]
def isDefEq (t s : Expr) : RecM Bool := do
  let r ← isDefEqCore t s
  if r then
    modify fun st => { st with eqvManager := st.eqvManager.addEquiv t s }
  pure r

/-- Infers the type of application `e`, assuming that `e` is already well-typed. -/
def inferApp (e : Expr) : RecM Expr := do
  e.withApp fun f args =>
  let rec loop fType j i : RecM Expr :=
    if i < args.size then
      match fType with
      | .forallE _ _ body _ => loop body j (i+1)
      | _ => do
        let fType := fType.instantiateRevRange j i args
        let fType := (← ensureForallCore fType e).bindingBody!
        loop fType i (i+1)
    else
      return fType.instantiateRevRange j args.size args
  do loop (← inferType f) 0 0

/-- Infers the type of let-expression `e`. -/
def inferLet (e : Expr) (inferOnly : Bool) : RecM Expr := loop #[] e where
  loop fvars : Expr → RecM Expr
  | .letE name type val body _ => do
    let type := type.instantiateRev fvars
    let val := val.instantiateRev fvars
    if !inferOnly then
      _ ← ensureSortCore (← inferType type inferOnly) type
      let valType ← inferType val inferOnly
      if !(← isDefEq valType type) then
        throw <| .letTypeMismatch (← getEnv) (← getLCtx) name valType type
    withLetDecl name type val fun fv =>
      loop (fvars.push fv) body
  | e => do
    let r ← inferType (e.instantiateRev fvars) inferOnly
    let r := r.cheapBetaReduce
    return (← getLCtx).mkForall fvars r

/-- Gets the universe level of the sort that `e`'s type is defeq to, failing if `e` is not
a type. -/
def getSortLevel (e : Expr) : RecM Level := do
  let .sort u ← ensureSortCore (← inferType e) e | unreachable!
  return u

/-- Checks if `e` is a proposition, that is, if its type is a sort whose level normalizes to
zero. -/
def isProp (e : Expr) : RecM Bool := return (← getSortLevel e).isAlwaysZero

/-- The concrete syntax retained by projection inference for subsequent
canonical `.casesOn` expansion.  The raw parameter-instantiated constructor
type and declared field count determine the complete field telescope, but are
retained without traversing its suffix in the production checker. -/
structure SingletonConstructor (constructors : List Name) where
  name : Name
  exact : constructors = [name]

/-- Pure, proof-retaining form of the legacy singleton-constructor pattern.
The equality field is erased at runtime; success and failure are exactly the
same list-shape test. -/
def singletonConstructor? :
    (constructors : List Name) → Option (SingletonConstructor constructors)
  | [name] => some ⟨name, rfl⟩
  | _ => none

/-- Exact successful execution trace for the common-parameter loop.  The
proof object is erased; its indices retain every substitution performed by
the production computation. -/
inductive ProjectionParameterResult : List Expr → Expr → Type
  | nil (constructorType : Expr) :
      ProjectionParameterResult [] constructorType
  | cons (argument : Expr) (arguments : List Expr)
      (constructorType : Expr) (name : Name) (domain body : Expr)
      (info : BinderInfo)
      (tail : ProjectionParameterResult arguments
        (body.instantiate1 argument)) :
      ProjectionParameterResult (argument :: arguments) constructorType

def ProjectionParameterResult.result :
    ProjectionParameterResult arguments constructorType → Expr
  | .nil constructorType => constructorType
  | .cons _ _ _ _ _ _ _ tail => tail.result

/-- Exact successful execution trace for the selected-field prefix loop. -/
inductive ProjectionFieldResult (typeName : Name) (struct : Expr) :
    Nat → Nat → Expr → Type
  | nil (position : Nat) (type : Expr) :
      ProjectionFieldResult typeName struct position 0 type
  | dependent (position remaining : Nat) (type : Expr)
      (name : Name) (domain body : Expr) (info : BinderInfo)
      (tail : ProjectionFieldResult typeName struct (position + 1) remaining
        (body.instantiate1 (.proj typeName position struct))) :
      ProjectionFieldResult typeName struct position (remaining + 1) type
  | independent (position remaining : Nat) (type : Expr)
      (name : Name) (domain body : Expr) (info : BinderInfo)
      (tail : ProjectionFieldResult typeName struct (position + 1) remaining
        body) :
      ProjectionFieldResult typeName struct position (remaining + 1) type

def ProjectionFieldResult.result :
    ProjectionFieldResult typeName struct position remaining type → Expr
  | .nil _ type => type
  | .dependent _ _ _ _ _ _ _ tail => tail.result
  | .independent _ _ _ _ _ _ _ tail => tail.result

/-- Positions at which the executable loop inserted a preceding primitive
projection into a dependent field body. -/
def ProjectionFieldResult.projectionPositions :
    ProjectionFieldResult typeName struct position remaining type → List Nat
  | .nil .. => []
  | .dependent position _ _ _ _ _ _ tail =>
      position :: tail.projectionPositions
  | .independent _ _ _ _ _ _ _ tail => tail.projectionPositions

/-- Truncate a successful selected-field trace to any earlier field.  This
is the executable evidence used by the well-founded projection proof: a
dependent step at position `p` can replay precisely the first `p` steps,
without inspecting any later field. -/
def ProjectionFieldResult.take
    (trace : ProjectionFieldResult typeName struct position remaining type)
    (count : Nat) (hcount : count ≤ remaining) :
    ProjectionFieldResult typeName struct position count type :=
  match count, trace with
  | 0, _ => .nil position type
  | count + 1, .dependent position remaining type name domain body info tail =>
      .dependent position count type name domain body info
        (tail.take count (Nat.le_of_succ_le_succ hcount))
  | count + 1, .independent position remaining type name domain body info tail =>
      .independent position count type name domain body info
        (tail.take count (Nat.le_of_succ_le_succ hcount))

structure ProjectionExpansion where
  typeName : Name
  index : Nat
  struct : Expr
  /-- The exact successful production family lookup.  Retaining it is pure:
  the checker already inspected this value before selecting the singleton
  constructor. -/
  familyInfo : InductiveVal
  /-- The weak-head-normal major type whose head and argument spine passed
  the projection checks. -/
  familyType : Expr
  /-- Exact input type supplied by ordinary major inference. -/
  sourceType : Expr
  constructorName : Name
  familySingle : familyInfo.ctors = [constructorName]
  constructorInfo : ConstantInfo
  familyLevels : List Level
  params : List Expr
  indices : List Expr
  rawConstructorType : Expr
  parameterResult : ProjectionParameterResult params rawConstructorType
  constructorType : Expr
  constructorType_eq : constructorType = parameterResult.result
  fieldResult : ProjectionFieldResult typeName struct 0 index constructorType
  numFields : Nat
  selectedFieldType : Expr
  selectedFieldType_eq : selectedFieldType = fieldResult.result

/-- A projection inference result couples the legacy inferred type with the
exact concrete data needed to construct its canonical eliminator expansion. -/
structure ProjectionResult where
  type : Expr
  expansion : ProjectionExpansion

structure ExactProjectionResult (typeName : Name) (index : Nat)
    (struct structType : Expr) extends ProjectionResult where
  typeName_eq : toProjectionResult.expansion.typeName = typeName
  index_eq : toProjectionResult.expansion.index = index
  struct_eq : toProjectionResult.expansion.struct = struct
  sourceType_eq : toProjectionResult.expansion.sourceType = structType

/-- Consume the common-parameter prefix of a constructor type. -/
def instantiateProjectionParametersExact :
    (arguments : List Expr) → (constructorType : Expr) →
    (∀ {α}, RecM α) →
      RecM (ProjectionParameterResult arguments constructorType)
  | [], constructorType, _ => return .nil constructorType
  | argument :: arguments, constructorType, fail => do
      let .forallE name domain body info ← whnf constructorType
        | fail
      let tail ← instantiateProjectionParametersExact arguments
        (body.instantiate1 argument) fail
      return .cons argument arguments constructorType name domain body info tail

def instantiateProjectionParameters
    (arguments : List Expr) (constructorType : Expr)
    (fail : ∀ {α}, RecM α) : RecM Expr := do
  return (← instantiateProjectionParametersExact arguments
    constructorType fail).result

/-- Consume exactly the fields preceding the selected projection. -/
def instantiateProjectionFieldsExact (typeName : Name) (index : Nat)
    (struct : Expr) (maybePropType : Bool) (constructorTail : Expr)
    (fail : ∀ {α}, RecM α) :
    RecM (ProjectionFieldResult typeName struct 0 index constructorTail) :=
  let rec loop (position remaining : Nat) (type : Expr) :
      RecM (ProjectionFieldResult typeName struct position remaining type) :=
    match remaining with
    | 0 => return .nil position type
    | remaining + 1 => do
      let .forallE name domain body info ← whnf type
        | fail
      if body.hasLooseBVars then
        if maybePropType then
          unless ← isProp domain do
            fail
        let tail ← loop (position + 1) remaining
          (body.instantiate1 (.proj typeName position struct))
        return .dependent position remaining type name domain body info tail
      else
        let tail ← loop (position + 1) remaining body
        return .independent position remaining type name domain body info tail
  loop 0 index constructorTail

def instantiateProjectionFields (typeName : Name) (index : Nat)
    (struct : Expr) (maybePropType : Bool) (constructorTail : Expr)
    (fail : ∀ {α}, RecM α) : RecM Expr := do
  return (← instantiateProjectionFieldsExact typeName index struct maybePropType
    constructorTail fail).result

/-- Infer a structure projection while retaining the already-computed raw
constructor metadata.  It performs exactly the legacy WHNF/type checks: no
field after `index` is traversed or normalized. -/
def inferProjResultExact (typeName : Name) (idx : Nat)
    (struct structType : Expr) :
    RecM (ExactProjectionResult typeName idx struct structType) := do
  let e := Expr.proj typeName idx struct
  let type ← whnf structType
  type.withApp fun I args => do
  let env ← getEnv
  let fail {_} := do throw <| .invalidProj env (← getLCtx) e
  let .const I_name I_levels := I | fail
  if typeName != I_name then fail
  let .inductInfo I_val ← env.get I_name | fail
  let some singleton := singletonConstructor? I_val.ctors | fail
  let c := singleton.name
  if args.size != I_val.numParams + I_val.numIndices then fail
  let c_info ← env.get c
  let rawConstructorType := c_info.instantiateTypeLevelParams I_levels
  let parameterResult ← instantiateProjectionParametersExact
    (args.toList.take I_val.numParams) rawConstructorType fail
  let constructorType := parameterResult.result
  let maybePropType := !(← getSortLevel type).isNeverZero
  let fieldResult ← instantiateProjectionFieldsExact typeName idx struct maybePropType
    constructorType fail
  let r := fieldResult.result
  let .forallE _ dom _ _ ← whnf r | fail
  if maybePropType then if !(← isProp dom) then fail
  let result : ProjectionResult := {
    type := dom
    expansion := {
      typeName
      index := idx
      struct
      familyInfo := I_val
      familyType := type
      sourceType := structType
      constructorName := c
      familySingle := singleton.exact
      constructorInfo := c_info
      familyLevels := I_levels
      params := args.toList.take I_val.numParams
      indices := args.toList.drop I_val.numParams
      rawConstructorType
      parameterResult
      constructorType
      constructorType_eq := rfl
      fieldResult
      numFields := match c_info with
        | .ctorInfo ctorInfo => ctorInfo.numFields
        | _ => 0
      selectedFieldType := r
      selectedFieldType_eq := rfl } }
  return {
    toProjectionResult := result
    typeName_eq := rfl
    index_eq := rfl
    struct_eq := rfl
    sourceType_eq := rfl }

def inferProjResult (typeName : Name) (idx : Nat)
    (struct structType : Expr) : RecM ProjectionResult := do
  return (← inferProjResultExact typeName idx struct structType).toProjectionResult

structure ProjectionBinder where
  name : Name
  domain : Expr
  info : BinderInfo

structure ProjectionTelescope (count : Nat) where
  binders : List ProjectionBinder
  result : Expr
  count_eq : binders.length = count

def takeForallBinders : (count : Nat) → Expr →
    RecM (ProjectionTelescope count)
  | 0, body => return { binders := [], result := body, count_eq := rfl }
  | count + 1, type => do
      let .forallE name domain body info ← whnf type
        | throw <| .other "projection certificate telescope is too short"
      let tail ← takeForallBinders count body
      return {
        binders := { name, domain, info } :: tail.binders
        result := tail.result
        count_eq := by simp [tail.count_eq] }

def instantiateForallPrefix : List Expr → Expr → RecM Expr
  | [], type => return type
  | argument :: arguments, type => do
      let .forallE _ _ body _ ← whnf type
        | throw <| .other "projection certificate parameter telescope is too short"
      instantiateForallPrefix arguments (body.instantiate1 argument)

def wrapProjectionLambdas (binders : List ProjectionBinder) (body : Expr) : Expr :=
  binders.foldr (fun binder body =>
    .lam binder.name binder.domain body binder.info) body

def projectionBoundVars (count : Nat) : List Expr :=
  (List.range count).map fun index => .bvar (count - index - 1)

/-- Transparent pattern abstraction used by the certified projection motive.
Unlike `Expr.abstract`, whose production implementation is opaque to the
verifier, this definition exposes the exact occurrence replacement needed by
the cancellation proof.  The first matching pattern becomes the binder at
the corresponding position in the surrounding lambda telescope. -/
def abstractProjectionPatterns (patterns : List Expr) :
    (expression : Expr) → (depth : Nat := 0) → Expr
  | expression, depth =>
    match patterns.findIdx? (fun pattern => expression == pattern) with
    | some index => .bvar (depth + (patterns.length - index - 1))
    | none =>
      match expression with
      | .bvar index =>
          .bvar (if index < depth then index else index + patterns.length)
      | .fvar id => .fvar id
      | .mvar id => .mvar id
      | .sort level => .sort level
      | .const name levels => .const name levels
      | .app fn argument =>
          .app (abstractProjectionPatterns patterns fn depth)
            (abstractProjectionPatterns patterns argument depth)
      | .lam name domain body info =>
          .lam name (abstractProjectionPatterns patterns domain depth)
            (abstractProjectionPatterns patterns body (depth + 1)) info
      | .forallE name domain body info =>
          .forallE name (abstractProjectionPatterns patterns domain depth)
            (abstractProjectionPatterns patterns body (depth + 1)) info
      | .letE name type value body nondep =>
          .letE name (abstractProjectionPatterns patterns type depth)
            (abstractProjectionPatterns patterns value depth)
            (abstractProjectionPatterns patterns body (depth + 1)) nondep
      | .lit literal => .lit literal
      | .mdata data body =>
          .mdata data (abstractProjectionPatterns patterns body depth)
      | .proj name index body =>
          .proj name index (abstractProjectionPatterns patterns body depth)

/-- Exact syntax returned by the untrusted projection-candidate generator.
The equality is computational evidence only: acceptance still parses and
checks `candidate` below. -/
structure GeneratedProjectionCandidate (projection : ProjectionResult) where
  candidate : Expr
  resultLevel : Level
  indexBinders : List ProjectionBinder
  fieldBinders : List ProjectionBinder
  fieldCount : fieldBinders.length = projection.expansion.numFields
  exact : candidate = mkAppN
    (.const (mkCasesOnName projection.expansion.typeName)
      (resultLevel :: projection.expansion.familyLevels))
    (projection.expansion.params ++
      [wrapProjectionLambdas
        (indexBinders ++ [{
          name := `_major
          domain := mkAppN
            (.const projection.expansion.typeName
              projection.expansion.familyLevels)
            ((projection.expansion.params.map fun parameter =>
                parameter.liftLooseBVars 0 indexBinders.length) ++
              projectionBoundVars indexBinders.length).toArray
          info := .default }])
        (abstractProjectionPatterns
          (projection.expansion.indices ++
            [projection.expansion.struct]) projection.type)] ++
      projection.expansion.indices ++
      [projection.expansion.struct,
        wrapProjectionLambdas fieldBinders
          (.bvar (projection.expansion.numFields -
            projection.expansion.index - 1))]).toArray

/-- Construct one deterministic candidate from retained inference data.  This
generator is untrusted: its output is parsed and fully checked below. -/
def generateProjectionCandidate (projection : ProjectionResult) :
    RecM (GeneratedProjectionCandidate projection) := do
  let expansion := projection.expansion
  let resultLevel ← getSortLevel projection.type
  let familyType := expansion.familyInfo.instantiateTypeLevelParams
    expansion.familyLevels
  let familyAfterParams ← instantiateForallPrefix expansion.params familyType
  let indexTelescope ← takeForallBinders
    expansion.familyInfo.numIndices familyAfterParams
  let indexBinders := indexTelescope.binders
  let indexCount := indexBinders.length
  let liftedParams := expansion.params.map fun parameter =>
    parameter.liftLooseBVars 0 indexCount
  let majorDomain := mkAppN
    (.const expansion.typeName expansion.familyLevels)
    (liftedParams ++ projectionBoundVars indexCount).toArray
  let motiveBinders := indexBinders ++ [{
    name := `_major
    domain := majorDomain
    info := .default }]
  let motiveBody := abstractProjectionPatterns
    (expansion.indices ++ [expansion.struct]) projection.type
  let motive := wrapProjectionLambdas motiveBinders motiveBody
  let fieldTelescope ← takeForallBinders
    expansion.numFields expansion.constructorType
  let fieldBinders := fieldTelescope.binders
  let minor := wrapProjectionLambdas fieldBinders
    (.bvar (expansion.numFields - expansion.index - 1))
  let candidate := mkAppN
    (.const (mkCasesOnName expansion.typeName)
      (resultLevel :: expansion.familyLevels))
    (expansion.params ++ [motive] ++ expansion.indices ++
      [expansion.struct, minor]).toArray
  return {
    candidate, resultLevel, indexBinders, fieldBinders
    fieldCount := fieldTelescope.count_eq
    exact := rfl }

structure ProjectionProposal (typeName : Name) (index : Nat)
    (struct structType : Expr) where
  exactProjection : ExactProjectionResult typeName index struct structType
  generated : GeneratedProjectionCandidate
    exactProjection.toProjectionResult

def generateProjectionProposal (typeName : Name) (index : Nat)
    (struct structType : Expr) :
    RecM (ProjectionProposal typeName index struct structType) := do
  let exactProjection ← inferProjResultExact typeName index struct structType
  let generated ← generateProjectionCandidate exactProjection.toProjectionResult
  return { exactProjection, generated }

def takeLambdas : Nat → Expr → Option (List Expr × Expr)
  | 0, body => some ([], body)
  | count + 1, .lam _ domain body _ => do
      let (domains, result) ← takeLambdas count body
      return (domain :: domains, result)
  | _, _ => none

def projectionMinorDomains? (numFields index : Nat) (minor : Expr) :
    Option (List Expr) := do
  let (domains, body) ← takeLambdas numFields minor
  if body == .bvar (numFields - index - 1) then return domains else none

structure ProjectionShell (numFields index : Nat) where
  resultLevel : Level
  motive : Expr
  minor : Expr
  fieldDomains : List Expr
  minorRun : projectionMinorDomains? numFields index minor = some fieldDomains

structure ParsedProjectionMinor (numFields index : Nat) (minor : Expr) where
  domains : List Expr
  exact : projectionMinorDomains? numFields index minor = some domains

def parsedProjectionMinor? (numFields index : Nat) (minor : Expr) :
    Option (ParsedProjectionMinor numFields index minor) :=
  match h : projectionMinorDomains? numFields index minor with
  | some domains => some ⟨domains, h⟩
  | none => none

def ProjectionExpansion.parseShell? (expansion : ProjectionExpansion)
    (candidate : Expr) :
    Option (ProjectionShell expansion.numFields expansion.index) := do
  let .const eliminator levels := candidate.getAppFn | none
  let resultLevel :: familyLevels := levels | none
  unless eliminator == mkCasesOnName expansion.typeName do none
  unless familyLevels == expansion.familyLevels do none
  let args := candidate.getAppArgs.toList
  let parameterCount := expansion.params.length
  let indexCount := expansion.indices.length
  unless args.length == parameterCount + 1 + indexCount + 2 do none
  unless args.take parameterCount == expansion.params do none
  let afterParameters := args.drop parameterCount
  let motive :: afterMotive := afterParameters | none
  unless afterMotive.take indexCount == expansion.indices do none
  let afterIndices := afterMotive.drop indexCount
  let [major, minor] := afterIndices | none
  unless major == expansion.struct do none
  let parsedMinor ← parsedProjectionMinor?
    expansion.numFields expansion.index minor
  return {
    resultLevel, motive, minor
    fieldDomains := parsedMinor.domains
    minorRun := parsedMinor.exact }

structure ParsedProjectionShell (expansion : ProjectionExpansion)
    (candidate : Expr) where
  shell : ProjectionShell expansion.numFields expansion.index
  exact : expansion.parseShell? candidate = some shell

def ProjectionExpansion.parsedShell? (expansion : ProjectionExpansion)
    (candidate : Expr) : Option (ParsedProjectionShell expansion candidate) :=
  match h : expansion.parseShell? candidate with
  | some shell => some ⟨shell, h⟩
  | none => none

def projectionFree : Expr → Bool
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lit _ => true
  | .app fn arg => projectionFree fn && projectionFree arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
      projectionFree domain && projectionFree body
  | .letE _ type value body _ =>
      projectionFree type && projectionFree value && projectionFree body
  | .mdata _ body => projectionFree body
  | .proj .. => false

structure ProjectionFreeCertificate (candidate : Expr) : Type where
  exact : projectionFree candidate = true

def projectionFreeCertificate? (candidate : Expr) :
    Option (ProjectionFreeCertificate candidate) :=
  match h : projectionFree candidate with
  | true => some ⟨h⟩
  | false => none

/-- Executable scope check for a generated projection candidate.  Candidate
generation is deliberately untrusted, so validation records directly that it
did not invent free variables or metavariables before invoking checked type
inference.  Loose bound variables remain the responsibility of `inferType`,
which performs its existing top-level check. -/
def projectionCandidateScopeValid (lctx : LocalContext) : Expr → Bool
  | .bvar _ => true
  | .fvar fvarId => (lctx.find? fvarId).isSome
  | .mvar _ => false
  | .sort level => !level.hasMVar
  | .const _ levels => levels.all fun level => !level.hasMVar
  | .app fn argument =>
      projectionCandidateScopeValid lctx fn &&
        projectionCandidateScopeValid lctx argument
  | .lam _ domain body _ | .forallE _ domain body _ =>
      projectionCandidateScopeValid lctx domain &&
        projectionCandidateScopeValid lctx body
  | .letE _ type value body _ =>
      projectionCandidateScopeValid lctx type &&
        projectionCandidateScopeValid lctx value &&
        projectionCandidateScopeValid lctx body
  | .lit _ => true
  | .mdata _ body | .proj _ _ body =>
      projectionCandidateScopeValid lctx body

structure ProjectionCertificate where
  projection : ProjectionResult
  candidate : Expr
  shell : ProjectionShell projection.expansion.numFields
    projection.expansion.index
  shellRun : projection.expansion.parseShell? candidate = some shell
  candidateType : Expr

def validateProjectionResult (projection : ProjectionResult)
    (candidate : Expr) : RecM ProjectionCertificate :=
  fun methods context state =>
    match projection.expansion.parsedShell? candidate with
    | none => .error <| .other "projection expansion is not canonical"
    | some parsed =>
      if projectionCandidateScopeValid context.lctx candidate then
        match inferType candidate (inferOnly := false) methods context state with
        | .error error => .error error
        | .ok (candidateType, inferenceState) =>
          match isDefEq candidateType projection.type methods context inferenceState with
          | .error error => .error error
          | .ok (false, _) => .error <|
              .other "projection expansion type does not match projection type"
          | .ok (true, finalState) => .ok ({
              projection, candidate
              shell := parsed.shell
              shellRun := parsed.exact
              candidateType }, finalState)
      else
        .error <| .other "projection expansion contains an out-of-scope variable"

def validateProjectionCandidate (typeName : Name) (index : Nat)
    (struct structType candidate : Expr) : RecM ProjectionCertificate := do
  let projection ← inferProjResult typeName index struct structType
  validateProjectionResult projection candidate

/-- Run legacy inference once, generate an untrusted candidate, and accept
only after native checker certification. -/
def inferProjCertified (typeName : Name) (index : Nat)
    (struct structType : Expr) : RecM ProjectionCertificate := do
  let proposal ← generateProjectionProposal typeName index struct structType
  validateProjectionResult proposal.exactProjection.toProjectionResult
    proposal.generated.candidate

/-- Infers the type of structure projection `e`. -/
def inferProj (typeName : Name) (idx : Nat) (struct structType : Expr) : RecM Expr := do
  return (← inferProjCertified typeName idx struct structType).projection.type

@[inherit_doc inferType]
def inferType' (e : Expr) (inferOnly : Bool) : RecM Expr := do
  if e.hasLooseBVars then
    throw <| .other
      s!"type checker does not support loose bound variables, \
         replace them with free variables before invoking it"
  let state ← get
  if let some r := (cond inferOnly state.inferTypeI state.inferTypeC)[e]? then
    return r
  let r ← match e with
    | .lit l =>
      if !inferOnly then
        match l with
        | .natVal _ => _ ← (← getEnv).get ``Nat
        | .strVal _ => _ ← (← getEnv).get ``Char.ofNat; _ ← (← getEnv).get ``String.ofList
      pure (mkConst l.typeName)
    | .mdata _ e => inferType' e inferOnly
    | .proj s idx e => inferProj s idx e (← inferType' e inferOnly)
    | .fvar n => inferFVar (← readThe Context) n
    | .mvar _ => throw <| .other "kernel type checker does not support meta variables"
    | .bvar _ => unreachable!
    | .sort l =>
      if !inferOnly then
        checkLevel (← readThe Context) l
      pure <| .sort (.succ l)
    | .const c ls => inferConstant (← readThe Context) c ls inferOnly
    | .lam .. => inferLambda e inferOnly
    | .forallE .. => inferForall e inferOnly
    | .app f a =>
      if inferOnly then
        inferApp e
      else
        let fType ← ensureForallCore (← inferType' f inferOnly) e
        let aType ← inferType' a inferOnly
        let dType := fType.bindingDomain!
        -- it can be shown that if `e` is typeable as `T`, then `T` is typeable as `Sort l`
        -- for some universe level `l`, so this use of `isDefEq` is valid
        let ok ← if a.isAppOfArity ``eagerReduce 2 then
          withTheReader Context (fun s => {s with eagerReduce := true}) <|
            isDefEq dType aType
        else
          isDefEq dType aType
        if !ok then throw <| .appTypeMismatch (← getEnv) (← getLCtx) e fType aType
        pure <| fType.bindingBody!.instantiate1 a
    | .letE .. => inferLet e inferOnly
  modify fun s => cond inferOnly
    { s with inferTypeI := s.inferTypeI.insert e r }
    { s with inferTypeC := s.inferTypeC.insert e r }
  return r

/-- Reduces `e` to its weak-head normal form, without unfolding definitions. This is a conservative
version of `whnf` (which does unfold definitions), to be used for efficiency purposes.

Setting `cheapProj` to `true` will cause the struct argument to be reduced "lazily" (using
`whnfCore` rather than `whnf`) when reducing struct projections, and suppresses caching of the
result. This can be a useful optimization if we're checking the definitional equality of two struct
projections of the same projection, where we might save some work by directly checking if the struct
arguments are defeq (rather than eagerly applying a projection).

The kernel has a companion `cheap_rec` flag doing the same for the major premise of a recursor, but
nothing has set it since lean4#9275 removed the old compiler, so it is omitted here. -/
def whnfCore (e : Expr) (cheapProj := false) : RecM Expr :=
  fun m => m.whnfCore e cheapProj

def reduceRecursor (e : Expr) : RecM (Option Expr) := do
  let env ← getEnv
  if env.quotInit then
    if let some r ← quotReduceRec e whnf then
      return r
  if let some r ← inductiveReduceRec env e whnf inferType isDefEq then
    return r
  return none

/-- Reduces the free variable `e`: to the `whnfCore` of its definition if `e` is a let variable,
and to itself if it is a lambda variable. -/
def whnfFVar (e : Expr) (cheapProj : Bool) : RecM Expr := do
  if let some (.ldecl (value := v) ..) := (← getLCtx).find? e.fvarId! then
    return ← whnfCore v cheapProj
  return e

/-- `reduceProj` on a structure that has already been reduced (C++ `reduce_proj_core`). -/
def reduceProjCore (idx : Nat) (struct : Expr) : RecM (Option Expr) := do
  let mut c := struct
  if let .lit (.strVal s) := c then
    c ← whnf (.strLitToConstructor s)
  c.withApp fun mk args => do
  let .const mkC _ := mk | return none
  let env ← getEnv
  let .ctorInfo mkInfo ← env.get mkC | return none
  return args[mkInfo.numParams + idx]?

/-- Reduces a projection of `struct` at index `idx` (when `struct` is reducible to a constructor
application). -/
def reduceProj (idx : Nat) (struct : Expr) (cheapProj : Bool) : RecM (Option Expr) :=
  -- an explicit `>>=`: with the new `do` elaborator, `reduceProjCore idx (← if ..)` lifts the
  -- bind into both branches, which `reduceProj.WF` cannot see through
  (if cheapProj then whnfCore struct cheapProj else whnf struct) >>= reduceProjCore idx

def isLetFVar (lctx : LocalContext) (fvar : FVarId) : Bool :=
  lctx.find? fvar matches some (.ldecl ..)

@[inherit_doc whnfCore]
def whnfCore' (e : Expr) (cheapProj := false) : RecM Expr := do
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit .. => return e
  | .mdata _ e => return ← whnfCore' e cheapProj
  | .fvar id => if !isLetFVar (← getLCtx) id then return e
  | .app .. | .letE .. | .proj .. => pure ()
  if let some r := (← get).whnfCoreCache[e]? then
    return r
  let rec save r := do
    if !cheapProj then
      modify fun s => { s with whnfCoreCache := s.whnfCoreCache.insert e r }
    return r
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .const .. | .lam .. | .lit ..
  | .mdata .. => unreachable!
  | .fvar _ => return ← whnfFVar e cheapProj
  | .app .. =>
    -- beta-reduce at the head as much as possible, apply any remaining `rargs`
    -- to the resulting expression, and re-run `whnfCore`
    e.withAppRev fun f0 rargs => do
    -- the head may still be a let variable/binding, projection, or mdata-wrapped expression
    let f ← whnfCore f0 cheapProj
    if let .lam _ _ body _ := f then
      let rec loop m (f : Expr) : RecM Expr :=
        let rec cont := do
          let r := f.instantiateRange (rargs.size - m) rargs.size rargs
          let r := r.mkAppRevRange 0 (rargs.size - m) rargs
          save <|← whnfCore r cheapProj
        if let .lam _ _ body _ := f then
          if m < rargs.size then loop (m + 1) body
          else cont
        else cont
      loop 1 body
    else if f == f0 then
      if let some r ← reduceRecursor e then
        whnfCore r cheapProj
      else
        pure e
    else
      let r := f.mkAppRevRange 0 rargs.size rargs
      -- the recursive call re-decomposes `r` and reaches the `f == f0` branch above, so
      -- `reduceRecursor` is still applied; adding arguments can only enable further normalization
      -- if the head reduced to a partial recursor application
      save <|← whnfCore r cheapProj
  | .letE _ _ val body _ =>
    save <|← whnfCore (body.instantiate1 val) cheapProj
  | .proj _ idx s =>
    if let some m ← reduceProj idx s cheapProj then
      save <|← whnfCore m cheapProj
    else
      save e

/-- Checks if the head of `e` is a constant that can be delta-reduced, applied to the right number
of universe levels, returning its `ConstantInfo` if so. See `ConstantInfo.deltaValue?` for which
constants qualify. -/
def isDelta (env : Environment) (e : Expr) : Option ConstantInfo := do
  if let .const c ls := e.getAppFn then
    if let some ci := env.find? c then
      if ci.deltaValue?.isSome && ls.length == ci.numLevelParams then
        return ci
  none

def instantiateDeltaValue (ci : ConstantInfo) (ls : List Level) : Expr :=
  ci.deltaValue?.get!.instantiateLevelParams ci.levelParams ls

/-- If `e` is itself a constant that can be delta-reduced, returns its value with the constant's
level parameters instantiated. Unlike `unfoldDefinition`, this does not look through applications:
`e` must be a `.const`. -/
def unfoldDefinitionCore (e : Expr) : RecM (Option Expr) := do
  let .const _ ls := e | return none
  let env ← getEnv
  let some d := isDelta env e | return none
  unless 0 < ls.length do return some (instantiateDeltaValue d ls)
  if let some r := (← get).unfold[e]? then return some r
  let r := instantiateDeltaValue d ls
  modify fun s => { s with unfold := s.unfold.insert e r }
  return some r

/-- Unfolds the definition at the head of the application `e` (or `e` itself if it is not an
application). -/
def unfoldDefinition (e : Expr) : RecM (Option Expr) := do
  if e.isApp then
    let f0 := e.getAppFn
    let some f ← unfoldDefinitionCore f0 | return none
    let rargs := e.getAppRevArgs
    return f.mkAppRevRange 0 rargs.size rargs
  else
    unfoldDefinitionCore e

def reduceNative (_env : Environment) (e : Expr) : Except Exception (Option Expr) := do
  let .app f (.const c _) := e | return none
  if f == .const ``reduceBool [] then
    throw <| .other s!"lean4lean does not support 'reduceBool {c}' reduction"
  else if f == .const ``reduceNat [] then
    throw <| .other s!"lean4lean does not support 'reduceNat {c}' reduction"
  return none

def rawNatLitExt? (e : Expr) : Option Nat := if e == .natZero then some 0 else e.rawNatLit?

/-- Reduces the application `f a b` to a Nat literal if `a` and `b` can be reduced to Nat literals.

Note: `f` should have an (efficient) external implementation. -/
def reduceBinNatOp (f : Nat → Nat → Nat) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  return some <| .lit <| .natVal <| f v1 v2

def reducePowMaxExp : Nat := 1 <<< 24

def reducePow (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  if v2 > reducePowMaxExp then return none
  return some <| .lit <| .natVal <| Nat.pow v1 v2

/-- Reduces the application `f a b` to a boolean expression if `a` and `b` can be reduced to Nat
literals.

Note: `f` should have an (efficient) external implementation. -/
def reduceBinNatPred (f : Nat → Nat → Bool) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  return toExpr <| f v1 v2

/-- Reduces `e` to a literal if possible, where the unary operation `Nat.succ` and the binary
operations and predicates with an external implementation may be applied: `Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.pow`, `Nat.gcd`, `Nat.mod`, `Nat.div`, `Nat.land`, `Nat.lor`, `Nat.xor`,
`Nat.shiftLeft`, `Nat.shiftRight` produce a `Nat` literal, while the predicates `Nat.beq` and
`Nat.ble` produce a `Bool` literal. -/
def reduceNat (e : Expr) : RecM (Option Expr) := do
  let nargs := e.getAppNumArgs
  if nargs == 1 then
    let f := e.appFn!
    if f == .const ``Nat.succ [] then
      let some v := rawNatLitExt? (← whnf e.appArg!) | return none
      return some <| .lit <| .natVal <| v + 1
  else if nargs == 2 then
    let .app (.app (.const f _) a) b := e | return none
    if f == ``Nat.add then return ← reduceBinNatOp Nat.add a b
    if f == ``Nat.sub then return ← reduceBinNatOp Nat.sub a b
    if f == ``Nat.mul then return ← reduceBinNatOp Nat.mul a b
    if f == ``Nat.pow then return ← reducePow a b
    if f == ``Nat.gcd then return ← reduceBinNatOp Nat.gcd a b
    if f == ``Nat.mod then return ← reduceBinNatOp Nat.mod a b
    if f == ``Nat.div then return ← reduceBinNatOp Nat.div a b
    if f == ``Nat.beq then return ← reduceBinNatPred Nat.beq a b
    if f == ``Nat.ble then return ← reduceBinNatPred Nat.ble a b
    if f == ``Nat.land then return ← reduceBinNatOp Nat.land a b
    if f == ``Nat.lor then return ← reduceBinNatOp Nat.lor a b
    if f == ``Nat.xor then return ← reduceBinNatOp Nat.xor a b
    if f == ``Nat.shiftLeft then return ← reduceBinNatOp Nat.shiftLeft a b
    if f == ``Nat.shiftRight then return ← reduceBinNatOp Nat.shiftRight a b
  return none

@[inherit_doc whnf]
def whnf' (e : Expr) : RecM Expr := do
  -- Do not cache easy cases
  match e with
  | .bvar .. | .sort .. | .mvar .. | .forallE .. | .lit .. => return e
  | .mdata _ e => return ← whnf' e
  | .fvar id =>
    if !isLetFVar (← getLCtx) id then
      return e
  | .lam .. | .app .. | .const .. | .letE .. | .proj .. => pure ()
  -- check cache
  if let some r := (← get).whnfCache[e]? then
    return r
  let rec loop t
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let env ← getEnv
    let t ← whnfCore' t
    if let some t ← reduceNative env t then return t
    if let some t ← reduceNat t then return t
    let some t ← unfoldDefinition t | return t
    loop t fuel
  let ctx ← readThe Context
  let r ← loop e <| if ctx.eagerReduce then ctx.fuel.whnfEager else ctx.fuel.whnf
  modify fun s => { s with whnfCache := s.whnfCache.insert e r }
  return r

/-- If `t` and `s` are lambda expressions, checks that their domains are defeq and recurses on the
bodies, substituting in a new free variable for that binder (this substitution is delayed for
efficiency purposes using the `subst` parameter). Otherwise, does a normal defeq check. -/
def isDefEqLambda (t s : Expr) (subst : Array Expr := #[]) : RecM Bool :=
  match t, s with
  | .lam _ tDom tBody _, .lam name sDom sBody bi => do
    let sType ← if tDom == sDom then pure none else
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEq tType sType) then return false
      pure (some sType)
    if tBody.hasLooseBVars || sBody.hasLooseBVars then
      let sType := sType.getD (sDom.instantiateRev subst)
      withLocalDecl name bi sType fun fv => do
        isDefEqLambda tBody sBody (subst.push fv)
    else
      isDefEqLambda tBody sBody (subst.push default)
  | t, s => isDefEq (t.instantiateRev subst) (s.instantiateRev subst)

/-- If `t` and `s` are for-all expressions, checks that their domains are defeq and recurses on the
bodies, substituting in a new free variable for that binder (this substitution is delayed for
efficiency purposes using the `subst` parameter). Otherwise, does a normal defeq check. -/
def isDefEqForall (t s : Expr) (subst : Array Expr := #[]) : RecM Bool :=
  match t, s with
  | .forallE _ tDom tBody _, .forallE name sDom sBody bi => do
    let sType ← if tDom == sDom then pure none else
      let sType := sDom.instantiateRev subst
      let tType := tDom.instantiateRev subst
      if !(← isDefEq tType sType) then return false
      pure (some sType)
    if tBody.hasLooseBVars || sBody.hasLooseBVars then
      let sType := sType.getD (sDom.instantiateRev subst)
      withLocalDecl name bi sType fun fv =>
        isDefEqForall tBody sBody (subst.push fv)
    else
      isDefEqForall tBody sBody (subst.push default)
  | t, s => isDefEq (t.instantiateRev subst) (s.instantiateRev subst)

/-- Decides definitional equality of `t` and `s` in the cases that can be settled without
reduction, returning `.undef` to defer to the calling function otherwise.

It returns `.true` if they are α-equivalent or have previously been checked for definitional
equality, and otherwise decides two sorts by level equivalence and two literals by equality,
returning `.false` where these disagree. Two lambdas or two for-alls are handed to
`isDefEqLambda`/`isDefEqForall`, which may return either. All remaining cases — including two
constants, two free variables, two applications and two projections — are deferred. -/
def quickIsDefEq (t s : Expr) (useHash := false) : RecM LBool := do
  -- optimization for terms that are already α-equivalent or were previously checked
  if ← modifyGet fun (.mk a1 a2 a3 a4 a5 a6 a7 (eqvManager := m)) =>
    let (b, m) := m.isEquiv useHash t s
    (b, .mk a1 a2 a3 a4 a5 a6 a7 (eqvManager := m))
  then return .true
  match t, s with
  | .lam .., .lam .. => toLBoolM <| isDefEqLambda t s
  | .forallE .., .forallE .. => toLBoolM <| isDefEqForall t s
  | .sort a1, .sort a2 => pure (a1.isEquiv a2).toLBool
  | .mdata _ a1, .mdata _ a2 => toLBoolM <| isDefEq a1 a2
  | .mvar .., .mvar .. => unreachable!
  | .lit a1, .lit a2 => pure (a1 == a2).toLBool
  | _, _ => return .undef

/-- Assuming that `t` and `s` have the same function heads, returns true if they are applications
with definitionally equal arguments (in which case they are defeq), and false otherwise (deferring
further defeq checking to caller). -/
def isDefEqArgs (t s : Expr) : RecM Bool := do
  match t, s with
  | .app tf ta, .app sf sa =>
    if !(← isDefEq ta sa) then return false
    isDefEqArgs tf sf
  | .app .., _ | _, .app .. => return false
  | _, _ => return true

/-- Assuming `t` and `s` are WHNF, checks if they are defeq on account of `t` being an η-expansion
of `s`.

Assuming that `s` has a function type `(x : A) → B x`, it η-expands to `fun (x : A) => s x`
(which it is definitionally equal to by the η rule). -/
def tryEtaExpansionCore (t s : Expr) : RecM Bool := do
  if t.isLambda && !s.isLambda then
    let .forallE name ty _ bi ← whnf (← inferType s) | return false
    isDefEq t (.lam name ty (.app s (.bvar 0)) bi)
  else return false

@[inherit_doc tryEtaExpansionCore]
def tryEtaExpansion (t s : Expr) : RecM Bool :=
  tryEtaExpansionCore t s <||> tryEtaExpansionCore s t

/-- Assuming `t` and `s` in WHNF, checks if they are defeq on account of `s` being defeq to the
struct-η-expansion of `t`.

Assuming that `t` has a non-recursive structure type `S` with constructor `S.mk` and projections
`pᵢ`, it struct-η-expands to `S.mk (p₁ t) ... (pₙ t)` (which it is definitionally equal to by the
struct-η rule). -/
def tryEtaStructCore (t s : Expr) : RecM Bool := do
  let .const f _ := s.getAppFn | return false
  let env ← getEnv
  let .ctorInfo fInfo ← env.get f | return false
  unless s.getAppNumArgs == fInfo.numParams + fInfo.numFields do return false
  unless env.isNonRecStructure fInfo.induct do return false
  unless ← isDefEq (← inferType t) (← inferType s) do return false
  let args := s.getAppArgs
  for h : i in [fInfo.numParams:args.size] do
    -- since `t` is in WHNF, and assuming it is not a constructor application, this projection
    -- cannot reduce (so we are directly checking if `s` is defeq to the struct-η-expansion of `t`)
    unless ← isDefEq (.proj fInfo.induct (i - fInfo.numParams) t) args[i] do return false
  return true

@[inherit_doc tryEtaStructCore]
def tryEtaStruct (t s : Expr) : RecM Bool :=
  -- when `t` and `s` are both constructor applications, `isDefEqApp` has already compared their
  -- arguments and returned false, and the projections in `tryEtaStructCore` reduce back to those
  -- same arguments, so both calls below merely redo that work. The kernel has the same redundancy.
  tryEtaStructCore t s <||> tryEtaStructCore s t

/-- Checks if applications `t` and `s` (should be WHNF) are defeq on account of their function heads
and arguments being defeq. -/
def isDefEqApp (t s : Expr) : RecM Bool := do
  unless t.isApp && s.isApp do return false
  t.withApp fun tf tArgs =>
  s.withApp fun sf sArgs => do
  if _h : tArgs.size = sArgs.size then
    unless ← isDefEq tf sf do return false
    let rec loop i := do
      if _h : i < tArgs.size then
        unless ← isDefEq tArgs[i] sArgs[i] do return false
        loop (i+1)
      else return true
    loop 0
  else return false

/-- Checks if `t` and `s` are definitionally equivalent according to proof irrelevance (that is,
they are proofs of the same proposition). -/
def isDefEqProofIrrel (t s : Expr) : RecM LBool := do
  let tType ← inferType t
  if !(← isProp tType) then return .undef
  toLBoolM <| isDefEq tType (← inferType s)

def failedBefore (failure : Std.HashSet (Expr × Expr)) (t s : Expr) : Bool :=
  if t.hash < s.hash then
    failure.contains (t, s)
  else if t.hash > s.hash then
    failure.contains (s, t)
  else
    failure.contains (t, s) || failure.contains (s, t)

def cacheFailure (t s : Expr) : M Unit := do
  let k := if t.hash ≤ s.hash then (t, s) else (s, t)
  modify fun st => { st with failure := st.failure.insert k }

def tryUnfoldProjApp (e : Expr) : RecM (Option Expr) := do
  let f := e.getAppFn
  if !f.isProj then return none
  let e' ← whnfCore e
  return if e' != e then e' else none

/-- Performs a single step of δ-reduction on `tn`, `sn`, or both (according to optimizations)
followed by weak-head normalization (without further δ-reduction). Returns `.bool` if the resulting
terms are settled by `quickIsDefEq`, or if they are applications of the same defined constant with
defeq args. Otherwise returns `.continue`, indicating to the calling `lazyDeltaReduction` that
δ-reduction is to be continued.

If neither side has a δ-reducible head, returns `.unknown` with the terms unchanged, leaving further
defeq-checking to `isDefEqCore'`. Note that these are weak-head normal forms with respect to
`cheapProj := true`, so a projection at the head may still be reducible. -/
def lazyDeltaReductionStep (tn sn : Expr) : RecM ReductionStatus := do
  let env ← getEnv
  let delta e := do whnfCore (← unfoldDefinition e).get! (cheapProj := true)
  let cont tn sn :=
    return match ← quickIsDefEq tn sn with
    | .undef => .continue tn sn
    | .true => .true
    | .false => .false tn sn
  match isDelta env tn, isDelta env sn with
  | none, none => return .unknown tn sn
  | some _, none =>
    -- `sn` was normalized with `cheapProj := true`, so a projection at its head may not have been
    -- reduced; `tryUnfoldProjApp` retries it with the struct argument fully normalized
    if let some sn' ← tryUnfoldProjApp sn then
      cont tn sn'
    else
      cont (← delta tn) sn
  | none, some _ =>
    if let some tn' ← tryUnfoldProjApp tn then
      cont tn' sn
    else
      cont tn (← delta sn)
  | some dt, some ds =>
    let ht := dt.hints
    let hs := ds.hints
    if ht.lt' hs then
      cont tn (← delta sn)
    else if hs.lt' ht then
      cont (← delta tn) sn
    else
      if tn.isApp && sn.isApp && ptrEqConstantInfo dt ds && dt.hints.isRegular
        && !failedBefore (← get).failure tn sn
      then
        if Level.isEquivList tn.getAppFn.constLevels! sn.getAppFn.constLevels! then
          if ← isDefEqArgs tn sn then
            return .true
        cacheFailure tn sn
      cont (← delta tn) (← delta sn)

@[inline] def isNatZero (t : Expr) : Bool :=
  t == .natZero || t matches .lit (.natVal 0)

def isNatSuccOf? : Expr → Option Expr
  | .lit (.natVal (n+1)) => return .lit (.natVal n)
  | .app (.const ``Nat.succ _) e => return e
  | _ => none

/-- Returns `.true` if `t` and `s` are both zero, either as a literal or as `Nat.zero`. If they are
both successors of natural numbers `t'` and `s'`, either as literals or `Nat.succ` applications,
checks that `t'` and `s'` are definitionally equal. Otherwise, defers to the calling function. -/
def isDefEqOffset (t s : Expr) : RecM LBool := do
  if isNatZero t && isNatZero s then
    return .true
  match isNatSuccOf? t, isNatSuccOf? s with
  | some t', some s' => toLBoolM <| isDefEqCore t' s'
  | _, _ => return .undef

/-- Repeatedly δ-reduces the `cheapProj := true` weak-head normal forms `tn` and `sn` until the
question is settled. Returns `.bool` if:
- they are both zero or both natural number successors (as literals or `Nat.succ` applications)
- one of them can be converted to a natural number/boolean literal
- a `lazyDeltaReductionStep` settles them

Otherwise returns `.unknown` with the reduced terms, deferring to the calling function. Throws
`.deterministicTimeout` after `FuelConfig.lazyDelta` steps. -/
def lazyDeltaReduction (tn sn : Expr) : RecM ReductionStatus := do
  loop tn sn (← readThe Context).fuel.lazyDelta
where
  loop tn sn
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    let r ← isDefEqOffset tn sn
    if r != .undef then return .bool tn sn (r == .true)
    if !tn.hasFVar && !sn.hasFVar || (← readThe Context).eagerReduce then
      if let some tn' ← reduceNat tn then
        return .bool tn' sn (← isDefEqCore tn' sn)
      else if let some sn' ← reduceNat sn then
        return .bool tn sn' (← isDefEqCore tn sn')
    let env ← getEnv
    if let some tn' ← reduceNative env tn then
      return .bool tn' sn (← isDefEqCore tn' sn)
    else if let some sn' ← reduceNative env sn then
      return .bool tn sn' (← isDefEqCore tn sn')
    match ← lazyDeltaReductionStep tn sn with
    | .continue tn sn => loop tn sn fuel
    | r => return r

/-- C++ `lazy_delta_proj_reduction`: for `t.idx =?= s.idx`, lazily delta-unfold the two
structures, and once that stalls compare the projected *fields* rather than the structures. -/
def lazyDeltaProjReduction (t s : Expr) (idx : Nat) : RecM Bool := do
  loop t s (← readThe Context).fuel.lazyDelta
where
  finish tn sn := do
    if let some tf ← reduceProjCore idx tn then
      if let some sf ← reduceProjCore idx sn then
        return ← isDefEqCore tf sf
    isDefEqCore tn sn
  loop tn sn
  | 0 => throw .deterministicTimeout
  | fuel+1 => do
    match ← lazyDeltaReductionStep tn sn with
    | .continue tn sn => loop tn sn fuel
    | .true => return true
    | .unknown tn sn | .false tn sn => finish tn sn

/-- If `t` is a string literal and `s` is a `String.ofList` application, checks that they are defeq
after expanding `t` into a `String.ofList` application of an explicit character list. Otherwise,
defers to the calling function. -/
def tryStringLitExpansionCore (t s : Expr) : RecM LBool := do
  let .lit (.strVal st) := t | return .undef
  let .app sf _ := s | return .undef
  unless sf == .const ``String.ofList [] do return .undef
  toLBoolM <| isDefEqCore (.strLitToConstructor st) s

@[inherit_doc tryStringLitExpansionCore]
def tryStringLitExpansion (t s : Expr) : RecM LBool := do
  match ← tryStringLitExpansionCore t s with
  | .undef => tryStringLitExpansionCore s t
  | r => return r

/-- Checks if `t` and `s` are defeq on account of both being of a unit type (a type with one
constructor without any fields or indices). -/
def isDefEqUnitLike (t s : Expr) : RecM Bool := do
  let tType ← whnf (← inferType t)
  let .const I _ := tType.getAppFn | return false
  let env ← getEnv
  let .inductInfo { isRec := false, ctors := [c], numIndices := 0, .. } ← env.get I
    | return false
  let .ctorInfo { numFields := 0, .. } ← env.get c | return false
  isDefEqCore tType (← inferType s)

@[inherit_doc isDefEqCore]
def isDefEqCore' (t s : Expr) : RecM Bool := do
  let r ← quickIsDefEq t s (useHash := true)
  if r != .undef then return r == .true

  if (!t.hasFVar || (← readThe Context).eagerReduce) && s.isConstOf ``true then
    if (← whnf t).isConstOf ``true then return true

  let tn ← whnfCore t (cheapProj := true)
  let sn ← whnfCore s (cheapProj := true)

  if !(ptrEqExpr tn t && ptrEqExpr sn s) then
    let r ← quickIsDefEq tn sn
    if r != .undef then return r == .true

  let r ← isDefEqProofIrrel tn sn
  if r != .undef then return r == .true

  match ← lazyDeltaReduction tn sn with
  | .continue .. => unreachable!
  | .true => return true
  | .false .. => return false
  | .unknown tn sn =>

  match tn, sn with
  | .const tf tl, .const sf sl =>
    if tf == sf && Level.isEquivList tl sl then return true
  | .fvar tv, .fvar sv => if tv == sv then return true
  | .proj _ ti te, .proj _ si se =>
    -- optimized by the previous reduction functions using `cheapProj := true`
    if ti == si then if ← lazyDeltaProjReduction te se ti then return true
  | _, _ => pure ()

  -- the previous reduction functions used `cheapProj := true`, so we may not have a complete WHNF
  let tnn ← whnfCore tn
  let snn ← whnfCore sn
  if !(ptrEqExpr tnn tn && ptrEqExpr snn sn) then
    -- if projection reduced, need to re-run (as we may not have a WHNF)
    return ← isDefEqCore tnn snn

  -- tn and sn are both in WHNF
  if ← isDefEqApp tn sn then return true
  if ← tryEtaExpansion tn sn then return true
  if ← tryEtaStruct tn sn then return true
  let r ← tryStringLitExpansion tn sn
  if r != .undef then return r == .true
  if ← isDefEqUnitLike tn sn then return true
  return false

end Inner

open Inner

def Methods.withFuel : Nat → Methods
  | 0 =>
    { isDefEqCore := fun _ _ => throw .deepRecursion
      whnfCore := fun _ _ => throw .deepRecursion
      whnf := fun _ => throw .deepRecursion
      inferType := fun _ _ => throw .deepRecursion }
  | n + 1 =>
    { isDefEqCore := fun t s => isDefEqCore' t s (withFuel n)
      whnfCore := fun e p => whnfCore' e p (withFuel n)
      whnf := fun e => whnf' e (withFuel n)
      inferType := fun e i => inferType' e i (withFuel n) }

/-- Runs `x` with a limit on the recursion depth, taken from `FuelConfig.recDepth`. -/
def RecM.run (x : RecM α) : M α := do x (Methods.withFuel (← readThe Context).fuel.recDepth)

def RecM.runTermElab (x : RecM α) (safety := DefinitionSafety.safe) : Elab.Term.TermElabM α :=
  x.run.runTermElab safety

instance : MonadLift RecM Elab.Term.TermElabM := ⟨RecM.runTermElab⟩

@[inherit_doc whnf']
def whnf (e : Expr) : M Expr := (Inner.whnf e).run

def whnfCore (e : Expr) : M Expr := (Inner.whnfCore e).run

def unfoldDefinition (e : Expr) : M Expr := return (← (Inner.unfoldDefinition e).run).getD e

/-- Infers the type of expression `e`. If `inferOnly := false`, this function throws an error
whenever `e` is not typeable according to Lean's algorithmic typing judgment (barring resource
exhaustion: it may also throw `.deterministicTimeout` or `.deepRecursion` on a typeable term).
Setting `inferOnly := true` optimizes to avoid unnecessary checks in the case that `e` is already
known to be well-typed. -/
def inferType (e : Expr) (inferOnly := true) : M Expr := (Inner.inferType e inferOnly).run

/-- Infers the type of expression `e` and checks that `e` is well-typed according to Lean's typing
judgment. Use `inferType` to infer the type alone. -/
abbrev checkType (e : Expr) : M Expr := inferType e (inferOnly := false)

@[inherit_doc isDefEqCore]
def isDefEq (t s : Expr) : M Bool := (Inner.isDefEq t s).run

@[inherit_doc Inner.isProp]
def isProp (t : Expr) : M Bool := (Inner.isProp t).run

@[inherit_doc ensureSortCore]
def ensureSort (t : Expr) (s := t) : M Expr := (ensureSortCore t s).run

@[inherit_doc ensureForallCore]
def ensureForall (t : Expr) (s := t) : M Expr := (ensureForallCore t s).run

/-- Ensures that `e` is a type/proposition. If it is not, throws an error. -/
def ensureType (e : Expr) (inferOnly := true) : M Expr := do ensureSort (← inferType e inferOnly) e

def etaExpand (e : Expr) : M Expr :=
  let rec loop fvars
  | .lam name dom body bi => do
    let d := dom.instantiateRev fvars
    withLocalDecl name bi d fun fv => do
      let fvars := fvars.push fv
      loop fvars body
  | it => do
    let itType ← whnf <| ← inferType <| it.instantiateRev fvars
    if !itType.isForall then return e
    let rec loop2 fvars args
    | 0, _ => throw .deepRecursion
    | fuel + 1, .forallE name dom body bi => do
      let d := dom.instantiateRev fvars
      withLocalDecl name bi d fun arg => do
        let fvars := fvars.push arg
        let args := args.push arg
        loop2 fvars args fuel <| ← whnf <| body.instantiate1 arg
    | _, it => return (← getLCtx).mkLambda fvars (mkAppN it args)
    loop2 fvars #[] (← readThe Context).fuel.etaExpand itType
  loop #[] e

-- for testing:

-- example : "hi" = sorry := by
--   run_tac
--     let env ← Lean.getEnv
--     let lctx ← getLCtx
--     let (_, lhs, _) := (← Elab.Tactic.getMainTarget).eq?.get!
--     logInfo lhs
--     let ty ← show M _ from withReader ({· with env := .empty `h}) (inferType lhs)
--     logInfo ty
--     let sort ← inferType ty
--     logInfo sort
