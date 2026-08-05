import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.VDecl

namespace Lean4Lean

/-- The semantic output of compiling an inductive declaration. The staging is
significant: all inductive headers are available while checking constructors,
and all recursors are available while checking their reduction equations. -/
structure VInductBlock where
  types : List VConstVal
  ctors : List VConstVal
  recursors : List VConstVal
  rules : List VDefEq

namespace VEnv

/-- Add a list of constants from left to right, failing on the first name
collision. -/
def addConsts : VEnv → List VConstVal → Option VEnv
  | env, [] => some env
  | env, ci :: cis => do
    let env ← env.addConst ci.name ci.toVConstant
    env.addConsts cis

/-- Reduction equations do not introduce names and therefore cannot fail. -/
def addDefEqs : VEnv → List VDefEq → VEnv
  | env, [] => env
  | env, df :: dfs => addDefEqs (env.addDefEq df) dfs

end VEnv

def VInductDecl.typeConstants (decl : VInductDecl) : List VConstVal :=
  decl.types.map VInductiveType.toVConstVal

def VInductDecl.constructorConstants (decl : VInductDecl) : List VConstVal :=
  decl.types.flatMap VInductiveType.ctors

def VInductDecl.sourceNames (decl : VInductDecl) : List Name :=
  decl.typeConstants.map VConstVal.name ++ decl.constructorConstants.map VConstVal.name

/-- Split exactly `n` leading forall binders, retaining domains in outermost to
innermost order. -/
def VExpr.takeForalls : Nat → VExpr → Option (List VExpr × VExpr)
  | 0, e => some ([], e)
  | n + 1, .forallE dom body => do
    let (doms, result) ← body.takeForalls n
    return (dom :: doms, result)
  | _ + 1, _ => none

/-- Head and left-to-right arguments of an application spine. -/
def VExpr.getAppFnArgs (e : VExpr) : VExpr × List VExpr :=
  go e []
where
  go : VExpr → List VExpr → VExpr × List VExpr
    | .app fn arg, args => go fn (arg :: args)
    | fn, args => (fn, args)

@[simp] theorem VExpr.getAppFnArgs_const :
    getAppFnArgs (.const name levels) = (.const name levels, []) := rfl

private theorem VExpr.getAppFnArgs.go_append
    (e : VExpr) (pre suffix : List VExpr) :
    getAppFnArgs.go e (pre ++ suffix) =
      let (fn, args) := getAppFnArgs.go e pre
      (fn, args ++ suffix) := by
  induction e generalizing pre with
  | app fn arg ihFn _ =>
    simpa only [getAppFnArgs.go, List.cons_append] using
      ihFn (arg :: pre)
  | _ => simp [getAppFnArgs.go]

@[simp] theorem VExpr.getAppFnArgs_app :
    getAppFnArgs (.app fn arg) =
      let (head, args) := fn.getAppFnArgs
      (head, args ++ [arg]) := by
  change getAppFnArgs.go fn [arg] =
    let (head, args) := getAppFnArgs.go fn []
    (head, args ++ [arg])
  simpa using getAppFnArgs.go_append fn [] [arg]

def VExpr.containsAnyConst (names : List Name) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const name _ => names.contains name
  | .app fn arg | .lam fn arg | .forallE fn arg =>
    fn.containsAnyConst names || arg.containsAnyConst names

/-- The common parameters as de Bruijn variables beneath `depth` additional
constructor-field binders. -/
def VInductDecl.paramVars (decl : VInductDecl) (depth : Nat) : List VExpr :=
  (List.range decl.nparams).reverse.map fun i => .bvar (depth + i)

def VInductDecl.ParamsDefEq (env : VEnv) (decl : VInductDecl)
    (params params' : List VExpr) : Prop :=
  VEnv.IsDefEqCtx env decl.uvars [] params.reverse params'.reverse

/-- A fully applied occurrence of one of the simultaneously declared types.
Recursive occurrences use precisely the common parameter variables, and their
indices contain no recursive occurrence. -/
def VInductDecl.ValidIndAppAt (decl : VInductDecl) (target : Option Name)
    (depth : Nat) (e : VExpr) : Prop :=
  let (fn, args) := e.getAppFnArgs
  ∃ type ∈ decl.types, (target = none ∨ target = some type.name) ∧
    ∃ levels,
      fn = .const type.name levels ∧
      levels.length = decl.uvars ∧
      args.length = decl.nparams + type.numIndices ∧
      args.take decl.nparams = decl.paramVars depth ∧
      ∀ arg ∈ args.drop decl.nparams,
        arg.containsAnyConst (decl.types.map (·.name)) = false

/- Positivity is recursively modulo definitional equality: the executable
checker exposes every higher-order body to WHNF, not only the outermost field
type.  `SyntacticallyPositive` classifies one exposed head, while `Positive`
records the definitional-equality step and recurs under `forallE`. -/
namespace VInductDecl

mutual

/-- Positivity modulo one WHNF/definitional-equality step. -/
inductive Positive (env : VEnv) (decl : VInductDecl) :
    List VExpr → Nat → VExpr → Prop
  | unfold :
    env.IsDefEq decl.uvars ctx e exposed type →
    SyntacticallyPositive env decl ctx depth exposed →
    Positive env decl ctx depth e
/-- The exposed-head cases of strict positivity. -/
inductive SyntacticallyPositive (env : VEnv)
    (decl : VInductDecl) : List VExpr → Nat → VExpr → Prop
  | nonrecursive :
    e.containsAnyConst (decl.types.map (·.name)) = false →
    SyntacticallyPositive env decl ctx depth e
  | forallE :
    dom.containsAnyConst (decl.types.map (·.name)) = false →
    env.IsDefEq decl.uvars ctx dom checkedDom (.sort domLevel) →
    env.IsDefEq decl.uvars (dom :: ctx) body checkedBody bodyType →
    Positive env decl (checkedDom :: ctx) (depth + 1) checkedBody →
    SyntacticallyPositive env decl ctx depth (.forallE dom body)
  | recursive :
    decl.ValidIndAppAt none depth e →
    SyntacticallyPositive env decl ctx depth e

end

end VInductDecl

/-- Constructor fields followed by the constructor's target application. -/
inductive VInductDecl.CtorTailWF (env : VEnv) (decl : VInductDecl)
    (target : VInductiveType) : List VExpr → Nat → VExpr → Prop
  | result :
    decl.ValidIndAppAt (some target.name) depth result' →
    env.IsDefEq decl.uvars ctx result result' type →
    decl.CtorTailWF env target ctx depth result
  | field :
    env.HasType decl.uvars ctx dom (.sort fieldLevel) →
    (target.resultLevel = .zero ∨ fieldLevel ≤ target.resultLevel) →
    (decl.isUnsafe = true ∨ decl.Positive env ctx depth dom) →
    env.IsDefEq decl.uvars ctx dom checkedDom (.sort checkedLevel) →
    env.IsDefEq decl.uvars (dom :: ctx) body checkedBody bodyType →
    decl.CtorTailWF env target (checkedDom :: ctx) (depth + 1) checkedBody →
    decl.CtorTailWF env target ctx depth (.forallE dom body)

/-- Shape of one inductive type after normalization: common parameters,
exactly the recorded indices, and the recorded result sort. -/
def VInductDecl.TypeShape (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (type : VInductiveType) : Prop :=
  ∃ normalized ownParams afterParams indices result exprType,
    env.IsDefEq decl.uvars [] type.type normalized exprType ∧
    normalized.takeForalls decl.nparams = some (ownParams, afterParams) ∧
    afterParams.takeForalls type.numIndices = some (indices, result) ∧
    decl.ParamsDefEq env params ownParams ∧
    env.IsDefEq decl.uvars (indices.reverse ++ ownParams.reverse)
      result (.sort type.resultLevel) (.sort (.succ type.resultLevel))

def VInductDecl.CtorShape (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (target : VInductiveType) (ctor : VConstVal) : Prop :=
  ∃ normalized ownParams tail exprType,
    env.IsDefEq decl.uvars [] ctor.type normalized exprType ∧
    normalized.takeForalls decl.nparams = some (ownParams, tail) ∧
    decl.ParamsDefEq env params ownParams ∧
    decl.CtorTailWF env target ownParams.reverse 0 tail

/-- Source-level obligations that cannot be erased by ordinary or nested
compilation. In particular constructor types are checked in an environment
containing all mutually declared headers, before any nested occurrence is
lowered. -/
def VInductDecl.SourceWF (env : VEnv) (decl : VInductDecl) : Prop :=
  decl.types ≠ [] ∧
  decl.sourceNames.Nodup ∧
  (∀ type ∈ decl.types, type.uvars = decl.uvars) ∧
  (∀ ctor ∈ decl.constructorConstants, ctor.uvars = decl.uvars) ∧
  ∃ envTypes envCtors,
    env.addConsts decl.typeConstants = some envTypes ∧
    envTypes.addConsts decl.constructorConstants = some envCtors ∧
    (∀ type ∈ decl.types, type.toVConstant.WF env) ∧
    ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes

/-- Formation conditions for ordinary and mutually recursive inductive blocks.
Nested declarations use the same source judgment; their lowering must later
produce these conditions for the expanded mutual family. -/
def VInductDecl.FormationWF (env : VEnv) (decl : VInductDecl) : Prop :=
  ∃ params resultLevel envTypes,
    env.addConsts decl.typeConstants = some envTypes ∧
    (∀ type ∈ decl.types,
      type.resultLevel ≈ resultLevel ∧ decl.TypeShape env params type) ∧
    ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
      decl.CtorShape envTypes params type ctor

/-- Abstract well-formedness starts from the original source declaration.
The ordinary/nested formation and positivity judgments extend `SourceWF`
below; keeping this named projection prevents compilation proofs from replacing
source typing with checks of generated artifacts. -/
def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop :=
  decl.SourceWF env ∧ decl.FormationWF env

theorem VInductDecl.SourceWF.originalTypes
    {env : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env) :
    ∀ type ∈ decl.types, type.toVConstant.WF env := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypes, hctors, hwf, _⟩
  exact hwf

/-- In particular, source constructor types are checked before nested lowering.
This is the abstract obligation whose absence exposed the erased-parameter
kernel bug: a proof about generated auxiliary constructors cannot discharge it. -/
theorem VInductDecl.SourceWF.originalConstructors
    {env : VEnv} {decl : VInductDecl}
    (H : decl.SourceWF env) :
    ∃ envTypes,
      env.addConsts decl.typeConstants = some envTypes ∧
      ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes := by
  rcases H with ⟨_, _, _, _, envTypes, envCtors, htypes, hctors, _, hwf⟩
  exact ⟨envTypes, htypes, hwf⟩

theorem VInductDecl.WF.originalConstructors
    {env : VEnv} {decl : VInductDecl}
    (H : decl.WF env) :
    ∃ envTypes,
      env.addConsts decl.typeConstants = some envTypes ∧
      ∀ ctor ∈ decl.constructorConstants, ctor.toVConstant.WF envTypes :=
  H.1.originalConstructors

/-- Install a compiled block in dependency order. -/
def VInductBlock.install (env : VEnv) (block : VInductBlock) : Option VEnv := do
  let env ← env.addConsts block.types
  let env ← env.addConsts block.ctors
  let env ← env.addConsts block.recursors
  return env.addDefEqs block.rules

/-- A compiled block is semantically well formed when every declaration is
well formed at the stage where it is installed, and installation succeeds. -/
def VInductBlock.WF (env : VEnv) (block : VInductBlock) : Prop :=
  ∃ envTypes envCtors envRecursors,
    env.addConsts block.types = some envTypes ∧
    envTypes.addConsts block.ctors = some envCtors ∧
    envCtors.addConsts block.recursors = some envRecursors ∧
    (∀ ci ∈ block.types, ci.toVConstant.WF env) ∧
    (∀ ci ∈ block.ctors, ci.toVConstant.WF envTypes) ∧
    (∀ ci ∈ block.recursors, ci.toVConstant.WF envCtors) ∧
    ∀ df ∈ block.rules, df.WF envRecursors

theorem VInductBlock.WF.exists_install (H : VInductBlock.WF env block) :
    ∃ env', VInductBlock.install env block = some env' := by
  rcases H with ⟨envTypes, envCtors, envRecursors, htypes, hctors, hrecs, _⟩
  exact ⟨envRecursors.addDefEqs block.rules, by
    simp [VInductBlock.install, htypes, hctors, hrecs]⟩

def VExpr.mkApps (fn : VExpr) (args : List VExpr) : VExpr :=
  args.foldl .app fn

def VExpr.wrapLams (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .lam body

def VExpr.wrapForalls (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .forallE body

@[simp] theorem VExpr.takeForalls_wrapForalls_append
    (pre suff : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls (pre ++ suff) body).takeForalls pre.length =
      some (pre, VExpr.wrapForalls suff body) := by
  induction pre with
  | nil => rfl
  | cons dom pre ih =>
    change (do
      let (domains, result) ←
        (VExpr.wrapForalls (pre ++ suff) body).takeForalls pre.length
      return (dom :: domains, result)) = _
    rw [ih]
    rfl

@[simp] theorem VExpr.takeForalls_wrapForalls
    (domains : List VExpr) (body : VExpr) :
    (VExpr.wrapForalls domains body).takeForalls domains.length =
      some (domains, body) := by
  simpa [wrapForalls] using
    VExpr.takeForalls_wrapForalls_append domains [] body

/-- `e` is an application of one of the constructor fields represented by its
de Bruijn index at the outside of the rule telescope. `depth` accounts for
binders introduced inside a higher-order recursive call. -/
def VExpr.IsFieldApp (fieldVars : List Nat) (depth : Nat) (e : VExpr) : Prop :=
  ∃ field ∈ fieldVars, ∃ args,
    e.getAppFnArgs = (.bvar (field + depth), args)

def VExpr.bvarHead? (e : VExpr) : Option Nat :=
  match e.getAppFnArgs.1 with
  | .bvar i => some i
  | _ => none

/-- Syntactic guard for an iota-rule right-hand side. A recursor constant may
only occur through `recCall`, and its major premise must be an application of
a designated constructor field. Ordinary applications cannot smuggle in a
recursor because the `const` constructor excludes their names. -/
inductive VExpr.GuardedIota (recursors : List Name) (fieldVars : List Nat) :
    Nat → VExpr → Prop
  | bvar : GuardedIota recursors fieldVars depth (.bvar n)
  | sort : GuardedIota recursors fieldVars depth (.sort u)
  | const : name ∉ recursors →
      GuardedIota recursors fieldVars depth (.const name levels)
  | app :
      GuardedIota recursors fieldVars depth fn →
      GuardedIota recursors fieldVars depth arg →
      GuardedIota recursors fieldVars depth (.app fn arg)
  | lam :
      GuardedIota recursors fieldVars depth dom →
      GuardedIota recursors fieldVars (depth + 1) body →
      GuardedIota recursors fieldVars depth (.lam dom body)
  | forallE :
      GuardedIota recursors fieldVars depth dom →
      GuardedIota recursors fieldVars (depth + 1) body →
      GuardedIota recursors fieldVars depth (.forallE dom body)
  | recCall :
      recursor ∈ recursors →
      (∀ arg ∈ init ++ [major],
        GuardedIota recursors fieldVars depth arg) →
      major.IsFieldApp fieldVars depth →
      GuardedIota recursors fieldVars depth
        (VExpr.mkApps (.const recursor levels) (init ++ [major]))

def VInductDecl.ownedConstructors
    (decl : VInductDecl) : List (VInductiveType × VConstVal) :=
  decl.types.flatMap fun type => type.ctors.map (type, ·)

def VInductDecl.recursorName (_decl : VInductDecl) (type : VInductiveType) : Name :=
  .mkStr type.name "rec"

/-- Final result of the recursor telescope for one mutual-family member. At
this point all motives and minors, this type's indices, and the major premise
are in scope. -/
def VInductDecl.recursorResult (decl : VInductDecl)
    (ownerIdx numMinors : Nat) (owner : VInductiveType) : VExpr :=
  let motiveOffset :=
    1 + owner.numIndices + numMinors + (decl.types.length - 1 - ownerIdx)
  let indexVars := (List.range owner.numIndices).reverse.map fun i =>
    VExpr.bvar (i + 1)
  VExpr.mkApps (.bvar motiveOffset) (indexVars ++ [.bvar 0])

/-- Independent shape of a generated recursor. Besides its conventional name
and universe count, the leading telescope contains exactly the common
parameters, one motive per mutual type, one minor per constructor, the owner's
indices, and one major premise; its result applies the matching motive to the
indices and major premise. -/
structure VInductDecl.RecursorShape (decl : VInductDecl)
    (owner : VInductiveType) (recursor : VConstVal) where
  ownerIdx : Nat
  owner_lt : ownerIdx < decl.types.length
  owner_eq : decl.types[ownerIdx] = owner
  name : recursor.name = decl.recursorName owner
  uvars : recursor.uvars = decl.uvars ∨ recursor.uvars = decl.uvars + 1
  params : List VExpr
  motives : List VExpr
  minors : List VExpr
  indices : List VExpr
  major : List VExpr
  afterParams : VExpr
  afterMotives : VExpr
  afterMinors : VExpr
  afterIndices : VExpr
  result : VExpr
  params_take : recursor.type.takeForalls decl.nparams =
    some (params, afterParams)
  motives_take : afterParams.takeForalls decl.types.length =
    some (motives, afterMotives)
  minors_take : afterMotives.takeForalls decl.ownedConstructors.length =
    some (minors, afterMinors)
  indices_take : afterMinors.takeForalls owner.numIndices =
    some (indices, afterIndices)
  major_take : afterIndices.takeForalls 1 = some (major, result)
  result_eq : result = decl.recursorResult ownerIdx minors.length owner

/-- Canonical constructor for `RecursorShape` from the single wrapped
telescope produced by recursor generation. -/
def VInductDecl.RecursorShape.ofWrapped
    {decl : VInductDecl} {owner : VInductiveType} {recursor : VConstVal}
    {ownerIdx : Nat} {params motives minors indices major : List VExpr}
    {result : VExpr}
    (owner_lt : ownerIdx < decl.types.length)
    (owner_eq : decl.types[ownerIdx] = owner)
    (name : recursor.name = decl.recursorName owner)
    (uvars : recursor.uvars = decl.uvars ∨
      recursor.uvars = decl.uvars + 1)
    (hparams : params.length = decl.nparams)
    (hmotives : motives.length = decl.types.length)
    (hminors : minors.length = decl.ownedConstructors.length)
    (hindices : indices.length = owner.numIndices)
    (hmajor : major.length = 1)
    (htype : recursor.type = VExpr.wrapForalls
      (params ++ motives ++ minors ++ indices ++ major) result)
    (hresult : result = decl.recursorResult ownerIdx minors.length owner) :
    decl.RecursorShape owner recursor := by
  refine {
    ownerIdx, owner_lt, owner_eq, name, uvars, params, motives, minors, indices,
    major
    afterParams := VExpr.wrapForalls (motives ++ minors ++ indices ++ major) result
    afterMotives := VExpr.wrapForalls (minors ++ indices ++ major) result
    afterMinors := VExpr.wrapForalls (indices ++ major) result
    afterIndices := VExpr.wrapForalls major result
    result
    params_take := ?_
    motives_take := ?_
    minors_take := ?_
    indices_take := ?_
    major_take := ?_
    result_eq := hresult }
  · rw [← hparams]
    rw [htype]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append params
        (motives ++ minors ++ indices ++ major) result
  · rw [← hmotives]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append motives
        (minors ++ indices ++ major) result
  · rw [← hminors]
    simpa only [List.append_assoc] using
      VExpr.takeForalls_wrapForalls_append minors (indices ++ major) result
  · rw [← hindices]
    exact VExpr.takeForalls_wrapForalls_append indices major result
  · rw [← hmajor]
    exact VExpr.takeForalls_wrapForalls major result

/-- One declarative iota equation. The left-hand side is a recursor whose final
argument is the matching constructor application. The right-hand side may call
any sibling recursor in a mutual block, but only on explicitly identified
constructor fields. Typing of the complete equation is supplied separately by
`VInductBlock.WF`. -/
structure VInductDecl.IotaRule (decl : VInductDecl) (block : VInductBlock)
    (owner : VInductiveType) (ctor : VConstVal) (rule : VDefEq) where
  recursor : VConstVal
  recursor_mem : recursor ∈ block.recursors
  recursor_name : recursor.name = decl.recursorName owner
  rule_uvars : rule.uvars = recursor.uvars
  domains : List VExpr
  lhsBody : VExpr
  rhsBody : VExpr
  typeBody : VExpr
  lhs_wrapped : rule.lhs = VExpr.wrapLams domains lhsBody
  rhs_wrapped : rule.rhs = VExpr.wrapLams domains rhsBody
  type_wrapped : rule.type = VExpr.wrapForalls domains typeBody
  recursorLevels : List VLevel
  leadingArgs : List VExpr
  ctorLevels : List VLevel
  ctorArgs : List VExpr
  lhs_pattern :
    lhsBody = VExpr.mkApps (.const recursor.name recursorLevels)
      (leadingArgs ++ [VExpr.mkApps (.const ctor.name ctorLevels) ctorArgs])
  recursor_levels : recursorLevels.length = recursor.uvars
  ctor_levels : ctorLevels.length = decl.uvars
  leading_arity : leadingArgs.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + owner.numIndices
  constructor_arity : decl.nparams ≤ ctorArgs.length
  parameter_args : ctorArgs.take decl.nparams =
    leadingArgs.take decl.nparams
  domains_arity : domains.length = decl.nparams + decl.types.length +
    decl.ownedConstructors.length + (ctorArgs.length - decl.nparams)
  fieldVars : List Nat
  fieldVars_eq : fieldVars =
    (ctorArgs.drop decl.nparams).filterMap VExpr.bvarHead?
  fields_in_scope : ∀ field ∈ fieldVars, field < domains.length
  rhs_guarded : rhsBody.GuardedIota (block.recursors.map (·.name)) fieldVars 0

/-- Independent ordinary/mutual compilation interface. It is deliberately
stronger than mere well-typedness: source constants are preserved exactly,
recursor names and arities are constrained, and constructor/rule coverage is
total and ordered. -/
structure VInductDecl.OrdinaryCompilation
    (decl : VInductDecl) (block : VInductBlock) : Prop where
  types : block.types = decl.typeConstants
  ctors : block.ctors = decl.constructorConstants
  recursors : List.Forall₂ (fun type recursor =>
    Nonempty (decl.RecursorShape type recursor))
    decl.types block.recursors
  rules : List.Forall₂ (fun owned rule =>
    Nonempty (decl.IotaRule block owned.1 owned.2 rule))
    decl.ownedConstructors block.rules
  names : List.Nodup ((block.types ++ block.ctors ++ block.recursors).map (·.name))

/-- Pure abstract compilation, kept separate from the executable
`AddInductive` implementation. Nested compilation will enter through a second
constructor after proving that lowering yields an ordinary compilation. -/
inductive VInductDecl.CompilesTo (env : VEnv) : VInductDecl → VInductBlock → Prop
  | ordinary : VInductDecl.OrdinaryCompilation decl block →
      VInductDecl.CompilesTo env decl block

/-- Relational abstract environment extension for inductive declarations.
Unlike the old placeholder function, this exposes the compiled block witness
needed by the implementation-refinement proof. -/
inductive VEnv.AddInduct (env : VEnv) (decl : VInductDecl) : VEnv → Prop where
  | intro :
    decl.WF env →
    VInductDecl.CompilesTo env decl block →
    VInductBlock.WF env block →
    VInductBlock.install env block = some env' →
    VEnv.AddInduct env decl env'
