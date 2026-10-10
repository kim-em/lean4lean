import Lean4Lean.Verify.Inductive.Basic

/-! # The lowering run and what it certifies

`Environment.addInductive` always runs the source checks (`checkInductiveSources`) and the
nested lowering (`ElimNestedInductive.run`) before `addInductiveAfterLowering`. The lowering
verification (`Nested/Lowering/**`, wave 3) certifies the result of a successful run as
`NestedLoweringOutput` (`loweringRun.WF`, the one stub of this file): the lowered block is the
source families, headers unchanged and constructors lowered, followed by the auxiliary
families, each a cached parameter specialization of a container of the environment, with the
restoration of a lowered source constructor type being its source (up to `Expr.eqv`). The
ordinary branch reads only the zero-auxiliary case (`loweringRun.types_nonempty`,
`loweringRun.ordinary_types_eq_source`); the nested branch (`Nested/**`) reads the rest.

Wave 3 scaffold: `NestedLoweringOutput` is a frozen interface; the Lowering owner may add
fields the restoration consumers request. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The source checks of `Environment.addInductive`: no metavariable or free variable in any
header or constructor type, and no reserved auxiliary name. Stated as the executable's own
verdict. -/
def SourceSyntaxChecks (env : Environment) (types : List InductiveType) : Prop :=
  checkInductiveSources env types = .ok ()

/-- Loose-bound-variable closedness of a whole source block. Lowering re-closes constructor
types over the opened parameters, which would silently repair loose bound variables, so the
source-facing statements carry this as a hypothesis. -/
def SourceBVarClosed (types : List InductiveType) : Prop :=
  ∀ type ∈ types, type.type.Closed ∧ ∀ ctor ∈ type.ctors, ctor.type.Closed

/-- The lowering run of `Environment.addInductive`. -/
abbrev loweringRun (env : Environment) (fuel nparams : Nat) (types : List InductiveType)
    (lparams : List Name) : Except Exception ElimNestedInductive.Result :=
  (ElimNestedInductive.run fuel nparams types env).run'
    { lvls := lparams.map .param, newTypes := types.toArray }

/-- The auxiliary families of a lowering result, those appended after the source families. -/
abbrev auxTypes (res : ElimNestedInductive.Result) (sourceTypes : List InductiveType) :
    List InductiveType :=
  res.types.drop sourceTypes.length

/-- The constructors of the auxiliary families are installed in `loweredEnv` as constructors
of their family: what `ElimNestedInductive.Result.restoreNested` reads off the lowered
environment (`getNestedIfAuxCtor`). The lowered run establishes it for its output. -/
def LoweredAuxiliariesInstalled (res : ElimNestedInductive.Result)
    (sourceTypes : List InductiveType) (loweredEnv : Environment) : Prop :=
  ∀ t ∈ auxTypes res sourceTypes, ∀ c ∈ t.ctors,
    ∃ cval : ConstructorVal, loweredEnv.find? c.name = some (.ctorInfo cval) ∧ cval.induct = t.name

/-- No constant of `e` is a cached auxiliary family of `result` or a constructor of one in
`env` (`getNestedIfAuxCtor`): restoration leaves every constant of `e` in place. Projections
follow the body only, as `restoreNestedNode` does. -- WAVE 3 COMPAT (lowering), from the source
branch's `Nested/Lowering/Basic.lean`. -/
def RestoreSourceDisjoint (result : ElimNestedInductive.Result) (env : Environment) :
    Expr → Prop
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => True
  | .const name _ =>
      result.aux2nested.find? name = none ∧ result.getNestedIfAuxCtor env name = none
  | .app fn arg => RestoreSourceDisjoint result env fn ∧ RestoreSourceDisjoint result env arg
  | .lam _ dom body _ | .forallE _ dom body _ =>
      RestoreSourceDisjoint result env dom ∧ RestoreSourceDisjoint result env body
  | .letE _ type value body _ =>
      RestoreSourceDisjoint result env type ∧ RestoreSourceDisjoint result env value ∧
      RestoreSourceDisjoint result env body
  | .mdata _ body | .proj _ _ body => RestoreSourceDisjoint result env body

/-- **What a successful lowering run certifies** about its result `res` (owner: Lowering;
produced by `loweringRun.WF`). The restoration consumers read it through these fields; the
Lowering owner may add fields. -/
structure NestedLoweringOutput (env : Environment) (fuel nparams : Nat)
    (sourceTypes : List InductiveType) (lparams : List Name)
    (res : ElimNestedInductive.Result) : Prop where
  nparams_eq : res.nparams = nparams
  params_size : res.params.size = nparams
  /-- `ElimNestedInductive.run` rejects the empty block. -/
  source_nonempty : sourceTypes ≠ []
  /-- The lowered block is the source families followed by the auxiliary families, one per
  cache entry. -/
  types_length : res.types.length = sourceTypes.length + res.aux2nested.size
  /-- The source families keep their names, header types and constructor names; only the
  constructor types are lowered. -/
  source_headers : List.Forall₂ (fun lowered source => lowered.name = source.name ∧
      lowered.type = source.type ∧ lowered.ctors.map (·.name) = source.ctors.map (·.name))
    (res.types.take sourceTypes.length) sourceTypes
  /-- With no auxiliary family the lowered block is literally the source block. -/
  ordinary : res.aux2nested.size = 0 → SourceSyntaxChecks env sourceTypes →
    SourceBVarClosed sourceTypes → res.types = sourceTypes
  /-- Every auxiliary family is cached: `aux2nested` maps its name to the nested occurrence it
  replaces (open over `res.params`), and every cache entry names an auxiliary family. -/
  aux_cached : ∀ t ∈ auxTypes res sourceTypes, ∃ nested, res.aux2nested.find? t.name = some nested
  cached_aux : ∀ n nested, res.aux2nested.find? n = some nested →
    n ∈ (auxTypes res sourceTypes).map (·.name)
  /-- A cached nested occurrence is a container application: an inductive type of `env` at
  exactly its parameters, mentioning only the lowering's parameter variables. -/
  nested_app : ∀ n nested, res.aux2nested.find? n = some nested →
    ∃ (I : Name) (ls : List Level) (info : InductiveVal) (args : Array Expr),
      nested = mkAppN (.const I ls) args ∧ env.find? I = some (.inductInfo info) ∧
      args.size = info.numParams ∧
      nested.FVarsIn (fun fv => Expr.fvar fv ∈ res.params.toList)
  /-- Auxiliary families are fresh in `env` and carry the reserved names `_nested.i`.
  -- WAVE 3 COMPAT (lowering): disjointness from the source names and constructor freshness are
  -- not lowering facts (`mkUniqueName` consults only `env`; an auxiliary constructor name is a
  -- kernel constructor name with its family prefix replaced); they come from the lowered
  -- installation. -/
  aux_fresh : ∀ t ∈ auxTypes res sourceTypes,
    env.find? t.name = none ∧ ∃ i : Nat, t.name = .num `_nested i
  /-- An auxiliary constructor is a constructor of a container family `J` of `env`, renamed
  under the auxiliary family. -- WAVE 3 COMPAT (lowering) -/
  aux_ctor_names : ∀ t ∈ auxTypes res sourceTypes, ∀ c ∈ t.ctors,
    ∃ (J : Name) (info : InductiveVal), env.find? J = some (.inductInfo info) ∧
      ∃ cJ ∈ info.ctors, c.name = cJ.replacePrefix J t.name
  /-- The lowering's local context declares exactly the parameters, as free variables. -/
  -- WAVE 3 COMPAT (lowering): `LocalContext.fvars` lists the most recent declaration first.
  lctx_params : res.params.toList.reverse.map (·.fvarId!) = res.lctx.fvars ∧
    ∀ p ∈ res.params.toList, p.isFVar
  /-- Restoration inverts lowering on the source constructors, in any environment in which
  the source constructor type does not mention a cached family or a constructor of one
  (`RestoreSourceDisjoint`): the restored lowered constructor type is the source constructor
  type up to `Expr.eqv` (binder names). -- WAVE 3 COMPAT (lowering): the premise was
  `LoweredAuxiliariesInstalled`, which does not exclude a source constant registered in
  `loweredEnv` as a constructor of an auxiliary family. -/
  restore_source : SourceSyntaxChecks env sourceTypes → SourceBVarClosed sourceTypes →
    ∀ loweredEnv, List.Forall₂ (fun lowered source => List.Forall₂
        (fun (lc sc : Constructor) => RestoreSourceDisjoint res loweredEnv sc.type →
          (res.restoreNested loweredEnv lc.type == sc.type) = true)
        lowered.ctors source.ctors)
      (res.types.take sourceTypes.length) sourceTypes

/-- The hypothesis-free part of `loweringRun.WF` the ordinary branch reads: the source block is
nonempty, the lowered block extends it, and with no auxiliary family it is the source block. -/
theorem loweringRun.sourceShape {env : Environment} {fuel nparams : Nat}
    {types : List InductiveType} {lparams : List Name} {res : ElimNestedInductive.Result}
    (h : loweringRun env fuel nparams types lparams = .ok res) :
    types ≠ [] ∧ types.length ≤ res.types.length ∧
      (res.aux2nested.size = 0 → SourceSyntaxChecks env types → SourceBVarClosed types →
        res.types = types) := by
  -- WAVE 3 STUB (Lowering): `NestedLowering` without the environment invariants.
  have := h; sorry

/-- **The lowering boundary theorem**: a successful lowering run certifies its result. -/
theorem loweringRun.WF {env : Environment} {ves : VEnvs} {fuel nparams : Nat}
    {types : List InductiveType} {lparams : List Name} {res : ElimNestedInductive.Result}
    (wf : ves.WF env) -- WAVE 3 COMPAT (lowering): `nested_app` needs the environment invariants
    (h : loweringRun env fuel nparams types lparams = .ok res) :
    NestedLoweringOutput env fuel nparams types lparams res := by
  -- WAVE 3 STUB (Lowering): the source branch's `Nested/Lowering/**` (`NestedLowering`,
  -- `NestedLoweringOutputClosed`, `ElimNestedInductive.run.refines`, `LowerNextStep`,
  -- `ConstructorRestorationInverse.restoredType_eqv_source`,
  -- `NestedLoweringOutput.types_eq_source_of_aux2nested_size_eq_zero`).
  have := h; sorry

/-- A lowering result has at least the source families. -/
theorem loweringRun.types_nonempty {env : Environment} {fuel nparams : Nat}
    {types : List InductiveType} {lparams : List Name} {res : ElimNestedInductive.Result}
    (h : loweringRun env fuel nparams types lparams = .ok res) : res.types ≠ [] := by
  obtain ⟨hne, hle, -⟩ := loweringRun.sourceShape h
  intro hnil
  rw [hnil] at hle
  exact hne (List.eq_nil_of_length_eq_zero (by simpa using hle))

/-- A lowering run that introduces no auxiliary family returns the source types literally. -/
theorem loweringRun.ordinary_types_eq_source {env : Environment} {fuel nparams : Nat}
    {types : List InductiveType} {lparams : List Name} {res : ElimNestedInductive.Result}
    (hsources : SourceSyntaxChecks env types) (hclosed : SourceBVarClosed types)
    (h : loweringRun env fuel nparams types lparams = .ok res)
    (haux : res.aux2nested.size = 0) : res.types = types :=
  (loweringRun.sourceShape h).2.2 haux hsources hclosed

/-- `Environment.addInductive` is the source checks, the lowering run and
`addInductiveAfterLowering`. -/
theorem Environment.addInductive.WF (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig)
    (Q : Environment → Prop)
    (Hfinish : ∀ res, SourceSyntaxChecks env types →
      loweringRun env fuel.inductiveFuel nparams types lparams = .ok res →
      (Environment.addInductiveAfterLowering env lparams nparams types isUnsafe allowPrimitive
        fuel res).WF Q) :
    (Environment.addInductive env lparams nparams types isUnsafe allowPrimitive fuel).WF Q := by
  unfold Environment.addInductive
  refine Except.WF.bind (x := checkInductiveSources env types) (Q := fun _ =>
    SourceSyntaxChecks env types) (fun u h => by cases u; exact h) fun _ hsrc => ?_
  exact Except.WF.bind (x := loweringRun env fuel.inductiveFuel nparams types lparams)
    (Q := fun res => loweringRun env fuel.inductiveFuel nparams types lparams = .ok res)
    (fun _ h => h) fun res hres => Hfinish res hsrc hres

end VerifyInductive
end Lean4Lean
