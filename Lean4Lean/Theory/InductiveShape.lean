import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.VDecl

/-!
# Syntactic shapes of inductive declarations

Pure definitions describing the shapes of inductive headers and constructors.
They are separated from `Lean4Lean.Theory.Inductive` so that the environment
well-formedness predicates in `Lean4Lean.Theory.Typing.Lemmas` can record
declaration-level facts when projection metadata is registered.
-/

namespace Lean4Lean

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

def VExpr.wrapLams (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .lam body

def VExpr.wrapForalls (domains : List VExpr) (body : VExpr) : VExpr :=
  domains.foldr .forallE body

/-- The common parameters as de Bruijn variables beneath `depth` additional
constructor-field binders. -/
def VInductDecl.paramVars (decl : VInductDecl) (depth : Nat) : List VExpr :=
  (List.range decl.nparams).reverse.map fun i => .bvar (depth + i)

def VInductDecl.ParamsDefEq (env : VEnv) (decl : VInductDecl)
    (params params' : List VExpr) : Prop :=
  VEnv.IsDefEqCtx env decl.uvars [] params.reverse params'.reverse

/-- Constant support inherited from source syntax. Projection owner names are
metadata rather than expression subterms, matching `Expr.findAny`. -/
inductive VExpr.SourceConstFree (names : List Name) : VExpr → Prop
  | bvar (index : Nat) : SourceConstFree names (.bvar index)
  | sort (level : VLevel) : SourceConstFree names (.sort level)
  | const (name : Name) (levels : List VLevel) (fresh : name ∉ names) :
      SourceConstFree names (.const name levels)
  | proj (typeName : Name) (index : Nat) :
      SourceConstFree names struct →
      SourceConstFree names (.proj typeName index struct)
  | app : SourceConstFree names fn → SourceConstFree names arg →
      SourceConstFree names (.app fn arg)
  | lam : SourceConstFree names domain → SourceConstFree names body →
      SourceConstFree names (.lam domain body)
  | forallE : SourceConstFree names domain →
      SourceConstFree names body → SourceConstFree names (.forallE domain body)

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
        arg.SourceConstFree (decl.types.map (·.name))

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

/-- Raw common-parameter shape of one constructor before normalization.
This is separate from `CtorShape`: normalization may change the visible
forall prefix, while the executable checker compares the original prefix
directly with the mutual header parameters. -/
def VInductDecl.CtorParameterShape (env : VEnv) (decl : VInductDecl)
    (params : List VExpr) (ctor : VConstVal) : Prop :=
  ∃ ownParams tail,
    ctor.type.takeForalls decl.nparams = some (ownParams, tail) ∧
    decl.ParamsDefEq env params ownParams

/-- Raw syntactic shape of a source constructor: exactly the telescope walked
by the executable constructor check.  The constructor type is a syntactic
forall telescope covering the common parameters, whose codomain is a valid
application of the owning family beneath the field binders, at the
declaration's own universe parameters. -/
def VInductDecl.RawCtorShape (decl : VInductDecl) (type : VInductiveType)
    (ctor : VConstVal) : Prop :=
  ∃ doms result,
    ctor.type = VExpr.wrapForalls doms result ∧
    decl.nparams ≤ doms.length ∧
    decl.ValidIndAppAt (some type.name) (doms.length - decl.nparams) result ∧
    result.getAppFnArgs.1 = .const type.name (VLevel.params decl.uvars)

/-- Source-facing common-parameter formation retained by both ordinary and
nested declarations.  The family headers identify the shared semantic
parameter telescope, while every original constructor retains its raw
pre-normalization prefix against that same telescope. -/
def VInductDecl.SourceParameterWF (env : VEnv)
    (decl : VInductDecl) : Prop :=
  ∃ params envTypes,
    env.addConstVals decl.typeConstants = some envTypes ∧
    (∀ type ∈ decl.types, decl.TypeShape env params type) ∧
    (∀ type ∈ decl.types, ∀ ctor ∈ type.ctors,
      decl.CtorParameterShape envTypes params ctor) ∧
    ∀ type ∈ decl.types, ∀ ctor ∈ type.ctors, decl.RawCtorShape type ctor

end Lean4Lean
