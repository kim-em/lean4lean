import Lean4Lean.Theory.Typing.EnvTables.EnvSchemaMajors
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VLevel

/-!
# Syntactic decomposition of computation rules

The functions that turn a stored equation into a pre-decomposed `Rule` of the semantic signature
(`EnvSig.lean`), and the syntactic family of a constructor type.

A rule with a major is read off the equation `df` and its field count `nf` alone:
`df.lhs = fun Ds => head pre major`, `major = c lv margs`; the rule's binders are `Ds`, its
arguments before the major are `pre`, its fields are the trailing `nf` variables of the major
(`(List.range nf).reverse`, the de Bruijn indices of `vars nf 0`), and its right side is `df.rhs`
with the `Ds.length` binders removed. The field index table (`fieldIndexOf`) records, for every
rule field `i`, the first argument position `j` before the major that is literally the field
variable; failing that, if the field is a *leftover parameter* (the major's constructor is
registered as a structure constructor with `np` parameters while the rule's major supplies only
`p < np` parameter arguments, and `i < np - p`), the position of the rule's `i`-th index argument,
`npre + i` (where `npre = Ds.length - nf` is the number of prefix variables); else `none`.
-/

namespace Lean4Lean.EnvTables
open InductiveSignature

/-- The family of a constructor type: the head constant of the body of its forall telescope. -/
def familyOfType (ty : VExpr) : Option Name :=
  match ty.forallResult.getAppFnArgs.1 with
  | .const F _ => some F
  | _ => none

/-! ## Lemmas -/

theorem familyOfType_shape (doms : List VExpr) (F : Name) (ls : List VLevel) (args : List VExpr) :
    familyOfType (VExpr.wrapForalls doms (VExpr.mkApps (.const F ls) args)) = some F := by
  unfold familyOfType
  rw [VExpr.forallResult_wrapForalls,
    VExpr.forallResult_of_head (VExpr.getAppFnArgs_mkApps_head _ _),
    VExpr.getAppFnArgs_mkApps_const]

end Lean4Lean.EnvTables
