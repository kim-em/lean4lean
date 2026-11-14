import Lean4Lean.Theory.VExpr.Telescope

/-! Projection metadata of structures: the record `VEnv.projections` stores for a registered
structure. -/

namespace Lean4Lean

/-- Kernel data needed to type primitive projections.  Unlike a synthesized
eliminator term, this record contains only declaration data: all projection
types are computed from the constructor telescope below. -/
structure VProjectionInfo where
  uvars : Nat
  nparams : Nat
  nindices : Nat
  resultLevel : VLevel
  ctorName : Name
  ctorType : VExpr

structure VProjectionEntry where
  typeName : Name
  info : VProjectionInfo

/-- Number of constructor fields: the syntactic forall arity of the constructor
type beyond the common parameters. -/
def VProjectionInfo.numFields (info : VProjectionInfo) : Nat :=
  info.ctorType.forallArity - info.nparams

end Lean4Lean
