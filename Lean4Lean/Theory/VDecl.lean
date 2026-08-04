import Lean4Lean.Theory.VEnv

namespace Lean4Lean

structure VConstVal extends VConstant where
  name : Name

structure VDefVal extends VConstVal where
  value : VExpr

def VDefVal.toDefEq (v : VDefVal) : VDefEq :=
  ⟨v.uvars, .const v.name (VLevel.params v.uvars), v.value, v.type⟩

structure VInductiveType extends VConstVal where
  /-- Number of indices after the common parameters. This is recovered from
  the checked source arity by the executable implementation. -/
  numIndices : Nat
  /-- Sort level at the end of the parameter/index telescope. -/
  resultLevel : VLevel
  ctors : List VConstVal

structure VInductDecl where
  uvars : Nat
  nparams : Nat
  types : List VInductiveType
  /-- Unsafe inductive declarations skip the strict-positivity check. They are
  represented explicitly so that the abstract declaration judgment does not
  accidentally ascribe the safe formation rule to them. -/
  isUnsafe : Bool

inductive VDecl where
  /-- Reserve a constant name, which cannot be used in expressions.
  Used to represent unsafe declarations in safe mode -/
  | block (n : Name)
  | axiom (_ : VConstVal)
  | def (_ : VDefVal)
  | opaque (_ : VDefVal)
  | example (_ : VDefVal)
  | quot
  | induct (_ : VInductDecl)
