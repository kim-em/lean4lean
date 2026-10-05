import Lean4Lean.Theory.Typing.AnchoredProfiles
import Lean4Lean.Theory.Typing.Strong

/-! Lower-rank relation signatures and frozen argument admission.
These declarations do not construct a relation or refer to higher ranks. -/

namespace Lean4Lean.AnchoredSemantics
open VExpr VEnv AnchoredProfiles

def Relevant (level : VLevel) (relevant : Bool) : Prop :=
  if relevant then ¬level ≈ .zero else level ≈ .zero

/-- The only instances used below are constructed by recursion on rank.
The record is a device for passing the already constructed lower rank. -/
structure Relations (n : Nat) where
  code : List VExpr → VExpr → VExpr → Profile n → Prop
  term : List VExpr → VExpr → VExpr → VExpr → Profile n → Profile n → Prop

def Admission (env : VEnv) (U : Nat) (lower : Relations n)
    (Γ : List VExpr) (key : Key n) (left right : VExpr) : Prop :=
  env.IsDefEq U Γ key.anchor left key.domain ∧
  env.IsDefEq U Γ left right key.domain ∧
  ∃ support : Profile n,
    key.input.HasType support ∧ support.HasType (.sort true) ∧
    lower.code Γ key.domain key.domain support ∧
    lower.term Γ key.anchor left key.domain key.input support ∧
    lower.term Γ left right key.domain key.input support

end Lean4Lean.AnchoredSemantics
