import Lean4Lean.Theory.Typing.HeadInjectivity.Model.FamSort
import Lean4Lean.Theory.Typing.HeadInjectivity.Model.EmptyRule

/-! # Uniqueness conditions of a registered ι rule

The two uniqueness facts the soundness of an ι rule reads off the environment:

* `PatUniq`: the registered ι pattern of a recursor head is determined by the head and the
  constructor;
* `LeadUniq`: the leading arguments of the rule are determined by the recursor's type and the
  constructor (`IotaStatic`). -/

namespace Lean4Lean
namespace VEnv
namespace Model

variable {env : VEnv} {U : Nat} {Δ : List VExpr}

/-- The uniqueness of a registered ι pattern per head and constructor, as the left-to-right
direction reads it off the `pat` clause. -/
def PatUniq (env : VEnv) (n ctor : Name) (k nind cnp nf : Nat) (rhs : VExpr) : Prop :=
  ∀ k' nind' ctor' cnp' nf' rhs' (hc' : rhs'.Closed),
    env.pats (SimplePattern.iota n (k' + nind') ctor' (cnp' + nf')).toPattern
      (SimplePattern.iotaRHS' n ctor' k' nind' cnp' nf' rhs' hc', .true) →
    k' + nind' = k + nind ∧ (ctor' = ctor → k' = k ∧ nind' = nind ∧ cnp' = cnp ∧ nf' = nf ∧ rhs' = rhs)

/-- The uniqueness of the lead read off the recursor type for a constructor. -/
def LeadUniq (ci : VConstant) (ctor : Name) (k nind nf : Nat) (lead : List VExpr) : Prop :=
  ∀ doms' dsH' RH' I' lsI' iargs' lead',
    IotaStatic ci ctor k nind nf doms' dsH' RH' I' lsI' iargs' lead' → lead' = lead

end Model
end VEnv
end Lean4Lean
