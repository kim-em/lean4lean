import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.Typing.ShapeModel.ShapeTyping

/-!
# The semantic signature of the shape model

The interpretation of `VExpr` in the shape domain (`Interp.lean`) does not read the
environment's inductive declarations, eliminators and projections directly. It reads a
*semantic signature* `SemSig`: which constants are constructors (with their family and arity),
the sort level and constructor list of each inductive family, which constructors are
structure constructors with eta, the computation rules (pre-decomposed into their left-hand
argument pattern and right-hand body), the generic types of abstract eliminators, and the
constructor read by each projection. A later milestone builds a `SemSig` from a well-formed
environment and proves `SemSig.Coherent` for it.

`SemSig` is a class, so that the shape domain parameters `ShapeParams` (`isStruct`, `famProp`)
are found by instance resolution from it; `SemSig.Coherent` is a `Prop`-valued class for the same
reason. Each field of `SemSig.Coherent` is used by `Const.compat_join` (`Interp.lean`).
-/

namespace Lean4Lean.ShapeModel
open Lean4Lean

/-- The head of a constant spine: a named constant or an eliminator of a mutual block. -/
inductive Head
  | const (c : Name)
  | elim (block : Name) (owner : Nat)
  deriving DecidableEq

/-- Constructor data: the inductive family it builds, and its numbers of parameters and fields. -/
structure CtorInfo where
  family : Name
  nparams : Nat
  nfields : Nat

/-- The constructor application that is the last argument of a computation rule. -/
structure RuleMajor where
  ctor : Name
  /-- the major constructor's universe levels, over the rule's universe params -/
  levels : List VLevel
  /-- de Bruijn indices (under the rule binders) of its trailing field variables, in order -/
  fields : List Nat

/-- A computation rule `fun Ds => head args ≡ fun Ds => rhs`, pre-decomposed. -/
structure Rule where
  head : Head
  uvars : Nat
  nbind : Nat
  /-- one entry per argument before the major: `some b` iff the argument is `bvar b` -/
  vars : List (Option Nat)
  /-- the last argument, if the rule has one (definitions have none) -/
  major : Option RuleMajor
  /-- right-hand body, under the `nbind` binders -/
  rhs : VExpr

def Rule.arity (r : Rule) : Nat := r.vars.length + if r.major.isSome then 1 else 0

/-- The semantic signature read by the interpretation. -/
class SemSig where
  ctor : Name → Option CtorInfo
  /-- result sort level of an inductive family (over its params) -/
  famLevel : Name → Option VLevel
  /-- the constructors of a family, in order -/
  famCtors : Name → List Name
  /-- structure constructor with eta (collapse) -/
  isStruct : Name → Bool
  rules : Rule → Prop
  /-- closed generic type of an abstract eliminator -/
  elimType : Name → Nat → Option VExpr
  /-- `proj S i` reads fields of this constructor of `S` -/
  structCtor : Name → Option Name

/-- The rigid former `c` is a proposition at the evaluated levels `lvls`: its family level is
identically zero there (`true` for non-families). -/
noncomputable def SemSig.famProp [S : SemSig] (c : Name) (lvls : List SLvl) : Bool :=
  match S.famLevel c with
  | some l => decide (SLvl.IsZero fun v => l.eval (lvls.map (· v)))
  | none => true

/-- The number of fields of a constructor (`0` for a non-constructor). -/
def SemSig.nfields [S : SemSig] (c : Name) : Nat :=
  match S.ctor c with
  | some ci => ci.nfields
  | none => 0

noncomputable instance SemSig.shapeParams [S : SemSig] : ShapeParams where
  isStruct := S.isStruct
  famProp := SemSig.famProp
  nfields := SemSig.nfields

/-- The evaluated universe levels of the major constructor of a rule, at the levels `ls`. -/
def RuleMajor.lvls (mj : RuleMajor) (ls : List VLevel) : List SLvl :=
  mj.levels.map fun l => (l.inst ls).eval

theorem RuleMajor.lvls_congr {mj : RuleMajor} {ls ls' : List VLevel}
    (h : List.Forall₂ (· ≈ ·) ls ls') : mj.lvls ls = mj.lvls ls' := by
  simp only [lvls, List.map_inj_left]
  exact fun l _ => VLevel.inst_congr (l := l) (VLevel.equiv_def'.2 rfl) h

/-- Coherence of a semantic signature: the facts about rules and constructors that make the
interpretation of a constant spine deterministic up to compatibility. -/
class SemSig.Coherent [S : SemSig] : Prop where
  /-- Two rules with the same head have the same number of arguments before the major, and
  either both or neither has a major argument. -/
  same_shape : S.rules r₁ → S.rules r₂ → r₁.head = r₂.head →
    r₁.vars.length = r₂.vars.length ∧ r₁.major.isSome = r₂.major.isSome
  /-- Two rules with the same head and majors have majors of the same family, at equivalent
  levels. -/
  major_family : S.rules r₁ → S.rules r₂ → r₁.head = r₂.head →
    r₁.major = some mj₁ → r₂.major = some mj₂ →
    S.ctor mj₁.ctor = some ci₁ → S.ctor mj₂.ctor = some ci₂ →
    ci₁.family = ci₂.family ∧ List.Forall₂ (· ≈ ·) mj₁.levels mj₂.levels
  /-- Two rules with the same head and the same major constructor are equal. -/
  major_ctor_eq : S.rules r₁ → S.rules r₂ → r₁.head = r₂.head →
    r₁.major = some mj₁ → r₂.major = some mj₂ → mj₁.ctor = mj₂.ctor → r₁ = r₂
  /-- Two rules with the same head and no major are equal. -/
  no_major_eq : S.rules r₁ → S.rules r₂ → r₁.head = r₂.head →
    r₁.major = none → r₂.major = none → r₁ = r₂
  /-- A constructor heads no rule. -/
  ctor_no_rule : S.ctor c = some ci → S.rules r → r.head ≠ .const c
  /-- A structure constructor is the only constructor of its family. -/
  struct_unique : S.isStruct c → S.ctor c = some ci → S.ctor c' = some ci' →
    ci'.family = ci.family → c' = c

end Lean4Lean.ShapeModel
