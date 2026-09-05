import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Theory.Typing.RecursorLemmas
import Lean4Lean.Theory.Quot

/-!
# Recursor rules as a checking invariant

The executable checker reduces a recursor application by looking up the `RecursorRule` for the
constructor at the head of the major premise. The abstract environment stores each such rule as a
closed lambda-wrapped equation. This file states, for a checking environment, that every visible
recursor's rules are stored equations of the shape `VIotaRuleShape`, that the recursor's type and
each constructor's type have the shapes `VRecursorShape` and `VConstructorShape`, that the major
inductive type constant is rigid, and (for K-like recursors) that the inductive type is a
proposition whose parameters type the unique constructor. The quotient reduction rules are covered
by the same shapes for `Quot.lift`, and by proof irrelevance for `Quot.ind`.
-/

namespace Lean4Lean
open Lean

/-- The stored equation `df` is the iota rule of `rec` for `rule`: it has the rule shape, its
right-hand side translates the executable rule's right-hand side, and the rule's constructor has
the constructor shape at `cnparams` parameters. -/
structure RecursorRuleAlignment (venv : VEnv) (rec : RecursorVal) (rule : RecursorRule)
    (indLevels : List VLevel) (cnparams : Nat) (df : VDefEq) : Prop where
  shape : Nonempty (VIotaRuleShape venv rec.name rec.levelParams.length rec.numParams cnparams
    rec.numMotives rec.numMinors rec.numIndices rule.ctor indLevels rule.nfields df)
  rhs : TrExprS venv rec.levelParams [] rule.rhs df.rhs
  ctor : ∃ ctorUvars, indLevels.length = ctorUvars ∧
    Nonempty (VConstructorShape venv rule.ctor ctorUvars cnparams rule.nfields rec.numIndices
      rec.getMajorInduct)

/-- The recursor `rec` has the recursor shape, its major inductive is rigid, and every rule is a
stored equation. -/
def RecursorAlignment (venv : VEnv) (rec : RecursorVal) : Prop :=
  ∃ indLevels cnparams, cnparams ≤ rec.numParams ∧
    Nonempty (VRecursorShape venv rec.name rec.levelParams.length rec.numParams cnparams
      rec.numMotives rec.numMinors rec.numIndices rec.getMajorInduct indLevels) ∧
    venv.Rigid rec.getMajorInduct ∧
    ∀ rule ∈ rec.rules, ∃ df, RecursorRuleAlignment venv rec rule indLevels cnparams df

/-- A K-like recursor eliminates from a proposition with a single constructor whose only
arguments are the parameters; the parameters of any application of the inductive type are typed
along the constructor's telescope. -/
def KLikeAlignment (venv : VEnv) (rec : RecursorVal) (ctorName : Name) : Prop :=
  ∃ indUvars indDoms ctorDoms ctorBody,
    venv.constants rec.getMajorInduct = some ⟨indUvars, VExpr.wrapForalls indDoms (.sort .zero)⟩ ∧
    indDoms.length = rec.numParams + rec.numIndices ∧
    venv.constants ctorName = some ⟨indUvars, VExpr.wrapForalls ctorDoms ctorBody⟩ ∧
    ctorDoms.length = rec.numParams ∧
    ∀ U Γ (ls : List VLevel) (args : List VExpr),
      VExpr.WF venv U Γ (VExpr.mkApps (.const rec.getMajorInduct ls) args) →
      args.length = rec.numParams + rec.numIndices →
      ∀ k (hk : k < args.length) (hk' : k < ctorDoms.length),
        venv.HasType U Γ args[k] ((ctorDoms[k].instL ls).instOuter (args.take k))

/-- Every visible recursor of the constant map is aligned with the abstract environment. -/
def RecursorRulesCoherent (safety : DefinitionSafety) (C : ConstMap) (venv : VEnv) : Prop :=
  ∀ {name rec}, C.find? name = some (.recInfo rec) → safety ≤ (ConstantInfo.recInfo rec).safety →
    RecursorAlignment venv rec ∧
    (rec.k = true → ∃ info ctorName, C.find? rec.getMajorInduct = some (.inductInfo info) ∧
      info.ctors = [ctorName] ∧ KLikeAlignment venv rec ctorName)

/-- The quotient constants and the `Quot.lift` equation are present, and `Quot` is rigid. -/
structure QuotCoherent (venv : VEnv) : Prop where
  quot : venv.constants ``Quot = some quotConst
  quotMk : venv.constants ``Quot.mk = some quotMkConst
  lift : venv.constants ``Quot.lift = some quotLiftConst
  ind : venv.constants ``Quot.ind = some quotIndConst
  defeq : venv.defeqs quotDefEq
  rigid : venv.Rigid ``Quot

variable {venv : VEnv}

/-- `Quot.lift` has the recursor shape with five parameters, of which the first two are the
parameters of `Quot.mk`. -/
def QuotCoherent.liftRecursorShape (H : QuotCoherent venv) :
    VRecursorShape venv ``Quot.lift 2 5 2 0 0 0 ``Quot [.param 0] where
  type := quotLiftConst.type
  const := H.lift
  doms := [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
    .sort (.param 1), .forallE (.bvar 2) (.bvar 1),
    .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
        (.app (.bvar 3) (.bvar 1))))),
    .app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]
  result := .bvar 3
  type_eq := rfl
  doms_length := rfl
  major_eq := rfl

/-- `Quot.mk` has the constructor shape with two parameters and one field. -/
def QuotCoherent.mkConstructorShape (H : QuotCoherent venv) :
    VConstructorShape venv ``Quot.mk 1 2 1 0 ``Quot where
  type := quotMkConst.type
  const := H.quotMk
  doms := [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1]
  indices := []
  type_eq := rfl
  doms_length := rfl
  indices_length := rfl

/-- The `Quot.lift` equation has the iota rule shape. -/
def QuotCoherent.liftRuleShape (H : QuotCoherent venv) :
    VIotaRuleShape venv ``Quot.lift 2 5 2 0 0 0 ``Quot.mk [.param 0] 1 quotDefEq where
  defeq := H.defeq
  uvars := rfl
  doms := [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
    .sort (.param 1), .forallE (.bvar 2) (.bvar 1),
    .forallE (.bvar 3) (.forallE (.bvar 4) (.forallE (.app (.app (.bvar 4) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [.param 1]) (.bvar 4)) (.app (.bvar 3) (.bvar 2)))
        (.app (.bvar 3) (.bvar 1))))),
    .bvar 4]
  lhsBody := quotDefEq.lhs.stripLams
  rhsBody := .app (.bvar 2) (.bvar 0)
  typeBody := .bvar 3
  lhs_eq := rfl
  rhs_eq := rfl
  type_eq := rfl
  doms_length := rfl
  indexArgs := []
  indexArgs_length := rfl
  lhs_pattern := rfl

end Lean4Lean
