import Lean4Lean.Theory.Typing.ShapeModel.EnvSchemaMajors
import Lean4Lean.Theory.Typing.ShapeModel.EnvSigFinite
import Lean4Lean.Theory.Typing.ShapeModel.Signature

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

namespace Lean4Lean.ShapeModel
open InductiveSignature

/-- The leading lambda domains of a term. -/
def lamDoms : VExpr → List VExpr
  | .lam d b => d :: lamDoms b
  | _ => []

/-- Remove `n` leading lambda binders. -/
def dropLams : Nat → VExpr → VExpr
  | n + 1, .lam _ b => dropLams n b
  | _, e => e

/-- The family of a constructor type: the head constant of the body of its forall telescope. -/
def familyOfType (ty : VExpr) : Option Name :=
  match ty.forallResult.getAppFnArgs.1 with
  | .const F _ => some F
  | _ => none

/-- The variable an argument literally is. -/
def argVar : VExpr → Option Nat
  | .bvar b => some b
  | _ => none

/-- The constant and levels of a head (default for a non-constant). -/
def constHead : VExpr → Name × List VLevel
  | .const c lv => (c, lv)
  | _ => (default, [])

/-- The field index table of a rule with arguments `pre` before the major, `npre` prefix
variables, `nf` fields and `leftover` leftover parameters (see the module docstring). -/
def fieldIndexOf (pre : List VExpr) (npre nf leftover : Nat) : List (Option Nat) :=
  (List.range nf).map fun i =>
    match pre.findIdx? (fun a => decide (a = .bvar (nf - 1 - i))) with
    | some j => some j
    | none => if i < leftover ∧ npre + i < pre.length then some (npre + i) else none

/-- The rule of an equation with a constructor major and `nf` fields. `np c` is the number of
parameters of `c` as a registered structure constructor (`0` if it is none). -/
def majorRule (np : Name → Nat) (h : Head) (u : Nat) (df : VDefEq) (nf : Nat) : Rule :=
  let Ds := lamDoms df.lhs
  let args := df.lhs.stripLams.getAppFnArgs.2
  let pre := args.dropLast
  let mj := (args.getLastD (.sort .zero)).getAppFnArgs
  { head := h, uvars := u, nbind := Ds.length, vars := pre.map argVar,
    major := some ⟨(constHead mj.1).1, (constHead mj.1).2, (List.range nf).reverse⟩,
    fieldIndex := fieldIndexOf pre (Ds.length - nf) nf ((np (constHead mj.1).1) - (mj.2.length - nf)),
    rhs := dropLams Ds.length df.rhs }

/-- The rule of a definition: no binders, no arguments. -/
def defRule (v : VDefVal) : Rule :=
  ⟨.const v.name, v.uvars, 0, [], none, [], v.value⟩

/-! ## Lemmas -/

theorem lamDoms_wrapLams {body : VExpr} (hb : ∀ d b, body ≠ .lam d b) (Ds : List VExpr) :
    lamDoms (VExpr.wrapLams Ds body) = Ds := by
  induction Ds with
  | nil =>
    cases body <;> simp_all [VExpr.wrapLams, lamDoms]
  | cons D Ds ih => simp [VExpr.wrapLams, lamDoms] at ih ⊢; exact ih

theorem dropLams_wrapLams (Ds : List VExpr) (R : VExpr) :
    dropLams Ds.length (VExpr.wrapLams Ds R) = R := by
  induction Ds with
  | nil => cases R <;> rfl
  | cons D Ds ih => exact ih

theorem mkApps_ne_lam {hd : VExpr} (hhd : ∀ d b, hd ≠ .lam d b) (xs : List VExpr) :
    ∀ d b, VExpr.mkApps hd xs ≠ .lam d b := by
  induction xs generalizing hd with
  | nil => exact hhd
  | cons x xs ih => exact ih (fun d b h => by cases h)

theorem mkApps_ne_forallE {hd : VExpr} (hhd : ∀ d b, hd ≠ .forallE d b) (xs : List VExpr) :
    ∀ d b, VExpr.mkApps hd xs ≠ .forallE d b := by
  induction xs generalizing hd with
  | nil => exact hhd
  | cons x xs ih => exact ih (fun d b h => by cases h)

theorem familyOfType_shape (doms : List VExpr) (F : Name) (ls : List VLevel) (args : List VExpr) :
    familyOfType (VExpr.wrapForalls doms (VExpr.mkApps (.const F ls) args)) = some F := by
  unfold familyOfType
  rw [VExpr.forallResult_wrapForalls,
    VExpr.forallResult_of_head (VExpr.getAppFnArgs_mkApps_head _ _),
    VExpr.getAppFnArgs_mkApps_const]

theorem forallArity_shape (doms : List VExpr) (F : Name) (ls : List VLevel) (args : List VExpr) :
    (VExpr.wrapForalls doms (VExpr.mkApps (.const F ls) args)).forallArity = doms.length := by
  rw [VExpr.forallArity_wrapForalls,
    VExpr.forallArity_eq_zero_of_getAppFnArgs (VExpr.getAppFnArgs_mkApps_const _ _ _)]
  rfl

theorem vars_succ_length (count below : Nat) : (vars count below).length = count := by
  simp [vars]

/-- The rule of an equation in rule shape. -/
theorem majorRule_eq {np : Name → Nat} {h : Head} {u : Nat} {df : VDefEq} {hd : VExpr}
    (hhd : hd.getAppFnArgs = (hd, [])) (hlam : ∀ d b, hd ≠ .lam d b)
    {Ds pre ps : List VExpr} {c : Name} {lv : List VLevel} {nf : Nat} {R : VExpr}
    (hl : df.lhs = VExpr.wrapLams Ds (VExpr.mkApps hd
      (pre ++ [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)])))
    (hr : df.rhs = VExpr.wrapLams Ds R) :
    majorRule np h u df nf =
      { head := h, uvars := u, nbind := Ds.length, vars := pre.map argVar,
        major := some ⟨c, lv, (List.range nf).reverse⟩,
        fieldIndex := fieldIndexOf pre (Ds.length - nf) nf (np c - ps.length),
        rhs := R } := by
  have hDs : lamDoms df.lhs = Ds := by
    rw [hl]; exact lamDoms_wrapLams (mkApps_ne_lam hlam _) Ds
  have hstrip : df.lhs.stripLams = VExpr.mkApps hd
      (pre ++ [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)]) := by
    rw [hl, stripLams_wrapLams', mkApps_snoc]; rfl
  have hargs : df.lhs.stripLams.getAppFnArgs.2 =
      pre ++ [VExpr.mkApps (.const c lv) (ps ++ vars nf 0)] := by
    rw [hstrip, spine_mkApps_exact _ _ hhd]
  simp only [majorRule, hDs, hargs, List.dropLast_concat, List.getLastD_concat,
    VExpr.getAppFnArgs_mkApps_const, constHead, hr, dropLams_wrapLams, List.length_append,
    vars_succ_length, Nat.add_sub_cancel]

/-- The arguments and major of the rule of an equation, read off its left body. -/
theorem majorRule_strip {np : Name → Nat} {h : Head} {u : Nat} {df : VDefEq} {hd : VExpr}
    (hhd : hd.getAppFnArgs = (hd, [])) {pre margs : List VExpr} {c : Name} {lv : List VLevel}
    {nf : Nat} (hs : df.lhs.stripLams = .app (VExpr.mkApps hd pre) (VExpr.mkApps (.const c lv) margs)) :
    (majorRule np h u df nf).vars = pre.map argVar ∧
      (majorRule np h u df nf).major = some ⟨c, lv, (List.range nf).reverse⟩ := by
  have hargs : df.lhs.stripLams.getAppFnArgs.2 = pre ++ [VExpr.mkApps (.const c lv) margs] := by
    rw [hs, ← mkApps_snoc, spine_mkApps_exact _ _ hhd]
  simp only [majorRule, hargs, List.dropLast_concat, List.getLastD_concat,
    VExpr.getAppFnArgs_mkApps_const, constHead, and_self]

end Lean4Lean.ShapeModel
