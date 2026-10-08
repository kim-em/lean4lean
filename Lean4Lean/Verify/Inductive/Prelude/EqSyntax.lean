import Lean4Lean.Verify.Inductive.Rules.Translation
import Lean4Lean.Theory.Inductive.CanonicalEqSignature

/-! # Production syntax of the bootstrap equality

The declaration of `Eq` submitted by `Init.Prelude`, and the type and iota rule
of the recursor `Eq.rec` that the kernel generates for it, stated literally
(generic only in binder and universe-parameter names).  The three types
translate (`TrExprSyn`, hence every `TrExprS` derivation) to the corresponding
stored terms of `VEnv.HasCanonicalEq`; the iota-rule expressions are checked
against the stored rule by `Lean4Lean/Tests/PreludeEq.lean`. -/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

namespace VerifyInductive

/-- The concrete family type submitted by Lean's bootstrap declaration of
`Eq`. Binder names are operationally retained by `Expr`, although abstract
translation erases them. -/
def eqBootstrapType (u alphaName lhsName rhsName : Name) : Expr :=
  .forallE alphaName (.sort (.param u))
    (.forallE lhsName (.bvar 0)
      (.forallE rhsName (.bvar 1) (.sort .zero) .default) .default)
    .implicit

/-- The concrete constructor type submitted for `Eq.refl`. -/
def eqBootstrapReflType (u alphaName valueName : Name) : Expr :=
  .forallE alphaName (.sort (.param u))
    (.forallE valueName (.bvar 0)
      (.app (.app (.app (.const ``Eq [.param u]) (.bvar 1)) (.bvar 0))
        (.bvar 0)) .default)
    .implicit

end VerifyInductive

open VerifyInductive

/-! ### Production expressions -/

/-- Binder names of the production `Eq.rec` type and iota rule. They are
erased by translation. -/
structure EqRecBinderNames where
  alpha : Name
  lhs : Name
  motive : Name
  motiveRhs : Name
  motiveProof : Name
  refl : Name
  rhs : Name
  proof : Name

/-- The motive domain of the production `Eq.rec.{u, v}` (`u` is the motive
universe, `v` the sort of `α`), under `α` and `a`. -/
def eqRecMotiveExprU (u v : Name) (n : EqRecBinderNames) : Expr :=
  .forallE n.motiveRhs (.bvar 1)
    (.forallE n.motiveProof
      (.app (.app (.app (.const ``Eq [.param v]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.sort (.param u)) .default) .default

/-- The minor premise domain of the production `Eq.rec`, under `α`, `a` and
the motive. -/
def eqRecMinorExpr (v : Name) : Expr :=
  .app (.app (.bvar 0) (.bvar 1))
    (.app (.app (.const ``Eq.refl [.param v]) (.bvar 2)) (.bvar 1))

/-- The type of `Eq.rec.{u, v}` as produced by the kernel for the `Init.Prelude`
declaration of `Eq`:
`∀ {α : Sort v} {a : α} {motive : ∀ b, @Eq α a b → Sort u},
  motive a (Eq.refl a) → ∀ {b : α} (t : @Eq α a b), motive b t`. -/
def eqRecTypeExpr (u v : Name) (n : EqRecBinderNames) : Expr :=
  .forallE n.alpha (.sort (.param v))
    (.forallE n.lhs (.bvar 0)
      (.forallE n.motive (eqRecMotiveExprU u v n)
        (.forallE n.refl (eqRecMinorExpr v)
          (.forallE n.rhs (.bvar 3)
            (.forallE n.proof
              (.app (.app (.app (.const ``Eq [.param v]) (.bvar 4)) (.bvar 3)) (.bvar 0))
              (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) .default)
            .implicit) .default) .implicit) .implicit) .implicit

/-- The right-hand side of the single recursor rule of `Eq.rec`, as stored by
the kernel: `fun α a motive refl => refl`. -/
def eqRecRuleRhsExpr (u v : Name) (n : EqRecBinderNames) : Expr :=
  .lam n.alpha (.sort (.param v))
    (.lam n.lhs (.bvar 0)
      (.lam n.motive (eqRecMotiveExprU u v n)
        (.lam n.refl (eqRecMinorExpr v) (.bvar 0) .default) .default) .default) .implicit

/-- The left-hand side of the iota rule of `Eq.rec`, which the kernel does not
store: `fun α a motive refl => @Eq.rec α a motive refl a (@Eq.refl α a)`. -/
def eqRecRuleLhsExpr (u v : Name) (n : EqRecBinderNames) : Expr :=
  .lam n.alpha (.sort (.param v))
    (.lam n.lhs (.bvar 0)
      (.lam n.motive (eqRecMotiveExprU u v n)
        (.lam n.refl (eqRecMinorExpr v)
          (.app (.app (.app (.app (.app (.app (.const ``Eq.rec [.param u, .param v])
            (.bvar 3)) (.bvar 2)) (.bvar 1)) (.bvar 0)) (.bvar 2))
            (.app (.app (.const ``Eq.refl [.param v]) (.bvar 3)) (.bvar 2))) .default)
        .default) .default) .implicit

/-- The type of the iota rule of `Eq.rec`:
`∀ α a motive refl, motive a (@Eq.refl α a)`. -/
def eqRecRuleTypeExpr (u v : Name) (n : EqRecBinderNames) : Expr :=
  .forallE n.alpha (.sort (.param v))
    (.forallE n.lhs (.bvar 0)
      (.forallE n.motive (eqRecMotiveExprU u v n)
        (.forallE n.refl (eqRecMinorExpr v)
          (.app (.app (.bvar 1) (.bvar 2))
            (.app (.app (.const ``Eq.refl [.param v]) (.bvar 3)) (.bvar 2))) .default)
        .default) .default) .implicit

/-! ### Translation targets -/

section
variable {u v : Name}

private theorem ofLevel_two_left : VLevel.ofLevel [u, v] (.param u) = some (.param 0) := by
  simp [VLevel.ofLevel]

private theorem ofLevel_two_right (huv : u ≠ v) :
    VLevel.ofLevel [u, v] (.param v) = some (.param 1) := by
  have h : (u == v) = false := by simpa using huv
  simp [VLevel.ofLevel, List.idxOf_cons, h]

private theorem ofLevel_one : VLevel.ofLevel [u] (.param u) = some (.param 0) := by
  simp [VLevel.ofLevel]

private theorem mapM_one :
    [Level.param u].mapM (VLevel.ofLevel [u]) = some [.param 0] := by
  simp [List.mapM_cons, ofLevel_one]

private theorem mapM_two_right (huv : u ≠ v) :
    [Level.param v].mapM (VLevel.ofLevel [u, v]) = some [.param 1] := by
  simp [List.mapM_cons, ofLevel_two_right huv]

private theorem mapM_two (huv : u ≠ v) :
    [Level.param u, .param v].mapM (VLevel.ofLevel [u, v]) =
      some [.param 0, .param 1] := by
  simp [List.mapM_cons, ofLevel_two_left, ofLevel_two_right huv]

end

/-- Build a `TrExprSyn` derivation whose target is given. -/
syntax "canonical_eq_tr_syn" : tactic
macro_rules | `(tactic| canonical_eq_tr_syn) => `(tactic|
  repeat' (first
    | apply TrExprSyn.forallE
    | apply TrExprSyn.lam
    | apply TrExprSyn.app
    | (apply TrExprSyn.bvar; rfl)
    | (apply TrExprSyn.sort; first
        | exact ofLevel_two_left | exact ofLevel_two_right ‹_› | exact ofLevel_one
        | rfl)
    | (apply TrExprSyn.const; first
        | exact mapM_one | exact mapM_two_right ‹_› | exact mapM_two ‹_›)))

theorem eqBootstrapType_syn (u alphaName lhsName rhsName : Name) :
    TrExprSyn [u] [] (eqBootstrapType u alphaName lhsName rhsName)
      canonicalEqType := by
  unfold eqBootstrapType canonicalEqType
  canonical_eq_tr_syn

theorem eqBootstrapReflType_syn (u alphaName valueName : Name) :
    TrExprSyn [u] [] (eqBootstrapReflType u alphaName valueName)
      canonicalEqReflType := by
  unfold eqBootstrapReflType canonicalEqReflType
  canonical_eq_tr_syn

theorem eqRecTypeExpr_syn {u v : Name} (huv : u ≠ v) (n : EqRecBinderNames) :
    TrExprSyn [u, v] [] (eqRecTypeExpr u v n) canonicalEqRecType := by
  unfold eqRecTypeExpr eqRecMotiveExprU eqRecMinorExpr canonicalEqRecType
    canonicalEqRecMotive canonicalEqRecMinor
  canonical_eq_tr_syn

/-! ### Every translation is the stored term -/

section
variable {env : VEnv} {e : VExpr}

theorem TrExprS.eq_canonicalEqType {u a b c : Name}
    (H : TrExprS env [u] [] (eqBootstrapType u a b c) e) : e = canonicalEqType :=
  H.toSyn.unique (eqBootstrapType_syn u a b c)

theorem TrExprS.eq_canonicalEqReflType {u a b : Name}
    (H : TrExprS env [u] [] (eqBootstrapReflType u a b) e) : e = canonicalEqReflType :=
  H.toSyn.unique (eqBootstrapReflType_syn u a b)

theorem TrExprS.eq_canonicalEqRecType {u v : Name} (huv : u ≠ v) {n : EqRecBinderNames}
    (H : TrExprS env [u, v] [] (eqRecTypeExpr u v n) e) : e = canonicalEqRecType :=
  H.toSyn.unique (eqRecTypeExpr_syn huv n)

end

/-! ### Production constants -/

/-- A production constant with the type `Init.Prelude` gives `Eq`. -/
def IsProductionEq (ci : ConstantInfo) : Prop :=
  ci.safety = .safe ∧ ∃ u a b c, ci.levelParams = [u] ∧ ci.type = eqBootstrapType u a b c

/-- A production constant with the type `Init.Prelude` gives `Eq.refl`. -/
def IsProductionEqRefl (ci : ConstantInfo) : Prop :=
  ci.safety = .safe ∧ ∃ u a b, ci.levelParams = [u] ∧ ci.type = eqBootstrapReflType u a b

/-- A production constant with the type the kernel generates for `Eq.rec`. -/
def IsProductionEqRec (ci : ConstantInfo) : Prop :=
  ci.safety = .safe ∧
    ∃ u v n, u ≠ v ∧ ci.levelParams = [u, v] ∧ ci.type = eqRecTypeExpr u v n

end Lean4Lean
