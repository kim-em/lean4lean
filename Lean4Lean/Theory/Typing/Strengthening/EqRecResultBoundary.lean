import Lean4Lean.Theory.Typing.Strengthening.EqRecReplay

/-! # Result typing does not align general Eq.rec indices

For type casts, a common type of the source and its payload recovers conversion
of the cast endpoints. This argument does not extend to arbitrary motives.
A constant motive erases both endpoint dependencies from the result type.
The final theorem gives a well-formed context and a type-valued application
whose source and minor share a sort but whose equality endpoints cannot convert.
It does not assert a nonequality of the recursor application and its minor.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr
variable {env : VEnv}

/-- A motive that returns T independently of the endpoint and its proof. -/
def constantEqMotive (w : VLevel) (α a T : VExpr) : VExpr :=
  .lam α (.lam (eqApp w α.lift a.lift (.bvar 0)) (T.liftN 2))

/-- Any type gives a well-typed constant equality motive. -/
theorem constantEqMotive_typed (henv : env.Ordered) (heq : env.HasCanonicalEq)
    (hw : w.WF U) (hα : env.HasType U Γ α (.sort w))
    (ha : env.HasType U Γ a α) (hT : env.HasType U Γ T (.sort v)) :
    env.HasType U Γ (constantEqMotive w α a T)
      (.forallE α (.forallE (eqApp w α.lift a.lift (.bvar 0)) (.sort v))) := by
  have hE := HasType.eqApp heq hw (hα.weak henv) (ha.weak henv)
    (show env.HasType U (α :: Γ) (.bvar 0) α.lift from .bvar .zero)
  have hT' := (hT.weak henv (B := α)).weak henv
    (B := eqApp w α.lift a.lift (.bvar 0))
  apply HasType.lam hα
  apply HasType.lam hE
  simpa [HasType, ← liftN_succ, liftN] using hT'

/-- Applying a constant motive computes to T even at nonconvertible endpoints. -/
theorem constantEqMotive_app (henv : env.WF) (heq : env.HasCanonicalEq)
    (hw : w.WF U) (hΓ : OnCtx Γ (env.IsType U))
    (hα : env.HasType U Γ α (.sort w)) (ha : env.HasType U Γ a α)
    (hT : env.HasType U Γ T (.sort v)) (hb : env.HasType U Γ b α)
    (hp : env.HasType U Γ p (eqApp w α a b)) :
    env.IsDefEq U Γ (.app (.app (constantEqMotive w α a T) b) p) T (.sort v) := by
  have hm := constantEqMotive_typed henv.ordered heq hw hα ha hT
  have h1 := hm.app hb
  simp [inst, instVar, eqApp, inst_liftN_lo] at h1
  have h2 := h1.app (by simpa [eqApp] using hp)
  simp only [inst] at h2
  have hbeta := SimAt.mkApps_wrapLams henv hΓ
    (args := [b, p]) (doms := [α, eqApp w α.lift a.lift (.bvar 0)])
    (body := T.liftN 2) rfl
  rw [SingletonLayout.liftN_instOuter_len (by rfl : [b, p].length = 2)] at hbeta
  exact hbeta _ h2

/-- General Eq.rec with a constant motive has the minor's type independently
of definitional endpoint alignment. An equality proof is still required. -/
theorem constant_eqRec_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (hv : v.WF U) (hw : w.WF U) (hΓ : OnCtx Γ (env.IsType U))
    (hα : env.HasType U Γ α (.sort w)) (ha : env.HasType U Γ a α)
    (hT : env.HasType U Γ T (.sort v)) (hx : env.HasType U Γ x T)
    (hb : env.HasType U Γ b α) (hp : env.HasType U Γ p (eqApp w α a b)) :
    env.HasType U Γ (eqRecApp v w α a (constantEqMotive w α a T) x b p) T := by
  have hM := constantEqMotive_typed henv.ordered heq hw hα ha hT
  have hrefl := HasType.eqReflApp heq hw hα ha
  have hx' := (constantEqMotive_app henv heq hw hΓ hα ha hT ha hrefl).symm.defeq hx
  have hr := HasType.eqRecApp heq hv hw hα ha hM hx' hb hp
  exact (constantEqMotive_app henv heq hw hΓ hα ha hT hb hp).defeq hr

namespace EqRecResultBoundary

/-- The two endpoints are types of the same sort, with different rigid shapes. -/
def left : VExpr := .sort .zero
def right : VExpr := .forallE (.sort .zero) (.sort .zero)
def carrier : VExpr := .sort (.succ .zero)
def equality : VExpr := eqApp (.succ (.succ .zero)) carrier left right
def context : List VExpr := [equality]

/-- The Pi endpoint is Type-valued, just like Prop. -/
theorem right_typed (env : VEnv) (U : Nat) (Γ : List VExpr) :
    env.HasType U Γ right carrier := by
  have h := HasType.forallE (env := env) (U := U) (Γ := Γ) (HasType.sort (l := .zero) (by trivial))
    (HasType.sort (l := .zero) (by trivial))
  exact (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq h

/-- Assuming a propositional equality of these endpoints gives a valid context;
context well-formedness does not require a closed inhabitant of that equality. -/
theorem context_wf (heq : env.HasCanonicalEq) : OnCtx context (env.IsType U) := by
  exact ⟨trivial, _, HasType.eqApp heq (by trivial) (HasType.sort (by trivial))
    (HasType.sort (by trivial)) (right_typed env U [])⟩

/-- Matching source/minor sort typings cannot establish the endpoint equality
required for general K. This refutes extending the cast uniqueness argument
to arbitrary Eq.rec motives, while leaving typed computational repair open. -/
theorem common_result_does_not_align (henv : env.WF) (heq : env.HasCanonicalEq) (U : Nat) :
    OnCtx context (env.IsType U) ∧
    env.HasType U context
      (eqRecApp (.succ (.succ .zero)) (.succ (.succ .zero)) carrier left
        (constantEqMotive (.succ (.succ .zero)) carrier left carrier) right right (.bvar 0)) carrier ∧
    env.HasType U context right carrier ∧
    ¬ env.IsDefEqU U context left right := by
  have hΓ := context_wf (U := U) heq
  have hp : env.HasType U context (.bvar 0) equality := by
    have h : env.HasType U context (.bvar 0) equality.lift := .bvar .zero
    simpa [equality, carrier, left, right, eqApp, liftN] using h
  refine ⟨hΓ, constant_eqRec_typed henv heq (by trivial) (by trivial) hΓ
    (HasType.sort (by trivial)) (HasType.sort (by trivial)) (HasType.sort (by trivial))
    (right_typed env U context) (right_typed env U context) hp,
    right_typed env U context, ?_⟩
  exact IsDefEqU.sort_forallE_inv henv hΓ

end EqRecResultBoundary
end Lean4Lean.VEnv.Strengthening
