import Lean4Lean.Theory.Typing.Strengthening.CastComputation

/-! # Nonlinear cast matching and raw eta elimination

Beta plus syntactically reflexive K contraction does not admit the raw eta
elimination theorem used by the finite-demand head model. Eta may make two
endpoints identical and thereby enable K. This is a syntax counterexample for
that fragment, not a typed counterexample or a boundary for all CastCompute rules.
EqRecEtaBoundary gives a separate typed example using the general K rule.
-/
namespace Lean4Lean.VEnv.Strengthening.CastEtaBoundary
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- The minimal computational fragment testing nonlinear K against eta. -/
inductive Compute : Bool → VExpr → VExpr → Prop where
  | refl : Compute eta e e
  | trans : Compute eta a b → Compute eta b c → Compute eta a c
  | beta : Compute eta (.app (.lam A b) a) (b.inst a)
  | cast : Compute eta (typeCast u X X p x) x
  | eqRec : Compute eta (eqRecApp v w α a motive minor a proof) minor
  | eta : Compute true e (.lam A (.app e.lift (.bvar 0)))
  | app : Compute eta f f' → Compute eta a a' → Compute eta (.app f a) (.app f' a')
  | lam : Compute eta A A' → Compute eta b b' → Compute eta (.lam A b) (.lam A' b')
  | forallE : Compute eta A A' → Compute eta B B' → Compute eta (.forallE A B) (.forallE A' B')
  | proj : Compute eta m m' → Compute eta (.proj s i m) (.proj s i m')

/-- A conservative root test: every beta or cast redex is marked. -/
def rootRedex : VExpr → Bool
  | .app (.lam _ _) _ => true
  | .app (.app (.app (.app (.app (.app (.const ``Eq.rec _) _) X) _) _) Y) _ => X == Y
  | _ => false

/-- A decidable sufficient certificate that no beta/K computation can occur. -/
def normal (e : VExpr) : Bool := !rootRedex e && match e with
  | .app f a => normal f && normal a
  | .lam A b | .forallE A b => normal A && normal b
  | .proj _ _ m => normal m
  | _ => true

/-- Without eta, every certified term is fixed by the whole compatible closure. -/
theorem Compute.eq_of_normal (R : Compute false e out) (hn : normal e = true) : out = e := by
  generalize hm : false = mode at R
  induction R with
  | refl => rfl
  | trans _ _ ih1 ih2 =>
    have h := ih1 hn hm
    exact (ih2 (h.symm ▸ hn) hm).trans h
  | beta => simp [normal, rootRedex] at hn
  | cast => simp [normal, rootRedex, typeCast, eqRecApp] at hn
  | eqRec => simp [normal, rootRedex, eqRecApp] at hn
  | eta => cases hm
  | app _ _ ihf iha =>
    simp only [normal, Bool.and_eq_true] at hn
    rw [ihf hn.2.1 hm, iha hn.2.2 hm]
  | lam _ _ ihA ihb =>
    simp only [normal, Bool.and_eq_true] at hn
    rw [ihA hn.2.1 hm, ihb hn.2.2 hm]
  | forallE _ _ ihA ihB =>
    simp only [normal, Bool.and_eq_true] at hn
    rw [ihA hn.2.1 hm, ihB hn.2.2 hm]
  | proj _ ihm =>
    simp only [normal, Bool.and_eq_true] at hn
    rw [ihm hn.2 hm]

/-- The short endpoint contains a neutral function argument. -/
def left : VExpr := .app (.bvar 1) (.bvar 0)
/-- The other endpoint expands exactly that argument. -/
def right : VExpr := .app (.bvar 1) (.lam (.sort .zero) (.app (.bvar 1) (.bvar 0)))
/-- A Pi payload makes the obstruction a head-exposure test. -/
def payload : VExpr := .forallE (.sort .zero) (.sort .zero)
/-- This source has no beta or syntactically reflexive cast redex anywhere. -/
def source : VExpr := typeCast (.succ .zero) left right (.bvar 2) payload

/-- Eta relates the endpoint pair. No typing claim is made for this raw example. -/
theorem endpoint_eta : Compute true left right := .app .refl .eta

/-- The same endpoint expansion is available beneath the cast motive's binder. -/
theorem lifted_endpoint_eta : Compute true left.lift right.lift := by
  exact Compute.app .refl (.eta (e := .bvar 1) (A := .sort .zero))

/-- Expand both copies of the short endpoint, then contract the now-matched cast. -/
theorem source_exposes_pi : Compute true source payload := by
  apply Compute.trans (b := typeCast (.succ .zero) right right (.bvar 2) payload) ?_ .cast
  have hm : Compute true (castMotive (.succ .zero) left) (castMotive (.succ .zero) right) :=
    .lam .refl (.lam (.app (.app .refl lifted_endpoint_eta) .refl) .refl)
  exact .app (.app (.app (.app (.app .refl endpoint_eta) hm) .refl) .refl) .refl

/-- Direct reduction of the source is stuck even though eta enables a Pi head. -/
theorem source_no_pi : ¬ Compute false source (.forallE A B) := by
  intro R
  have hn : normal source = true := by decide
  have he := R.eq_of_normal hn
  cases he

/-- The untyped beta/K fragment refutes universal eta-free Pi exposure.
Additional declaration rules or endpoint typings could repair this particular
example; neither possibility is excluded by this theorem. -/
theorem raw_eta_elimination_failure :
    Compute true source payload ∧ ¬ ∃ A B, Compute false source (.forallE A B) :=
  ⟨source_exposes_pi, fun ⟨_, _, R⟩ => source_no_pi R⟩

end Lean4Lean.VEnv.Strengthening.CastEtaBoundary
