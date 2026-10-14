import Lean4Lean.Theory.Typing.Strengthening.CastEtaBoundary
import Lean4Lean.Theory.Typing.Strengthening.EqRecResultBoundary

/-! # Typed eta obstruction for syntactic K matching

General Eq.rec permits a constant motive and function-valued endpoints.
Consequently the raw beta/K eta-removal obstruction survives source typing.
This concerns only the specified computational fragment, not full reduction
or strengthening. Endpoint conversion below does replay this example.
-/
namespace Lean4Lean.VEnv.Strengthening.EqRecEtaBoundary
open _root_.Lean4Lean _root_.Lean4Lean.VExpr CastEtaBoundary
variable {env : VEnv}

def carrier : VExpr := .forallE (.sort .zero) (.sort .zero)
def expanded (i : Nat) : VExpr := .lam (.sort .zero) (.app (.bvar (i+1)) (.bvar 0))
def equality : VExpr := eqApp (.succ .zero) carrier (.bvar 0) (expanded 0)
def context : List VExpr := [equality, carrier]
def source : VExpr := eqRecApp (.succ (.succ .zero)) (.succ .zero) carrier (.bvar 1)
  (constantEqMotive (.succ .zero) carrier (.bvar 1) (.sort (.succ .zero)))
  carrier (expanded 1) (.bvar 0)

/-- The carrier and the chosen minor are both Type-valued. -/
theorem carrier_typed (env : VEnv) (U : Nat) (Γ : List VExpr) :
    env.HasType U Γ carrier (.sort (.succ .zero)) :=
  EqRecResultBoundary.right_typed env U Γ

/-- The endpoint's eta expansion is well typed in the base context. -/
theorem base_function (env : VEnv) (U : Nat) :
    env.HasType U [carrier] (.bvar 0) carrier := by
  have h : env.HasType U [carrier] (.bvar 0) carrier.lift := .bvar .zero
  simpa [carrier, liftN] using h

/-- The equality assumption between a function and its eta expansion gives a
well-formed context in every canonical-Eq environment. -/
theorem context_wf (heq : env.HasCanonicalEq) : OnCtx context (env.IsType U) := by
  exact ⟨⟨trivial, _, carrier_typed env U []⟩, _,
    HasType.eqApp heq (by trivial) (carrier_typed env U [carrier])
      (base_function env U) (IsDefEq.eta (base_function env U)).hasType.1⟩

/-- The neutral endpoint remains well typed beneath the equality assumption. -/
theorem function_typed (henv : env.WF) :
    env.HasType U context (.bvar 1) carrier := by
  have h := (base_function env U).weak henv.ordered (B := equality)
  simpa [context, carrier, liftN] using h.hasType.1

/-- The complete stuck source is a type; no untyped endpoint is hidden in it. -/
theorem source_typed (henv : env.WF) (heq : env.HasCanonicalEq) :
    env.HasType U context source (.sort (.succ .zero)) := by
  have hp : env.HasType U context (.bvar 0)
      (eqApp (.succ .zero) carrier (.bvar 1) (expanded 1)) := by
    have h : env.HasType U context (.bvar 0) equality.lift := .bvar .zero
    simpa [equality, carrier, expanded, eqApp, liftN] using h
  exact constant_eqRec_typed henv heq (by trivial) (by trivial) (context_wf heq)
    (carrier_typed env U context) (function_typed henv) (.sort (by trivial))
    (carrier_typed env U context) (IsDefEq.eta (function_typed henv)).hasType.1 hp

/-- A single endpoint eta expansion enables the syntactic K rule. -/
theorem source_exposes_pi : Compute true source carrier := by
  apply Compute.trans (b := eqRecApp (.succ (.succ .zero)) (.succ .zero) carrier (expanded 1)
    (constantEqMotive (.succ .zero) carrier (.bvar 1) (.sort (.succ .zero)))
    carrier (expanded 1) (.bvar 0)) ?_ .eqRec
  exact .app (.app (.app (.app (.app .refl .eta) .refl) .refl) .refl) .refl

/-- Beta and syntactic K alone cannot change this source at all. -/
theorem source_fixed (H : Compute false source out) : out = source :=
  H.eq_of_normal (by decide)

/-- Source typing does not restore raw eta removal for the beta/general-K
fragment. The obstruction is already a type-valued recursor with constant motive. -/
theorem typed_eta_elimination_failure (henv : env.WF) (heq : env.HasCanonicalEq) (U : Nat) :
    OnCtx context (env.IsType U) ∧
    env.HasType U context source (.sort (.succ .zero)) ∧
    Compute true source carrier ∧ ¬ ∃ A B, Compute false source (.forallE A B) := by
  refine ⟨context_wf heq, source_typed henv heq, source_exposes_pi, ?_⟩
  rintro ⟨A, B, H⟩
  have h := source_fixed H
  cases h

/-- Typed endpoint eta replays this case below already. Thus the negative
result rules out the raw simulation premise, not typed strengthening. -/
theorem source_eq_minor (henv : env.WF) (heq : env.HasCanonicalEq) :
    env.IsDefEq U context source carrier (.sort (.succ .zero)) :=
  eqRecApp_simAt henv heq (context_wf heq)
    ⟨_, (IsDefEq.eta (function_typed henv)).symm⟩ _ (source_typed henv heq)

end Lean4Lean.VEnv.Strengthening.EqRecEtaBoundary
