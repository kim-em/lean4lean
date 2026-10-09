import Lean4Lean.Theory.Typing.Strengthening.TypingFront
import Lean4Lean.Environment
import Lean4Lean.Theory.Meta

namespace Lean4Lean.Round9Regression
open VEnv VExpr

def S1 : VExpr := .sort (.succ .zero)
def S2 : VExpr := .sort (.succ (.succ .zero))
def Pi : VExpr := .forallE (.sort .zero) (.sort .zero)
def betaType (X : VExpr) : VExpr := .app (.lam S1 (.bvar 0)) X

def guardType (X : VExpr) : VExpr := eqApp (.succ (.succ .zero)) S1 X (betaType X)
def guardProof (X : VExpr) : VExpr := eqReflApp (.succ (.succ .zero)) S1 X

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem pi_typed : env.HasType U Γ Pi S1 := StrengtheningObstructions.bodyPi_typed

theorem beta_type_eq (hX : env.HasType U Γ X S1) :
    env.IsDefEq U Γ (betaType X) X S1 := by
  simpa [betaType, S1, inst, instVar, lift, liftN] using
    (IsDefEq.beta (HasType.bvar (env := env) (U := U) (Lookup.zero (ty := S1))) hX)

/-- A genuinely converted constructor typing; the expected endpoint is not syntactically X. -/
theorem constructor_guard (heq : env.HasCanonicalEq) (hX : env.HasType U Γ X S1) :
    env.HasType U Γ (guardProof X) (guardType X) := by
  have hr := HasType.eqReflApp heq (w := .succ (.succ .zero)) trivial
    (HasType.sort (l := .succ .zero) trivial) hX
  exact (IsDefEq.eqApp_r heq (w := .succ (.succ .zero)) trivial (HasType.sort (l := .succ .zero) trivial) hX (beta_type_eq hX).symm).defeq hr

theorem constructor_guard_above (henv : env.WF) (heq : env.HasCanonicalEq) (Q : VExpr) :
    env.HasType U (Q :: Γ) (guardProof Pi).lift (guardType Pi).lift :=
  (constructor_guard heq pi_typed).weak henv.ordered

/-- Exact syntax of a type-level recursor, without adding any definition to the environment. -/
def motive (X : VExpr) : VExpr :=
  .lam S1 (.lam (eqApp (.succ (.succ .zero)) S1 X.lift (.bvar 0)) S1)

def redType (X : VExpr) : VExpr :=
  eqRecApp (.succ (.succ .zero)) (.succ (.succ .zero)) S1 X (motive X) Pi
    (betaType X) (guardProof X)

theorem motive_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (hX : env.HasType U Γ X S1) :
    env.HasType U Γ (motive X)
      (.forallE S1 (.forallE (eqApp (.succ (.succ .zero)) S1 X.lift (.bvar 0)) S2)) := by
  have hX' := hX.weak henv.ordered (B := S1)
  have hY : env.HasType U (S1 :: Γ) (.bvar 0) S1 := .bvar .zero
  have hEq := HasType.eqApp heq (w := .succ (.succ .zero)) trivial
    (HasType.sort (l := .succ .zero) trivial) hX' hY
  exact .lam (HasType.sort (l := .succ .zero) trivial)
    (.lam hEq (HasType.sort (l := .succ .zero) trivial))

theorem motive_app (henv : env.WF) (heq : env.HasCanonicalEq)
    (hX : env.HasType U Γ X S1) (hY : env.HasType U Γ Y S1)
    (hh : env.HasType U Γ h (eqApp (.succ (.succ .zero)) S1 X Y)) :
    env.IsDefEq U Γ (.app (.app (motive X) Y) h) S1 S2 := by
  have hX' := hX.weak henv.ordered (B := S1)
  have hY' : env.HasType U (S1 :: Γ) (.bvar 0) S1 := .bvar .zero
  have hEq := HasType.eqApp heq (w := .succ (.succ .zero)) trivial
    (HasType.sort (l := .succ .zero) trivial) hX' hY'
  have hb := IsDefEq.beta (HasType.lam hEq (HasType.sort (l := .succ .zero) trivial)) hY
  simp [eqApp, S1, inst, instVar, lift, inst_lift] at hb
  have happ := IsDefEq.appDF hb hh
  have hb2 := IsDefEq.beta (HasType.sort (env := env) (U := U)
    (Γ := eqApp (.succ (.succ .zero)) S1 X Y :: Γ) (l := .succ .zero) trivial) hh
  simpa [motive, S1, S2, eqApp, inst, instVar, lift, liftN, liftN_liftN,
    inst_liftN_lo, inst_lift] using happ.trans hb2

theorem redType_typed (henv : env.WF) (heq : env.HasCanonicalEq)
    (hX : env.HasType U Γ X S1) : env.HasType U Γ (redType X) S1 := by
  have hM := motive_typed henv heq hX
  have hr := HasType.eqReflApp heq (w := .succ (.succ .zero)) trivial
    (HasType.sort (l := .succ .zero) trivial) hX
  have hm := (motive_app henv heq hX hX hr).symm.defeq
    (pi_typed (env := env) (U := U) (Γ := Γ))
  have hY := (beta_type_eq hX).hasType.1
  have hh := constructor_guard heq hX
  have hrec := HasType.eqRecApp heq (v := .succ (.succ .zero))
    (w := .succ (.succ .zero)) trivial trivial
    (HasType.sort (l := .succ .zero) trivial) hX hM hm hY hh
  exact (motive_app henv heq hX hY hh).defeq hrec

def originalType : VExpr := .app (.lam S1 (redType (.bvar 0))) Pi

theorem originalType_typed (henv : env.WF) (heq : env.HasCanonicalEq) :
    env.HasType U Γ originalType S1 := by
  have hb := redType_typed henv heq
    (HasType.bvar (env := env) (U := U) (Lookup.zero (Γ := Γ) (ty := S1)))
  simpa [originalType, S1, lift, liftN, inst] using
    HasType.app (HasType.lam (HasType.sort (l := .succ .zero) trivial) hb) (pi_typed (env := env))

/-- Immediate syntactic subexpressions, without quotienting by reduction. -/
def nodes : VExpr → List VExpr
  | e@(.app f a) => e :: (nodes f ++ nodes a)
  | e@(.lam A b) | e@(.forallE A b) => e :: (nodes A ++ nodes b)
  | e@(.proj _ _ m) => e :: nodes m
  | e => [e]

theorem new_guard_term : guardProof Pi ∈ nodes (redType Pi) ∧
    guardProof Pi ∉ nodes originalType := by decide

theorem new_endpoint_term : betaType Pi ∈ nodes (redType Pi) ∧
    betaType Pi ∉ nodes originalType := by decide

theorem nonliteral_alignment : betaType Pi ≠ Pi := by decide

theorem beta_creates_redex [VEnv.Params] (Γ : List VExpr) :
    FullStep Γ originalType (redType Pi) := by
  have hh : (redType (.bvar 0)).inst Pi = redType Pi := by decide
  rw [originalType, ← hh]
  exact .core (.beta .rfl .rfl)

open InductiveSignature RecursorData CaseSchema

def eqBody : EquationBody :=
  (EquationBody.extract canonicalEqRecRule.lhs canonicalEqRecRule.rhs canonicalEqRecRule.type).getD
    { domains := [], lhs := S1, rhs := S1, type := S2 }

def recPrefix : VExpr := mkApps (.const ``Eq.rec [.succ (.succ .zero), .succ (.succ .zero)])
  [S1, Pi, motive Pi, Pi, betaType Pi]

def program : PrefixUnfolding where
  domains := [guardType Pi]
  result := .app (.app (motive Pi) (betaType Pi)) (.bvar 0)
  constructor := guardProof Pi
  equation := canonicalEqRecRule
  equationBody := eqBody
  captures := [S1, Pi, motive Pi, Pi]
  levels := [.succ (.succ .zero), .succ (.succ .zero)]

/-- A complete abstract replay check, including the nonliteral endpoint alignment. -/
theorem prefix_check (henv : env.WF) (heq : env.HasCanonicalEq) :
    UnfoldingCheck env U Γ recPrefix program := by
  have hP : env.HasType U Γ Pi S1 := pi_typed
  have hr : env.HasType U Γ (guardProof Pi)
      (eqApp (.succ (.succ .zero)) S1 Pi Pi) :=
    HasType.eqReflApp heq trivial (HasType.sort (l := .succ .zero) trivial) hP
  have hM := motive_typed henv heq hP
  have hm := (motive_app henv heq hP hP hr).symm.defeq hP
  have h4 := HasType.eqRec4 heq (v := .succ (.succ .zero)) (w := .succ (.succ .zero))
    trivial trivial (HasType.sort (l := .succ .zero) trivial) hP hM hm
  have h5 := h4.app (beta_type_eq hP).hasType.1
  refine {
    source_typed := ?_
    remaining_nonempty := by decide
    equation_present := heq.2.2.2
    equation_body := by rfl
    levels_wf := by simp [program, VLevel.WF]
    levels_length := rfl
    captures_length := rfl
    captures_typed := ?_
    major_prop := ?_
    recursor_lhs := ?_ }
  · exact h5
  · intro j hj hd
    have hp : env.HasType U (guardType Pi :: Γ) Pi S1 := pi_typed
    have hrr : env.HasType U (guardType Pi :: Γ) (guardProof Pi)
        (eqApp (.succ (.succ .zero)) S1 Pi Pi) :=
      HasType.eqReflApp heq trivial (HasType.sort (l := .succ .zero) trivial) hp
    match j with
    | 0 => exact HasType.sort (l := .succ .zero) trivial
    | 1 => exact hp
    | 2 => exact motive_typed henv heq hp
    | 3 => exact (motive_app henv heq hp hp hrr).symm.defeq hp
    | j+4 => have : j+4 < 4 := hj; omega
  · refine ⟨guardType Pi, ?_, ?_, ?_⟩
    · exact HasType.eqApp heq trivial (HasType.sort (l := .succ .zero) trivial)
        pi_typed (beta_type_eq pi_typed).hasType.1
    · exact .bvar .zero
    · exact constructor_guard heq pi_typed
  · refine ⟨``Eq.rec, program.levels, program.levels,
      [S1, Pi, motive Pi, Pi, betaType Pi, guardProof Pi],
      [S1, Pi, motive Pi, Pi, Pi, guardProof Pi], rfl, rfl,
      (by simp [program, VLevel.WF]), (by simp [program, VLevel.WF]),
      .cons rfl (.cons rfl .nil), ?_⟩
    refine .cons ⟨_, HasType.sort (l := .succ .zero) trivial⟩
      (.cons ⟨_, pi_typed⟩ (.cons ⟨_, motive_typed henv heq pi_typed⟩
      (.cons ⟨_, pi_typed⟩ (.cons ⟨_, beta_type_eq pi_typed⟩ (.cons ?_ .nil)))))
    exact ⟨_, HasType.eqReflApp heq (w := .succ (.succ .zero)) trivial
      (HasType.sort (l := .succ .zero) trivial) pi_typed⟩

/-- Once the registry/generator selects this program, the exact full head step follows.
The registry and generation facts are explicit assumptions, not claimed proved here. -/
theorem prefix_step (henv : env.WF) (heq : env.HasCanonicalEq)
    (data : RecursorData)
    (lookup : henv.registry.recursors ``Eq.rec = some data)
    (registered : RecursorRegistered env data) (name : data.name = ``Eq.rec)
    (large : data.largeTarget = true)
    (zero : data.sourceLevel program.levels ≈ .zero)
    (generated : data.singletonUnfolding env U program.levels
      [S1, Pi, motive Pi, Pi, betaType Pi] = some program) :
    letI := henv.params U
    FullStep Γ recPrefix program.rhs := by
  letI := henv.params U
  exact .delta (.intro lookup registered name large
    (by simp [VLevel.WF]) zero generated (prefix_check henv heq))

theorem redType_defeq_pi (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) : env.IsDefEq U Γ (redType Pi) Pi S1 := by
  have hc := IsDefEq.appDF ((prefix_check henv heq).defeq henv hΓ)
    (constructor_guard heq (pi_typed (env := env) (U := U) (Γ := Γ)))
  have hc' := (show env.IsDefEqU U Γ (redType Pi)
      (.app (.lam (guardType Pi) Pi) (guardProof Pi)) from ⟨_, hc⟩).of_l henv hΓ
    (redType_typed henv heq pi_typed)
  have hb := IsDefEq.beta (pi_typed (env := env) (U := U) (Γ := guardType Pi :: Γ))
    (constructor_guard heq (pi_typed (env := env) (U := U) (Γ := Γ)))
  exact hc'.trans hb

theorem original_defeq_pi (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) : env.IsDefEq U Γ originalType Pi S1 := by
  letI := henv.params U
  exact ((beta_creates_redex Γ).defeq hΓ (originalType_typed henv heq)).trans
    (redType_defeq_pi henv heq hΓ)

theorem original_exposes_and_inhabited (henv : env.WF) (heq : env.HasCanonicalEq)
    (hΓ : OnCtx Γ (env.IsType U)) :
    env.HasType U Γ (.lam (.sort .zero) (.bvar 0)) originalType ∧
    (letI := henv.params U; ∃ A B, FullReduction Γ originalType (.forallE A B)) := by
  have hid : env.HasType U Γ (.lam (.sort .zero) (.bvar 0)) Pi :=
    .lam (HasType.sort (l := .zero) trivial) (.bvar .zero)
  exact ⟨(original_defeq_pi henv heq hΓ).symm.defeq hid,
    StrengtheningTypingFront.exposure_reduces henv heq hΓ
      (originalType_typed henv heq) ⟨_, original_defeq_pi henv heq hΓ⟩⟩

/-- The constructor is checked beneath the fresh major and the removed binder. -/
theorem actual_above_guard (henv : env.WF) (heq : env.HasCanonicalEq) (Q : VExpr) :
    UnfoldingCheck env U (Q :: Γ) recPrefix program ∧
    env.HasType U (guardType Pi :: Q :: Γ) (guardProof Pi) (guardType Pi) :=
  ⟨prefix_check henv heq, constructor_guard heq pi_typed⟩

end Lean4Lean.Round9Regression

namespace Lean4Lean.Round9Executable
open Lean Meta

-- The only inductive block installed in the executable test environment is Eq.
run_meta do
  let realEnv ← getEnv
  let some (.inductInfo I) := realEnv.find? ``Eq | throwError "missing Eq"
  let some (.ctorInfo C) := realEnv.find? ``Eq.refl | throwError "missing Eq.refl"
  let decl := Declaration.inductDecl I.levelParams I.numParams
    [{ name := ``Eq, type := I.type, ctors := [{ name := ``Eq.refl, type := C.type }] }] false
  let empty ← mkEmptyEnvironment
  let env ← match Lean4Lean.addDecl empty.toKernelEnv decl (check := true) with
    | .error e => throwError "Eq rejected: {e.toMessageData {}}"
    | .ok env => pure env
  -- X : Type, M := fun Y (_ : Eq Type X Y) => Type.
  let type := Expr.sort (.succ .zero)
  let prop := Expr.sort .zero
  let two := Level.succ (.succ .zero)
  let pi := Expr.forallE `P prop prop .default
  let btype (x : Expr) := mkApp (.lam `Y type (.bvar 0) .default) x
  let eqTy (x y : Expr) := mkApp3 (.const ``Eq [two]) type x y
  let refl (x : Expr) := mkApp2 (.const ``Eq.refl [two]) type x
  let motive (x : Expr) := .lam `Y type
    (.lam `h (eqTy (x.liftLooseBVars 0 1) (.bvar 0)) type .default) .default
  let red (x : Expr) := mkAppN (.const ``Eq.rec [two, two])
    #[type, x, motive x, pi, btype x, refl x]
  let original := mkApp (.lam `X type (red (.bvar 0)) .default) pi
  let cfg : TypeChecker.Context := { env := env }
  let check (e : Expr) := (TypeChecker.inferType e (inferOnly := false)) cfg {}
  match check original with
  | .error e => throwError "original type rejected: {e.toMessageData {}}"
  | .ok _ => pure ()
  match check (red pi) with
  | .error e => throwError "beta reduct rejected: {e.toMessageData {}}"
  | .ok _ => pure ()
  -- Force the converted expected type through an explicit lambda application.
  let ascribed := mkApp (.lam `h (eqTy pi (btype pi)) (.bvar 0) .default) (refl pi)
  match check ascribed with
  | .error e => throwError "nonliteral constructor guard rejected: {e.toMessageData {}}"
  | .ok _ => pure ()
  match TypeChecker.whnf original cfg {} with
  | .error e => throwError "exposure failed: {e.toMessageData {}}"
  | .ok (out, _) =>
    unless out.equal pi do throwError "wrong exposed type: {out}"
  logInfo "Eq-only executable regression: original, reduct and converted guard checked; whnf exposed Pi."

end Lean4Lean.Round9Executable

namespace Lean4Lean.Round9StructureRegression
structure Box where
  field : Type

-- A demanded major is a structure, although the whole expression is a TYPE.
-- Lean's conversion check accepts eta-expanding the neutral major, followed by iota.
example (s : Box) :
    Box.rec (motive := fun _ => Type) (fun _ => Prop → Prop) s = (Prop → Prop) := rfl
end Lean4Lean.Round9StructureRegression

namespace Lean4Lean.Round9Regression

theorem reduct_grows : sizeOf originalType < sizeOf (redType Pi) := by decide

theorem supported_original : originalType.lift = originalType := by decide

theorem supported_redex : (redType Pi).lift = redType Pi := by decide

end Lean4Lean.Round9Regression

#print axioms Lean4Lean.Round9Regression.constructor_guard
#print axioms Lean4Lean.Round9Regression.originalType_typed
#print axioms Lean4Lean.Round9Regression.new_guard_term
#print axioms Lean4Lean.Round9Regression.new_endpoint_term
#print axioms Lean4Lean.Round9Regression.beta_creates_redex
#print axioms Lean4Lean.Round9Regression.prefix_check
#print axioms Lean4Lean.Round9Regression.prefix_step
#print axioms Lean4Lean.Round9Regression.original_exposes_and_inhabited
#print axioms Lean4Lean.Round9Regression.actual_above_guard
#print axioms Lean4Lean.Round9Regression.reduct_grows
