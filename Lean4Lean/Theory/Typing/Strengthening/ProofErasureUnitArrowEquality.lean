import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitArrowFamilyReturn

/-! # Ordinary canonical inhabitants of arbitrary finite unit-arrow types

The computational caller result has an ordinary counterpart: eta and registered
unit equality identify every typed inhabitant with a fixed closed value. This
supplies positive record carriers at retained parameters of any finite order.
-/
namespace Lean4Lean.VEnv.Strengthening.ConstructorDemand
open _root_.Lean4Lean Params ProofShape
variable [Params]
variable (hi : env.projections s (PositiveHeaderRegistration.info 0 [] s uc))
variable (hS : env.HasType univs [] (.const s []) (.sort (.succ .zero)))
local notation "U" => unitCarrier hi hS

/-- The ordinary expression whose erasure is the canonical simple value. -/
def UnitArrows.value (Q : UnitArrows) : VExpr := match Q with
  | .unit => .const uc []
  | .arrow A B => .lam (A.control U).expr B.value

/-- The canonical value has its literal simple type in every ordinary context. -/
theorem UnitArrows.value_typed (Q : UnitArrows) :
    env.HasType univs Γ (Q.value hi hS) (Q.control U).expr := by
  induction Q generalizing Γ with
  | unit => exact .const (henv.ordered.projectionConstructor hi) (by simp) rfl
  | arrow A B _ ihB =>
    exact .lam (HeterogeneousControl.ControlType.typed A.wf) ihB

/-- The simple carrier contains no universe parameters to instantiate. -/
theorem UnitArrows.control_instL (Q : UnitArrows) : (Q.control U).expr.instL ls = (Q.control U).expr := by
  induction Q with
  | unit => rfl
  | arrow A B ihA ihB => simp only [UnitArrows.control, HeterogeneousControl.ControlType.expr, VExpr.instL, ihA, ihB]

/-- Every canonical value is closed; no context strengthening is needed. -/
theorem UnitArrows.value_closed (Q : UnitArrows) : (Q.value hi hS).Closed :=
  (Q.value_typed hi hS (Γ := [])).closedN henv.ordered (by trivial)

/-- Erasure preserves the selected ordinary lambda annotations and unit leaf. -/
theorem UnitArrows.value_erase (Q : UnitArrows) (hΓ : OnCtx Γ (env.IsType univs)) :
    proofErase Γ (Q.value hi hS) = Q.canonical s uc := by
  induction Q generalizing Γ with
  | unit => exact if_neg (HeterogeneousControl.ControlType.not_isProof
      (t := .atom U) hΓ (UnitArrows.value_typed hi hS .unit))
  | arrow A B _ ihB =>
    have hA : env.HasType univs Γ (A.control U).expr (.sort (A.control U).level) :=
      HeterogeneousControl.ControlType.typed A.wf
    rw [show proofErase Γ ((UnitArrows.arrow A B).value hi hS) = .lam _ _ from
      if_neg (HeterogeneousControl.ControlType.not_isProof hΓ ((UnitArrows.arrow A B).value_typed hi hS)),
      A.erase hi hS hΓ, ihB (Γ := (A.control U).expr :: Γ) ⟨hΓ, _, hA⟩]
    rfl

/-- Ordinary eta and unit equality make every simple unit type a singleton.
The argument may be an arbitrary typed term; it has no native or computational
premise. This ordinary equality is not claimed to orient erased computation. -/
theorem UnitArrows.value_equal (Q : UnitArrows)
    (hf : env.HasType univs Γ f (Q.control U).expr) :
    env.IsDefEq univs Γ f (Q.value hi hS) (Q.control U).expr := by
  induction Q generalizing Γ f with
  | unit =>
    exact IsDefEq.unitLike hi (params := []) rfl rfl rfl hf (UnitArrows.value_typed hi hS .unit)
  | arrow A B _ ihB =>
    have hA : env.HasType univs Γ (A.control U).expr (.sort (A.control U).level) :=
      HeterogeneousControl.ControlType.typed A.wf
    have hf' : env.HasType univs ((A.control U).expr :: Γ) f.lift
        (HeterogeneousControl.ControlType.arrow (A.control U) (B.control U)).expr := by
      simpa only [HasType, VExpr.lift, UnitArrows.control, (HeterogeneousControl.ControlType.arrow
        (A.control U) (B.control U)).closedN.liftN_eq (Nat.zero_le _)] using hf.weak henv.ordered
    have hx : env.HasType univs ((A.control U).expr :: Γ) (.bvar 0) (A.control U).expr := by
      apply HasType.bvar
      simpa only [VExpr.lift, (A.control U).closedN.liftN_eq (Nat.zero_le _)] using
        (Lookup.zero (Γ := Γ) (ty := (A.control U).expr))
    have hb : env.HasType univs ((A.control U).expr :: Γ) (.app f.lift (.bvar 0)) (B.control U).expr := by
      simpa only [HasType, VExpr.inst_eq, VExpr.Subst.liftN, HeterogeneousControl.ControlType.expr_subst] using hf'.app hx
    exact (IsDefEq.eta hf).symm.trans (.lamDF hA (ihB hb))

end Lean4Lean.VEnv.Strengthening.ConstructorDemand
