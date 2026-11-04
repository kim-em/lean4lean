import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedJointChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure

/-! # Carrier readout for recursive computed-domain checking

An assigned carrier that cannot expose a record or Pi needs no recovered
domain: its guard already contains ordinary endpoint comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private variableHead variableHead_mkApps
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointCarrierExposure
variable [Params]
namespace ProofShape

/-- Every carrier guard factors through ordinary endpoint checking or an
actually exposed structural carrier. Symmetry and endpoint reductions stay in
the resulting guard; successive carrier computations compose into one path. -/
theorem ComputedJointCarrierGuard.checked_or_exposed
    (H : ComputedJointCarrierGuard Step Δ A a b) :
    ComputedJointCompare Step Δ true a b ∨
      ∃ B, ScopedCompute Step Δ A B ∧ CarrierExposure B ∧ ComputedJointCarrierGuard Step Δ B a b := by
  change ComputedJointCheck Step Δ (.carrier A) a b at H
  generalize E : JointCheckKind.carrier A = kind at H
  induction H generalizing A with
  | carrierChecked H => exact .inl H
  | carrierSubsingleton H =>
    cases E
    refine .inr ⟨_, .refl, ?_, .carrierSubsingleton H⟩
    cases H with
    | unit hi hx hf hp => exact .record hi hx hp
    | forallE => exact .function
  | carrierFunction S H =>
    cases E
    exact .inr ⟨_, .refl, .function, .carrierFunction S H⟩
  | carrierSymm _ ih =>
    rcases ih E with HC | ⟨B, R, HB, H⟩
    · exact .inl (.symm HC)
    · exact .inr ⟨B, R, HB, .carrierSymm H⟩
  | carrierCompute R _ ih =>
    cases E
    rcases ih rfl with HC | ⟨B, R', HB, H⟩
    · exact .inl HC
    · exact .inr ⟨B, R.trans R', HB, H⟩
  | carrierReduce Ra Rb _ ih =>
    rcases ih E with HC | ⟨B, R, HB, H⟩
    · exact .inl (.compute Ra Rb HC)
    · exact .inr ⟨B, R, HB, .carrierReduce Ra Rb H⟩
  | carrierIntro hi hx hp hadm H =>
    cases E
    exact .inr ⟨_, .refl, .record hi hx hp, .carrierIntro hi hx hp hadm H⟩
  | carrierNested hi hx hp hadm HT H =>
    cases E
    exact .inr ⟨_, .refl, .record hi hx hp, .carrierNested hi hx hp hadm HT H⟩
  | leaf | app | appCarrier | appComputed | proj | lam | forallE | lamSorted | forallSorted | lamCommon |
      etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases E

/-- A carrier with no path to a structural checking shape contributes no extra
checking power. This criterion needs no confluence, normality or original typing. -/
theorem ComputedJointCarrierGuard.checked_of_no_exposure
    (hn : ∀ {B}, ScopedCompute Step Δ A B → ¬ CarrierExposure B)
    (H : ComputedJointCarrierGuard Step Δ A a b) : ComputedJointCompare Step Δ true a b := by
  rcases H.checked_or_exposed with HC | ⟨B, R, HB, _⟩
  · exact HC
  · exact (hn R HB).elim

/-- At a variable-headed type, carrier checking is ordinary common-mode
comparison, even if its arguments reduce or diverge. -/
theorem ComputedJointCarrierGuard.bvar_spine_checked
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ComputedJointCarrierGuard Step Δ (mkApps (.bvar i) args) a b) :
    ComputedJointCompare Step Δ true a b := by
  apply H.checked_of_no_exposure
  intro B R HB
  obtain ⟨args', rfl, _⟩ := R.bvar_spine hhead
  generalize E : mkApps (.bvar i) args' = out at HB
  cases HB with
  | record | function =>
    have HE := congrArg variableHead E
    simp only [variableHead_mkApps, variableHead] at HE
    cases HE

/-- A guard at a variable-headed assigned domain transfers to any selected
recovered domain. Sound use supplies endpoint typings at that selected domain;
this raw certificate conversion asserts no equality between the carrier types. -/
theorem ComputedJointCarrierGuard.bvar_spine_reindex
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : ComputedJointCarrierGuard Step Δ (mkApps (.bvar i) args) a b) :
    ComputedJointCarrierGuard Step Δ B a b := .carrierChecked (H.bvar_spine_checked hhead)

/-- Inert assigned domains need no native function recovery or exact lambda
exposure. This is an existing application certificate, not a new checking rule. -/
theorem ComputedJointCompare.app_of_inert_carrier
    (hn : ∀ {B}, ScopedCompute Step Δ A B → ¬ CarrierExposure B)
    (HF : ComputedJointCompare Step Δ false f g)
    (HX : ComputedJointCarrierGuard Step Δ A x y) :
    ComputedJointCompare Step Δ mode (.app f x) (.app g y) :=
  .app HF (HX.checked_of_no_exposure hn)

/-- Variable-headed assigned domains bypass recovery even when the function
is a lambda with a different written annotation. Arguments in the domain may
contain eta expansions or arbitrary computations. -/
theorem ComputedJointCompare.app_of_neutral_carrier
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (HF : ComputedJointCompare Step Δ false f g)
    (HX : ComputedJointCarrierGuard Step Δ (mkApps (.bvar i) args) x y) :
    ComputedJointCompare Step Δ mode (.app f x) (.app g y) :=
  .app HF (HX.bvar_spine_checked hhead)

end ProofShape
end Lean4Lean.VEnv.Strengthening
