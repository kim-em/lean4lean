import Lean4Lean.Theory.Typing.Strengthening.DeclarationHeadExposure

/-! # Replaying recovered declaration computations below

The finite head model is instantiated by actual equations in a well-formed
environment. Replaying its beta/delta path uses source typing in the smaller
context; it does not require descending intermediate typings from the ambient
eta path. Pattern computation and structure eta are outside this result.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- All stored equations whose instantiated left side is a constant. The level
instance of an equation need not equal the levels appearing on its left side. -/
def Definitions.ofEnv (env : VEnv) (U : Nat) (henv : env.WF) : Definitions where
  unfolds c ls rhs := ∃ df us, env.defeqs df ∧ (∀ u ∈ us, u.WF U) ∧
    us.length = df.uvars ∧ df.lhs.instL us = .const c ls ∧ df.rhs.instL us = rhs
  closed := by
    rintro c ls rhs ⟨df, us, hd, _, _, _, rfl⟩
    exact ((henv.ordered.defEqWF hd).2.closedN henv.ordered ⟨⟩).instL

/-- A declaration collection is sound when every unfolding is a stored or derived
untyped definitional equality, uniformly over contexts. -/
def Definitions.Sound (D : Definitions) (env : VEnv) (U : Nat) : Prop :=
  ∀ Γ c ls rhs, D.unfolds c ls rhs → IsDefEqU env U Γ (.const c ls) rhs

/-- Actual stored constant equations provide a sound declaration collection. -/
theorem Definitions.ofEnv_sound (henv : env.WF) : (Definitions.ofEnv env U henv).Sound env U := by
  rintro Γ c ls rhs ⟨df, us, hd, hw, hl, he, hr⟩
  have h := IsDefEq.extra (Γ := Γ) hd hw hl
  rw [he, hr] at h
  exact ⟨_, h⟩

/-- Finite beta/delta computation preserves every source typing. Declaration
conversion is aligned to that typing by uniqueness, not by strengthening. -/
theorem Compute.simAt (R : Compute D e out) (henv : env.WF) (hD : D.Sound env U)
    (hΓ : OnCtx Γ (env.IsType U)) : env.SimAt U Γ e out := by
  induction R generalizing Γ with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans (ih1 hΓ) (ih2 hΓ)
  | beta => exact henv.betaSubjectReduction _ _ _ _ hΓ
  | delta hd => exact fun _ ht => (hD _ _ _ _ hd).of_l henv hΓ ht
  | app _ _ ih1 ih2 => exact .app henv.orderedStrong hΓ (ih1 hΓ) (ih2 hΓ)
  | lam _ _ ih1 ih2 => exact .lam henv.orderedStrong hΓ (ih1 hΓ) ih2
  | forallE _ _ ih1 ih2 => exact .forallE henv.orderedStrong hΓ (ih1 hΓ) ih2
  | proj _ ih => exact .proj henv.orderedStrong hΓ (ih hΓ)

/-- If a lifted type reaches a Pi by beta/delta and function eta, its function can
be assigned a Pi type below. This covers recursive declaration unfolding. -/
theorem ComputeEta.function_type_below (henv : env.WF) (hD : D.Sound env U)
    (hΓ : OnCtx Γ (env.IsType U)) (hf : HasType env U Γ f T)
    (R : ComputeEta D (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType env U Γ f (.forallE A' B') ∧ IsDefEqU env U Γ T (.forallE A' B') := by
  obtain ⟨A', B', RB⟩ := R.pi_exposure_below
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have HT := RB.simAt henv hD hΓ (.sort u) hT
  exact ⟨A', B', HT.defeq hf, _, HT⟩

/-- The recovered Pi type licenses function eta below with its own recovered
annotation, without importing any of the ambient expansion's annotations. -/
theorem ComputeEta.function_eta_below [Params]
    (hD : D.Sound Params.env Params.univs)
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (hf : HasType Params.env Params.univs Γ f T)
    (R : ComputeEta D (T.lift' ρ) (.forallE A B)) :
    ∃ A' B', HasType Params.env Params.univs Γ f (.forallE A' B') ∧
      FullReduction Γ f (.lam A' (.app f.lift (.bvar 0))) := by
  obtain ⟨A', B', ht, _⟩ := R.function_type_below Params.henv hD hΓ hf
  exact ⟨A', B', ht, .tail .rfl (.funEta ht)⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
