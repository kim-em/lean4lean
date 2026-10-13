import Lean4Lean.Theory.Typing.Strengthening.PureObservationSubstitution
import Lean4Lean.Theory.Typing.FullReduction

/-! # Pi-head exposure through beta and function-eta expansion

A finite path using beta, arbitrary function-eta expansion, and congruence cannot
create a Pi/sort head that beta alone could not expose. No normalization hypothesis
is needed. Actual beta paths lower syntactically, so this also reconstructs a Pi
function type below from such an exposure above. Declaration computation and
structure eta are not part of this fragment.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr

/-- Compatible beta reduction and function-eta expansion. The annotation of eta
is arbitrary syntax: the head-exposure theorem does not need it to be well typed. -/
inductive BetaEta : VExpr → VExpr → Prop where
  | refl : BetaEta e e
  | trans : BetaEta a b → BetaEta b c → BetaEta a c
  | beta : BetaEta (.app (.lam A b) a) (b.inst a)
  | eta : BetaEta e (.lam A (.app e.lift (.bvar 0)))
  | app : BetaEta f f' → BetaEta a a' → BetaEta (.app f a) (.app f' a')
  | lam : BetaEta A A' → BetaEta b b' → BetaEta (.lam A b) (.lam A' b')
  | forallE : BetaEta A A' → BetaEta B B' → BetaEta (.forallE A B) (.forallE A' B')
  | proj : BetaEta m m' → BetaEta (.proj S i m) (.proj S i m')

/-- Ordinary finite beta reduction embeds in the combined relation. -/
theorem BetaEta.of_beta (H : BetaRed e out) : BetaEta e out := by
  induction H with
  | refl => exact .refl
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | beta => exact .beta
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Every observation at the end of a beta/eta path was already available at its
start. The lambda-domain congruence is harmless because it is not evaluated. -/
theorem BetaEta.obs_back (R : BetaEta e out) (H : Obs D S out o) : Obs D S e o := by
  induction R generalizing S o with
  | refl => exact H
  | trans _ _ ih1 ih2 => exact ih1 (ih2 H)
  | beta => exact H.beta_back
  | eta => exact H.eta_back
  | app _ _ ihf iha =>
    obtain ⟨keys, hf, ha⟩ := H.app_inv
    exact .app (ihf hf) (fun key hk => iha (ha key hk))
  | lam _ _ _ ihb =>
    obtain ⟨keys, result, hb, hl⟩ := H.lam_inv
    exact .sub (.lam (ihb hb)) hl
  | forallE => exact .sub .pi H.pi_inv
  | proj => exact H.proj_false.elim

/-- A Pi head reached with beta and function eta can be exposed using beta alone.
The domains/bodies of the beta reduct need not be the path's final annotations. -/
theorem BetaEta.pi_exposure (R : BetaEta e (.forallE A B)) :
    ∃ D C, BetaRed e (.forallE D C) :=
  by
  obtain ⟨D, C, hr⟩ := (R.obs_back (D := .empty) (S := fun _ _ => False) .pi).pi_exposure
  exact ⟨D, C, hr.to_beta⟩

/-- The analogous operational adequacy result for a sort head. -/
theorem BetaEta.sort_exposure (R : BetaEta e (.sort u)) : ∃ v, BetaRed e (.sort v) :=
  by
  obtain ⟨v, hr⟩ := (R.obs_back (D := .empty) (S := fun _ _ => False) .sort).sort_exposure
  exact ⟨v, hr.to_beta⟩

/-- Pi exposure of a lifted term in this fragment produces an actual beta path to
a Pi below. No typing or scoped-annotation premise on the ambient eta steps is used. -/
theorem BetaEta.pi_exposure_below {e : VExpr} (R : BetaEta (e.lift' ρ) (.forallE A B)) :
    ∃ D C, BetaRed e (.forallE D C) := by
  obtain ⟨D, C, RB⟩ := R.pi_exposure
  obtain ⟨out, R0, he⟩ := betaRed_lift_inv RB
  obtain ⟨D0, C0, rfl, _, _⟩ := lift'_eq_forallE he.symm
  exact ⟨D0, C0, R0⟩

section
variable [Params]
open Params

/-- A function's type can be exposed below when its lifted type has a beta/eta
path to a Pi. This supplies a genuine smaller-context function typing. General
full-reduction head exposure, including declaration rules, is still missing. -/
theorem function_type_below (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : HasType env univs Γ f T) (R : BetaEta (T.lift' ρ) (.forallE A B)) :
    ∃ D C, HasType env univs Γ f (.forallE D C) ∧
      IsDefEqU env univs Γ T (.forallE D C) := by
  obtain ⟨D, C, RB⟩ := R.pi_exposure_below
  obtain ⟨u, hT⟩ := hf.isType henv hΓ
  have HT := RB.simAt henv.orderedStrong henv.betaSubjectReduction hΓ (.sort u) hT
  exact ⟨D, C, HT.defeq hf, _, HT⟩

/-- The recovered function type permits eta expansion in the smaller context,
without borrowing the ambient path's annotation or replaying any of its eta steps. -/
theorem function_eta_below (hΓ : OnCtx Γ (Params.env.IsType univs))
    (hf : HasType env univs Γ f T) (R : BetaEta (T.lift' ρ) (.forallE A B)) :
    ∃ D C, HasType env univs Γ f (.forallE D C) ∧
      FullReduction Γ f (.lam D (.app f.lift (.bvar 0))) := by
  obtain ⟨D, C, ht, _⟩ := function_type_below hΓ hf R
  exact ⟨D, C, ht, .tail .rfl (.funEta ht)⟩

end
end Lean4Lean.VEnv.Strengthening.PureObservation
