import Lean4Lean.Theory.Typing.Strengthening.ReannotationBarrier

/-! # Inhabited proposition endpoints still encode the entire front

The proposition `P → P` is inhabited independently of P. Conversion of two
such propositions nevertheless determines their domains. Thus the two
inhabitants available in a generated family guard cannot alone justify a
strictly smaller strengthening obligation.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A proposition retaining its parameter as a domain while always inhabited. -/
def inhabitedProbe (P : VExpr) : VExpr := .forallE P P.lift

/-- The probe stays in Prop even when its domain has no inhabitant. -/
theorem inhabitedProbe_prop (hP : env.HasType univs Γ P (.sort .zero)) :
    env.HasType univs Γ (inhabitedProbe P) (.sort .zero) := by
  exact (IsDefEq.sortDF (by trivial) (by trivial) VLevel.imax_self).defeq
    (HasType.forallE hP (hP.weak henv))

/-- The identity is a proof of the probe without any inhabitant of P. -/
theorem inhabitedProbe_proof (hP : env.HasType univs Γ P (.sort .zero)) :
    env.HasType univs Γ (.lam P (.bvar 0)) (inhabitedProbe P) :=
  HasType.lam hP (.bvar .zero)

/-- Conversion of the inhabited probes is exactly conversion of their domains. -/
theorem inhabitedProbe_conversion_iff (hΓ : OnCtx Γ (env.IsType univs))
    (hP : env.HasType univs Γ P (.sort .zero)) :
    env.IsDefEqU univs Γ (inhabitedProbe P) (inhabitedProbe Q) ↔
      env.IsDefEqU univs Γ P Q := by
  constructor
  · intro H
    obtain ⟨u, h⟩ := (H.forallE_inv henv hΓ).1
    exact ⟨_, h⟩
  · intro H
    have HPQ := H.of_l henv hΓ hP
    exact ⟨_, IsDefEq.forallEDF HPQ (HPQ.weak henv)⟩

/-- Proposition reflection with both endpoint propositions inhabited below.
The theorem below shows that this is not a smaller front. -/
def InhabitedPropositionFront : Prop :=
  ∀ {Γ X P Q p q}, OnCtx Γ (env.IsType univs) → env.IsType univs Γ X →
    env.HasType univs Γ P (.sort .zero) → env.HasType univs Γ Q (.sort .zero) →
    env.HasType univs Γ p P → env.HasType univs Γ q Q →
    env.IsDefEqU univs (X :: Γ) P.lift Q.lift → env.IsDefEqU univs Γ P Q

/-- Requiring a separately typed proof of each endpoint proposition leaves
exactly the original strengthening obligation. No canonical Eq is needed. -/
theorem inhabitedFront_iff_propositionFront : InhabitedPropositionFront ↔ PropositionFront := by
  constructor
  · intro H Γ X P Q hΓ hX hP hQ HE
    have hΓ' : OnCtx (X :: Γ) (env.IsType univs) := ⟨hΓ, hX⟩
    have hP' : env.HasType univs (X :: Γ) P.lift (.sort .zero) := hP.weak henv
    have HI := (inhabitedProbe_conversion_iff hΓ' hP').2 HE
    have HI' : env.IsDefEqU univs (X :: Γ) (inhabitedProbe P).lift (inhabitedProbe Q).lift := by
      simpa only [inhabitedProbe, lift, liftN, ← lift_liftN'] using HI
    exact (inhabitedProbe_conversion_iff hΓ hP).1
      (H hΓ hX (inhabitedProbe_prop hP) (inhabitedProbe_prop hQ)
        (inhabitedProbe_proof hP) (inhabitedProbe_proof hQ) HI')
  · intro H Γ X P Q p q hΓ hX hP hQ _ _ HE
    exact H hΓ hX hP hQ HE

end Lean4Lean.VEnv.Strengthening
