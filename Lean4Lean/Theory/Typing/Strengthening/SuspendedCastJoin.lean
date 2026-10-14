import Lean4Lean.Theory.Typing.Strengthening.HeterogeneousSubstitutionEquality
import Lean4Lean.Theory.Typing.Strengthening.CastComputation

/-! # Computational joins under delayed substitutions

Concrete computation preserves scope and arbitrary raw substitution. Its replay
supplies the smaller endpoint typings needed by suspension descent. No typing for
an open smaller template or its intermediate reducts is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open PureObservation (Definitions)
variable [Params]
variable {a b : VExpr}
local notation:65 Γ " ⊢ " e " : " A:36 => HasType Params.env univs Γ e A
local notation:65 Γ " ⊢ " e1 " ≡ " e2:36 => IsDefEqU Params.env univs Γ e1 e2

/-- A concrete computational join whose final comparison records its typing
mode. The computation includes beta, closed pattern equations, and syntactic K;
it does not assume coverage of every indexed-prefix or eta reduction. -/
def CastBiJoin (D : Definitions) (mode : Bool) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ a' b' n, CastCompute D a a' ∧ CastCompute D b b' ∧ BiNormal mode n Γ a' b'

/-- Reflect a join while preserving its certificate, with unrelated proof
arguments suspended. Each computed endpoint receives its typing by replay below. -/
theorem CastBiJoin.suspended_reflect
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hΓ₂ : OnCtx Γ₂ (env.IsType univs))
    (S₁ : SubstLiftSquare Γ Γ₁ Δ ρ κ₁ σ₁ τ₁)
    (S₂ : SubstLiftSquare Γ Γ₂ Δ ρ κ₂ σ₂ τ₂) (Hσ : ProofSubstRel Γ σ₁ σ₂)
    (ha : Γ ⊢ a.subst σ₁ : A) (hb : Γ ⊢ b.subst σ₂ : B)
    (H : CastBiJoin D mode Δ (a.lift' ρ) (b.lift' ρ))
    (hmode : if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ (a.subst σ₁)) :
    CastBiJoin D mode Γ (a.subst σ₁) (b.subst σ₂) := by
  obtain ⟨a', b', n, Ra, Rb, H⟩ := H
  obtain ⟨a₀, Ra₀, rfl⟩ := Ra.lift_inv
  obtain ⟨b₀, Rb₀, rfl⟩ := Rb.lift_inv
  have Ra₁ := Ra₀.subst (σ := σ₁)
  have Rb₂ := Rb₀.subst (σ := σ₂)
  have Ea := Ra₁.simAt heq hs hΓ A ha
  have Eb := Rb₂.simAt heq hs hΓ B hb
  have hmode' : if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ (a₀.subst σ₁) := by
    cases mode with
    | true => exact hmode
    | false =>
      rintro ⟨P, ht, hP⟩
      exact hmode ⟨P, ((show Γ ⊢ _ ≡ _ from ⟨_, Ea⟩).symm.of_l henv hΓ ht).hasType.2, hP⟩
  obtain ⟨_, H₀⟩ := BiNormal.suspended_reflect n hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ
    Ea.hasType.2 Eb.hasType.2 H hmode'
  exact ⟨_, _, _, Ra₁, Rb₂, H₀⟩

/-- Arbitrary already-established argument equalities can instead be kept
opaque, yielding equality of the original smaller instances after both replays. -/
theorem CastBiJoin.suspended_defeq
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hΓ₁ : OnCtx Γ₁ (env.IsType univs)) (hΓ₂ : OnCtx Γ₂ (env.IsType univs))
    (S₁ : SubstLiftSquare Γ Γ₁ Δ ρ κ₁ σ₁ τ₁)
    (S₂ : SubstLiftSquare Γ Γ₂ Δ ρ κ₂ σ₂ τ₂) (Hσ : DefEqProofSubstRel Γ σ₁ σ₂)
    (ha : Γ ⊢ a.subst σ₁ : A) (hb : Γ ⊢ b.subst σ₂ : B)
    (H : CastBiJoin D mode Δ (a.lift' ρ) (b.lift' ρ))
    (hmode : if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ (a.subst σ₁)) :
    Γ ⊢ a.subst σ₁ ≡ b.subst σ₂ := by
  obtain ⟨a', b', n, Ra, Rb, H⟩ := H
  obtain ⟨a₀, Ra₀, rfl⟩ := Ra.lift_inv
  obtain ⟨b₀, Rb₀, rfl⟩ := Rb.lift_inv
  have Ea := (Ra₀.subst (σ := σ₁)).simAt heq hs hΓ A ha
  have Eb := (Rb₀.subst (σ := σ₂)).simAt heq hs hΓ B hb
  have hmode' : if mode then Γ ⊢ A ≡ B else ¬ IsProof Γ (a₀.subst σ₁) := by
    cases mode with
    | true => exact hmode
    | false =>
      rintro ⟨P, ht, hP⟩
      exact hmode ⟨P, ((show Γ ⊢ _ ≡ _ from ⟨_, Ea⟩).symm.of_l henv hΓ ht).hasType.2, hP⟩
  have H₀ := BiNormal.suspended_defeq n hΓ hΓ₁ hΓ₂ S₁ S₂ Hσ
    Ea.hasType.2 Eb.hasType.2 H hmode'
  exact (show Γ ⊢ _ ≡ _ from ⟨_, Ea⟩).trans henv hΓ
    (H₀.trans henv hΓ ⟨_, Eb.symm⟩)

end Lean4Lean.VEnv.Strengthening
