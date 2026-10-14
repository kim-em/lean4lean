import Lean4Lean.Theory.Typing.Strengthening.NormalEtaSimulation

/-! # A composable terminal eta/normal phase

Finite typed eta followed by ordinary normal comparison is transitive and
compatible with every expression constructor. This settles composition of the
terminal phase, while computation-before-eta postponement remains separate.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- The terminal phase retains both eta forms and one normal comparison. -/
def EtaNormal (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ x, TypedEtaExpansion Γ a x ∧ NormalEq Γ x b

theorem EtaNormal.normal (H : NormalEq Γ a b) : EtaNormal Γ a b := ⟨a, .refl, H⟩

theorem EtaNormal.expansion (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedEtaExpansion Γ a b) (ht : env.HasType univs Γ a T) : EtaNormal Γ a b :=
  ⟨b, R, .refl (R.simAt hΓ _ ht).hasType.2⟩

/-- Source typing supplies a common type for the complete terminal phase. -/
theorem EtaNormal.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : EtaNormal Γ a b) (ht : env.HasType univs Γ a T) : env.IsDefEq univs Γ a b T := by
  obtain ⟨x, R, N⟩ := H
  have hx := R.simAt hΓ _ ht
  exact hx.trans ((N.defeq hΓ).of_l henv hΓ hx.hasType.2)

/-- Normal/eta exchange makes terminal phases transitive. -/
theorem EtaNormal.trans (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaNormal Γ a b) (H2 : EtaNormal Γ b c) : EtaNormal Γ a c := by
  obtain ⟨x, R1, N1⟩ := H1
  obtain ⟨y, R2, N2⟩ := H2
  obtain ⟨z, R3, N3⟩ := normal_eta_simulation hΓ N1 R2
  exact ⟨z, R1.trans R3, N3.trans hΓ N2⟩

/-- Ambient context conversion preserves actual eta-root typings and the
ordinary normal comparison. -/
theorem EtaNormal.defeqDFC (H : EtaNormal Γ₁ a b)
    (hΓ : OnCtx Γ₀ (env.IsType univs)) (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (ht : env.HasType univs Γ₁ a T) : EtaNormal Γ₂ a b := by
  obtain ⟨x, R, N⟩ := H
  exact ⟨x, R.defeqDFC hΓ W ht, N.defeqDFC hΓ W⟩

/-- Weakening retains the whole terminal phase. -/
theorem EtaNormal.weakN (H : EtaNormal Γ a b) (W : Ctx.LiftN n k Γ Γ') :
    EtaNormal Γ' (a.liftN n k) (b.liftN n k) := by
  obtain ⟨x, R, N⟩ := H
  exact ⟨_, R.weakN W, N.weakN W⟩

theorem EtaNormal.app (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (ha : env.HasType univs Γ a A)
    (HF : EtaNormal Γ f g) (HA : EtaNormal Γ a b) :
    EtaNormal Γ (.app f a) (.app g b) := by
  obtain ⟨f', Rf, Nf⟩ := HF
  obtain ⟨a', Ra, Na⟩ := HA
  have hf' := (Rf.simAt hΓ _ hf).hasType.2
  have ha' := (Ra.simAt hΓ _ ha).hasType.2
  exact ⟨_, .app Rf Ra, .appDF hf' ((Nf.defeq hΓ).of_l henv hΓ hf').hasType.2
    ha' ((Na.defeq hΓ).of_l henv hΓ ha').hasType.2 Nf Na⟩

theorem EtaNormal.lam (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HA : EtaNormal Γ A A') (HB : EtaNormal (A :: Γ) b b') :
    EtaNormal Γ (.lam A b) (.lam A' b') := by
  obtain ⟨A0, RA, NA⟩ := HA
  obtain ⟨b0, Rb, NB⟩ := HB
  have hAA := RA.simAt hΓ _ hA
  exact ⟨_, .lam RA Rb, .lamDF hAA
    (hAA.trans ((NA.defeq hΓ).of_l henv hΓ hAA.hasType.2)) NB⟩

theorem EtaNormal.forallE (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (HA : EtaNormal Γ A A') (HB : EtaNormal (A :: Γ) B B') :
    EtaNormal Γ (.forallE A B) (.forallE A' B') := by
  obtain ⟨A0, RA, NA⟩ := HA
  obtain ⟨B0, RB, NB⟩ := HB
  exact ⟨_, .forallE RA RB, .forallEDF (RA.simAt hΓ _ hA) NA
    (RB.simAt ⟨hΓ, _, hA⟩ _ hB).hasType.2 NB⟩

theorem EtaNormal.proj (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ (.proj s i m) T) (HM : EtaNormal Γ m m') :
    EtaNormal Γ (.proj s i m) (.proj s i m') := by
  obtain ⟨m0, Rm, NM⟩ := HM
  exact ⟨_, .proj Rm, .projDF ((TypedEtaExpansion.proj Rm).simAt hΓ _ hp).hasType.2 NM⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
