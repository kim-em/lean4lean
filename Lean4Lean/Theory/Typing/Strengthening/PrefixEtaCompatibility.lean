import Lean4Lean.Theory.Typing.Strengthening.EtaNormal
import Lean4Lean.Theory.Typing.Strengthening.PrefixEtaPhase

/-! # Compatibility of computation/eta/normal phases

The existing three-phase representation is closed under every compatible
expression constructor and under appending the complete eta/normal terminal
phase. Transitivity across a later computation remains a postponement problem.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Regroup the two terminal phases without changing their witnesses. -/
theorem PrefixEtaNormal.terminal_iff : PrefixEtaNormal D Γ a b ↔
    ∃ x, PrefixCompute D Γ a x ∧ EtaNormal Γ x b := by
  constructor
  · rintro ⟨x, y, RC, RE, HN⟩; exact ⟨x, RC, y, RE, HN⟩
  · rintro ⟨x, RC, y, RE, HN⟩; exact ⟨x, y, RC, RE, HN⟩

theorem PrefixEtaNormal.of_terminal (H : EtaNormal Γ a b) : PrefixEtaNormal D Γ a b :=
  terminal_iff.2 ⟨a, .refl, H⟩

/-- Every actual computation has a three-phase representation. -/
theorem PrefixEtaNormal.compute (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (R : PrefixCompute D Γ a b) (ht : env.HasType univs Γ a T) : PrefixEtaNormal D Γ a b :=
  terminal_iff.2 ⟨b, R, .normal (.refl (R.simAt hs hΓ _ ht).hasType.2)⟩

/-- Earlier computation concatenates without moving any phase. -/
theorem PrefixEtaNormal.prepend_compute (R : PrefixCompute D Γ a b)
    (H : PrefixEtaNormal D Γ b c) : PrefixEtaNormal D Γ a c := by
  obtain ⟨x, RC, HE⟩ := terminal_iff.1 H
  exact terminal_iff.2 ⟨x, R.trans RC, HE⟩

/-- The complete terminal phase may be appended, including both eta forms and
arbitrary normal comparison. This needs neither canonical Eq nor a front. -/
theorem PrefixEtaNormal.append_terminal (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixEtaNormal D Γ a b) (HE : EtaNormal Γ b c) : PrefixEtaNormal D Γ a c := by
  obtain ⟨x, RC, HE0⟩ := terminal_iff.1 H
  exact terminal_iff.2 ⟨x, RC, HE0.trans hΓ HE⟩

/-- Context conversion retains every computational and eta witness. -/
theorem PrefixEtaNormal.defeqDFC (hs : D.Sound env univs)
    (H : PrefixEtaNormal D Γ₁ a b) (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂) (ht : env.HasType univs Γ₁ a T) :
    PrefixEtaNormal D Γ₂ a b := by
  obtain ⟨x, RC, HE⟩ := terminal_iff.1 H
  exact terminal_iff.2 ⟨x, RC.defeqDFC hs hΓ W ht,
    HE.defeqDFC hΓ W (RC.simAt hs (W.isType' hΓ) _ ht).hasType.2⟩

theorem PrefixEtaNormal.app (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (ha : env.HasType univs Γ a A)
    (HF : PrefixEtaNormal D Γ f g) (HA : PrefixEtaNormal D Γ a b) :
    PrefixEtaNormal D Γ (.app f a) (.app g b) := by
  obtain ⟨f0, RF, NF⟩ := terminal_iff.1 HF
  obtain ⟨a0, RA, NA⟩ := terminal_iff.1 HA
  exact terminal_iff.2 ⟨_, .app RF RA,
    .app hΓ (RF.simAt hs hΓ _ hf).hasType.2 (RA.simAt hs hΓ _ ha).hasType.2 NF NA⟩

theorem PrefixEtaNormal.lam (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b T)
    (HA : PrefixEtaNormal D Γ A A') (HB : PrefixEtaNormal D (A :: Γ) b b') :
    PrefixEtaNormal D Γ (.lam A b) (.lam A' b') := by
  obtain ⟨A0, RA, NA⟩ := terminal_iff.1 HA
  obtain ⟨b0, RB, NB⟩ := terminal_iff.1 HB
  have hAA := RA.simAt hs hΓ _ hA
  have hb0 := (RB.simAt hs ⟨hΓ, _, hA⟩ _ hb).hasType.2
  exact terminal_iff.2 ⟨_, .lam RA RB,
    .lam hΓ hAA.hasType.2 NA (NB.defeqDFC hΓ (.succ .zero hAA) hb0)⟩

theorem PrefixEtaNormal.forallE (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (HA : PrefixEtaNormal D Γ A A') (HB : PrefixEtaNormal D (A :: Γ) B B') :
    PrefixEtaNormal D Γ (.forallE A B) (.forallE A' B') := by
  obtain ⟨A0, RA, NA⟩ := terminal_iff.1 HA
  obtain ⟨B0, RB, NB⟩ := terminal_iff.1 HB
  have hAA := RA.simAt hs hΓ _ hA
  have hB0 := (RB.simAt hs ⟨hΓ, _, hA⟩ _ hB).hasType.2
  exact terminal_iff.2 ⟨_, .forallE RA RB,
    .forallE hΓ hAA.hasType.2 (hB0.defeqDFC henv (.succ .zero hAA)) NA
      (NB.defeqDFC hΓ (.succ .zero hAA) hB0)⟩

theorem PrefixEtaNormal.proj (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ (.proj s i m) T) (HM : PrefixEtaNormal D Γ m m') :
    PrefixEtaNormal D Γ (.proj s i m) (.proj s i m') := by
  obtain ⟨m0, RM, NM⟩ := terminal_iff.1 HM
  exact terminal_iff.2 ⟨_, .proj RM,
    .proj hΓ ((PrefixCompute.proj RM).simAt hs hΓ _ hp).hasType.2 NM⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
