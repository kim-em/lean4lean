import Lean4Lean.Theory.Typing.Strengthening.SymmetricPrefixEtaPhase
import Lean4Lean.Theory.Typing.Strengthening.SymmetricEtaAlgebra

/-! # Compatibility of symmetric computational and eta joins

Compatible constructors act independently on the two computational paths and
then use terminal eta compatibility. Binder bodies are compared in an explicit
common original domain. Its conversions remain opaque; these results do not
assert mixed computation/eta transitivity or strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Every actual computation has a symmetric phase from a typed source. -/
theorem PrefixEtaJoin.compute (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (R : PrefixCompute D Γ a b) (ht : env.HasType univs Γ a T) : PrefixEtaJoin D Γ a b :=
  ⟨b, b, R, .refl, (EtaNormal.normal (.refl (R.simAt hs hΓ _ ht).hasType.2)).join⟩

/-- Context conversion transports both computational and terminal eta paths. -/
theorem PrefixEtaJoin.defeqDFC (hs : D.Sound env univs)
    (H : PrefixEtaJoin D Γ₁ a b) (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (ha : env.HasType univs Γ₁ a A) (hb : env.HasType univs Γ₁ b B) :
    PrefixEtaJoin D Γ₂ a b := by
  obtain ⟨a0, b0, RA, RB, HJ⟩ := H
  exact ⟨_, _, RA.defeqDFC hs hΓ W ha, RB.defeqDFC hs hΓ W hb,
    HJ.defeqDFC hΓ W (RA.simAt hs (W.isType' hΓ) _ ha).hasType.2
      (RB.simAt hs (W.isType' hΓ) _ hb).hasType.2⟩

/-- Application compatibility retains the aligned original Pi and argument types. -/
theorem PrefixEtaJoin.app (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf1 : env.HasType univs Γ f1 (.forallE A B)) (hf2 : env.HasType univs Γ f2 (.forallE A B))
    (ha1 : env.HasType univs Γ a1 A) (ha2 : env.HasType univs Γ a2 A)
    (HF : PrefixEtaJoin D Γ f1 f2) (HA : PrefixEtaJoin D Γ a1 a2) :
    PrefixEtaJoin D Γ (.app f1 a1) (.app f2 a2) := by
  obtain ⟨f1', f2', RF1, RF2, NF⟩ := HF
  obtain ⟨a1', a2', RA1, RA2, NA⟩ := HA
  exact ⟨_, _, .app RF1 RA1, .app RF2 RA2,
    .app hΓ (RF1.simAt hs hΓ _ hf1).hasType.2 (RF2.simAt hs hΓ _ hf2).hasType.2
      (RA1.simAt hs hΓ _ ha1).hasType.2 (RA2.simAt hs hΓ _ ha2).hasType.2 NF NA⟩

/-- Projection compatibility uses the actual left projection typing. -/
theorem PrefixEtaJoin.proj (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ (.proj family index a) T) (H : PrefixEtaJoin D Γ a b) :
    PrefixEtaJoin D Γ (.proj family index a) (.proj family index b) := by
  obtain ⟨a0, b0, RA, RB, HJ⟩ := H
  exact ⟨_, _, .proj RA, .proj RB,
    .proj hΓ ((PrefixCompute.proj RA).simAt hs hΓ _ hp).hasType.2 HJ⟩

/-- Lambda domains use the normal calculus's opaque conversions from a common
original domain. Only the bodies need symmetric computational phases. -/
theorem PrefixEtaJoin.lam (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (e1 : env.IsDefEq univs Γ A A1 (.sort u)) (e2 : env.IsDefEq univs Γ A A2 (.sort u))
    (ht1 : env.HasType univs (A :: Γ) b1 B1) (ht2 : env.HasType univs (A :: Γ) b2 B2)
    (H : PrefixEtaJoin D (A :: Γ) b1 b2) : PrefixEtaJoin D Γ (.lam A1 b1) (.lam A2 b2) := by
  obtain ⟨b1', b2', R1, R2, HJ⟩ := H
  have hA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, e1.hasType.1⟩
  exact ⟨_, _, .lam .refl (R1.defeqDFC hs hΓ (.succ .zero e1) ht1),
    .lam .refl (R2.defeqDFC hs hΓ (.succ .zero e2) ht2),
    .lam hΓ e1 e2 (R1.simAt hs hA _ ht1).hasType.2 (R2.simAt hs hA _ ht2).hasType.2 HJ⟩

/-- Pi compatibility computes both domains and bodies, retaining an explicit
common original domain for the body phases. -/
theorem PrefixEtaJoin.forallE (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (e1 : env.IsDefEq univs Γ A A1 (.sort u)) (e2 : env.IsDefEq univs Γ A A2 (.sort u))
    (ht1 : env.HasType univs (A :: Γ) B1 (.sort v))
    (ht2 : env.HasType univs (A :: Γ) B2 (.sort w))
    (HA : PrefixEtaJoin D Γ A1 A2) (HB : PrefixEtaJoin D (A :: Γ) B1 B2) :
    PrefixEtaJoin D Γ (.forallE A1 B1) (.forallE A2 B2) := by
  obtain ⟨A1', A2', RA1, RA2, NA⟩ := HA
  obtain ⟨B1', B2', RB1, RB2, NB⟩ := HB
  have hA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, _, e1.hasType.1⟩
  exact ⟨_, _, .forallE RA1 (RB1.defeqDFC hs hΓ (.succ .zero e1) ht1),
    .forallE RA2 (RB2.defeqDFC hs hΓ (.succ .zero e2) ht2),
    .forallE hΓ (e1.trans (RA1.simAt hs hΓ _ e1.hasType.2))
      (e2.trans (RA2.simAt hs hΓ _ e2.hasType.2))
      (RB1.simAt hs hA _ ht1).hasType.2 (RB2.simAt hs hA _ ht2).hasType.2 NA NB⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
