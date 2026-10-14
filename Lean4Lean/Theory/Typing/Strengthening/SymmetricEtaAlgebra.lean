import Lean4Lean.Theory.Typing.Strengthening.SymmetricEtaHeads
import Lean4Lean.Theory.Typing.Strengthening.EtaFiniteConfluence

/-! # Composition and compatibility of symmetric terminal eta joins

Exact confluence of finite typed eta aligns the two expansions of an original
middle term. Normal/eta exchange then transports the two normal comparisons to
that common expansion. Opaque binder-domain equalities remain ordinary normal
comparison premises; no strengthening or computational postponement is claimed.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Symmetric eta/normal joins compose through an originally typed middle.
The proof uses exact eta confluence and normal/eta exchange, with no front. -/
theorem EtaJoin.trans (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : EtaJoin Γ a b) (H2 : EtaJoin Γ b c) (hb : env.HasType univs Γ b T) :
    EtaJoin Γ a c := by
  obtain ⟨a1, b1, RA, RB1, N1⟩ := H1
  obtain ⟨b2, c1, RB2, RC, N2⟩ := H2
  obtain ⟨middle, EB1, EB2⟩ := RB1.confluent hΓ RB2 hb
  obtain ⟨a2, EA, NA⟩ := normal_eta_simulation hΓ N1 EB1
  obtain ⟨c2, EC, NC⟩ := normal_eta_simulation hΓ (N2.symm hΓ) EB2
  exact ⟨a2, c2, RA.trans EA, RC.trans EC, NA.trans hΓ (NC.symm hΓ)⟩

/-- A preceding ordinary normal comparison can be absorbed without changing
the other endpoint's eta path. -/
theorem EtaJoin.normal_left (hΓ : OnCtx Γ (env.IsType univs))
    (N : NormalEq Γ a b) (H : EtaJoin Γ b c) : EtaJoin Γ a c := by
  obtain ⟨b1, c1, RB, RC, HN⟩ := H
  obtain ⟨a1, RA, N'⟩ := normal_eta_simulation hΓ N RB
  exact ⟨a1, c1, RA, RC, N'.trans hΓ HN⟩

/-- Compatible weakening preserves both expansions and their normal comparison. -/
theorem EtaJoin.weakN (H : EtaJoin Γ a b) (W : Ctx.LiftN n k Γ Γ') :
    EtaJoin Γ' (a.liftN n k) (b.liftN n k) := by
  obtain ⟨a1, b1, RA, RB, HN⟩ := H
  exact ⟨_, _, RA.weakN W, RB.weakN W, HN.weakN W⟩

/-- Context conversion uses the original typings of both endpoints. -/
theorem EtaJoin.defeqDFC (H : EtaJoin Γ₁ a b) (hΓ : OnCtx Γ₀ (env.IsType univs))
    (W : IsDefEqCtx env univs Γ₀ Γ₁ Γ₂)
    (ha : env.HasType univs Γ₁ a A) (hb : env.HasType univs Γ₁ b B) : EtaJoin Γ₂ a b := by
  obtain ⟨a1, b1, RA, RB, HN⟩ := H
  exact ⟨a1, b1, RA.defeqDFC hΓ W ha, RB.defeqDFC hΓ W hb, HN.defeqDFC hΓ W⟩

/-- Application compatibility at aligned original Pi and argument types. -/
theorem EtaJoin.app (hΓ : OnCtx Γ (env.IsType univs))
    (hf1 : env.HasType univs Γ f1 (.forallE A B)) (hf2 : env.HasType univs Γ f2 (.forallE A B))
    (ha1 : env.HasType univs Γ a1 A) (ha2 : env.HasType univs Γ a2 A)
    (HF : EtaJoin Γ f1 f2) (HA : EtaJoin Γ a1 a2) : EtaJoin Γ (.app f1 a1) (.app f2 a2) := by
  obtain ⟨f1', f2', RF1, RF2, NF⟩ := HF
  obtain ⟨a1', a2', RA1, RA2, NA⟩ := HA
  exact ⟨_, _, .app RF1 RA1, .app RF2 RA2,
    .appDF (RF1.simAt hΓ _ hf1).hasType.2 (RF2.simAt hΓ _ hf2).hasType.2
      (RA1.simAt hΓ _ ha1).hasType.2 (RA2.simAt hΓ _ ha2).hasType.2 NF NA⟩

/-- Projection compatibility retains the selected projection's actual typing. -/
theorem EtaJoin.proj (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ (.proj family index a) T) (H : EtaJoin Γ a b) :
    EtaJoin Γ (.proj family index a) (.proj family index b) := by
  obtain ⟨a1, b1, RA, RB, HN⟩ := H
  exact ⟨_, _, .proj RA, .proj RB,
    .projDF ((TypedEtaExpansion.proj RA).simAt hΓ _ hp).hasType.2 HN⟩

/-- Lambda compatibility with the normal calculus's explicit common original
domain. Its domain conversions remain opaque and are not asserted to descend. -/
theorem EtaJoin.lam (hΓ : OnCtx Γ (env.IsType univs))
    (e1 : env.IsDefEq univs Γ A A1 (.sort u)) (e2 : env.IsDefEq univs Γ A A2 (.sort u))
    (ht1 : env.HasType univs (A :: Γ) b1 B1) (ht2 : env.HasType univs (A :: Γ) b2 B2)
    (H : EtaJoin (A :: Γ) b1 b2) : EtaJoin Γ (.lam A1 b1) (.lam A2 b2) := by
  obtain ⟨b1', b2', R1, R2, HN⟩ := H
  exact ⟨_, _, .lam .refl (R1.defeqDFC hΓ (.succ .zero e1) ht1),
    .lam .refl (R2.defeqDFC hΓ (.succ .zero e2) ht2), .lamDF e1 e2 HN⟩

/-- Pi compatibility uses separate eta expansions of the two domains and
compares bodies in their common original domain context. -/
theorem EtaJoin.forallE (hΓ : OnCtx Γ (env.IsType univs))
    (e1 : env.IsDefEq univs Γ A A1 (.sort u)) (e2 : env.IsDefEq univs Γ A A2 (.sort u))
    (ht1 : env.HasType univs (A :: Γ) B1 (.sort v))
    (ht2 : env.HasType univs (A :: Γ) B2 (.sort w))
    (HA : EtaJoin Γ A1 A2) (HB : EtaJoin (A :: Γ) B1 B2) :
    EtaJoin Γ (.forallE A1 B1) (.forallE A2 B2) := by
  obtain ⟨A1', A2', RA1, RA2, NA⟩ := HA
  obtain ⟨B1', B2', RB1, RB2, NB⟩ := HB
  have e1' := e1.trans (RA1.simAt hΓ _ e1.hasType.2)
  exact ⟨_, _, .forallE RA1 (RB1.defeqDFC hΓ (.succ .zero e1) ht1),
    .forallE RA2 (RB2.defeqDFC hΓ (.succ .zero e2) ht2),
    .forallEDF e1' NA (RB1.simAt ⟨hΓ, _, e1.hasType.1⟩ _ ht1).hasType.2 NB⟩

end Lean4Lean.VEnv.Strengthening.PureObservation
