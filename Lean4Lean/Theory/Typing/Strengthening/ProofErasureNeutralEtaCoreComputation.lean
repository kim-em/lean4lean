import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNeutralEtaCorePrimitives
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLevelCoreConfluence

/-! # Protected neutral eta marks through full ordinary core computation

The protected variable cannot become a lambda under local substitution. Its
eta body has no core step, while its annotation retains a full core history.
Primitive simulation therefore extends beta simulation to all ordinary rules.
Typed confluence at one source supplies independent paired residuals.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params] {Guard : ProofShape → Nat → Prop}

private theorem neutral_bvar_core_normal : NormalSyntax (ErasedLevelCore D) (.bvar i) := by
  refine ⟨?_, trivial⟩
  intro out H
  rcases H with H | H
  · exact erased_iota_primitive_head H
  · cases H

private theorem neutral_body_core_fixed
    (R : Compute (ErasedLevelCore D) (.app (.bvar i) (.bvar 0)) out) :
    out = .app (.bvar i) (.bvar 0) := by
  apply NormalSyntax.fixed (Step := ErasedLevelCore D) ?_ R
  refine ⟨?_, (by intro A b H; cases H), neutral_bvar_core_normal, neutral_bvar_core_normal⟩
  intro out H
  rcases H with H | H
  · exact erased_iota_primitive_head H
  · cases H

/-- Every level-core path has a paired path when the marked domain guard
retains its own level-core reducts. All primitive matching cases are proved;
the guard premise concerns only the recorded ambient domain pairs. -/
theorem ProofShape.NeutralEtaVariant.level_core_left
    (hg : ∀ {A i A'}, Guard A i → Compute (ErasedLevelCore D) A A' → Guard A' i)
    (R : Compute (ErasedLevelCore D) a a') (V : NeutralEtaVariant Guard n a b) :
    ∃ b', Compute (ErasedLevelCore D) b b' ∧ NeutralEtaVariant Guard n a' b' := by
  induction R generalizing n b with
  | base R =>
    obtain ⟨b', RB, VB⟩ := erased_level_core_neutral_eta_variant R V
    exact ⟨b', .base RB, VB⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨b₁, RB, V₁⟩ := ih₁ V
    obtain ⟨b₂, RC, V₂⟩ := ih₂ V₁
    exact ⟨b₂, RB.trans RC, V₂⟩
  | app RF RX ihf ihx =>
    cases V with
    | refl => exact ⟨_, .app RF RX, .refl⟩
    | app VF VX =>
      obtain ⟨g, RG, VG⟩ := ihf VF
      obtain ⟨y, RY, VY⟩ := ihx VX
      exact ⟨_, .app RG RY, .app VG VY⟩
  | proj R ih =>
    cases V with
    | refl => exact ⟨_, .proj R, .refl⟩
    | proj V =>
      obtain ⟨b, RB, VB⟩ := ih V
      exact ⟨_, .proj RB, .proj VB⟩
  | lam RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .lam RA RB, .refl⟩
    | lam VA VB =>
      obtain ⟨C, RC, VC⟩ := ihA VA
      obtain ⟨c, Rc, Vc⟩ := ihB VB
      exact ⟨_, .lam RC Rc, .lam VC Vc⟩
    | etaL HG =>
      obtain ⟨A', RA', rfl⟩ := RA.level_core_lift_inv
      obtain rfl := neutral_body_core_fixed RB
      exact ⟨_, .refl, .etaL (hg HG RA')⟩
  | forallE RA RB ihA ihB =>
    cases V with
    | refl => exact ⟨_, .forallE RA RB, .refl⟩
    | forallE VA VB =>
      obtain ⟨C, RC, VC⟩ := ihA VA
      obtain ⟨c, Rc, Vc⟩ := ihB VB
      exact ⟨_, .forallE RC Rc, .forallE VC Vc⟩
  | beta R =>
    obtain ⟨b', RB, VB⟩ := NeutralEtaVariant.beta_left (Guard := Guard)
      (fun H R => hg H (.beta R)) R V
    exact ⟨b', .beta RB, VB⟩

omit [Params] in
/-- Guard implication preserves all protected syntax, including both eta
orientations. This embeds beta-origin marks into full core-origin marks. -/
theorem ProofShape.NeutralEtaVariant.guard_mono
    (V : NeutralEtaVariant Guard n a b) (hg : ∀ {A i}, Guard A i → Guard' A i) :
    NeutralEtaVariant Guard' n a b := by
  induction V with
  | refl => exact .refl
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | etaL HG => exact .etaL (hg HG)
  | etaR HG => exact .etaR (hg HG)

/-- Independent ordinary core paths have further protected eta residuals.
Only the right source needs a typed representative for core confluence; no
confluence of the eta-expanded stages or join of the eta pair is assumed. -/
theorem neutral_eta_level_core_residuals
    (hc : TypedCoreConfluence (ErasedLevelCore D))
    (hg : ∀ {A i A'}, Guard A i → Compute (ErasedLevelCore D) A A' → Guard A' i)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (V : NeutralEtaVariant Guard n a (proofErase Γ e))
    (RA : Compute (ErasedLevelCore D) a p)
    (RB : Compute (ErasedLevelCore D) (proofErase Γ e) q) :
    ∃ p' q', Compute (ErasedLevelCore D) p p' ∧ Compute (ErasedLevelCore D) q q' ∧
      NeutralEtaVariant Guard n p' q' := by
  obtain ⟨b₁, RB₁, V₁⟩ := NeutralEtaVariant.level_core_left (Guard := Guard) (fun H R => hg H R) RA V
  obtain ⟨q', RQ, RB₁'⟩ := hc hΓ ht RB RB₁
  obtain ⟨p', RP, V₂⟩ := NeutralEtaVariant.level_core_left (Guard := Guard) (fun H R => hg H R) RB₁' V₁.symm
  exact ⟨p', q', RP, RQ, V₂.symm⟩

end Lean4Lean.VEnv.Strengthening
