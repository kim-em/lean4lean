import Lean4Lean.Theory.Typing.Strengthening.NormalBetaSimulation

/-! # Postponing normal comparison after beta reduction

Finite paths of beta computation and ordinary normal comparison factor into
beta computation followed by one normal comparison. Compatibility includes
lambda annotations, whose equalities remain opaque in that comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Beta computation followed by ordinary normal comparison. This is not a
recursive-domain certificate and is not claimed to descend through binders. -/
def BetaNormal (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ x, BetaRed a x ∧ NormalEq Γ x b

private theorem beta_eq (hΓ : OnCtx Γ (env.IsType univs)) (R : BetaRed a b)
    (ht : env.HasType univs Γ a T) : env.IsDefEq univs Γ a b T :=
  R.simAt henv.orderedStrong henv.betaSubjectReduction hΓ _ ht

theorem BetaNormal.normal (H : NormalEq Γ a b) : BetaNormal Γ a b := ⟨a, .refl, H⟩

theorem BetaNormal.beta (hΓ : OnCtx Γ (env.IsType univs)) (R : BetaRed a b)
    (ht : env.HasType univs Γ a T) : BetaNormal Γ a b :=
  ⟨b, R, .refl (beta_eq hΓ R ht).hasType.2⟩

theorem BetaNormal.defeq (hΓ : OnCtx Γ (env.IsType univs))
    (H : BetaNormal Γ a b) (ht : env.HasType univs Γ a T) : env.IsDefEq univs Γ a b T := by
  obtain ⟨x, R, N⟩ := H
  have hax := beta_eq hΓ R ht
  exact hax.trans ((N.defeq hΓ).of_l henv hΓ hax.hasType.2)

theorem BetaNormal.trans (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : BetaNormal Γ a b) (H2 : BetaNormal Γ b c) : BetaNormal Γ a c := by
  obtain ⟨x, R1, N1⟩ := H1
  obtain ⟨y, R2, N2⟩ := H2
  obtain ⟨z, R3, N3⟩ := normal_beta_simulation hΓ N1 R2
  exact ⟨z, R1.trans R3, N3.trans hΓ N2⟩

theorem BetaNormal.app (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (ha : env.HasType univs Γ a A)
    (HF : BetaNormal Γ f g) (HA : BetaNormal Γ a b) :
    BetaNormal Γ (.app f a) (.app g b) := by
  obtain ⟨f', Rf, Nf⟩ := HF
  obtain ⟨a', Ra, Na⟩ := HA
  have hf' := (beta_eq hΓ Rf hf).hasType.2
  have ha' := (beta_eq hΓ Ra ha).hasType.2
  exact ⟨_, .app Rf Ra, .appDF hf' ((Nf.defeq hΓ).of_l henv hΓ hf').hasType.2
    ha' ((Na.defeq hΓ).of_l henv hΓ ha').hasType.2 Nf Na⟩

theorem BetaNormal.lam (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HA : BetaNormal Γ A A') (HB : BetaNormal (A :: Γ) b b') :
    BetaNormal Γ (.lam A b) (.lam A' b') := by
  obtain ⟨A0, RA, NA⟩ := HA
  obtain ⟨b0, Rb, NB⟩ := HB
  have hAA := beta_eq hΓ RA hA
  exact ⟨_, .lam RA Rb, .lamDF hAA (hAA.trans ((NA.defeq hΓ).of_l henv hΓ hAA.hasType.2)) NB⟩

theorem BetaNormal.forallE (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (HA : BetaNormal Γ A A') (HB : BetaNormal (A :: Γ) B B') :
    BetaNormal Γ (.forallE A B) (.forallE A' B') := by
  obtain ⟨A0, RA, NA⟩ := HA
  obtain ⟨B0, RB, NB⟩ := HB
  exact ⟨_, .forallE RA RB, .forallEDF (beta_eq hΓ RA hA) NA
    (beta_eq (Γ := A :: Γ) ⟨hΓ, _, hA⟩ RB hB).hasType.2 NB⟩

theorem BetaNormal.proj (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ (.proj s i m) T) (HM : BetaNormal Γ m m') :
    BetaNormal Γ (.proj s i m) (.proj s i m') := by
  obtain ⟨m0, Rm, NM⟩ := HM
  exact ⟨_, .proj Rm, .projDF (beta_eq hΓ (.proj Rm) hp).hasType.2 NM⟩

/-- The compatible beta/function-eta fragment of full reduction. Eta requires
actual typing; there are no stored-rule, prefix, projection-iota or structure-eta
steps. This restriction is explicit rather than a claim about full computation. -/
inductive TypedBetaEta : List VExpr → VExpr → VExpr → Prop where
  | beta : BetaRed a b → TypedBetaEta Γ a b
  | eta : env.HasType univs Γ f (.forallE A B) →
      TypedBetaEta Γ f (.lam A (.app f.lift (.bvar 0)))
  | trans : TypedBetaEta Γ a b → TypedBetaEta Γ b c → TypedBetaEta Γ a c
  | app : TypedBetaEta Γ f f' → TypedBetaEta Γ a a' →
      TypedBetaEta Γ (.app f a) (.app f' a')
  | lam : TypedBetaEta Γ A A' → TypedBetaEta (A :: Γ) b b' →
      TypedBetaEta Γ (.lam A b) (.lam A' b')
  | forallE : TypedBetaEta Γ A A' → TypedBetaEta (A :: Γ) B B' →
      TypedBetaEta Γ (.forallE A B) (.forallE A' B')
  | proj : TypedBetaEta Γ m m' → TypedBetaEta Γ (.proj s i m) (.proj s i m')

/-- Every typed path in this fragment factors into beta alone followed by
ordinary normal equality. No normalization assumption is used. -/
theorem TypedBetaEta.factor (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedBetaEta Γ a b) (ht : env.HasType univs Γ a T) : BetaNormal Γ a b := by
  induction R generalizing T with
  | beta R => exact .beta hΓ R ht
  | eta hf => exact .normal (.etaR hf (.refl (HasType.app (hf.weak henv) (.bvar .zero))))
  | trans _ _ ih1 ih2 =>
    have H1 := ih1 hΓ ht
    exact H1.trans hΓ (ih2 hΓ (H1.defeq hΓ ht).hasType.2)
  | app _ _ ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app hΓ hf ha (ihf hΓ hf) (iha hΓ ha)
  | lam _ _ ihA ihb =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam hΓ hA (ihA hΓ hA) (ihb ⟨hΓ, _, hA⟩ hb)
  | forallE _ _ ihA ihB =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE hΓ hA hB (ihA hΓ hA) (ihB ⟨hΓ, _, hA⟩ hB)
  | proj _ ihm =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj hΓ ht (ihm hΓ hm.hasType.2)

end Lean4Lean.VEnv.Strengthening
