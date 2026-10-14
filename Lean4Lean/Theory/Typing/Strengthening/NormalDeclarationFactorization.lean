import Lean4Lean.Theory.Typing.Strengthening.NormalDeclarationSimulation

/-! # Postponing normal comparison after beta/delta reduction

Finite paths of beta/delta computation and ordinary normal comparison factor into
beta/delta computation followed by one normal comparison. Compatibility includes
lambda annotations, whose equalities remain opaque in that comparison.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

omit [Params] in
/-- Enlarging the available equations preserves every finite computation. -/
theorem Compute.mono (hD : ∀ {c ls rhs}, D.unfolds c ls rhs → D'.unfolds c ls rhs)
    (R : Compute D a b) : Compute D' a b := by
  induction R with
  | refl => exact .refl
  | beta => exact .beta
  | delta H => exact .delta (hD H)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Beta/delta computation followed by ordinary normal comparison. This is not a
recursive-domain certificate and is not claimed to descend through binders. -/
def ComputeNormal (D : Definitions) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ x, Compute D a x ∧ NormalEq Γ x b

private theorem compute_eq (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (R : Compute D a b)
    (ht : env.HasType univs Γ a T) : env.IsDefEq univs Γ a b T :=
  R.simAt henv hs hΓ _ ht

theorem ComputeNormal.normal (H : NormalEq Γ a b) : ComputeNormal D Γ a b := ⟨a, .refl, H⟩

theorem ComputeNormal.compute (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (R : Compute D a b)
    (ht : env.HasType univs Γ a T) : ComputeNormal D Γ a b :=
  ⟨b, R, .refl (compute_eq hs hΓ R ht).hasType.2⟩

theorem ComputeNormal.defeq (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (H : ComputeNormal D Γ a b) (ht : env.HasType univs Γ a T) : env.IsDefEq univs Γ a b T := by
  obtain ⟨x, R, N⟩ := H
  have hax := compute_eq hs hΓ R ht
  exact hax.trans ((N.defeq hΓ).of_l henv hΓ hax.hasType.2)

theorem ComputeNormal.trans (hs : D.Sound env univs) (hl : D.LevelStable univs) (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : ComputeNormal D Γ a b) (H2 : ComputeNormal D Γ b c) : ComputeNormal D Γ a c := by
  obtain ⟨x, R1, N1⟩ := H1
  obtain ⟨y, R2, N2⟩ := H2
  obtain ⟨z, R3, N3⟩ := normal_compute_simulation hs hl hΓ N1 R2
  exact ⟨z, R1.trans R3, N3.trans hΓ N2⟩

theorem ComputeNormal.app (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (ha : env.HasType univs Γ a A)
    (HF : ComputeNormal D Γ f g) (HA : ComputeNormal D Γ a b) :
    ComputeNormal D Γ (.app f a) (.app g b) := by
  obtain ⟨f', Rf, Nf⟩ := HF
  obtain ⟨a', Ra, Na⟩ := HA
  have hf' := (compute_eq hs hΓ Rf hf).hasType.2
  have ha' := (compute_eq hs hΓ Ra ha).hasType.2
  exact ⟨_, .app Rf Ra, .appDF hf' ((Nf.defeq hΓ).of_l henv hΓ hf').hasType.2
    ha' ((Na.defeq hΓ).of_l henv hΓ ha').hasType.2 Nf Na⟩

theorem ComputeNormal.lam (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HA : ComputeNormal D Γ A A') (HB : ComputeNormal D (A :: Γ) b b') :
    ComputeNormal D Γ (.lam A b) (.lam A' b') := by
  obtain ⟨A0, RA, NA⟩ := HA
  obtain ⟨b0, Rb, NB⟩ := HB
  have hAA := compute_eq hs hΓ RA hA
  exact ⟨_, .lam RA Rb, .lamDF hAA (hAA.trans ((NA.defeq hΓ).of_l henv hΓ hAA.hasType.2)) NB⟩

theorem ComputeNormal.forallE (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (HA : ComputeNormal D Γ A A') (HB : ComputeNormal D (A :: Γ) B B') :
    ComputeNormal D Γ (.forallE A B) (.forallE A' B') := by
  obtain ⟨A0, RA, NA⟩ := HA
  obtain ⟨B0, RB, NB⟩ := HB
  exact ⟨_, .forallE RA RB, .forallEDF (compute_eq hs hΓ RA hA) NA
    (compute_eq (Γ := A :: Γ) hs ⟨hΓ, _, hA⟩ RB hB).hasType.2 NB⟩

theorem ComputeNormal.proj (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ (.proj s i m) T) (HM : ComputeNormal D Γ m m') :
    ComputeNormal D Γ (.proj s i m) (.proj s i m') := by
  obtain ⟨m0, Rm, NM⟩ := HM
  exact ⟨_, .proj Rm, .projDF (compute_eq hs hΓ (.proj Rm) hp).hasType.2 NM⟩

/-- The compatible beta/delta/function-eta fragment of full reduction. Eta requires
actual typing; there are no applied-pattern, prefix, projection-iota or structure-eta
steps. This restriction is explicit rather than a claim about full computation. -/
inductive TypedComputeEta (D : Definitions) : List VExpr → VExpr → VExpr → Prop where
  | compute : Compute D a b → TypedComputeEta D Γ a b
  | eta : env.HasType univs Γ f (.forallE A B) →
      TypedComputeEta D Γ f (.lam A (.app f.lift (.bvar 0)))
  | trans : TypedComputeEta D Γ a b → TypedComputeEta D Γ b c → TypedComputeEta D Γ a c
  | app : TypedComputeEta D Γ f f' → TypedComputeEta D Γ a a' →
      TypedComputeEta D Γ (.app f a) (.app f' a')
  | lam : TypedComputeEta D Γ A A' → TypedComputeEta D (A :: Γ) b b' →
      TypedComputeEta D Γ (.lam A b) (.lam A' b')
  | forallE : TypedComputeEta D Γ A A' → TypedComputeEta D (A :: Γ) B B' →
      TypedComputeEta D Γ (.forallE A B) (.forallE A' B')
  | proj : TypedComputeEta D Γ m m' → TypedComputeEta D Γ (.proj s i m) (.proj s i m')

/-- Enlarging the equations leaves the existing eta typing witnesses intact. -/
theorem TypedComputeEta.mono
    (hD : ∀ {c ls rhs}, D.unfolds c ls rhs → D'.unfolds c ls rhs)
    (R : TypedComputeEta D Γ a b) : TypedComputeEta D' Γ a b := by
  induction R with
  | compute R => exact .compute (R.mono hD)
  | eta ht => exact .eta ht
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Every typed path in this fragment factors into beta/delta alone followed by
ordinary normal equality. No normalization assumption is used. -/
theorem TypedComputeEta.factor (hs : D.Sound env univs) (hl : D.LevelStable univs) (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedComputeEta D Γ a b) (ht : env.HasType univs Γ a T) : ComputeNormal D Γ a b := by
  induction R generalizing T with
  | compute R => exact .compute hs hΓ R ht
  | eta hf => exact .normal (.etaR hf (.refl (HasType.app (hf.weak henv) (.bvar .zero))))
  | trans _ _ ih1 ih2 =>
    have H1 := ih1 hΓ ht
    exact H1.trans hs hl hΓ (ih2 hΓ (H1.defeq hs hΓ ht).hasType.2)
  | app _ _ ihf iha =>
    obtain ⟨_, _, hf, ha⟩ := ht.app_inv henv hΓ
    exact .app hs hΓ hf ha (ihf hΓ hf) (iha hΓ ha)
  | lam _ _ ihA ihb =>
    obtain ⟨⟨_, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    exact .lam hs hΓ hA (ihA hΓ hA) (ihb ⟨hΓ, _, hA⟩ hb)
  | forallE _ _ ihA ihB =>
    obtain ⟨⟨_, hA⟩, _, hB⟩ := ht.forallE_inv henv
    exact .forallE hs hΓ hA hB (ihA hΓ hA) (ihB ⟨hΓ, _, hA⟩ hB)
  | proj _ ihm =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    exact .proj hs hΓ ht (ihm hΓ hm.hasType.2)

/-- Saturation supplies the level-stability hypothesis for every sound collection.
The input path may use the original equations; the output uses only their sound
universe closure and beta, followed by one ordinary normal comparison. -/
theorem TypedComputeEta.factor_levelClosure (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (R : TypedComputeEta D Γ a b)
    (ht : env.HasType univs Γ a T) : ComputeNormal (D.levelClosure univs) Γ a b :=
  (R.mono (Definitions.sound_in_levelClosure henv hs)).factor
    (Definitions.levelClosure_sound henv hs) Definitions.levelClosure_stable hΓ ht

/-- Actual stored equations with constant left-hand sides meet every hypothesis
of this factorization, including recursive equations. Applied patterns, prefixes,
projection-iota and structure eta remain outside the input relation. -/
theorem TypedComputeEta.factor_ofEnv (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedComputeEta (Definitions.ofEnv env univs henv) Γ a b)
    (ht : env.HasType univs Γ a T) :
    ComputeNormal ((Definitions.ofEnv env univs henv).levelClosure univs) Γ a b :=
  R.factor_levelClosure (Definitions.ofEnv_sound henv) hΓ ht

end Lean4Lean.VEnv.Strengthening.PureObservation
