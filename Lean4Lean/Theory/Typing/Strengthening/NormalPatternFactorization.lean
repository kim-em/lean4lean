import Lean4Lean.Theory.Typing.Strengthening.NormalPatternSimulation

/-! # Postponing normal comparison after pattern reduction

Finite paths of pattern computation and ordinary normal comparison factor into
pattern computation followed by one normal comparison. Compatibility includes
lambda annotations, whose equalities remain opaque in that comparison.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Enlarging closed equations preserves projection and pattern computation. -/
theorem PatternCompute.mono (hD : ∀ {c ls rhs}, D.unfolds c ls rhs → D'.unfolds c ls rhs)
    (R : PatternCompute D a b) : PatternCompute D' a b := by
  have hC {a b} (R : Compute D a b) : Compute D' a b := by
    induction R with
    | refl => exact .refl
    | beta => exact .beta
    | delta H => exact .delta (hD H)
    | trans _ _ ih1 ih2 => exact .trans ih1 ih2
    | app _ _ ih1 ih2 => exact .app ih1 ih2
    | lam _ _ ih1 ih2 => exact .lam ih1 ih2
    | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
    | proj _ ih => exact .proj ih
  have hP {a b} (R : ProjectionCompute D a b) : ProjectionCompute D' a b := by
    induction R with
    | base R => exact .base (hC R)
    | projIota hi hl hg => exact .projIota hi hl hg
    | trans _ _ ih1 ih2 => exact .trans ih1 ih2
    | app _ _ ih1 ih2 => exact .app ih1 ih2
    | lam _ _ ih1 ih2 => exact .lam ih1 ih2
    | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
    | proj _ ih => exact .proj ih
  induction R with
  | base R => exact .base (hP R)
  | pattern hp hm hc => exact .pattern hp hm hc
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih


/-- Beta/delta computation followed by ordinary normal comparison. This is not a
recursive-domain certificate and is not claimed to descend through binders. -/
def PatternNormal (D : Definitions) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ x, PatternCompute D a x ∧ NormalEq Γ x b

private theorem compute_eq (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (R : PatternCompute D a b)
    (ht : env.HasType univs Γ a T) : env.IsDefEq univs Γ a b T :=
  R.simAt hs hΓ _ ht

theorem PatternNormal.normal (H : NormalEq Γ a b) : PatternNormal D Γ a b := ⟨a, .refl, H⟩

theorem PatternNormal.compute (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (R : PatternCompute D a b)
    (ht : env.HasType univs Γ a T) : PatternNormal D Γ a b :=
  ⟨b, R, .refl (compute_eq hs hΓ R ht).hasType.2⟩

theorem PatternNormal.defeq (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (H : PatternNormal D Γ a b) (ht : env.HasType univs Γ a T) : env.IsDefEq univs Γ a b T := by
  obtain ⟨x, R, N⟩ := H
  have hax := compute_eq hs hΓ R ht
  exact hax.trans ((N.defeq hΓ).of_l henv hΓ hax.hasType.2)

theorem PatternNormal.trans (hs : D.Sound env univs) (hl : D.LevelStable univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : PatternNormal D Γ a b) (H2 : PatternNormal D Γ b c) : PatternNormal D Γ a c := by
  obtain ⟨x, R1, N1⟩ := H1
  obtain ⟨y, R2, N2⟩ := H2
  obtain ⟨z, R3, N3⟩ := normal_pattern_simulation hs hl hcon hΓ N1 R2
  exact ⟨z, R1.trans R3, N3.trans hΓ N2⟩

theorem PatternNormal.app (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (ha : env.HasType univs Γ a A)
    (HF : PatternNormal D Γ f g) (HA : PatternNormal D Γ a b) :
    PatternNormal D Γ (.app f a) (.app g b) := by
  obtain ⟨f', Rf, Nf⟩ := HF
  obtain ⟨a', Ra, Na⟩ := HA
  have hf' := (compute_eq hs hΓ Rf hf).hasType.2
  have ha' := (compute_eq hs hΓ Ra ha).hasType.2
  exact ⟨_, .app Rf Ra, .appDF hf' ((Nf.defeq hΓ).of_l henv hΓ hf').hasType.2
    ha' ((Na.defeq hΓ).of_l henv hΓ ha').hasType.2 Nf Na⟩

theorem PatternNormal.lam (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HA : PatternNormal D Γ A A') (HB : PatternNormal D (A :: Γ) b b') :
    PatternNormal D Γ (.lam A b) (.lam A' b') := by
  obtain ⟨A0, RA, NA⟩ := HA
  obtain ⟨b0, Rb, NB⟩ := HB
  have hAA := compute_eq hs hΓ RA hA
  exact ⟨_, .lam RA Rb, .lamDF hAA (hAA.trans ((NA.defeq hΓ).of_l henv hΓ hAA.hasType.2)) NB⟩

theorem PatternNormal.forallE (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (HA : PatternNormal D Γ A A') (HB : PatternNormal D (A :: Γ) B B') :
    PatternNormal D Γ (.forallE A B) (.forallE A' B') := by
  obtain ⟨A0, RA, NA⟩ := HA
  obtain ⟨B0, RB, NB⟩ := HB
  exact ⟨_, .forallE RA RB, .forallEDF (compute_eq hs hΓ RA hA) NA
    (compute_eq (Γ := A :: Γ) hs ⟨hΓ, _, hA⟩ RB hB).hasType.2 NB⟩

theorem PatternNormal.proj (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ (.proj s i m) T) (HM : PatternNormal D Γ m m') :
    PatternNormal D Γ (.proj s i m) (.proj s i m') := by
  obtain ⟨m0, Rm, NM⟩ := HM
  exact ⟨_, .proj Rm, .projDF (compute_eq hs hΓ (.proj Rm) hp).hasType.2 NM⟩

/-- The compatible pattern/function-eta fragment of full reduction. Eta requires
actual typing; there are no prefix or structure-eta
steps. This restriction is explicit rather than a claim about full computation. -/
inductive TypedPatternEta (D : Definitions) : List VExpr → VExpr → VExpr → Prop where
  | compute : PatternCompute D a b → TypedPatternEta D Γ a b
  | eta : env.HasType univs Γ f (.forallE A B) →
      TypedPatternEta D Γ f (.lam A (.app f.lift (.bvar 0)))
  | trans : TypedPatternEta D Γ a b → TypedPatternEta D Γ b c → TypedPatternEta D Γ a c
  | app : TypedPatternEta D Γ f f' → TypedPatternEta D Γ a a' →
      TypedPatternEta D Γ (.app f a) (.app f' a')
  | lam : TypedPatternEta D Γ A A' → TypedPatternEta D (A :: Γ) b b' →
      TypedPatternEta D Γ (.lam A b) (.lam A' b')
  | forallE : TypedPatternEta D Γ A A' → TypedPatternEta D (A :: Γ) B B' →
      TypedPatternEta D Γ (.forallE A B) (.forallE A' B')
  | proj : TypedPatternEta D Γ m m' → TypedPatternEta D Γ (.proj s i m) (.proj s i m')

/-- Enlarging the equations leaves the existing eta typing witnesses intact. -/
theorem TypedPatternEta.mono
    (hD : ∀ {c ls rhs}, D.unfolds c ls rhs → D'.unfolds c ls rhs)
    (R : TypedPatternEta D Γ a b) : TypedPatternEta D' Γ a b := by
  induction R with
  | compute R => exact .compute (R.mono hD)
  | eta ht => exact .eta ht
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Every typed path in this fragment factors into pattern alone followed by
ordinary normal equality. No normalization assumption is used. -/
theorem TypedPatternEta.factor (hs : D.Sound env univs) (hl : D.LevelStable univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedPatternEta D Γ a b) (ht : env.HasType univs Γ a T) : PatternNormal D Γ a b := by
  induction R generalizing T with
  | compute R => exact .compute hs hΓ R ht
  | eta hf => exact .normal (.etaR hf (.refl (HasType.app (hf.weak henv) (.bvar .zero))))
  | trans _ _ ih1 ih2 =>
    have H1 := ih1 hΓ ht
    exact H1.trans hs hl hcon hΓ (ih2 hΓ (H1.defeq hs hΓ ht).hasType.2)
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
universe closure, beta, patterns and projections, followed by normal comparison. -/
theorem TypedPatternEta.factor_levelClosure (hs : D.Sound env univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (R : TypedPatternEta D Γ a b)
    (ht : env.HasType univs Γ a T) : PatternNormal (D.levelClosure univs) Γ a b :=
  (R.mono (Definitions.sound_in_levelClosure henv hs)).factor
    (Definitions.levelClosure_sound henv hs) Definitions.levelClosure_stable hcon hΓ ht

/-- Actual stored equations with constant left-hand sides meet every hypothesis
of this factorization, including recursive equations. Prefixes and structure eta
remain outside the input relation. -/
theorem TypedPatternEta.factor_ofEnv
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedPatternEta (Definitions.ofEnv env univs henv) Γ a b)
    (ht : env.HasType univs Γ a T) :
    PatternNormal ((Definitions.ofEnv env univs henv).levelClosure univs) Γ a b :=
  R.factor_levelClosure (Definitions.ofEnv_sound henv) hcon hΓ ht

end Lean4Lean.VEnv.Strengthening.PureObservation
