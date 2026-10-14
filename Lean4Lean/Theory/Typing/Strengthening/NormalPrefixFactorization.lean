import Lean4Lean.Theory.Typing.Strengthening.NormalPrefixSimulation
import Lean4Lean.Theory.Typing.Strengthening.NormalPatternFactorization

/-! # Conditional eta postponement for finite prefix paths

Finite paths of actual pattern/prefix computation and typed function eta factor
into computation followed by ordinary normal comparison. The witnessed front
is assumed; structure eta and descent of opaque domains remain separate.
-/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params] {D : Definitions}

/-- Enlarging closed equations preserves every actual prefix check. -/
theorem PrefixCompute.mono (hD : ∀ {c ls rhs}, D.unfolds c ls rhs → D'.unfolds c ls rhs)
    (R : PrefixCompute D Γ a b) : PrefixCompute D' Γ a b := by
  induction R with
  | base R => exact .base (R.mono hD)
  | singleton R => exact .singleton R
  | quotient R => exact .quotient R
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Pattern and actual prefix computation followed by ordinary normal comparison. This is not a
recursive-domain certificate and is not claimed to descend through binders. -/
def PrefixNormal (D : Definitions) (Γ : List VExpr) (a b : VExpr) : Prop :=
  ∃ x, PrefixCompute D Γ a x ∧ NormalEq Γ x b

private theorem compute_eq (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (R : PrefixCompute D Γ a b)
    (ht : env.HasType univs Γ a T) : env.IsDefEq univs Γ a b T :=
  R.simAt hs hΓ _ ht

theorem PrefixNormal.normal (H : NormalEq Γ a b) : PrefixNormal D Γ a b := ⟨a, .refl, H⟩

theorem PrefixNormal.compute (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs)) (R : PrefixCompute D Γ a b)
    (ht : env.HasType univs Γ a T) : PrefixNormal D Γ a b :=
  ⟨b, R, .refl (compute_eq hs hΓ R ht).hasType.2⟩

theorem PrefixNormal.defeq (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixNormal D Γ a b) (ht : env.HasType univs Γ a T) : env.IsDefEq univs Γ a b T := by
  obtain ⟨x, R, N⟩ := H
  have hax := compute_eq hs hΓ R ht
  exact hax.trans ((N.defeq hΓ).of_l henv hΓ hax.hasType.2)

theorem PrefixNormal.trans (heq : env.HasCanonicalEq)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hs : D.Sound env univs) (hl : D.LevelStable univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (H1 : PrefixNormal D Γ a b) (H2 : PrefixNormal D Γ b c) : PrefixNormal D Γ a c := by
  obtain ⟨x, R1, N1⟩ := H1
  obtain ⟨y, R2, N2⟩ := H2
  obtain ⟨z, R3, N3⟩ := normal_prefix_simulation heq hs hl hfront hcon hΓ N1 R2
  exact ⟨z, R1.trans R3, N3.trans hΓ N2⟩

theorem PrefixNormal.app (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) (ha : env.HasType univs Γ a A)
    (HF : PrefixNormal D Γ f g) (HA : PrefixNormal D Γ a b) :
    PrefixNormal D Γ (.app f a) (.app g b) := by
  obtain ⟨f', Rf, Nf⟩ := HF
  obtain ⟨a', Ra, Na⟩ := HA
  have hf' := (compute_eq hs hΓ Rf hf).hasType.2
  have ha' := (compute_eq hs hΓ Ra ha).hasType.2
  exact ⟨_, .app Rf Ra, .appDF hf' ((Nf.defeq hΓ).of_l henv hΓ hf').hasType.2
    ha' ((Na.defeq hΓ).of_l henv hΓ ha').hasType.2 Nf Na⟩

theorem PrefixNormal.lam (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u))
    (HA : PrefixNormal D Γ A A') (HB : PrefixNormal D (A :: Γ) b b') :
    PrefixNormal D Γ (.lam A b) (.lam A' b') := by
  obtain ⟨A0, RA, NA⟩ := HA
  obtain ⟨b0, Rb, NB⟩ := HB
  have hAA := compute_eq hs hΓ RA hA
  exact ⟨_, .lam RA Rb, .lamDF hAA (hAA.trans ((NA.defeq hΓ).of_l henv hΓ hAA.hasType.2)) NB⟩

theorem PrefixNormal.forallE (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hB : env.HasType univs (A :: Γ) B (.sort v))
    (HA : PrefixNormal D Γ A A') (HB : PrefixNormal D (A :: Γ) B B') :
    PrefixNormal D Γ (.forallE A B) (.forallE A' B') := by
  obtain ⟨A0, RA, NA⟩ := HA
  obtain ⟨B0, RB, NB⟩ := HB
  exact ⟨_, .forallE RA RB, .forallEDF (compute_eq hs hΓ RA hA) NA
    (compute_eq (Γ := A :: Γ) hs ⟨hΓ, _, hA⟩ RB hB).hasType.2 NB⟩

theorem PrefixNormal.proj (hs : D.Sound env univs) (hΓ : OnCtx Γ (env.IsType univs))
    (hp : env.HasType univs Γ (.proj s i m) T) (HM : PrefixNormal D Γ m m') :
    PrefixNormal D Γ (.proj s i m) (.proj s i m') := by
  obtain ⟨m0, Rm, NM⟩ := HM
  exact ⟨_, .proj Rm, .projDF (compute_eq hs hΓ (.proj Rm) hp).hasType.2 NM⟩

/-- The compatible pattern/prefix/function-eta fragment of full reduction. Eta
requires actual typing. Structure eta remains outside this relation. -/
inductive TypedPrefixEta (D : Definitions) : List VExpr → VExpr → VExpr → Prop where
  | compute : PrefixCompute D Γ a b → TypedPrefixEta D Γ a b
  | eta : env.HasType univs Γ f (.forallE A B) →
      TypedPrefixEta D Γ f (.lam A (.app f.lift (.bvar 0)))
  | trans : TypedPrefixEta D Γ a b → TypedPrefixEta D Γ b c → TypedPrefixEta D Γ a c
  | app : TypedPrefixEta D Γ f f' → TypedPrefixEta D Γ a a' →
      TypedPrefixEta D Γ (.app f a) (.app f' a')
  | lam : TypedPrefixEta D Γ A A' → TypedPrefixEta D (A :: Γ) b b' →
      TypedPrefixEta D Γ (.lam A b) (.lam A' b')
  | forallE : TypedPrefixEta D Γ A A' → TypedPrefixEta D (A :: Γ) B B' →
      TypedPrefixEta D Γ (.forallE A B) (.forallE A' B')
  | proj : TypedPrefixEta D Γ m m' → TypedPrefixEta D Γ (.proj s i m) (.proj s i m')

/-- Enlarging the equations leaves the existing eta typing witnesses intact. -/
theorem TypedPrefixEta.mono
    (hD : ∀ {c ls rhs}, D.unfolds c ls rhs → D'.unfolds c ls rhs)
    (R : TypedPrefixEta D Γ a b) : TypedPrefixEta D' Γ a b := by
  induction R with
  | compute R => exact .compute (R.mono hD)
  | eta ht => exact .eta ht
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | proj _ ih => exact .proj ih

/-- Under the witnessed front, every typed path in this fragment factors into
pattern and prefix computation followed by normal equality. No normalization
assumption is used, and the final domain comparisons remain opaque. -/
theorem TypedPrefixEta.factor (heq : env.HasCanonicalEq)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hs : D.Sound env univs) (hl : D.LevelStable univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedPrefixEta D Γ a b) (ht : env.HasType univs Γ a T) : PrefixNormal D Γ a b := by
  induction R generalizing T with
  | compute R => exact .compute hs hΓ R ht
  | eta hf => exact .normal (.etaR hf (.refl (HasType.app (hf.weak henv) (.bvar .zero))))
  | trans _ _ ih1 ih2 =>
    have H1 := ih1 hΓ ht
    exact H1.trans heq hfront hs hl hcon hΓ (ih2 hΓ (H1.defeq hs hΓ ht).hasType.2)
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
The input path may use the original equations; the output retains actual
prefix checks and uses the sound universe closure of those equations. -/
theorem TypedPrefixEta.factor_levelClosure (heq : env.HasCanonicalEq)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hs : D.Sound env univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (R : TypedPrefixEta D Γ a b)
    (ht : env.HasType univs Γ a T) : PrefixNormal (D.levelClosure univs) Γ a b :=
  (R.mono (Definitions.sound_in_levelClosure henv hs)).factor heq hfront
    (Definitions.levelClosure_sound henv hs) Definitions.levelClosure_stable hcon hΓ ht

/-- Actual stored equations with constant left-hand sides meet every hypothesis
of this factorization, including recursive equations. Structure eta remains outside the input
relation, and the witnessed proposition front remains an explicit hypothesis. -/
theorem TypedPrefixEta.factor_ofEnv (heq : env.HasCanonicalEq)
    (hfront : GuardedSingleton.WitnessedPropDescent (fun Δ a b => env.IsDefEqU univs Δ a b))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r) (hΓ : OnCtx Γ (env.IsType univs))
    (R : TypedPrefixEta (Definitions.ofEnv env univs henv) Γ a b)
    (ht : env.HasType univs Γ a T) :
    PrefixNormal ((Definitions.ofEnv env univs henv).levelClosure univs) Γ a b :=
  R.factor_levelClosure heq hfront (Definitions.ofEnv_sound henv) hcon hΓ ht

end Lean4Lean.VEnv.Strengthening.PureObservation
