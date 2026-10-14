import Lean4Lean.Theory.Typing.Strengthening.SeparatedPrefixPaths
import Lean4Lean.Theory.Typing.Strengthening.ExactPrefixPeaks

/-! # Confluence with actual prefixes and selected closed structure equations

Separated ordinary computation supplies level zero. Actual prefix/projection
parallel reduction supplies level one. Exact mixed diamonds and prefix self-peaks
therefore give decreasing diagrams, without any eta or normal-comparison step.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params PureObservation
variable [Params]

/-- Ordinary computation over all stored and selected closed structure equations,
together with actual prefix/projection parallel computation. -/
def AugmentedComputeStep (Γ : List VExpr) (a b : VExpr) : Prop :=
  PatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) a b ∨
    DeltaPar Γ a b

/-- Arbitrary finite interleavings of augmented ordinary and actual prefix steps. -/
abbrev AugmentedCompute (Γ : List VExpr) := ReflTransGen (AugmentedComputeStep Γ)

private abbrev actualD : Definitions :=
  RegisteredStructure.definitions (Definitions.ofEnv env univs henv)

private theorem actual_sound : actualD.Sound env univs :=
  RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)

/-- Finite augmented computation preserves every source type. -/
theorem AugmentedCompute.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : AugmentedCompute Γ a b) (ha : env.HasType univs Γ a A) : env.HasType univs Γ b A := by
  induction H with
  | rfl => exact ha
  | tail _ H ih =>
    rcases H with H | H
    · exact (H.simAt actual_sound hΓ _ ih).hasType.2
    · exact H.full.hasType hΓ ih

private def AugmentedRel (Γ : List VExpr) (n : Nat) (a b : VExpr) : Prop :=
  VExpr.WF env univs Γ a ∧ match n with
    | 0 => SeparatedPatternCompute actualD a b
    | 1 => DeltaPar Γ a b
    | _ => False

private theorem augmented_zero (hΓ : OnCtx Γ (env.IsType univs)) :
    Levelled.Joinable (AugmentedRel Γ 0) := by
  have flatten {a b} (H : ReflTransGen (AugmentedRel Γ 0) a b) :
      SeparatedPatternCompute actualD a b := by
    induction H with
    | rfl => exact .base (.base .refl)
    | tail _ H ih => exact ih.trans H.2
  intro a b c H1 H2
  cases H1 with
  | rfl => exact ⟨c, H2, .rfl⟩
  | @tail b₀ _ H1 R1 =>
    have typed {a c} (H : ReflTransGen (AugmentedRel Γ 0) a c) (hc : VExpr.WF env univs Γ c) :
        VExpr.WF env univs Γ a := by
      induction H with
      | rfl => exact hc
      | tail _ R ih => exact ih R.1
    have hb := (R1.2.simAt actual_sound hΓ _ R1.1.choose_spec).hasType.2
    have ha := typed H1 R1.1
    have hc := ((flatten H2).simAt actual_sound hΓ _ ha.choose_spec).hasType.2
    obtain ⟨d, HB, HC⟩ := (flatten (.tail H1 R1)).confluent
      (fun H1 H2 => RegisteredStructure.definitions_ofEnv_unique H1 H2)
      (fun hr _ _ => RegisteredStructure.definitions_ofEnv_no_rigid hr) (flatten H2)
    exact ⟨d, .tail .rfl ⟨⟨_, hb⟩, HB⟩, .tail .rfl ⟨⟨_, hc⟩, HC⟩⟩

private theorem core_lo
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : ParRedS Γ a b) (ha : env.HasType univs Γ a A) :
    Levelled.LoStar (AugmentedRel Γ) 1 a b :=
  .tail .rfl ⟨0, by decide, ⟨_, ha⟩, (PatternCompute.of_parRedS_concrete hcon H).toSeparated hcon hΓ ⟨_, ha⟩⟩

private theorem augmented_peak
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n, 0 < n → ∀ a b c, AugmentedRel Γ n a b → AugmentedRel Γ n a c →
      ∃ d, Levelled.LoOptLo (AugmentedRel Γ) n b d ∧ Levelled.LoOptLo (AugmentedRel Γ) n c d := by
  intro n hn a b c ⟨⟨A, ha⟩, H1⟩ ⟨_, H2⟩
  match n, H1, H2 with
  | 0, _, _ => omega
  | 1, H1, H2 =>
    obtain ⟨d, ⟨b₁, DB, PB⟩, ⟨c₁, DC, PC⟩⟩ := ExactPrefix.parallel_peak hΓ H1 H2 ha
    have hb := H1.full.hasType hΓ ha
    have hc := H2.full.hasType hΓ ha
    exact ⟨d, ⟨b, b₁, .rfl, .inr ⟨⟨_, hb⟩, DB⟩, core_lo hcon hΓ PB (DB.full.hasType hΓ hb)⟩,
      ⟨c, c₁, .rfl, .inr ⟨⟨_, hc⟩, DC⟩, core_lo hcon hΓ PC (DC.full.hasType hΓ hc)⟩⟩
  | _ + 2, H1, _ => exact H1.elim

private theorem augmented_mixed (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n, 0 < n → ∀ a b c, AugmentedRel Γ n a b → Levelled.Lo (AugmentedRel Γ) n a c →
      ∃ d, Levelled.LoStar (AugmentedRel Γ) n b d ∧ Levelled.OptLo (AugmentedRel Γ) n c d := by
  intro n hn a b c ⟨⟨A, ha⟩, H1⟩ ⟨k, hk, _, H2⟩
  match n, k, hk, H1, H2 with
  | 0, _, hk, _, _ => omega
  | 1, 0, _, H1, H2 =>
    obtain ⟨d, HB, HC⟩ := H1.separated_path_diamond_exact hΓ H2 ha
    exact ⟨d, .tail .rfl ⟨0, by decide, ⟨_, H1.full.hasType hΓ ha⟩, HB⟩,
      ⟨d, .inr ⟨⟨_, (H2.simAt actual_sound hΓ _ ha).hasType.2⟩, HC⟩, .rfl⟩⟩
  | 1, _ + 1, hk, _, _ => omega
  | _ + 2, _, _, H1, _ => exact H1.elim

private theorem augmented_to_levels
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : AugmentedCompute Γ a b) (ha : env.HasType univs Γ a A) :
    Levelled.LoStar (AugmentedRel Γ) 2 a b := by
  induction H with
  | rfl => exact .rfl
  | tail H R ih =>
    have ht := AugmentedCompute.hasType hΓ H ha
    rcases R with R | R
    · exact ih.tail ⟨0, by decide, ⟨_, ht⟩, R.toSeparated hcon hΓ ⟨_, ht⟩⟩
    · exact ih.tail ⟨1, by decide, ⟨_, ht⟩, R⟩

private theorem augmented_from_levels (H : Levelled.LoStar (AugmentedRel Γ) 2 a b) :
    AugmentedCompute Γ a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ R ih =>
    obtain ⟨k, hk, _, R⟩ := R
    match k, hk, R with
    | 0, _, R => exact ih.tail (.inl R.toPattern)
    | 1, _, R => exact ih.tail (.inr R)
    | _ + 2, hk, _ => omega

/-- Exact confluence of finite computation including recursive stored definitions,
selected closed structure programs, all concrete ordinary patterns, actual
indexed singleton/quotient prefixes, and projections. No canonical Eq,
normalization, normal comparison or strengthening premise is used. -/
theorem AugmentedCompute.confluent
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A)
    (H1 : AugmentedCompute Γ a b) (H2 : AugmentedCompute Γ a c) :
    ∃ d, AugmentedCompute Γ b d ∧ AugmentedCompute Γ c d := by
  have HC := Levelled.joinable (R := AugmentedRel Γ) (augmented_zero hΓ)
    (augmented_peak hcon hΓ) (augmented_mixed hΓ) 1
  obtain ⟨d, HB, HC⟩ := HC a b c (augmented_to_levels hcon hΓ H1 ha) (augmented_to_levels hcon hΓ H2 ha)
  exact ⟨d, augmented_from_levels HB, augmented_from_levels HC⟩

end Lean4Lean.VEnv.Strengthening
