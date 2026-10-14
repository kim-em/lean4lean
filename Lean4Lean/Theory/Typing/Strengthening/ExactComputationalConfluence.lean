import Lean4Lean.Theory.Typing.Strengthening.ExactCoreTriangle
import Lean4Lean.Theory.Typing.Strengthening.ExactPrefixPeaks

/-! # Exact confluence of core, actual prefixes and projections

The two computational parallel relations have decreasing diagrams with exact
endpoints. Their finite union is therefore confluent from every typed source.
Function/structure eta and equivalent-universe comparison are not steps here.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- The computational part of the original full presentation, without eta or
normal-comparison steps. Projection roots belong to DeltaPar. -/
def PrefixCoreStep (Γ : List VExpr) (a b : VExpr) : Prop :=
  ParRed Γ a b ∨ DeltaPar Γ a b

/-- Finite mixed paths of core and actual prefix/projection computation. -/
abbrev PrefixCoreReduction (Γ : List VExpr) := ReflTransGen (PrefixCoreStep Γ)

/-- The union preserves every source type. -/
theorem PrefixCoreReduction.hasType (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixCoreReduction Γ a b) (ha : env.HasType univs Γ a A) : env.HasType univs Γ b A := by
  induction H with
  | rfl => exact ha
  | tail _ H ih =>
    rcases H with H | H
    · exact H.hasType hΓ ih
    · exact H.full.hasType hΓ ih

private def ComputationalRel (Γ : List VExpr) (n : Nat) (a b : VExpr) : Prop :=
  VExpr.WF env univs Γ a ∧ match n with
    | 1 => ParRed Γ a b
    | 2 => DeltaPar Γ a b
    | _ => False

private theorem core_lo (hΓ : OnCtx Γ (env.IsType univs))
    (H : ParRedS Γ a b) (ha : env.HasType univs Γ a A) :
    Levelled.LoStar (ComputationalRel Γ) 2 a b := by
  induction H with
  | rfl => exact .rfl
  | tail HP P ih => exact ih.tail ⟨1, by decide, ⟨_, ParRedS.hasType hΓ HP ha⟩, P⟩

private theorem computational_zero : Levelled.Joinable (ComputationalRel Γ 0) := by
  have eq_of {a b} (H : ReflTransGen (ComputationalRel Γ 0) a b) : a = b := by
    induction H with
    | rfl => rfl
    | tail _ H _ => exact H.2.elim
  intro a b c H1 H2
  cases eq_of H1
  cases eq_of H2
  exact ⟨a, .rfl, .rfl⟩

private theorem computational_peak (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n, 0 < n → ∀ a b c, ComputationalRel Γ n a b → ComputationalRel Γ n a c →
      ∃ d, Levelled.LoOptLo (ComputationalRel Γ) n b d ∧
        Levelled.LoOptLo (ComputationalRel Γ) n c d := by
  intro n hn a b c ⟨⟨A, ha⟩, H1⟩ ⟨_, H2⟩
  match n, H1, H2 with
  | 0, H1, _ => exact H1.elim
  | 1, H1, H2 =>
    obtain ⟨d, HB, HC⟩ := ParRed.diamond_exact hΓ ha H1 H2
    exact ⟨d, ⟨b, d, .rfl, .inr ⟨⟨_, H1.hasType hΓ ha⟩, HB⟩, .rfl⟩,
      ⟨c, d, .rfl, .inr ⟨⟨_, H2.hasType hΓ ha⟩, HC⟩, .rfl⟩⟩
  | 2, H1, H2 =>
    obtain ⟨d, ⟨b₁, DB, PB⟩, ⟨c₁, DC, PC⟩⟩ := ExactPrefix.parallel_peak hΓ H1 H2 ha
    have hb := H1.full.hasType hΓ ha
    have hc := H2.full.hasType hΓ ha
    exact ⟨d, ⟨b, b₁, .rfl, .inr ⟨⟨_, hb⟩, DB⟩, core_lo hΓ PB (DB.full.hasType hΓ hb)⟩,
      ⟨c, c₁, .rfl, .inr ⟨⟨_, hc⟩, DC⟩, core_lo hΓ PC (DC.full.hasType hΓ hc)⟩⟩
  | _ + 3, H1, _ => exact H1.elim

private theorem computational_mixed (hΓ : OnCtx Γ (env.IsType univs)) :
    ∀ n, 0 < n → ∀ a b c, ComputationalRel Γ n a b →
      Levelled.Lo (ComputationalRel Γ) n a c →
      ∃ d, Levelled.LoStar (ComputationalRel Γ) n b d ∧
        Levelled.OptLo (ComputationalRel Γ) n c d := by
  intro n hn a b c ⟨⟨A, ha⟩, H1⟩ ⟨k, hk, _, H2⟩
  match n, k, hk, H1, H2 with
  | 0, _, hk, _, _ => omega
  | 1, 0, _, _, H2 => exact H2.elim
  | 2, 0, _, _, H2 => exact H2.elim
  | 2, 1, _, H1, H2 =>
    obtain ⟨d, HB, HC⟩ := H1.parRed_diamond_exact hΓ H2 ha
    exact ⟨d, .tail .rfl ⟨1, by decide, ⟨_, H1.full.hasType hΓ ha⟩, HB⟩,
      ⟨d, .inr ⟨⟨_, H2.hasType hΓ ha⟩, HC⟩, .rfl⟩⟩
  | 1, _ + 1, hk, _, _ => omega
  | 2, _ + 2, hk, _, _ => omega
  | _ + 3, _, _, H1, _ => exact H1.elim

private theorem computational_to_levels (hΓ : OnCtx Γ (env.IsType univs))
    (H : PrefixCoreReduction Γ a b) (ha : env.HasType univs Γ a A) :
    Levelled.LoStar (ComputationalRel Γ) 3 a b := by
  induction H with
  | rfl => exact .rfl
  | tail H R ih =>
    have ht := PrefixCoreReduction.hasType hΓ H ha
    rcases R with R | R
    · exact ih.tail ⟨1, by decide, ⟨_, ht⟩, R⟩
    · exact ih.tail ⟨2, by decide, ⟨_, ht⟩, R⟩

private theorem computational_from_levels (H : Levelled.LoStar (ComputationalRel Γ) 3 a b) :
    PrefixCoreReduction Γ a b := by
  induction H with
  | rfl => exact .rfl
  | tail _ R ih =>
    obtain ⟨k, hk, _, R⟩ := R
    match k, hk, R with
    | 0, _, R => exact R.elim
    | 1, _, R => exact ih.tail (.inl R)
    | 2, _, R => exact ih.tail (.inr R)
    | _ + 3, hk, _ => omega

/-- Exact finite computational confluence for beta/pattern reduction, checked
singleton and quotient prefixes, and constructor projections. No normal
comparison, canonical Eq, normalization or strengthening premise is used. -/
theorem PrefixCoreReduction.confluent (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (H1 : PrefixCoreReduction Γ a b)
    (H2 : PrefixCoreReduction Γ a c) :
    ∃ d, PrefixCoreReduction Γ b d ∧ PrefixCoreReduction Γ c d := by
  have HC := Levelled.joinable (R := ComputationalRel Γ) computational_zero
    (computational_peak hΓ) (computational_mixed hΓ) 2
  obtain ⟨d, HB, HC⟩ := HC a b c (computational_to_levels hΓ H1 ha) (computational_to_levels hΓ H2 ha)
  exact ⟨d, computational_from_levels HB, computational_from_levels HC⟩

end Lean4Lean.VEnv.Strengthening
