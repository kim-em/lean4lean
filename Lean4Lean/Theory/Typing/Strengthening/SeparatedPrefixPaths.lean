import Lean4Lean.Theory.Typing.Strengthening.SeparatedPrefixDiamond

/-! # Exact finite commutation with augmented ordinary computation -/
namespace Lean4Lean.VEnv.Strengthening.PureObservation
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- A concrete-pattern interface embeds core parallel computation in ordinary
computation over any closed definition collection. -/
theorem PatternCompute.of_parRed_concrete
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : ParRed Γ e out) : PatternCompute D e out := by
  induction H with
  | bvar | sort | const => exact .refl
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | proj _ ih => exact .proj ih
  | beta _ _ ihb iha =>
    exact (PatternCompute.app (.lam .refl ihb) iha).trans (.base (.base .beta))
  | extra hp hm hc _ ih =>
    exact (PatternCompute.pattern hp hm (ConcretePattern.checkFromTyping henv (hcon hp) hc)).trans
      (PatternCompute.apply_pat _ ih)

/-- Finite core paths embed with unchanged endpoints. -/
theorem PatternCompute.of_parRedS_concrete
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (H : ParRedS Γ e out) : PatternCompute D e out := by
  induction H with
  | rfl => exact .refl
  | tail _ H ih => exact ih.trans (.of_parRed_concrete hcon H)

end Lean4Lean.VEnv.Strengthening.PureObservation

namespace Lean4Lean.VEnv
open _root_.Lean4Lean VExpr Params Strengthening Strengthening.PureObservation
variable [Params]

/-- One actual prefix/projection development commutes with an entire augmented
ordinary path, retaining one actual residual prefix/projection development. -/
theorem DeltaPar.separated_path_diamond_exact (hΓ : OnCtx Γ (env.IsType univs))
    (H : DeltaPar Γ a b)
    (H2 : SeparatedPatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) a c)
    (ha : env.HasType univs Γ a A) :
    ∃ d, SeparatedPatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) b d ∧
      DeltaPar Γ c d := by
  have hs := RegisteredStructure.definitions_sound (Definitions.ofEnv_sound henv)
  have aux {a c} (HP : ReflTransGen
      (SeparatedPar (RegisteredStructure.definitions (Definitions.ofEnv env univs henv))) a c)
      {b A} (HD : DeltaPar Γ a b) (ht : env.HasType univs Γ a A) :
      ∃ d, SeparatedPatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) b d ∧
        DeltaPar Γ c d := by
    have typed {a c} (HP : ReflTransGen
        (SeparatedPar (RegisteredStructure.definitions (Definitions.ofEnv env univs henv))) a c)
        (ht : env.HasType univs Γ a A) : env.HasType univs Γ c A := by
      induction HP with
      | rfl => exact ht
      | tail _ R ih => exact (R.simAt hs hΓ _ ih).hasType.2
    induction HP with
    | rfl => exact ⟨b, .base (.base .refl), HD⟩
    | tail HP P ih =>
      obtain ⟨middle, HB, HD⟩ := ih
      obtain ⟨d, PB, DD⟩ := HD.separated_diamond_exact hΓ P (typed HP ht)
      exact ⟨d, HB.trans PB.toCompute, DD⟩
  exact aux H2.toParallel H ha

/-- Finite actual-prefix/projection paths and augmented ordinary paths commute
exactly, without normalization or a strengthening front. -/
theorem DeltaPar.star_separated_commute_exact (hΓ : OnCtx Γ (env.IsType univs))
    (H : ReflTransGen (DeltaPar Γ) a b)
    (H2 : SeparatedPatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) a c)
    (ha : env.HasType univs Γ a A) :
    ∃ d, SeparatedPatternCompute (RegisteredStructure.definitions (Definitions.ofEnv env univs henv)) b d ∧
      ReflTransGen (DeltaPar Γ) c d := by
  induction H with
  | rfl => exact ⟨c, H2, .rfl⟩
  | tail HD D ih =>
    obtain ⟨middle, HP, HC⟩ := ih
    obtain ⟨d, PB, DD⟩ := D.separated_path_diamond_exact hΓ HP (DeltaPar.star_hasType hΓ HD ha)
    exact ⟨d, PB, HC.tail DD⟩

end Lean4Lean.VEnv
