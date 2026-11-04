import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedNativeEtaExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureExpansionStages

/-! # Recovered stages with native eta expansion

The existing controlled beta expansions and recovered guards remain available.
An additional guarded eta expansion selects its annotation at the preceding
stage. The system retains arbitrary-block descent and exact renaming.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
variable [Params]

/-- Controlled beta expansion at the base, with recovered singleton, Eq,
identity and eta guards using the entire preceding stage. -/
def ErasedEtaExpansionStage (D : Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => ErasedExpansionStage D 0
  | n + 1 => fun Δ a b => ErasedEtaExpansionStage D n Δ a b ∨
      CarrierRecoveredSingletonPrimitive (ErasedEtaExpansionStage D n) Δ a b ∨
      ComputedJointPrefixPrimitive (ErasedEtaExpansionStage D n) Δ a b ∨
      NativeIdentityExpansion (ErasedEtaExpansionStage D n) Δ a b ∨
      NativeEtaExpansion (ErasedEtaExpansionStage D n) Δ a b

/-- Every previous expanded stage embeds at the same index. -/
theorem erased_expansion_into_eta_stage : ∀ n {Δ a b},
    ErasedExpansionStage D n Δ a b → ErasedEtaExpansionStage D n Δ a b := by
  intro n
  induction n with
  | zero => exact id
  | succ n ih =>
    intro Δ a b H
    rcases H with H | H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.mono ih))
    · exact .inr (.inr (.inl (H.mono ih)))
    · exact .inr (.inr (.inr (.inl (H.mono ih))))

/-- The eta-expanded stages increase monotonically. -/
theorem erased_eta_expansion_stage_mono (hle : n ≤ m) {Δ a b}
    (H : ErasedEtaExpansionStage D n Δ a b) : ErasedEtaExpansionStage D m Δ a b := by
  induction hle with
  | refl => exact H
  | step _ ih => exact .inl ih

/-- Every eta-expanded stage descends through arbitrary inserted binder blocks. -/
theorem erased_eta_expansion_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ n, ErasedScopedPrimitiveDescent (ErasedEtaExpansionStage D n) := by
  intro n
  induction n with
  | zero => exact erased_expansion_stage_descent heq hs 0
  | succ n ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H | H | H
    · exact ih hΓ hΓ' W ht H
    · exact erased_singleton_with_descent heq (erased_carrier_recovered_family_descent ih) hΓ hΓ' W ht H.2
    · exact erased_computed_joint_prefix_descent heq ih hΓ hΓ' W ht H
    · exact erased_nativeIdentityExpansion_descent ih hΓ hΓ' W ht H
    · exact erased_nativeEtaExpansion_descent ih hΓ hΓ' W ht H

/-- Exact interpreted renaming preserves all eta-expanded primitive guards. -/
theorem erased_eta_expansion_stage_rename (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ n {Δ Δ' a b τ}, ErasedEtaExpansionStage D n Δ a b → ContextRenaming Δ Δ' τ →
      ErasedEtaExpansionStage D n Δ' (a.subst τ) (b.subst τ) := by
  intro n
  induction n with
  | zero => exact erased_expansion_stage_rename heq hs 0
  | succ n ih =>
    intro Δ Δ' a b τ H W
    rcases H with H | H | H | H | H
    · exact .inl (ih H W)
    · exact .inr (.inl (H.rename heq (erased_eta_expansion_stage_descent heq hs n)
        (erased_eta_expansion_stage_descent heq hs n) ih W))
    · exact .inr (.inr (.inl (H.rename ih W)))
    · exact .inr (.inr (.inr (.inl (H.rename ih W))))
    · exact .inr (.inr (.inr (.inr (H.rename ih W))))

/-- Finite eta-expanded guard depth, with no fixed upper bound. -/
def ErasedEtaExpansionUnion (D : Definitions) (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∃ n, ErasedEtaExpansionStage D n Δ a b

/-- The eta-expanded union retains source-typed binder descent. -/
theorem erased_eta_expansion_union_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (ErasedEtaExpansionUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht ⟨stage, H⟩
  exact erased_eta_expansion_stage_descent heq hs stage hΓ hΓ' W ht H

/-- The entire previous expansion union embeds in the eta-expanded union. -/
theorem erased_expansion_into_eta_union (H : ErasedExpansionUnion D Δ a b) :
    ErasedEtaExpansionUnion D Δ a b := by
  obtain ⟨n, H⟩ := H
  exact ⟨n, erased_expansion_into_eta_stage n H⟩

/-- A native eta guard over the union is already admitted at a finite stage. -/
theorem erased_eta_expansion_union_eta
    (H : NativeEtaExpansion (ErasedEtaExpansionUnion D) Δ a b) :
    ErasedEtaExpansionUnion D Δ a b := by
  cases H with
  | intro R S =>
    obtain ⟨n, R⟩ := R.finite_stage (Stages := ErasedEtaExpansionStage D)
      (fun {n m} hle {Δ a b} H => erased_eta_expansion_stage_mono hle H)
    exact ⟨n + 1, .inr (.inr (.inr (.inr (.intro R S))))⟩

end Lean4Lean.VEnv.Strengthening
