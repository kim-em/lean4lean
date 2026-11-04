import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureExpansion
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureUnitEtaStages

/-! # Recovered stages with native function and structure eta

The existing controlled beta expansions and recovered guards remain available.
Function eta selects its annotation and structure eta its complete parameter spine
at the preceding stage. Structure guards may themselves use all earlier eta rules. The system retains arbitrary-block descent and exact renaming.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape PureObservation
variable [Params]

/-- Controlled beta expansion at the base, with recovered singleton, Eq,
identity, function eta and structure eta guards using the entire preceding stage. -/
def ErasedStaticStructureEtaExpansionStage (D : Definitions) :
    Nat → List ProofShape → ProofShape → ProofShape → Prop
  | 0 => ErasedExpansionStage D 0
  | n + 1 => fun Δ a b => ErasedStaticStructureEtaExpansionStage D n Δ a b ∨
      CarrierRecoveredSingletonPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ a b ∨
      ComputedJointPrefixPrimitive (ErasedStaticStructureEtaExpansionStage D n) Δ a b ∨
      NativeIdentityExpansion (ErasedStaticStructureEtaExpansionStage D n) Δ a b ∨
      NativeEtaExpansion (ErasedStaticStructureEtaExpansionStage D n) Δ a b ∨
      NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionStage D n) Δ a b

/-- Every previous function-eta stage embeds at the same index. -/
theorem erased_eta_into_static_structure_eta_stage : ∀ n {Δ a b},
    ErasedEtaExpansionStage D n Δ a b → ErasedStaticStructureEtaExpansionStage D n Δ a b := by
  intro n
  induction n with
  | zero => exact id
  | succ n ih =>
    intro Δ a b H
    rcases H with H | H | H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.mono ih))
    · exact .inr (.inr (.inl (H.mono ih)))
    · exact .inr (.inr (.inr (.inl (H.mono ih))))
    · exact .inr (.inr (.inr (.inr (.inl (H.mono ih)))))

/-- The eta-expanded stages increase monotonically. -/
theorem erased_static_structure_eta_expansion_stage_mono (hle : n ≤ m) {Δ a b}
    (H : ErasedStaticStructureEtaExpansionStage D n Δ a b) : ErasedStaticStructureEtaExpansionStage D m Δ a b := by
  induction hle with
  | refl => exact H
  | step _ ih => exact .inl ih

/-- Every eta-expanded stage descends through arbitrary inserted binder blocks. -/
theorem erased_static_structure_eta_expansion_stage_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ n, ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionStage D n) := by
  intro n
  induction n with
  | zero => exact erased_expansion_stage_descent heq hs 0
  | succ n ih =>
    intro Γ Γ' n k e T out hΓ hΓ' W ht H
    rcases H with H | H | H | H | H | H
    · exact ih hΓ hΓ' W ht H
    · exact erased_singleton_with_descent heq (erased_carrier_recovered_family_descent ih) hΓ hΓ' W ht H.2
    · exact erased_computed_joint_prefix_descent heq ih hΓ hΓ' W ht H
    · exact erased_nativeIdentityExpansion_descent ih hΓ hΓ' W ht H
    · exact erased_nativeEtaExpansion_descent ih hΓ hΓ' W ht H
    · exact erased_nativeMaskedStructureExpansion_descent ih hΓ hΓ' W ht H

/-- Exact interpreted renaming preserves all eta-expanded primitive guards. -/
theorem erased_static_structure_eta_expansion_stage_rename (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ n {Δ Δ' a b τ}, ErasedStaticStructureEtaExpansionStage D n Δ a b → ContextRenaming Δ Δ' τ →
      ErasedStaticStructureEtaExpansionStage D n Δ' (a.subst τ) (b.subst τ) := by
  intro n
  induction n with
  | zero => exact erased_expansion_stage_rename heq hs 0
  | succ n ih =>
    intro Δ Δ' a b τ H W
    rcases H with H | H | H | H | H | H
    · exact .inl (ih H W)
    · exact .inr (.inl (H.rename heq (erased_static_structure_eta_expansion_stage_descent heq hs n)
        (erased_static_structure_eta_expansion_stage_descent heq hs n) ih W))
    · exact .inr (.inr (.inl (H.rename ih W)))
    · exact .inr (.inr (.inr (.inl (H.rename ih W))))
    · exact .inr (.inr (.inr (.inr (.inl (H.rename ih W)))))
    · exact .inr (.inr (.inr (.inr (.inr (H.rename ih W)))))

/-- Finite eta-expanded guard depth, with no fixed upper bound. -/
def ErasedStaticStructureEtaExpansionUnion (D : Definitions) (Δ : List ProofShape) (a b : ProofShape) : Prop :=
  ∃ n, ErasedStaticStructureEtaExpansionStage D n Δ a b

/-- The eta-expanded union retains source-typed binder descent. -/
theorem erased_static_structure_eta_expansion_union_descent (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ErasedScopedPrimitiveDescent (ErasedStaticStructureEtaExpansionUnion D) := by
  intro Γ Γ' n k e T out hΓ hΓ' W ht ⟨stage, H⟩
  exact erased_static_structure_eta_expansion_stage_descent heq hs stage hΓ hΓ' W ht H

/-- The entire previous function-eta union embeds in the eta-expanded union. -/
theorem erased_eta_into_static_structure_eta_union (H : ErasedEtaExpansionUnion D Δ a b) :
    ErasedStaticStructureEtaExpansionUnion D Δ a b := by
  obtain ⟨n, H⟩ := H
  exact ⟨n, erased_eta_into_static_structure_eta_stage n H⟩

/-- A native eta guard over the union is already admitted at a finite stage. -/
theorem erased_static_structure_eta_expansion_union_eta
    (H : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ a b) :
    ErasedStaticStructureEtaExpansionUnion D Δ a b := by
  cases H with
  | intro R S =>
    obtain ⟨n, R⟩ := R.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
      (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
    exact ⟨n + 1, .inr (.inr (.inr (.inr (.inl (.intro R S)))))⟩

/-- A structure guard over the union already has a finite stage, so no infinite
native recovery or global common-type completeness assumption is introduced. -/
theorem erased_static_structure_eta_expansion_union_structure
    (H : NativeMaskedStructureExpansion (ErasedStaticStructureEtaExpansionUnion D) Δ a b) :
    ErasedStaticStructureEtaExpansionUnion D Δ a b := by
  cases H with
  | intro hi hx ha hp RN =>
    obtain ⟨n, RN⟩ := RN.finite_stage (Stages := ErasedStaticStructureEtaExpansionStage D)
      (fun {n m} hle {Δ a b} H => erased_static_structure_eta_expansion_stage_mono hle H)
    exact ⟨n+1, .inr (.inr (.inr (.inr (.inr (.intro hi hx ha hp RN)))))⟩

/-- The earlier unit-eta language embeds at the same guard depth. -/
theorem erased_unit_into_static_structure_eta_stage : ∀ n {Δ a b},
    ErasedUnitEtaExpansionStage D n Δ a b → ErasedStaticStructureEtaExpansionStage D n Δ a b := by
  intro n
  induction n with
  | zero => exact id
  | succ n ih =>
    intro Δ a b H
    rcases H with H | H | H | H | H | H
    · exact .inl (ih H)
    · exact .inr (.inl (H.mono ih))
    · exact .inr (.inr (.inl (H.mono ih)))
    · exact .inr (.inr (.inr (.inl (H.mono ih))))
    · exact .inr (.inr (.inr (.inr (.inl (H.mono ih)))))
    · exact .inr (.inr (.inr (.inr (.inr ((H.mono ih).maskedStructure)))))

/-- Every finite unit-eta computation is retained by the full structure language. -/
theorem erased_unit_into_static_structure_eta_union (H : ErasedUnitEtaExpansionUnion D Δ a b) :
    ErasedStaticStructureEtaExpansionUnion D Δ a b := by
  obtain ⟨n, H⟩ := H
  exact ⟨n, erased_unit_into_static_structure_eta_stage n H⟩

end Lean4Lean.VEnv.Strengthening
