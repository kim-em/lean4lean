import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedFullContext

/-! # Native head exposure in the level-extended guarded union

Explicit universe steps preserve Pi exclusion and rigid constant families.
These precise root laws recover native Pi selection and nullary structure
exposure without requiring the false original primitive-head interface.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
variable [Params]

/-- Every root at a finite level-extended stage is an old primitive head or an
explicit universe conversion. Guard enlargement adds no other root shape. -/
theorem erased_level_recovered_stage_root : ∀ stage {Δ a b},
    ErasedLevelRecoveredStage D stage Δ a b → PrimitiveHead a ∨ LevelPrimitive univs a b := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b H
    exact H.elim (fun H => .inl (erased_iota_primitive_head H)) Or.inr
  | succ stage ih =>
    intro Δ a b H
    rcases H with H | H | H
    · exact ih H
    · exact .inl H.2.head
    · exact .inl H.head

/-- No level-extended stage has a primitive Pi root. Sort and constant universe
conversion are both compatible with this narrower exclusion. -/
theorem erased_level_recovered_stage_no_pi (stage : Nat) :
    ¬ ErasedLevelRecoveredStage D stage Δ (.forallE A B) out := by
  intro H
  rcases erased_level_recovered_stage_root stage H with H | H
  · exact H
  · cases H

/-- The closed union has no primitive Pi root. -/
theorem erased_level_recovered_union_no_pi :
    ¬ ErasedLevelRecoveredUnion D Δ (.forallE A B) out := by
  rintro ⟨stage, H⟩
  exact erased_level_recovered_stage_no_pi stage H

/-- At a rigid family head, the only possible root is explicit universe
conversion. This holds for arbitrary finite nesting of singleton/Eq guards. -/
theorem erased_level_recovered_stage_rigid_root (heq : env.HasCanonicalEq)
    (hc : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    ∀ stage {Δ a b}, ErasedLevelRecoveredStage D stage Δ a b → a.constHead = some family →
      LevelPrimitive univs a b := by
  intro stage
  induction stage with
  | zero =>
    intro Δ a b H hh
    rcases H with H | H
    · exact (erased_iota_primitive_no_rigid hc hD H hh).elim
    · exact H
  | succ stage ih =>
    intro Δ a b H hh
    rcases H with H | H | H
    · exact ih H hh
    · cases H.2 with
      | intro V _ _ _ =>
        have hn := Option.some.inj ((ProofShape.constHead_mkApps _ _).symm.trans hh)
        exact (V.not_rigid (hn ▸ hc)).elim
    · cases H with
      | intro _ =>
        obtain ⟨doms, hclosed, _, hp⟩ := heq.2.2.2
        exact (hc.pats _ _ hp (by
          simpa only [canonicalEqRecPattern, SimplePattern.iota_headConst] using Option.some.inj hh)).elim

/-- Rigid constants preserve family and equivalent universe arguments at every
finite level-extended stage. They need not be literally fixed. -/
theorem erased_level_recovered_stage_constant_levels (heq : env.HasCanonicalEq)
    (hc : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) (stage : Nat) :
    ConstantRootLevels (ErasedLevelRecoveredStage D stage) family := by
  intro Δ ls out H
  have H := erased_level_recovered_stage_rigid_root heq hc hD stage H rfl
  cases H with
  | const HL hw => exact ⟨_, rfl, HL⟩

/-- The union's rigid constant roots vary only by equivalent universes. -/
theorem erased_level_recovered_union_constant_levels (heq : env.HasCanonicalEq)
    (hc : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs) :
    ConstantRootLevels (ErasedLevelRecoveredUnion D) family := by
  rintro Δ ls out ⟨stage, H⟩
  exact erased_level_recovered_stage_constant_levels heq hc hD stage H

/-- Existing native recovery aligned with an assigned Pi selects a native Pi
and retains the assigned-to-selected domain comparison at every finite stage. -/
theorem proofErase_carrier_aligned_level_stage_recovered_pi_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) mode T
      (proofErase Γ (.forallE A B))) :
    ∃ D' C, env.HasType univs Γ f (.forallE D' C) ∧
      ScopedTypeRecovery (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D') (proofErase (D' :: Γ) C)) ∧
      CarrierAlignedCompare (ErasedLevelRecoveredStage D stage) (proofEraseCtx Γ) false
        (proofErase Γ A) (proofErase Γ D') :=
  proofErase_carrier_aligned_recovered_pi_domain_of_no_root (erased_level_recovered_stage_descent heq hs stage)
    (erased_level_recovered_stage_no_pi stage) hΓ hf R H

/-- Native Pi selection works in the closed union despite its sort roots. -/
theorem proofErase_carrier_aligned_level_union_recovered_pi_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode T
      (proofErase Γ (.forallE A B))) :
    ∃ D' C, env.HasType univs Γ f (.forallE D' C) ∧
      ScopedTypeRecovery (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ f)
        (.forallE (proofErase Γ D') (proofErase (D' :: Γ) C)) ∧
      CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) false
        (proofErase Γ A) (proofErase Γ D') :=
  proofErase_carrier_aligned_recovered_pi_domain_of_no_root (erased_level_recovered_union_descent heq hs)
    erased_level_recovered_union_no_pi hΓ hf R H

/-- Typed aligned checking against a rigid nullary family exposes that same
family at equivalent levels in the closed union. -/
theorem proofErase_carrier_aligned_level_union_nullary_exposure
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hc : env.Rigid family) (hD : ∀ levels rhs, ¬ D.unfolds family levels rhs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .const family ls) :
    ∃ ls', ScopedCompute (ErasedLevelRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ b) (.const family ls') ∧
      List.Forall₂ (· ≈ ·) ls ls' :=
  proofErase_carrier_aligned_nullary_levels_exposure_of_stable_root
    (erased_level_recovered_union_descent heq hs)
    (erased_level_recovered_union_constant_levels heq hc hD) hΓ ha hb H Ea

end Lean4Lean.VEnv.Strengthening
