import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredPrimitiveRenaming
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelUnionClosure

/-! # Exact renaming with explicit universe conversion -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
variable [Params]

omit [Params] in
/-- Universe steps contain no variables and survive arbitrary substitution. -/
theorem ProofShape.LevelPrimitive.subst (H : LevelPrimitive U a b) :
    LevelPrimitive U (a.subst τ) (b.subst τ) := by
  cases H with
  | sort H hw => exact .sort H hw
  | const H hw => exact .const H hw

/-- Every level-extended recovered stage preserves exact interpreted renaming. -/
theorem erased_level_recovered_stage_rename (heq : env.HasCanonicalEq) (hs : D.Sound env univs) :
    ∀ stage {Δ Δ' a b τ}, ErasedLevelRecoveredStage D stage Δ a b →
      ContextRenaming Δ Δ' τ →
      ErasedLevelRecoveredStage D stage Δ' (a.subst τ) (b.subst τ) := by
  intro stage
  induction stage with
  | zero =>
    intro Δ Δ' a b τ H _
    rcases H with H | H
    · exact .inl (erased_iota_primitive_subst H)
    · exact .inr H.subst
  | succ stage ih =>
    intro Δ Δ' a b τ H WR
    rcases H with H | H | H
    · exact .inl (ih H WR)
    · exact .inr (.inl (H.rename heq (erased_level_recovered_stage_descent heq hs stage)
        (erased_level_recovered_stage_descent heq hs stage) ih WR))
    · exact .inr (.inr (H.rename ih WR))

end Lean4Lean.VEnv.Strengthening
