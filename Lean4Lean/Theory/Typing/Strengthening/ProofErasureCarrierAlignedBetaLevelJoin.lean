import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSortSelection
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureBetaJoinFamily

/-! # Confluence of beta computation with explicit universe conversion

A mixed path factors into a beta path followed by structural universe variation.
Typed beta confluence joins the beta paths; source replay supplies the target
well-formedness needed to turn the remaining variation into an explicit path.
This proves confluence without normalization and without a guarded-stage
confluence assumption.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean Params ProofShape
namespace ProofShape

/-- All explicit universe steps in a finite path can be postponed until after
beta reduction, represented by one structural variant of the beta reduct. -/
theorem ScopedCompute.level_beta_factor
    (R : ScopedCompute (fun _ => LevelPrimitive U) Δ a b) :
    ∃ c, BetaRed a c ∧ StructuralVariant c b := by
  induction R with
  | base H => exact ⟨_, .refl, H.variant⟩
  | beta H => exact ⟨_, H, .refl⟩
  | trans R S ihR ihS =>
    obtain ⟨c, RC, VC⟩ := ihR
    obtain ⟨d, SD, VD⟩ := ihS
    obtain ⟨e, CE, VE⟩ := SD.variant VC.symm
    exact ⟨e, RC.trans CE, VE.symm.trans VD⟩
  | app _ _ ihf ihx =>
    obtain ⟨f, RF, VF⟩ := ihf
    obtain ⟨x, RX, VX⟩ := ihx
    exact ⟨_, .app RF RX, .app VF VX⟩
  | proj _ ih =>
    obtain ⟨m, RM, VM⟩ := ih
    exact ⟨_, .proj RM, .proj VM⟩
  | lam _ _ ihA ihB =>
    obtain ⟨A, RA, VA⟩ := ihA
    obtain ⟨B, RB, VB⟩ := ihB
    exact ⟨_, .lam RA RB, .lam VA VB⟩
  | forallE _ _ ihA ihB =>
    obtain ⟨A, RA, VA⟩ := ihA
    obtain ⟨B, RB, VB⟩ := ihB
    exact ⟨_, .forallE RA RB, .forallE VA VB⟩

end ProofShape
variable [Params]

/-- Two finite beta/universe paths from an actual typed erasure have an exact
common reduct. The paths may contain created beta redexes and arbitrarily many
universe conversions; no termination is needed. -/
theorem proofErase_carrier_aligned_beta_level_confluent
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) (proofErase Γ e) a)
    (S : ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) (proofErase Γ e) b) :
    ∃ c, ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) a c ∧
      ScopedCompute (fun _ => LevelPrimitive univs) (proofEraseCtx Γ) b c := by
  obtain ⟨a₀, RA, VA⟩ := R.level_beta_factor
  obtain ⟨b₀, SB, VB⟩ := S.level_beta_factor
  obtain ⟨c₀, AC, BC⟩ := proofErase_beta_confluent hΓ ht RA SB
  obtain ⟨a', AA, VA'⟩ := AC.variant VA
  obtain ⟨b', BB, VB'⟩ := BC.variant VB
  obtain ⟨e', HE, EE⟩ := proofErase_scoped_compute_realize erased_level_primitive_descent
    hΓ ht rfl rfl (S.trans (.beta BB))
  have V : StructuralVariant a' (proofErase Γ e') := by
    rw [EE]
    exact VA'.symm.trans VB'
  have RC := (proofErase_carrier_aligned_variant_level_compute V hΓ HE.hasType.2).scoped
    (Δ := proofEraseCtx Γ) (fun H => .base H)
  exact ⟨b', (ScopedCompute.beta AA).trans (by simpa only [EE] using RC), .beta BB⟩

end Lean4Lean.VEnv.Strengthening
