import Lean4Lean.Theory.Typing.Strengthening.ProofErasureOpaqueVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking

/-! # Directed joins of protected opaque occurrences

Each marked source joins its payload with a guarded path on the source side
and an ordinary core path on the payload side. These asymmetric joins propagate
through arbitrary syntax using only an actual typing of the source.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ambient_cons subst_shift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureStagedAnnotationChecking
open private level_lift from Lean4Lean.Theory.Typing.Strengthening.ProofErasureAnnotationCoreComputation
variable [Params] {Guard : ProofShape → ProofShape → Prop}

/-- Protected opaque occurrences admit a directed join in every typed source
context reached by exact renaming. The payload path stays in the ordinary level
core, which allows later use of ordinary core confluence instead of guarded
confluence. -/
theorem opaque_variant_join
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hguard : ∀ {a b}, Guard a b → ∃ shared,
      ScopedCompute Step Δ a shared ∧ ProofShape.Compute (ErasedLevelCore D) b shared)
    (V : OpaqueVariant Guard n a b)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a)
    (W : ContextRenaming Δ (proofEraseCtx Γ) (fun i => .bvar (i + n))) :
    ∃ shared, ScopedCompute Step (proofEraseCtx Γ) a shared ∧
      ProofShape.Compute (ErasedLevelCore D) b shared := by
  induction V generalizing Γ e T with
  | refl => exact ⟨_, .refl, .refl⟩
  | app VF VX ihf ihx =>
    obtain ⟨f, x, rfl, _, EF, EX⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    obtain ⟨g, RF, RG⟩ := ihf hΓ hf EF W
    obtain ⟨y, RX, RY⟩ := ihx hΓ hx EX W
    exact ⟨_, .app RF RX, .app RG RY⟩
  | proj V ih =>
    obtain ⟨m, rfl, _, EM⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨m', RL, RR⟩ := ih hΓ hm.hasType.2 EM W
    exact ⟨_, .proj RL, .proj RR⟩
  | lam VA VB ihA ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨C, RA, RC⟩ := ihA hΓ hA EA W
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨d, RB, RD⟩ := ihB hΓA hb EB (ambient_cons W hΓ hA)
    refine ⟨_, .lam RA ?_, .lam RC RD⟩
    simpa only [proofEraseCtx, EA] using RB
  | forallE VA VB ihA ihB =>
    obtain ⟨A, body, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.forallE_inv henv
    obtain ⟨C, RA, RC⟩ := ihA hΓ hA EA W
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨d, RB, RD⟩ := ihB hΓA hb EB (ambient_cons W hΓ hA)
    refine ⟨_, .forallE RA ?_, .forallE RC RD⟩
    simpa only [proofEraseCtx, EA] using RB
  | marked HG =>
    obtain ⟨shared, RL, RR⟩ := hguard HG
    refine ⟨shared.liftN _, ?_, RR.liftN level_lift⟩
    simpa only [subst_shift] using RL.rename hrename W

end Lean4Lean.VEnv.Strengthening
