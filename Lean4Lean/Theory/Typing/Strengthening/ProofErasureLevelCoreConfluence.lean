import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedLevelCore
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedCoreJoin

/-! # Postponing universe conversion in the ordinary erased core

Typed replay and structural simulation postpone all explicit universe changes
until after ordinary computation. Ordinary typed confluence then extends to the
level core. No normalization or confluence of guarded stages is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private erase_app_inv erase_proj_inv erase_lam_inv erase_forallE_inv
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Every typed finite level-core path factors as ordinary computation followed
by structural universe variation, including computations inside retained binders. -/
theorem proofErase_level_core_factor
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (R : ProofShape.Compute (ErasedLevelCore D) a out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (Ee : proofErase Γ e = a) :
    ∃ mid, ProofShape.Compute (ErasedIotaPrimitive D) a mid ∧ StructuralVariant mid out := by
  induction R generalizing Γ e T with
  | base R =>
    rcases R with R | R
    · exact ⟨_, .base R, .refl⟩
    · exact ⟨_, .refl, R.variant⟩
  | beta R => exact ⟨_, .beta R, .refl⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨mid, RC, VC⟩ := ih₁ hΓ ht Ee
    obtain ⟨e₁, HE, E₁⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
      hΓ ht rfl Ee (R₁.scoped (fun H => .base H))
    obtain ⟨last, RL, VL⟩ := ih₂ hΓ HE.hasType.2 E₁
    obtain ⟨em, HM, EM⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ ht (Ee ▸ RC)
    obtain ⟨last', RL', VL'⟩ := proofErase_carrier_aligned_compute_variant hs hlevels hcon
      RL hΓ hΓ HE.hasType.2 (HM.simAt hs hΓ _ ht).hasType.2 E₁
      (by simpa only [EM] using VC.symm)
    exact ⟨last', RC.trans (by simpa only [EM] using RL'), VL'.symm.trans VL⟩
  | app Rf Rx ihf ihx =>
    obtain ⟨f, x, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
    obtain ⟨f', RF, VF⟩ := ihf hΓ hf Ef
    obtain ⟨x', RX, VX⟩ := ihx hΓ hx Ex
    exact ⟨_, .app RF RX, .app VF VX⟩
  | proj Rm ihm =>
    obtain ⟨m, rfl, _, Em⟩ := erase_proj_inv Ee
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
    obtain ⟨m', RM, VM⟩ := ihm hΓ hm.hasType.2 Em
    exact ⟨_, .proj RM, .proj VM⟩
  | lam RA Rb ihA ihb =>
    obtain ⟨A, b, rfl, _, EA, Eb⟩ := erase_lam_inv Ee
    obtain ⟨⟨u, hA⟩, _, hb⟩ := ht.lam_inv henv hΓ
    obtain ⟨A', RA', VA⟩ := ihA hΓ hA EA
    obtain ⟨b', Rb', Vb⟩ := ihb (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hb Eb
    exact ⟨_, .lam RA' Rb', .lam VA Vb⟩
  | forallE RA RB ihA ihB =>
    obtain ⟨A, B, rfl, _, EA, EB⟩ := erase_forallE_inv Ee
    obtain ⟨⟨u, hA⟩, _, hB⟩ := ht.forallE_inv henv
    obtain ⟨A', RA', VA⟩ := ihA hΓ hA EA
    obtain ⟨B', RB', VB⟩ := ihB (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hB EB
    exact ⟨_, .forallE RA' RB', .forallE VA VB⟩

/-- Adding explicit universe conversion preserves typed-source confluence of
any sound, universe-compatible ordinary core with concrete patterns. -/
theorem proofErase_level_core_confluent
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hc : TypedCoreConfluence (ErasedIotaPrimitive D)) : TypedCoreConfluence (ErasedLevelCore D) := by
  intro Γ e T a b hΓ ht R S
  obtain ⟨a₀, RA, VA⟩ := proofErase_level_core_factor hs hlevels hcon R hΓ ht rfl
  obtain ⟨b₀, RB, VB⟩ := proofErase_level_core_factor hs hlevels hcon S hΓ ht rfl
  obtain ⟨c, AC, BC⟩ := hc hΓ ht RA RB
  obtain ⟨ea₀, HA₀, EA₀⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ ht RA
  obtain ⟨eb₀, HB₀, EB₀⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ ht RB
  obtain ⟨ea, HA, EA⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ht rfl rfl (R.scoped (fun H => .base H))
  obtain ⟨eb, HB, EB⟩ := proofErase_scoped_compute_realize (erased_level_core_descent hs)
    hΓ ht rfl rfl (S.scoped (fun H => .base H))
  obtain ⟨ca, ACA, VCA⟩ := proofErase_carrier_aligned_compute_variant hs hlevels hcon AC
    hΓ hΓ (HA₀.simAt hs hΓ _ ht).hasType.2 HA.hasType.2 EA₀ (by simpa only [EA] using VA)
  obtain ⟨cb, BCB, VCB⟩ := proofErase_carrier_aligned_compute_variant hs hlevels hcon BC
    hΓ hΓ (HB₀.simAt hs hΓ _ ht).hasType.2 HB.hasType.2 EB₀ (by simpa only [EB] using VB)
  obtain ⟨ecb, HCB, ECB⟩ := proofErase_compute_replay hs (erased_iota_replay hs) hΓ HB.hasType.2 BCB
  have V : StructuralVariant ca (proofErase Γ ecb) := by
    rw [ECB]
    exact VCA.symm.trans VCB
  have RC : ProofShape.Compute (ErasedLevelCore D) ca (proofErase Γ ecb) :=
    (proofErase_carrier_aligned_variant_level_compute V hΓ
    (HCB.simAt hs hΓ _ HB.hasType.2).hasType.2).mono (fun H => Or.inr H)
  have RAC : ProofShape.Compute (ErasedLevelCore D) a ca := by
    simpa only [EA] using ACA.mono (Step' := ErasedLevelCore D) (fun H => Or.inl H)
  exact ⟨cb, RAC.trans (by simpa only [ECB] using RC),
    by simpa only [EB] using BCB.mono (Step' := ErasedLevelCore D) (fun H => Or.inl H)⟩

end Lean4Lean.VEnv.Strengthening
