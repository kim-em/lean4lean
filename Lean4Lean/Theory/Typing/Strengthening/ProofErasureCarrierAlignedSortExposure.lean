import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSortRoot

/-! # Universe-preserving exposure for native aligned comparison

Actual sort typings exclude function and structure promotion. Existing
comparisons therefore expose equivalent universes even with level root steps.
No native coverage or semantic comparison completeness is assumed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private sort_not_lam sort_not_constructor
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
variable [Params]

private theorem computed_sort_levels_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : SortRootLevels Step)
    (H : ComputedJointCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    (∀ w, sa = .sort w → ∃ v, ScopedCompute Step Δ sb (.sort v) ∧ w ≈ v) ∧
    (∀ w, sb = .sort w → ∃ v, ScopedCompute Step Δ sa (.sort v) ∧ w ≈ v) := by
  change ComputedJointCheck Step Δ (.compare mode) sa sb at H
  generalize EK : JointCheckKind.compare mode = kind at H
  induction H generalizing Γ a b u v mode with
  | leaf H =>
    cases EK
    cases H with
    | refl =>
      constructor <;> intro w E <;> cases E <;> exact ⟨w, .refl, by rfl⟩
    | sort HL =>
      constructor
      · intro w E; cases E; exact ⟨_, .refl, HL⟩
      · intro w E; cases E; exact ⟨_, .refl, HL.symm⟩
    | const => constructor <;> intro _ E <;> cases E
    | etaL H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ ha (Ea.trans E)).elim
    | etaR H =>
      obtain ⟨_, _, E, _⟩ := H.shape
      exact (sort_not_lam hΓ hb (Eb.trans E)).elim
  | forallE | forallSorted => constructor <;> intro _ E <;> cases E
  | app | appCarrier | appComputed | proj => constructor <;> intro _ E <;> cases E
  | lam | lamSorted | lamCommon | etaBodyL | etaLams => exact (sort_not_lam hΓ ha Ea).elim
  | etaBodyR => exact (sort_not_lam hΓ hb Eb).elim
  | structFields hi hx hp hf => exact (sort_not_constructor hΓ ha hi hx hp hf Ea).elim
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB EK
    constructor
    · intro w E
      obtain ⟨w', HE, HL⟩ := ScopedCompute.sort_levels_inv hn (E ▸ RA)
      obtain ⟨v, R, HV⟩ := IH.1 w' HE
      exact ⟨v, RB.trans R, HL.trans HV⟩
    · intro w E
      obtain ⟨w', HE, HL⟩ := ScopedCompute.sort_levels_inv hn (E ▸ RB)
      obtain ⟨v, R, HV⟩ := IH.2 w' HE
      exact ⟨v, RA.trans R, HL.trans HV⟩
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea EK).symm
  | carrierIntro | carrierChecked | carrierSubsingleton | carrierFunction |
      carrierSymm | carrierCompute | carrierReduce | carrierNested => cases EK

private theorem recovered_carrier_sort_levels
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : SortRootLevels Step)
    (RA : ScopedTypeRecovery Step Δ sa rawC)
    (HC : ComputedJointCarrierGuard Step Δ rawC sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    (∀ w, sa = .sort w → ∃ v, ScopedCompute Step Δ sb (.sort v) ∧ w ≈ v) ∧
    (∀ w, sb = .sort w → ∃ v, ScopedCompute Step Δ sa (.sort v) ∧ w ≈ v) := by
  obtain ⟨C, haC, EC⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) ha EΓ (by simpa only [List.length_nil, ProofShape.liftN_zero, Ea] using RA)
  simp only [List.length_nil, ProofShape.liftN_zero] at EC
  have H := proofErase_computed_carrier_types_checked hstep hΓ ha hb (.inl haC)
    (by simpa only [EΓ, Ea, Eb, EC] using HC)
  simpa only [EΓ, Ea, Eb] using
    computed_sort_levels_pair hstep hn H hΓ ha hb rfl rfl rfl

private theorem recovered_sort_levels_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : SortRootLevels Step)
    (H : CarrierRecoveredCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    (∀ w, sa = .sort w → ∃ v, ScopedCompute Step Δ sb (.sort v) ∧ w ≈ v) ∧
    (∀ w, sb = .sort w → ∃ v, ScopedCompute Step Δ sa (.sort v) ∧ w ≈ v) := by
  induction H generalizing Γ a b u v with
  | base H => exact computed_sort_levels_pair hstep hn H hΓ ha hb EΓ Ea Eb
  | recovered RA RB HC => exact recovered_carrier_sort_levels hstep hn RA HC hΓ ha hb EΓ Ea Eb
  | app | proj => constructor <;> intro _ E <;> cases E
  | lam => exact (sort_not_lam hΓ ha Ea).elim
  | forallE => constructor <;> intro _ E <;> cases E
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB
    constructor
    · intro w E
      obtain ⟨w', HE, HL⟩ := ScopedCompute.sort_levels_inv hn (E ▸ RA)
      obtain ⟨v, R, HV⟩ := IH.1 w' HE
      exact ⟨v, RB.trans R, HL.trans HV⟩
    · intro w E
      obtain ⟨w', HE, HL⟩ := ScopedCompute.sort_levels_inv hn (E ▸ RB)
      obtain ⟨v, R, HV⟩ := IH.2 w' HE
      exact ⟨v, RA.trans R, HL.trans HV⟩
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea).symm

private theorem aligned_sort_levels_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hn : SortRootLevels Step)
    (H : CarrierAlignedCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    (∀ w, sa = .sort w → ∃ v, ScopedCompute Step Δ sb (.sort v) ∧ w ≈ v) ∧
    (∀ w, sb = .sort w → ∃ v, ScopedCompute Step Δ sa (.sort v) ∧ w ≈ v) := by
  induction H generalizing Γ a b u v with
  | base H => exact recovered_sort_levels_pair hstep hn H hΓ ha hb EΓ Ea Eb
  | commonCarrier RA HC => exact recovered_carrier_sort_levels hstep hn RA HC hΓ ha hb EΓ Ea Eb
  | aligned RA RB HT HC ihT => exact recovered_carrier_sort_levels hstep hn RA HC hΓ ha hb EΓ Ea Eb
  | recover RA RB HT HC ihT ihC => exact ihC hΓ ha hb EΓ Ea Eb
  | app | proj => constructor <;> intro _ E <;> cases E
  | lam | lamSorted | lamCommon | etaBodyL | etaLams => exact (sort_not_lam hΓ ha Ea).elim
  | etaBodyR => exact (sort_not_lam hΓ hb Eb).elim
  | structFields hi hx hp hf => exact (sort_not_constructor hΓ ha hi hx hp hf Ea).elim
  | forallE | forallSorted => constructor <;> intro _ E <;> cases E
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB
    constructor
    · intro w E
      obtain ⟨w', HE, HL⟩ := ScopedCompute.sort_levels_inv hn (E ▸ RA)
      obtain ⟨v, R, HV⟩ := IH.1 w' HE
      exact ⟨v, RB.trans R, HL.trans HV⟩
    · intro w E
      obtain ⟨w', HE, HL⟩ := ScopedCompute.sort_levels_inv hn (E ▸ RB)
      obtain ⟨v, R, HV⟩ := IH.2 w' HE
      exact ⟨v, RA.trans R, HL.trans HV⟩
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea).symm

/-- At actual type endpoints, full aligned comparison with a literal sort
computes the other endpoint to a sort at an equivalent universe. -/
theorem proofErase_carrier_aligned_sort_levels_exposure
    (hstep : ErasedScopedPrimitiveDescent Step) (hn : SortRootLevels Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .sort w) :
    ∃ w', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) (.sort w') ∧ w ≈ w' :=
  (aligned_sort_levels_pair hstep hn H hΓ ha hb rfl rfl rfl).1 w Ea

end Lean4Lean.VEnv.Strengthening
