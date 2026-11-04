import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypeResidual
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedTypedExposure

/-! # Pi exposure retaining the comparison with the assigned type

The selected native type may compute to a different Pi. Its resulting Pi keeps
an inferred comparison with the original assigned Pi, and native replay also
reconstructs an actual typing of the source at that Pi. This is a residual of
an existing certificate, not beta stability of arbitrary comparisons.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private sort_not_lam from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
open private ProofShape.typeHead ProofShape.typeHead_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveryExposure
open private computed_type_residual_pair
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypeResidual
variable [Params]

private def TypeResidualPair
    (Step : List ProofShape → ProofShape → ProofShape → Prop)
    (Cmp : ProofShape → ProofShape → Prop) (Δ : List ProofShape) (sa sb : ProofShape) : Prop :=
  (∀ tag, ProofShape.typeHead sa = some tag → ∃ out, ScopedCompute Step Δ sb out ∧
    ProofShape.typeHead out = some tag ∧ Cmp sa out) ∧
  (∀ tag, ProofShape.typeHead sb = some tag → ∃ out, ScopedCompute Step Δ sa out ∧
    ProofShape.typeHead out = some tag ∧ Cmp out sb)

omit [Params] in
private theorem TypeResidualPair.map (H : TypeResidualPair Step Cmp Δ sa sb)
    (h : ∀ {a b}, Cmp a b → Target a b) : TypeResidualPair Step Target Δ sa sb := by
  constructor
  · intro tag E
    obtain ⟨out, R, HE, HX⟩ := H.1 tag E
    exact ⟨out, R, HE, h HX⟩
  · intro tag E
    obtain ⟨out, R, HE, HX⟩ := H.2 tag E
    exact ⟨out, R, HE, h HX⟩

private theorem recovered_carrier_residual
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (RA : ScopedTypeRecovery Step Δ sa rawC)
    (HC : ComputedJointCarrierGuard Step Δ rawC sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    TypeResidualPair Step (ComputedJointCompare Step Δ false) Δ sa sb := by
  obtain ⟨C, haC, EC⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) ha EΓ (by simpa only [List.length_nil, ProofShape.liftN_zero, Ea] using RA)
  simp only [List.length_nil, ProofShape.liftN_zero] at EC
  have H := proofErase_computed_carrier_types_checked hstep hΓ ha hb (.inl haC)
    (by simpa only [EΓ, Ea, Eb, EC] using HC)
  simpa only [TypeResidualPair, EΓ, Ea, Eb] using
    computed_type_residual_pair hstep hhead H hΓ ha hb rfl rfl rfl

private theorem recovered_type_residual_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : CarrierRecoveredCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    TypeResidualPair Step (CarrierRecoveredCompare Step Δ false) Δ sa sb := by
  induction H generalizing Γ a b u v with
  | base H =>
    exact TypeResidualPair.map (computed_type_residual_pair hstep hhead H hΓ ha hb EΓ Ea Eb)
      (fun H => CarrierRecoveredCompare.base H)
  | recovered RA RB HC =>
    exact TypeResidualPair.map
      (recovered_carrier_residual hstep hhead RA HC hΓ ha hb EΓ Ea Eb) (fun H => CarrierRecoveredCompare.base H)
  | app | proj => constructor <;> intro _ E <;> cases E
  | lam => exact (sort_not_lam hΓ ha Ea).elim
  | forallE HA HB =>
    exact ⟨fun _ E => ⟨_, .refl, E, .forallE HA HB⟩, fun _ E => ⟨_, .refl, E, .forallE HA HB⟩⟩
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB
    constructor
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.1 tag (ProofShape.typeHead_compute hhead RA E)
      exact ⟨out, RB.trans R, HE, .compute RA .refl HX⟩
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.2 tag (ProofShape.typeHead_compute hhead RB E)
      exact ⟨out, RA.trans R, HE, .compute .refl RB HX⟩
  | symm H ih =>
    have IH := ih hΓ hb ha EΓ Eb Ea
    constructor
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.2 tag E
      exact ⟨out, R, HE, .symm HX⟩
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.1 tag E
      exact ⟨out, R, HE, .symm HX⟩

private theorem aligned_type_residual_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : CarrierAlignedCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    TypeResidualPair Step (CarrierAlignedCompare Step Δ false) Δ sa sb := by
  induction H generalizing Γ a b u v with
  | base H =>
    exact TypeResidualPair.map (recovered_type_residual_pair hstep hhead H hΓ ha hb EΓ Ea Eb)
      (fun H => CarrierAlignedCompare.base H)
  | commonCarrier RA HC =>
    exact TypeResidualPair.map
      (recovered_carrier_residual hstep hhead RA HC hΓ ha hb EΓ Ea Eb) (fun H => CarrierAlignedCompare.base (.base H))
  | aligned RA RB HT HC ihT =>
    exact TypeResidualPair.map
      (recovered_carrier_residual hstep hhead RA HC hΓ ha hb EΓ Ea Eb) (fun H => CarrierAlignedCompare.base (.base H))
  | app | proj => constructor <;> intro _ E <;> cases E
  | lam => exact (sort_not_lam hΓ ha Ea).elim
  | forallE HA HB =>
    exact ⟨fun _ E => ⟨_, .refl, E, .forallE HA HB⟩, fun _ E => ⟨_, .refl, E, .forallE HA HB⟩⟩
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB
    constructor
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.1 tag (ProofShape.typeHead_compute hhead RA E)
      exact ⟨out, RB.trans R, HE, .compute RA .refl HX⟩
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.2 tag (ProofShape.typeHead_compute hhead RB E)
      exact ⟨out, RA.trans R, HE, .compute .refl RB HX⟩
  | symm H ih =>
    have IH := ih hΓ hb ha EΓ Eb Ea
    constructor
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.2 tag E
      exact ⟨out, R, HE, .symm HX⟩
    · intro tag E
      obtain ⟨out, R, HE, HX⟩ := IH.1 tag E
      exact ⟨out, R, HE, .symm HX⟩

/-- Exposing a Pi from an aligned type comparison retains an inferred
comparison with the original assigned type at the same primitive relation. -/
theorem proofErase_carrier_aligned_pi_residual
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Eb : proofErase Γ b = .forallE A B) :
    ∃ A' B', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ a) (.forallE A' B') ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false (.forallE A' B') (proofErase Γ b) := by
  obtain ⟨out, R, HE, HX⟩ := (aligned_type_residual_pair hstep hhead H hΓ ha hb rfl rfl rfl).2 true
    (by rw [Eb]; rfl)
  cases out <;> try cases HE
  exact ⟨_, _, R, HX⟩

/-- Native Pi exposure also retains the residual inferred type comparison.
Both the recovery and the comparison use the original primitive relation. -/
theorem proofErase_carrier_aligned_recovered_pi_residual
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B))) :
    ∃ A' B', ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE A' B') ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false (.forallE A' B') (proofErase Γ (.forallE A B)) := by
  obtain ⟨T₀, hfT, ET⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) hf rfl (by simpa only [List.length_nil, ProofShape.liftN_zero] using R)
  simp only [List.length_nil, ProofShape.liftN_zero] at ET
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  obtain ⟨_, hT⟩ := hfT.isType henv hΓ
  have EPi : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  obtain ⟨A', B', RC, HX⟩ := proofErase_carrier_aligned_pi_residual hstep hhead hΓ hT hPi
    (by simpa only [ET] using H) EPi
  exact ⟨A', B', R.convert (by simpa only [ET] using RC), HX⟩

/-- The exposed native Pi has actual original domains and codomains, not just
raw shapes. Its source typing, exact native recovery and residual comparison
with the assigned Pi are returned together, without a recovery coverage premise. -/
theorem proofErase_carrier_aligned_recovered_pi_typed_residual
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T (proofErase Γ (.forallE A B))) :
    ∃ A' B', env.HasType univs Γ f (.forallE A' B') ∧
      ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (proofErase Γ (.forallE A' B')) ∧
      CarrierAlignedCompare Step (proofEraseCtx Γ) false
        (proofErase Γ (.forallE A' B')) (proofErase Γ (.forallE A B)) := by
  obtain ⟨D, C, RN, HN⟩ := proofErase_carrier_aligned_recovered_pi_residual hstep hhead hΓ hf R H
  obtain ⟨T₀, hfT, ET⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) hf rfl (by simpa only [List.length_nil, ProofShape.liftN_zero] using RN)
  simp only [List.length_nil, ProofShape.liftN_zero] at ET
  obtain ⟨A', B', rfl, _, _, _⟩ := erase_forallE_inv ET
  exact ⟨A', B', hfT, ET.symm ▸ RN, ET.symm ▸ HN⟩

end Lean4Lean.VEnv.Strengthening
