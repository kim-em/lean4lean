import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCompare
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypedExposure

/-! # Native type alignment retains typed sort and Pi exposure

At type endpoints, a recovered carrier guard reduces to ordinary computed
comparison: structure and function carriers cannot type a term already typed
at a sort. This handles both native promotion rules without assuming that
native outputs have literal sort syntax or that they join computationally.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private sort_not_lam from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedPiExposure
open private ProofShape.typeHead ProofShape.typeHead_compute
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoveryExposure
open private computed_type_exposure_pair types_inferred_raw
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedTypedExposure
variable [Params]

private theorem recovered_carrier_exposure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (RA : ScopedTypeRecovery Step Δ sa rawC)
    (HC : ComputedJointCarrierGuard Step Δ rawC sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    (∀ tag, ProofShape.typeHead sa = some tag → ∃ out, ScopedCompute Step Δ sb out ∧ ProofShape.typeHead out = some tag) ∧
    (∀ tag, ProofShape.typeHead sb = some tag → ∃ out, ScopedCompute Step Δ sa out ∧ ProofShape.typeHead out = some tag) := by
  obtain ⟨C, haC, EC⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) ha EΓ (by simpa only [List.length_nil, ProofShape.liftN_zero, Ea] using RA)
  simp only [List.length_nil, ProofShape.liftN_zero] at EC
  have H := proofErase_computed_carrier_types_checked hstep hΓ ha hb (.inl haC)
    (by simpa only [EΓ, Ea, Eb, EC] using HC)
  simpa only [EΓ, Ea, Eb] using
    computed_type_exposure_pair hstep hhead H hΓ ha hb rfl rfl rfl

private theorem recovered_type_exposure_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : CarrierRecoveredCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    (∀ tag, ProofShape.typeHead sa = some tag → ∃ out, ScopedCompute Step Δ sb out ∧ ProofShape.typeHead out = some tag) ∧
    (∀ tag, ProofShape.typeHead sb = some tag → ∃ out, ScopedCompute Step Δ sa out ∧ ProofShape.typeHead out = some tag) := by
  induction H generalizing Γ a b u v with
  | base H => exact computed_type_exposure_pair hstep hhead H hΓ ha hb EΓ Ea Eb
  | recovered RA RB HC => exact recovered_carrier_exposure hstep hhead RA HC hΓ ha hb EΓ Ea Eb
  | app | proj => constructor <;> intro _ E <;> cases E
  | lam => exact (sort_not_lam hΓ ha Ea).elim
  | forallE => exact ⟨fun _ E => ⟨_, .refl, E⟩, fun _ E => ⟨_, .refl, E⟩⟩
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB
    constructor
    · intro tag E
      obtain ⟨out, R, HE⟩ := IH.1 tag (ProofShape.typeHead_compute hhead RA E)
      exact ⟨out, RB.trans R, HE⟩
    · intro tag E
      obtain ⟨out, R, HE⟩ := IH.2 tag (ProofShape.typeHead_compute hhead RB E)
      exact ⟨out, RA.trans R, HE⟩
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea).symm

private theorem aligned_type_exposure_pair
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (H : CarrierAlignedCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    (∀ tag, ProofShape.typeHead sa = some tag → ∃ out, ScopedCompute Step Δ sb out ∧ ProofShape.typeHead out = some tag) ∧
    (∀ tag, ProofShape.typeHead sb = some tag → ∃ out, ScopedCompute Step Δ sa out ∧ ProofShape.typeHead out = some tag) := by
  induction H generalizing Γ a b u v with
  | base H => exact recovered_type_exposure_pair hstep hhead H hΓ ha hb EΓ Ea Eb
  | commonCarrier RA HC => exact recovered_carrier_exposure hstep hhead RA HC hΓ ha hb EΓ Ea Eb
  | aligned RA RB HT HC ihT => exact recovered_carrier_exposure hstep hhead RA HC hΓ ha hb EΓ Ea Eb
  | app | proj => constructor <;> intro _ E <;> cases E
  | lam => exact (sort_not_lam hΓ ha Ea).elim
  | forallE => exact ⟨fun _ E => ⟨_, .refl, E⟩, fun _ E => ⟨_, .refl, E⟩⟩
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have IH := ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB
    constructor
    · intro tag E
      obtain ⟨out, R, HE⟩ := IH.1 tag (ProofShape.typeHead_compute hhead RA E)
      exact ⟨out, RB.trans R, HE⟩
    · intro tag E
      obtain ⟨out, R, HE⟩ := IH.2 tag (ProofShape.typeHead_compute hhead RB E)
      exact ⟨out, RA.trans R, HE⟩
  | symm H ih => exact (ih hΓ hb ha EΓ Eb Ea).symm

private theorem recovered_types_inferred
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : CarrierRecoveredCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    CarrierRecoveredCompare Step Δ false sa sb := by
  induction H generalizing Γ a b u v with
  | base H => exact .base (types_inferred_raw hstep H hΓ ha hb EΓ Ea Eb)
  | recovered RA RB HC => exact .recovered RA RB HC
  | app HF HX => exact .app HF HX
  | proj H => exact .proj H
  | lam => exact (sort_not_lam hΓ ha Ea).elim
  | forallE HA HB => exact .forallE HA HB
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    exact .compute RA RB (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB)
  | symm H ih => exact .symm (ih hΓ hb ha EΓ Eb Ea)

private theorem aligned_types_inferred
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : CarrierAlignedCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb) :
    CarrierAlignedCompare Step Δ false sa sb := by
  induction H generalizing Γ a b u v with
  | base H => exact .base (recovered_types_inferred hstep H hΓ ha hb EΓ Ea Eb)
  | commonCarrier RA HC =>
    obtain ⟨C, haC, EC⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
      (Ctx.LiftN.zero []) ha EΓ (by simpa only [List.length_nil, ProofShape.liftN_zero, Ea] using RA)
    simp only [List.length_nil, ProofShape.liftN_zero] at EC
    have H := proofErase_computed_carrier_types_checked hstep hΓ ha hb (.inl haC)
      (by simpa only [EΓ, Ea, Eb, EC] using HC)
    have H := proofErase_computed_joint_types_inferred hstep hΓ ha hb H
    exact .base (.base (by simpa only [EΓ, Ea, Eb] using H))
  | aligned RA RB HT HC ihT => exact .aligned RA RB HT HC
  | app HF HX => exact .app HF HX
  | proj H => exact .proj H
  | lam => exact (sort_not_lam hΓ ha Ea).elim
  | forallE HA HB => exact .forallE HA HB
  | compute RA RB H ih =>
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    exact .compute RA RB (ih hΓ HA.hasType.2 HB.hasType.2 EΓ EA EB)
  | symm H ih => exact .symm (ih hΓ hb ha EΓ Eb Ea)

/-- Sort typings turn either aligned checking mode into inferred comparison
at the same primitive relation. The one-sided common carrier rule is discharged
by typed carrier inversion, not by assuming a missing second recovery. -/
theorem proofErase_carrier_aligned_types_inferred
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ a) (proofErase Γ b) :=
  aligned_types_inferred hstep H hΓ ha hb rfl rfl rfl

/-- At independently sort-typed endpoints, aligned comparison against a
literal universe supplies a computation to a universe at the same stage. -/
theorem proofErase_carrier_aligned_sort_exposure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .sort w) :
    ∃ w', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) (.sort w') := by
  obtain ⟨out, R, HE⟩ := (aligned_type_exposure_pair hstep hhead H hΓ ha hb rfl rfl rfl).1 false
    (by rw [Ea]; rfl)
  cases out <;> try cases HE
  exact ⟨_, R⟩

/-- At independently sort-typed endpoints, aligned comparison against a
literal Pi supplies a computation to a Pi at the same stage. Its domain need
not be syntactically equal to the originally assigned domain. -/
theorem proofErase_carrier_aligned_pi_exposure
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a (.sort u)) (hb : env.HasType univs Γ b (.sort v))
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b))
    (Ea : proofErase Γ a = .forallE A B) :
    ∃ A' B', ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ b) (.forallE A' B') := by
  obtain ⟨out, R, HE⟩ := (aligned_type_exposure_pair hstep hhead H hΓ ha hb rfl rfl rfl).1 true
    (by rw [Ea]; rfl)
  cases out <;> try cases HE
  exact ⟨_, _, R⟩

/-- An existing native recovery whose selected output compares with an actual
assigned Pi can expose a Pi without replacing native recovery by semantic
re-synthesis. The original comparison may use either checking mode. -/
theorem proofErase_carrier_aligned_recovered_pi
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B))
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) T)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) mode T
      (proofErase Γ (.forallE A B))) :
    ∃ A' B', ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE A' B') := by
  obtain ⟨T₀, hfT, ET⟩ := proofErase_scoped_typeRecovery_descend hstep hΓ hΓ
    (Ctx.LiftN.zero []) hf rfl (by simpa only [List.length_nil, ProofShape.liftN_zero] using R)
  simp only [List.length_nil, ProofShape.liftN_zero] at ET
  obtain ⟨u, hPi⟩ := hf.isType henv hΓ
  obtain ⟨v, hT⟩ := hfT.isType henv hΓ
  have EPi : proofErase Γ (.forallE A B) = .forallE (proofErase Γ A) (proofErase (A :: Γ) B) :=
    if_neg (not_isProof_of_sort hΓ hPi)
  obtain ⟨A', B', RC⟩ := proofErase_carrier_aligned_pi_exposure hstep hhead hΓ hPi hT
    (by simpa only [ET] using H.symm) EPi
  exact ⟨A', B', R.convert (by simpa only [ET] using RC)⟩

end Lean4Lean.VEnv.Strengthening
