import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortSpecialization

/-! # Whole carrier checking at images specializing to types

Only one endpoint needs an actual specializing interpretation. Source carriers
may have arbitrary syntax; all carrier computations and endpoint reductions
retain actual typings, so a structural checking escape is impossible.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem carrier_specialization_checked
    (hstep : ErasedScopedPrimitiveDescent Step)
    (H : ComputedJointCarrierGuard Step Δ rawC sa sb)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a C) (hb : env.HasType univs Γ b C)
    (ht : SortSpecialization Γ a ∨ SortSpecialization Γ b)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (EC : proofErase Γ C = rawC) :
    ComputedJointCompare Step Δ true sa sb := by
  change ComputedJointCheck Step Δ (.carrier rawC) sa sb at H
  generalize EK : JointCheckKind.carrier rawC = kind at H
  induction H generalizing Γ a b C rawC with
  | carrierChecked H => exact H
  | carrierIntro hi hx hp hadm H | carrierNested hi hx hp hadm HT H =>
    cases EK
    obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EC
    exact (ht.elim (fun h => h.not_structure hi ha) (fun h => h.not_structure hi hb)).elim
  | carrierSubsingleton H =>
    cases EK
    cases H with
    | unit hi hx hf hp =>
      obtain ⟨args, rfl, _⟩ := proofErase_const_spine_inv EC
      exact (ht.elim (fun h => h.not_structure hi ha) (fun h => h.not_structure hi hb)).elim
    | forallE H =>
      obtain ⟨_, _, rfl, _, _, _⟩ := erase_forallE_inv EC
      exact (ht.elim (fun h => h.not_function ha) (fun h => h.not_function hb)).elim
  | carrierFunction S H ih =>
    cases EK
    obtain ⟨_, _, rfl, _, _, _⟩ := erase_forallE_inv EC
    exact (ht.elim (fun h => h.not_function ha) (fun h => h.not_function hb)).elim
  | carrierSymm H ih => exact .symm (ih hΓ hb ha ht.symm EΓ Eb Ea EC EK)
  | carrierCompute RC H ih =>
    cases EK
    obtain ⟨_, hC⟩ := ha.isType henv hΓ
    obtain ⟨C', HC, EC'⟩ := proofErase_scoped_compute_realize hstep hΓ hC EΓ EC RC
    exact ih hΓ (HC.defeq ha) (HC.defeq hb) ht EΓ Ea Eb EC' rfl
  | carrierReduce RA RB H ih =>
    cases EK
    obtain ⟨a', HA, EA⟩ := proofErase_scoped_compute_realize hstep hΓ ha EΓ Ea RA
    obtain ⟨b', HB, EB⟩ := proofErase_scoped_compute_realize hstep hΓ hb EΓ Eb RB
    have ht' : SortSpecialization Γ a' ∨ SortSpecialization Γ b' :=
      ht.imp (fun h => h.back HA.symm) (fun h => h.back HB.symm)
    exact .compute RA RB (ih hΓ HA.hasType.2 HB.hasType.2 ht' EΓ EA EB EC rfl)
  | leaf | app | appCarrier | appComputed | proj | lam | forallE | lamSorted | forallSorted |
      lamCommon | etaBodyL | etaBodyR | structFields | etaLams | compute | symm => cases EK

/-- A full computed guard is ordinary comparison when either common-typed
endpoint admits an actual specialization to a type. The primitive relation and
endpoint syntax are retained, without assuming actual sort typings here. -/
theorem proofErase_computed_carrier_specialization_checked
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a C) (hb : env.HasType univs Γ b C)
    (ht : SortSpecialization Γ a ∨ SortSpecialization Γ b)
    (H : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) :=
  carrier_specialization_checked hstep H hΓ ha hb ht rfl rfl rfl rfl

/-- Any target carrier may reuse this checked argument certificate. Its sound
use supplies target typings separately; this theorem retains the checked syntax. -/
theorem proofErase_computed_carrier_specialization_reindex
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a C) (hb : env.HasType univs Γ b C)
    (ht : SortSpecialization Γ a ∨ SortSpecialization Γ b)
    (H : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCarrierGuard Step (proofEraseCtx Γ) target (proofErase Γ a) (proofErase Γ b) :=
  .carrierChecked (proofErase_computed_carrier_specialization_checked hstep hΓ ha hb ht H)

/-- An arbitrary actual carrier equal to a generic successor-universe type
parameter contributes only ordinary checking. The source carrier need not be
syntactically neutral, and every local binder above the parameter is retained. -/
theorem proofErase_computed_type_parameter_carrier_checked
    (hstep : ErasedScopedPrimitiveDescent Step)
    (W : Ctx.InstN Γ₀ (.sort u) (.sort (.succ u)) k Γ Γ')
    (hΓ : OnCtx Γ (env.IsType univs)) (hu : u.WF univs)
    (ha : env.HasType univs Γ a C) (hb : env.HasType univs Γ b C)
    (HE : env.IsDefEqU univs Γ C (.bvar k))
    (H : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare Step (proofEraseCtx Γ) true (proofErase Γ a) (proofErase Γ b) := by
  obtain ⟨_, hC⟩ := ha.isType henv hΓ
  have ha' := (HE.of_l henv hΓ hC).defeq ha
  exact proofErase_computed_carrier_specialization_checked hstep hΓ ha hb
    (.inl (SortSpecialization.type_parameter W hΓ hu ha')) H

/-- Specializable arguments repair application even if the function has no
native recovery at the selected carrier. Its supplied carrier readout is actual;
no target endpoint comparison is assumed. -/
theorem proofErase_computed_specialization_application
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (HT : SortSpecialization Γ x ∨ SortSpecialization Γ y)
    (HF : ComputedJointCompare Step (proofEraseCtx Γ) false f g)
    (HX : ComputedJointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ C)
      (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode
      (.app f (proofErase Γ x)) (.app g (proofErase Γ y)) :=
  .app HF (proofErase_computed_carrier_specialization_checked hstep hΓ hx hy HT HX)

end Lean4Lean.VEnv.Strengthening
