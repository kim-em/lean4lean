import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeFrameworkRecoverySubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedCoreGuardAlignment

/-! # Finite native alignment at a reduct of the selected carrier

The selected carrier may compute before the existing finite alignment is used.
This combines semantic input-family conversion with computationally joined
arbitrary results. The conversion closure uses typed core confluence; it does
not assert confluence of guarded singleton stages or arbitrary carrier joins.
-/
namespace Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private forall_parts from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCoreRecoveryReduction
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {hq : QuotRegistered env} {F : List VExpr → VExpr → Prop}

/-- Native recovery with finite family alignment to a reduct of the selected
output. The computation begins at selection, not at an assumed native type. -/
def Recovery (hq : QuotRegistered env) (F : List VExpr → VExpr → Prop)
    (Γ : List VExpr) (e : VExpr) (out : ProofShape) : Prop :=
  ∃ mid, NativeFamilyFramework.Recovery (definitions hq) F Γ e mid ∧
    Compute (Step hq) out mid

/-- Every previously aligned recovery enters with a reflexive selection path. -/
theorem Recovery.of_aligned
    (H : NativeFamilyFramework.Recovery (definitions hq) F Γ e out) :
    Recovery hq F Γ e out := ⟨out, H, .refl⟩

/-- Exact native recovery enters without an input-family assumption. -/
theorem Recovery.of_native
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) out) :
    Recovery hq F Γ e out :=
  .of_aligned (NativeFamilyFramework.Recovery.of_native (sound hq) hΓ ht R)

/-- A common reduct of native and assigned outputs supplies the combined
relation, even when no finite alignment selects the assigned syntax. -/
theorem Recovery.of_joined
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e T)
    (R : ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) native)
    (RA : Compute (Step hq) out shared) (RN : Compute (Step hq) native shared) :
    Recovery hq F Γ e out :=
  ⟨shared, NativeFamilyFramework.Recovery.of_native (sound hq) hΓ ht
    (R.convert (RN.scoped (fun H => .base H))), RA⟩

/-- Selecting a predecessor merely extends the retained computation path. -/
theorem Recovery.backward (H : Recovery hq F Γ e out)
    (RC : Compute (Step hq) source out) : Recovery hq F Γ e source := by
  obtain ⟨mid, H, R⟩ := H
  exact ⟨mid, H, RC.trans R⟩

/-- Forward computation of a typed selection joins its retained path. The
finite alignment can then compute to the common reduct on its selection side. -/
theorem Recovery.convert
    (H : Recovery hq F Γ e (proofErase Γ A))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (RC : Compute (Step hq) (proofErase Γ A) out) : Recovery hq F Γ e out := by
  obtain ⟨mid, H, R⟩ := H
  obtain ⟨shared, RM, RO⟩ := confluent hq hcon hΓ hA R RC
  exact ⟨shared, H.convert RM, RO⟩

/-- Lambda recovery retains the path beneath its written domain. -/
theorem Recovery.lam (H : Recovery hq F (A :: Γ) b out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hn : ¬ IsProof Γ (.lam A b)) :
    Recovery hq F Γ (.lam A b) (.forallE (proofErase Γ A) out) := by
  obtain ⟨mid, H, R⟩ := H
  exact ⟨_, H.lam hΓ hA hn, .forallE .refl R⟩

/-- A selected sort is fixed by core computation, so the original sort readout
still supplies an actual native universe, possibly at an equivalent level. -/
theorem Recovery.sort (H : Recovery hq F Γ e (.sort u))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ e (.sort v)) :
    ∃ w, env.HasType univs Γ e (.sort w) ∧
      ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) (.sort w) := by
  obtain ⟨mid, H, R⟩ := H
  have E := (R.scoped (Δ := proofEraseCtx Γ) (fun H => .base H)).sort_fixed
    (fun H => erased_iota_primitive_head H)
  subst mid
  exact H.sort (sound hq) hΓ ht

/-- A typed structure major retains native recovery at a reduct of the selected
carrier. The old alignment theorem recovers that intermediate carrier exactly. -/
theorem Recovery.projection_recovery (H : Recovery hq F Γ e out)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ (.proj s i e) T) :
    ∃ mid, ScopedTypeRecovery (fun _ => Step hq) (proofEraseCtx Γ) (proofErase Γ e) mid ∧
      Compute (Step hq) out mid := by
  obtain ⟨mid, H, R⟩ := H
  exact ⟨mid, H.projection_recovery hΓ ht, R⟩

variable [NativeFamilyFramework.InputLaws (definitions hq) F]

/-- Binder insertion preserves both finite alignment and the selected path. -/
theorem Recovery.weaken (H : Recovery hq F Γ e out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓA : OnCtx (A :: Γ) (env.IsType univs)) :
    Recovery hq F (A :: Γ) (e.liftN 1) (out.liftN 1) := by
  obtain ⟨mid, H, R⟩ := H
  exact ⟨_, H.weaken hΓ hΓA, R.liftN (fun H => erased_iota_primitive_liftN H)⟩

/-- Application computes the selected Pi components, then uses finite alignment
at the intermediate Pi. The codomain path survives arbitrary typed instantiation. -/
theorem Recovery.app (H : Recovery hq F Γ f (.forallE rawA rawB))
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ (.app f x) T)
    (hn : ¬ IsProof Γ (.app f x)) :
    Recovery hq F Γ (.app f x) (rawB.inst (proofErase Γ x)) := by
  obtain ⟨mid, H, R⟩ := H
  obtain ⟨A', B', rfl, _, RB⟩ := forall_parts hq R
  refine ⟨_, H.app (sound hq) hΓ ht hn, ?_⟩
  simpa only [ProofShape.inst_eq_subst] using RB.subst (fun H => erased_iota_primitive_subst H)

/-- A selected-domain argument guard computes forward to the intermediate Pi
before finite family readout selects the actual native input. Both stages are
proved for the whole recursive carrier guard, including dependent fields. -/
theorem Recovery.application_checked
    (H : Recovery hq F Γ f (.forallE rawA rawB))
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (EC : proofErase Γ C = rawA) (EE : proofErase (C :: Γ) E = rawB)
    (HF : ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ) false (proofErase Γ f) g)
    (HX : ComputedJointCarrierGuard (fun _ => Step hq) (proofEraseCtx Γ)
      rawA (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare (fun _ => Step hq) (proofEraseCtx Γ) mode
      (.app (proofErase Γ f) (proofErase Γ x)) (.app g (proofErase Γ y)) := by
  obtain ⟨mid, H, R⟩ := H
  obtain ⟨A', B', rfl, RA, _⟩ := forall_parts hq R
  obtain ⟨_, hPi⟩ := hf.isType henv hΓ
  have EPi : proofErase Γ (.forallE C E) = .forallE rawA rawB := by
    rw [show proofErase Γ (.forallE C E) = .forallE _ _ from if_neg (not_isProof_of_sort hΓ hPi), EC, EE]
  have hstep : ErasedScopedPrimitiveDescent (fun _ => Step hq) :=
    ErasedPrimitiveReplay.toDescent (sound hq) (erased_iota_replay (sound hq))
  obtain ⟨Pi', HPi, EPi'⟩ := proofErase_scoped_compute_realize hstep hΓ hPi rfl EPi
    (R.scoped (fun H => .base H))
  obtain ⟨C', E', rfl, _, EC', _⟩ := erase_forallE_inv EPi'
  have hf' := HPi.defeq hf
  have hx' := argument_at_displayed_domain hΓ hf hf' hx
  have hy' := argument_at_displayed_domain hΓ hf hf' hy
  have HX' := computed_carrier_compute_forward hq hcon hΓ hx hy
    (by simpa only [EC] using HX) (by simpa only [EC] using RA)
  exact H.application_checked (sound hq) hΓ hf' hx' hy' EC' HF HX'

end Lean4Lean.VEnv.Strengthening.ErasedQuotCore.NativeJoinFramework
