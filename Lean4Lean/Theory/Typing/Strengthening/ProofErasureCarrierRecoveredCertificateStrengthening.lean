import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredStageCertificateDescent
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredPrimitiveRenaming

/-! # Exact certificate strengthening at every stage and at the full union

Unused binder insertion preserves and reflects computation, selected recovery,
common-typed comparison and explicit-carrier checking. The finite stage and
literal raw outputs are unchanged. This is certificate strengthening, not
completeness of the checker for arbitrary declarative equality.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private ProofShape.subst_bvar_liftN
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Compatible computation with a prescribed raw output is invariant under
unused binder insertion at the original finite stage. Only the source needs a lower typing;
no lower original representative of the selected output is assumed. -/
theorem proofErase_carrier_recovered_stage_compute_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ProofShape.ScopedCompute (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ProofShape.ScopedCompute (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨e', _, R, E⟩ := proofErase_scoped_compute_certificate_descend
      (erased_carrier_recovered_stage_certificate_descent heq hs stage) hΓ hΓ' W ht rfl H
    have E' : proofErase Γ e' = out := ProofShape.lift'_inj (ρ := .consN (.skipN .refl n) k)
      (by simpa only [ProofShape.lift'_consN_skipN] using E)
    exact E' ▸ R
  · intro H
    have R := H.rename (erased_carrier_recovered_stage_rename heq hs stage) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [ProofShape.subst_bvar_liftN] using R

/-- Exact selected type recovery is invariant under
unused binder insertion at the original finite stage. Only the source needs a lower typing;
no lower original representative of the selected output is assumed. -/
theorem proofErase_carrier_recovered_stage_recovery_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ProofShape.ScopedTypeRecovery (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ProofShape.ScopedTypeRecovery (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨e', _, R, E⟩ := proofErase_scoped_recovery_certificate_descend
      (erased_carrier_recovered_stage_certificate_descent heq hs stage) hΓ hΓ' W ht rfl H
    have E' : proofErase Γ e' = out := ProofShape.lift'_inj (ρ := .consN (.skipN .refl n) k)
      (by simpa only [ProofShape.lift'_consN_skipN] using E)
    exact E' ▸ R
  · intro H
    have R := H.rename (erased_carrier_recovered_stage_rename heq hs stage) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [ProofShape.subst_bvar_liftN] using R

/-- Both comparison modes are invariant under binder insertion at common
typed endpoints without increasing their finite stage.
This preserves the actual comparison certificate, not just its reflection. -/
theorem proofErase_carrier_recovered_stage_compare_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A) :
    ProofShape.CarrierRecoveredCompare (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ') mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k) ↔
    ProofShape.CarrierRecoveredCompare (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b) := by
  constructor
  · intro H
    exact (proofErase_carrier_recovered_compare_certificate_descend (erased_carrier_recovered_stage_certificate_descent heq hs stage)
      hΓ hΓ' W rfl ha hb H).1 ⟨_, ha.isType henv hΓ |>.choose_spec⟩
  · intro H
    have R := H.rename (erased_carrier_recovered_stage_rename heq hs stage) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [ProofShape.subst_bvar_liftN] using R

/-- Explicit-carrier checking is invariant under unused binder insertion
at the original finite stage, with exactly the supplied lower carrier. -/
theorem proofErase_carrier_recovered_stage_carrier_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A) :
    ProofShape.ComputedJointCarrierGuard (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ')
      ((proofErase Γ A).liftN n k) ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k) ↔
    ProofShape.ComputedJointCarrierGuard (ErasedCarrierRecoveredStage D stage) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) := by
  constructor
  · exact proofErase_computed_joint_carrier_certificate_descend (erased_carrier_recovered_stage_certificate_descent heq hs stage) hΓ hΓ' W ha hb
  · intro H
    have R := H.rename (erased_carrier_recovered_stage_rename heq hs stage) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [ProofShape.JointCheckKind.subst, ProofShape.subst_bvar_liftN] using R

/-- Compatible computation with a prescribed raw output is invariant under
unused binder insertion in the full union. Only the source needs a lower typing;
no lower original representative of the selected output is assumed. -/
theorem proofErase_carrier_recovered_union_compute_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ProofShape.ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ProofShape.ScopedCompute (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨e', _, R, E⟩ := proofErase_scoped_compute_certificate_descend
      (erased_carrier_recovered_union_certificate_descent heq hs) hΓ hΓ' W ht rfl H
    have E' : proofErase Γ e' = out := ProofShape.lift'_inj (ρ := .consN (.skipN .refl n) k)
      (by simpa only [ProofShape.lift'_consN_skipN] using E)
    exact E' ▸ R
  · intro H
    have R := H.rename (erased_carrier_recovered_union_rename heq hs) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [ProofShape.subst_bvar_liftN] using R

/-- Exact selected type recovery is invariant under
unused binder insertion in the full union. Only the source needs a lower typing;
no lower original representative of the selected output is assumed. -/
theorem proofErase_carrier_recovered_union_recovery_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (ht : env.HasType univs Γ e T) :
    ProofShape.ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ')
      ((proofErase Γ e).liftN n k) (out.liftN n k) ↔
    ProofShape.ScopedTypeRecovery (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) (proofErase Γ e) out := by
  constructor
  · intro H
    obtain ⟨e', _, R, E⟩ := proofErase_scoped_recovery_certificate_descend
      (erased_carrier_recovered_union_certificate_descent heq hs) hΓ hΓ' W ht rfl H
    have E' : proofErase Γ e' = out := ProofShape.lift'_inj (ρ := .consN (.skipN .refl n) k)
      (by simpa only [ProofShape.lift'_consN_skipN] using E)
    exact E' ▸ R
  · intro H
    have R := H.rename (erased_carrier_recovered_union_rename heq hs) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [ProofShape.subst_bvar_liftN] using R

/-- Both comparison modes are invariant under binder insertion at common
typed endpoints in the full union.
This preserves the actual comparison certificate, not just its reflection. -/
theorem proofErase_carrier_recovered_union_compare_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A) :
    ProofShape.CarrierRecoveredCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ') mode
      ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k) ↔
    ProofShape.CarrierRecoveredCompare (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b) := by
  constructor
  · intro H
    exact (proofErase_carrier_recovered_compare_certificate_descend (erased_carrier_recovered_union_certificate_descent heq hs)
      hΓ hΓ' W rfl ha hb H).1 ⟨_, ha.isType henv hΓ |>.choose_spec⟩
  · intro H
    have R := H.rename (erased_carrier_recovered_union_rename heq hs) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [ProofShape.subst_bvar_liftN] using R

/-- Explicit-carrier checking is invariant under unused binder insertion
in the full union, with exactly the supplied lower carrier. -/
theorem proofErase_carrier_recovered_union_carrier_lift_iff
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ')
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A) :
    ProofShape.ComputedJointCarrierGuard (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ')
      ((proofErase Γ A).liftN n k) ((proofErase Γ a).liftN n k) ((proofErase Γ b).liftN n k) ↔
    ProofShape.ComputedJointCarrierGuard (ErasedCarrierRecoveredUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b) := by
  constructor
  · exact proofErase_computed_joint_carrier_certificate_descend (erased_carrier_recovered_union_certificate_descent heq hs) hΓ hΓ' W ha hb
  · intro H
    have R := H.rename (erased_carrier_recovered_union_rename heq hs) (ProofShape.ContextRenaming.of_liftN hΓ hΓ' W)
    simpa only [ProofShape.JointCheckKind.subst, ProofShape.subst_bvar_liftN] using R

end Lean4Lean.VEnv.Strengthening
