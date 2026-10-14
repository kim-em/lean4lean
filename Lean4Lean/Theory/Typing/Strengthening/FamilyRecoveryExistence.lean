import Lean4Lean.Theory.Typing.Strengthening.RecoveryExistence
import Lean4Lean.Theory.Typing.Strengthening.ProjectionRecoveryTotality

/-! # Recovery existence needs only head exposure

Once computation has typed replay, projection field selection follows from
exposing its family. The following local clauses are still unproved for the
staged computation; they characterize recovery existence, not strengthening.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
variable {C : List VExpr → VExpr → VExpr → Prop}

/-- The application clause is unchanged; the projection clause asks only for
the registered family head, with no field-selection premise. Both remain open
for the staged model. -/
structure RecoveryFamilyHeads (C : List VExpr → VExpr → VExpr → Prop) : Prop where
  app : ∀ {Γ f a T}, OnCtx Γ (env.IsType univs) →
    VExpr.WF env univs Γ (.app f a) → TypeRecoveryWith C Γ f T →
    ∃ A B, TypeRecoveryWith C Γ f (.forallE A B)
  proj : ∀ {Γ s i m T}, OnCtx Γ (env.IsType univs) →
    VExpr.WF env univs Γ (.proj s i m) → TypeRecoveryWith C Γ m T →
    ∃ ls args, TypeRecoveryWith C Γ m (mkApps (.const s ls) args)

/-- Source projection typing supplies the registration and total field
selection after the recovered major has been replayed. -/
theorem RecoveryFamilyHeads.heads (H : RecoveryFamilyHeads C)
    (hc : ComputeDescent C) : RecoveryHeads C where
  app := H.app
  proj hΓ ht R := by
    obtain ⟨ls, args, R'⟩ := H.proj hΓ ht R
    obtain ⟨_, ht'⟩ := ht
    obtain ⟨info, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ :=
      HasType.proj_inv henv hΓ ht'
    have hm' := R'.hasType hc hΓ ⟨_, hm.hasType.2⟩
    obtain ⟨F, hF⟩ := projection_recovered_field_exists henv hΓ hi ⟨_, ht'⟩ hm'
    exact ⟨info, ls, args, F, hi, R', hF⟩

/-- Erasing the selection witness needs no assumptions about computation. -/
theorem RecoveryHeads.familyHeads (H : RecoveryHeads C) : RecoveryFamilyHeads C where
  app := H.app
  proj hΓ ht R := by
    obtain ⟨_, ls, args, _, _, R', _⟩ := H.proj hΓ ht R
    exact ⟨ls, args, R'⟩

/-- Under checked computation descent, Pi and family exposure characterize
recovery existence exactly. Selection is not an additional open clause. -/
theorem recoveryExists_iff_familyHeads (hc : ComputeDescent C) :
    RecoveryExists C ↔ RecoveryFamilyHeads C :=
  ⟨fun H => H.heads.familyHeads, fun H => (H.heads hc).exists⟩

/-- Compute an inferred major type to its projection family. Parameters and
levels may change, and no selected field is prescribed. This computational
completeness obligation remains unproved for the staged model. -/
def RecoveryFamilyExposure (C : List VExpr → VExpr → VExpr → Prop) : Prop :=
  ∀ {Γ s i m T}, OnCtx Γ (env.IsType univs) →
    VExpr.WF env univs Γ (.proj s i m) → env.HasType univs Γ m T →
    ∃ ls args, C Γ T (mkApps (.const s ls) args)

/-- Typed replay transports the inferred major typing to the exposed family;
field-selection totality discharges the old extra witness. -/
theorem RecoveryFamilyExposure.projectionExposure (H : RecoveryFamilyExposure C)
    (hc : ComputeDescent C) : RecoveryProjectionExposure C := by
  intro Γ s i m T hΓ ht hm
  obtain ⟨ls, args, R⟩ := H hΓ ht hm
  obtain ⟨_, hT⟩ := hm.isType henv hΓ
  have hm' := (hc.simAt R hΓ _ hT).defeq hm
  obtain ⟨_, ht'⟩ := ht
  obtain ⟨info, _, _, _, _, _, _, hi, _⟩ := HasType.proj_inv henv hΓ ht'
  obtain ⟨F, hF⟩ := projection_recovered_field_exists henv hΓ hi ⟨_, ht'⟩ hm'
  exact ⟨info, ls, args, F, hi, R, hF⟩

/-- Dropping the registration and field witnesses gives family exposure. -/
theorem RecoveryProjectionExposure.familyExposure (H : RecoveryProjectionExposure C) :
    RecoveryFamilyExposure C := by
  intro Γ s i m T hΓ ht hm
  obtain ⟨_, ls, args, _, _, R, _⟩ := H hΓ ht hm
  exact ⟨ls, args, R⟩

/-- The operational projection premise is equivalent to mere family exposure
for every computational base with checked descent. -/
theorem recoveryProjectionExposure_iff_familyExposure (hc : ComputeDescent C) :
    RecoveryProjectionExposure C ↔ RecoveryFamilyExposure C :=
  ⟨RecoveryProjectionExposure.familyExposure, fun H => H.projectionExposure hc⟩

/-- Pi and family exposure suffice to synthesize some recoverable output for
every well-formed term, without exact-output completeness. -/
theorem RecoveryExists.of_head_exposure (hc : ComputeDescent C)
    (hPi : RecoveryPiExposure C) (hFamily : RecoveryFamilyExposure C) :
    RecoveryExists C :=
  (RecoveryHeads.of_type_exposure hc hPi (hFamily.projectionExposure hc)).exists

end Lean4Lean.VEnv.Strengthening
