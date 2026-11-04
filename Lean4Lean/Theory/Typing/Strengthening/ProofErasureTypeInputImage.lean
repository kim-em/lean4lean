import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypeInputTree
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureComputedCarrierTypeChecking
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortImageRecovery

/-! # Typed application and projection for callable image trees

An application obtains an actual universe-domain function typing from the image
tree. Its arguments are types, so their already supplied carrier guard reduces
to ordinary comparison when the selected carrier has an actual typed readout.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_forallE_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Replaying source function recovery supplies actual typings for both
arguments at exactly the selected erased domain. This is obtained before
substitution, with no native recovery assumption about the substituted image. -/
theorem proofErase_scoped_function_recovery_arguments
    (hstep : ErasedScopedPrimitiveDescent Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ) (proofErase Γ f) (.forallE A B)) :
    ∃ C' E', env.HasType univs Γ f (.forallE C' E') ∧
      env.HasType univs Γ x C' ∧ env.HasType univs Γ y C' ∧
      proofErase Γ C' = A ∧ proofErase (C' :: Γ) E' = B := by
  obtain ⟨T, hfT, ET⟩ := proofErase_scoped_typeRecovery_replay hstep hΓ hf R
  obtain ⟨C', E', rfl, _, EC, EE⟩ := erase_forallE_inv ET
  exact ⟨C', E', hfT, argument_at_displayed_domain hΓ hf hfT hx,
    argument_at_displayed_domain hΓ hf hfT hy, EC, EE⟩

/-- Actual images carrying a finite tree of type-input calls and projections.
Earlier non-functional images embed without changing their certificates. -/
inductive TypeInputImage (Γ : List VExpr) (e : VExpr) : Prop
  | projection : InstanceProjectionImage Γ e → TypeInputImage Γ e
  | typed : env.HasType univs Γ e A → TypeInputTree env A → TypeInputImage Γ e

/-- Typed substitution retains every callable and projection child. -/
theorem TypeInputImage.subst (H : TypeInputImage Γ e)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) :
    TypeInputImage Γ₀ (e.subst σ) := by
  cases H with
  | projection H => exact .projection (H.subst hΓ₀ W)
  | typed h HA => exact .typed (h.subst henv.orderedStrong W hΓ₀) HA.subst

/-- Backward equality replay uses the certified actual type of the image. -/
theorem TypeInputImage.back (H : TypeInputImage Γ e')
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ e e' T) :
    TypeInputImage Γ e := by
  cases H with
  | projection H => exact .projection (H.back hΓ HE)
  | typed h HA => exact .typed (HE.toU.of_r henv hΓ h).hasType.1 HA

/-- A function occurrence must come from a callable tree node. Its actual
input is a universe, and its dependent result retains a child tree. -/
theorem TypeInputImage.function (H : TypeInputImage Γ f)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE A B)) :
    ∃ u C, env.HasType univs Γ f (.forallE (.sort u) C) ∧ TypeInputTree env C := by
  cases H with
  | projection H => exact (H.not_function hΓ hf).elim
  | typed h HA =>
    cases HA with
    | projection HA => exact ((InstanceProjectionImage.typed h HA).not_function hΓ hf).elim
    | function HC => exact ⟨_, _, h, HC⟩
    | record hi _ _ _ _ _ _ =>
      obtain ⟨_, hPi⟩ := hf.isType henv hΓ
      exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
        ((hf.uniqU henv hΓ h).typeChain henv hΓ hPi)).elim

/-- Actual application follows the dependent child tree after argument
substitution. No lambda exposure or native function recovery is required. -/
theorem TypeInputImage.application (H : TypeInputImage Γ f)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.app f x) T) : TypeInputImage Γ (.app f x) := by
  obtain ⟨_, _, hf, hx⟩ := ht.app_inv henv hΓ
  obtain ⟨u, C, hf', HC⟩ := H.function hΓ hf
  have hx' := argument_at_displayed_domain hΓ hf hf' hx
  exact .typed (HasType.app hf' hx')
    (by simpa only [← VExpr.inst_eq] using HC.subst (σ := VExpr.Subst.one x))

/-- Typed projection follows the instantiated field tree, which may now be
callable. A callable major itself cannot have a structure type. -/
theorem TypeInputImage.projection_image (H : TypeInputImage Γ e)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (.proj s i e) T)
    (hn : ¬ IsProof Γ (.proj s i e)) : TypeInputImage Γ (.proj s i e) := by
  cases H with
  | projection H => exact .projection (H.projection hΓ ht hn)
  | typed h HA =>
    cases HA with
    | projection HA => exact .projection ((InstanceProjectionImage.typed h HA).projection hΓ ht hn)
    | function HC =>
      obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
      obtain ⟨_, hPi⟩ := h.isType henv hΓ
      exact (henv.headInversion.forallE_rigid hΓ (henv.projectionRigid hi)
        ((h.uniqU henv hΓ hm.hasType.2).typeChain henv hΓ hPi)).elim
    | @record c info ls ps fields hi₀ hc hp hx hpos HF HT =>
      obtain ⟨_, _, _, _, _, _, _, hi, _, _, _, _, _, _, hm, _, _⟩ := ht.proj_inv henv hΓ
      obtain ⟨_, hC⟩ := h.isType henv hΓ
      obtain ⟨E, _, _⟩ := henv.headInversion.rigid_rigid hΓ
        (henv.projectionRigid hi₀) (henv.projectionRigid hi)
        ((h.uniqU henv hΓ hm.hasType.2).typeChain henv hΓ hC)
      subst E
      have hj := ht.proj_index_lt henv hΓ hi₀
      have hF := info.fieldType_subst_some hc (HF i hj) (substitution := VExpr.Subst.one e)
      have hfield : info.fieldType c ls ps i e = some ((fields i).inst e) := by
        simpa [List.map_map, Function.comp_def, ← VExpr.inst_eq, VExpr.inst_lift, VExpr.inst, instVar] using hF
      have hproj := StructureReplay.positive_projection_native hΓ hi₀ hp hx h hpos hj hfield
      exact .typed hproj (by simpa only [← VExpr.inst_eq] using (HT i hj).subst (σ := VExpr.Subst.one e))

/-- The actual selected-carrier readout is sufficient to repair application
at a callable image. The supplied argument guard is consumed in full, including
carrier computation and endpoint reduction, without any new comparison premise. -/
theorem TypeInputImage.application_checked (H : TypeInputImage Γ f)
    (hstep : ErasedScopedPrimitiveDescent Step) (hΓ : OnCtx Γ (env.IsType univs))
    (hf : env.HasType univs Γ f (.forallE C E))
    (hx : env.HasType univs Γ x C) (hy : env.HasType univs Γ y C)
    (EC : proofErase Γ C = A)
    (HF : ComputedJointCompare Step (proofEraseCtx Γ) false (proofErase Γ f) g)
    (HX : ComputedJointCarrierGuard Step (proofEraseCtx Γ) A (proofErase Γ x) (proofErase Γ y)) :
    ComputedJointCompare Step (proofEraseCtx Γ) mode
      (.app (proofErase Γ f) (proofErase Γ x)) (.app g (proofErase Γ y)) := by
  obtain ⟨u, K, hf', _⟩ := H.function hΓ hf
  have hx' := argument_at_displayed_domain hΓ hf hf' hx
  have hy' := argument_at_displayed_domain hΓ hf hf' hy
  have HX' := proofErase_computed_carrier_types_checked hstep hΓ hx' hy' (.inl hx)
    (by simpa only [EC] using HX)
  exact .app HF HX'

end Lean4Lean.VEnv.Strengthening
