import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedJointVariants
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCoreRecords

/-! # Concrete joint transport with arbitrary function and record nesting

The actual core discharges both computation interfaces of joint transport.
Consequently ordinary finite checking certificates, including native
applications and recursive function/record guards, survive structural universe
changes of actual contexts and carriers. No future-stability certificate is an
input, and no completeness for arbitrary declarative equality is asserted.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private variant_type_eq
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedRecordTransfer
variable [Params]

/-- Structural variants of well-formed erased contexts determine actual
context conversion. No equality of the original proof terms is assumed. -/
theorem proofErase_carrier_aligned_context_variant_defeq
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (HΓ : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ')) :
    IsDefEqCtx env univs [] Γ Γ' := by
  induction Γ generalizing Γ' with
  | nil =>
    cases Γ' with
    | nil => exact .zero
    | cons => cases HΓ
  | cons A Γ ih =>
    cases Γ' with
    | nil => cases HΓ
    | cons B Γ' =>
      cases HΓ with
      | cons VA HΓ =>
        obtain ⟨hΓ, u, hA⟩ := hΓ
        obtain ⟨hΓ', v, hB⟩ := hΓ'
        have W := ih hΓ hΓ' HΓ
        have hB' := hB.defeqDFC henv (W.symm henv.ordered)
        have EB := proofErase_defeqCtx hΓ' (W.symm henv.ordered) hB
        have HE := variant_type_eq (Step := Step) hstep hΓ hA hB'
          (by simpa only [EB] using VA)
        exact .succ W (HE.of_l henv hΓ hA)

/-- Concrete core native recovery follows structural context and term variants. -/
theorem proofErase_carrier_aligned_core_recovery_variant
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (ht : env.HasType univs Γ e T) (ht' : env.HasType univs Γ' e' T')
    (HΓ : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (V : StructuralVariant (proofErase Γ e) (proofErase Γ' e'))
    (R : ScopedTypeRecovery (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ out', ScopedTypeRecovery (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ')
      (proofErase Γ' e') out' ∧ StructuralVariant out out' :=
  proofErase_carrier_aligned_recovery_variant (ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs))
    (structuralVariantCompute_core hs hlevels hcon) R hΓ hΓ' ht ht' rfl rfl HΓ V

/-- All ordinary computed comparisons over concrete core computation transport
through equal actual contexts with structural universe variants of their entries. -/
theorem proofErase_carrier_aligned_core_joint_context
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (W : IsDefEqCtx env univs [] Γ Γ')
    (HΓ : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCompare (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ') mode
      (proofErase Γ' a) (proofErase Γ' b) := by
  have H' := H.structural_variant (ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs))
    structuralVariantComputeContext_core (structuralVariantCompute_core hs hlevels hcon)
    hΓ ha hb rfl rfl rfl W HΓ
  rwa [proofErase_defeqCtx hΓ W ha, proofErase_defeqCtx hΓ W hb] at H'

/-- Well-formed structural context variants alone suffice for core joint
comparison; actual context conversion is reconstructed from their entries. -/
theorem proofErase_carrier_aligned_core_joint_context_variant
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (HΓ : List.Forall₂ StructuralVariant (proofEraseCtx Γ) (proofEraseCtx Γ'))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ComputedJointCompare (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ) mode
      (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCompare (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ') mode
      (proofErase Γ' a) (proofErase Γ' b) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedIotaPrimitive D) :=
    ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  exact proofErase_carrier_aligned_core_joint_context hs hlevels hcon hΓ
    (proofErase_carrier_aligned_context_variant_defeq (Step := fun _ => ErasedIotaPrimitive D) hstep hΓ hΓ' HΓ) HΓ ha hb H

/-- Every core computed carrier guard survives a structural universe variant of
its assigned type, including arbitrary alternation of function and record guards. -/
theorem proofErase_carrier_aligned_core_joint_carrier
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (hB : env.HasType univs Γ B (.sort v))
    (V : StructuralVariant (proofErase Γ A) (proofErase Γ B))
    (H : ComputedJointCarrierGuard (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    ComputedJointCarrierGuard (fun _ => ErasedIotaPrimitive D) (proofEraseCtx Γ)
      (proofErase Γ B) (proofErase Γ a) (proofErase Γ b) := by
  have hstep : ErasedScopedPrimitiveDescent (fun _ => ErasedIotaPrimitive D) :=
    ErasedPrimitiveReplay.toDescent hs (erased_iota_replay hs)
  obtain ⟨_, hA⟩ := ha.isType henv hΓ
  exact H.structural_variant hstep structuralVariantComputeContext_core
    (structuralVariantCompute_core hs hlevels hcon) hΓ ha hb rfl rfl rfl rfl
    (.refl hΓ) (.rfl (fun _ _ => .refl)) (variant_type_eq (Step := fun _ => ErasedIotaPrimitive D) hstep hΓ hA hB V) V

/-- One changed binder supports ordinary core checking, even when native
application recovery inside the body selects different universe syntax. -/
theorem proofErase_carrier_aligned_core_joint_binder
    (hs : D.Sound env univs) (hlevels : D.LevelCompatible univs)
    (hcon : ∀ {p r}, Pat p r → ConcretePattern env p r)
    (hΓ : OnCtx Γ (env.IsType univs)) (HE : env.IsDefEq univs Γ A B (.sort u))
    (V : StructuralVariant (proofErase Γ A) (proofErase Γ B))
    (ha : env.HasType univs (A :: Γ) a T) (hb : env.HasType univs (A :: Γ) b T)
    (H : ComputedJointCompare (fun _ => ErasedIotaPrimitive D) (proofEraseCtx (A :: Γ)) mode
      (proofErase (A :: Γ) a) (proofErase (A :: Γ) b)) :
    ComputedJointCompare (fun _ => ErasedIotaPrimitive D) (proofEraseCtx (B :: Γ)) mode
      (proofErase (B :: Γ) a) (proofErase (B :: Γ) b) :=
  proofErase_carrier_aligned_core_joint_context (Γ := A :: Γ) hs hlevels hcon ⟨hΓ, u, HE.hasType.1⟩
    (.succ (.refl hΓ) HE) (.cons V (.rfl (fun _ _ => .refl))) ha hb H

omit [Params] in
/-- For actual declarations and concrete patterns, full carrier-guard transport
has no compatibility premises. It preserves the existing computed judgment. -/
theorem proofErase_carrier_aligned_environment_joint_carrier
    {E : VEnv} (hE : E.WF) (U : Nat)
    (hΓ : OnCtx Γ (E.IsType U))
    (ha : E.HasType U Γ a A) (hb : E.HasType U Γ b A)
    (hB : E.HasType U Γ B (.sort v))
    (V : StructuralVariant (@proofErase (hE.params U) Γ A) (@proofErase (hE.params U) Γ B))
    (H : @ComputedJointCarrierGuard (hE.params U) (fun _ => @ErasedIotaPrimitive (hE.params U) (Definitions.ofEnv E U hE))
      (@proofEraseCtx (hE.params U) Γ) (@proofErase (hE.params U) Γ A)
      (@proofErase (hE.params U) Γ a) (@proofErase (hE.params U) Γ b)) :
    @ComputedJointCarrierGuard (hE.params U) (fun _ => @ErasedIotaPrimitive (hE.params U) (Definitions.ofEnv E U hE))
      (@proofEraseCtx (hE.params U) Γ) (@proofErase (hE.params U) Γ B)
      (@proofErase (hE.params U) Γ a) (@proofErase (hE.params U) Γ b) := by
  letI := hE.params U
  exact proofErase_carrier_aligned_core_joint_carrier (Definitions.ofEnv_sound hE)
    (Definitions.ofEnv_levelCompatible hE) (fun H => H) hΓ ha hb hB V H

end Lean4Lean.VEnv.Strengthening
