import Lean4Lean.Theory.Typing.Strengthening.ProofErasureStaticStructureVariableReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeBinder

/-! # Exact native demands at opaque type variables

An opaque type variable returns from all of its computations by beta alone.
Its computed binder therefore supplies exact stage-zero identity images.
Commonly recovered data arguments at this type satisfy exact substitution and
beta demands, without any assertion of common recovery for arbitrary values.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A binder computed from an opaque type variable admits stage-zero exact
identity images in the forward direction. Only the domain path uses the full
guarded union; its reverse path is pure beta. -/
theorem static_structure_native_computed_variable_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ (.bvar i) C (.sort u))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar i) (proofErase Γ C)) :
    StaticStructureEtaNativeSubstitution.ImageSubstitution D 0
      (proofEraseCtx (.bvar i :: Γ)) (proofEraseCtx (C :: Γ)) ProofShape.Subst.id := by
  have RB := proofErase_static_structure_union_type_variable_readout heq hs hΓ HAC.hasType.1 R
  have E : proofErase Γ (.bvar i) = .bvar i := if_neg (not_isProof_of_sort hΓ HAC.hasType.1)
  have RC : ScopedCompute (ErasedStaticStructureEtaExpansionStage D 0) (proofEraseCtx Γ)
      (proofErase Γ C) (proofErase Γ (.bvar i)) := E ▸ ScopedCompute.beta RB
  intro Γ' hΓ' EΓ'
  exact static_structure_native_backward_context heq hs hΓ HAC.symm RC hΓ' EΓ'

/-- Computation transports forward across a computed opaque type binder
with the original stage and exact output, including beneath nested binders. -/
theorem proofErase_static_structure_compute_variable_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ (.bvar i) C (.sort u))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar i) (proofErase Γ C))
    (ht : env.HasType univs (.bvar i :: Γ) e T)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (.bvar i :: Γ))
      (proofErase (.bvar i :: Γ) e) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) e) out := by
  have hΓA : OnCtx (.bvar i :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have R' := StaticStructureEtaNativeSubstitution.compute heq hs R hΓA ht rfl rfl
    (static_structure_native_computed_variable_context heq hs hΓ HAC RA)
  simp only [Nat.add_zero, ProofShape.subst_id] at R'
  simpa only [proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HAC) ht] using R'

/-- Every selected native result transports exactly across the same
computed opaque type binder, without increasing its guard depth. -/
theorem proofErase_static_structure_recovery_variable_context
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (HAC : env.IsDefEq univs Γ (.bvar i) C (.sort u))
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.bvar i) (proofErase Γ C))
    (ht : env.HasType univs (.bvar i :: Γ) e T)
    (R : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (.bvar i :: Γ))
      (proofErase (.bvar i :: Γ) e) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionStage D n) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) e) out := by
  have hΓA : OnCtx (.bvar i :: Γ) (env.IsType univs) := ⟨hΓ, u, HAC.hasType.1⟩
  have R' := StaticStructureEtaNativeSubstitution.recovery heq hs R hΓA ht rfl rfl
    (static_structure_native_computed_variable_context heq hs hΓ HAC RA)
  simp only [Nat.add_zero, ProofShape.subst_id] at R'
  simpa only [proofErase_defeqCtx hΓA (IsDefEqCtx.succ .zero HAC) ht] using R'

/-- Common native evidence at an opaque type variable yields exact recovery
at that assigned type for retained arguments. Proof arguments remain excluded
from the image demand; no universal common coverage is assumed. -/
theorem CommonNativeArgument.exact_type_variable
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hx : env.HasType univs Γ x (.bvar i))
    (H : CommonNativeArgument D Γ x (.bvar i))
    (hn : ¬ IsProof Γ x) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ (.bvar i)) := by
  obtain ⟨shared, RN, RC⟩ := H hn
  obtain ⟨u, hA⟩ := hx.isType henv hΓ
  have E : proofErase Γ (.bvar i) = .bvar i := if_neg (not_isProof_of_sort hΓ hA)
  rw [E] at RC ⊢
  exact RN.convert (.beta (proofErase_static_structure_union_type_variable_readout heq hs hΓ hA RC))

/-- Beta at a commonly recovered argument assigned an opaque type variable
preserves every selected native result exactly. This includes retained data;
the argument need not have been given an exact native certificate. -/
theorem static_structure_common_variable_beta_native_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ (.bvar i) (.sort u))
    (hb : env.HasType univs (.bvar i :: Γ) b B) (hx : env.HasType univs Γ x (.bvar i))
    (HX : CommonNativeArgument D Γ x (.bvar i))
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.app (.lam (.bvar i) b) x)) out) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (b.inst x)) out :=
  static_structure_root_beta_native_recovery heq hs hΓ hA hb hx (HX.exact_type_variable heq hs hΓ hx) RN

end Lean4Lean.VEnv.Strengthening
