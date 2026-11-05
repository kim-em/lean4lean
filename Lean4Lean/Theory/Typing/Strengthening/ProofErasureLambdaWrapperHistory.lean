import Lean4Lean.Theory.Typing.Strengthening.ProofErasureWrapperNativeOrigin
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeEtaDiamond

/-! # Historical native types of lambda wrapper frames

A generated identity frame keeps the Pi history of its annotation even after
its argument changes. The history is anchored at the original lambda domain;
it does not require the current argument to recover the old annotation. This
separates the two facts needed by a lambda observer: beta exposes the argument's
payload, whereas native eta reads the frame's stored type history.

This grammar covers nested literal constant/identity frames and root native
eta. It does not claim closure under arbitrary computation of control functions.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- A native type has a typed Pi predecessor whose domain is reached from the
original anchor. Its complete conversion tail is retained, including wrappers
around the Pi. This is a concrete path certificate, not a type-joining premise. -/
def NativePiHistory (D : PureObservation.Definitions) (Γ : List VExpr)
    (anchor out : ProofShape) : Prop :=
  ∃ A B u v, env.HasType univs Γ A (.sort u) ∧
    env.HasType univs (A :: Γ) B (.sort v) ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      anchor (proofErase Γ A) ∧
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (.forallE (proofErase Γ A) (proofErase (A :: Γ) B)) out

/-- Further computation appends to the stored Pi history without recovering
the original source again. -/
theorem NativePiHistory.compute (H : NativePiHistory D Γ anchor out)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) out out') :
    NativePiHistory D Γ anchor out' := by
  obtain ⟨A, B, u, v, hA, hB, RA, RP⟩ := H
  exact ⟨A, B, u, v, hA, hB, RA, RP.trans R⟩

/-- A selected literal Pi exposes a forward domain path from the original
anchor, even when its stored type history passed through arbitrary wrappers. -/
theorem NativePiHistory.domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : NativePiHistory D Γ anchor (.forallE X Y)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) anchor X := by
  obtain ⟨A, B, _, _, hA, hB, RA, RP⟩ := H
  obtain ⟨_, _, _, _, _, _, RX, _⟩ :=
    proofErase_static_structure_union_pi_components heq hs hΓ hA hB RP
  exact RA.trans RX

/-- Each frame stores two independent histories: its inner lambda payload,
and, for an identity frame, the Pi origin of the annotation selected when the
frame was created. No recovery of the current argument at that annotation is
required. Constant frames retain ordinary lower-body typing explicitly. -/
inductive LambdaWrapperHistory (D : PureObservation.Definitions) (Γ : List VExpr)
    (anchor : ProofShape) : VExpr → Prop where
  | payload : env.HasType univs Γ A (.sort u) → env.HasType univs (A :: Γ) b B →
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        anchor (proofErase Γ A) → LambdaWrapperHistory D Γ anchor (.lam A b)
  | constant : env.HasType univs Γ e T → env.HasType univs Γ x A →
      LambdaWrapperHistory D Γ anchor e →
      LambdaWrapperHistory D Γ anchor (.app (.lam A e.lift) x)
  | identity : env.HasType univs Γ e Q → NativePiHistory D Γ anchor (proofErase Γ Q) →
      LambdaWrapperHistory D Γ anchor e →
      LambdaWrapperHistory D Γ anchor (.app (.lam Q (.bvar 0)) e)

/-- Every native output of a historical frame has a typed Pi origin at its
anchor. The identity case reads the old annotation, and the constant case
recovers the lower body. Neither case substitutes a native argument certificate. -/
theorem LambdaWrapperHistory.native_origin
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : LambdaWrapperHistory D Γ anchor e)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) out) : NativePiHistory D Γ anchor out := by
  induction H generalizing out with
  | @payload A u b B hA hb RA =>
    have hn : ¬ IsProof Γ (.lam A b) := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
    rw [show proofErase Γ (.lam A b) = .lam _ _ from if_neg hn] at RN
    obtain ⟨C, RC, RP⟩ := RN.lam_compute
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨C', hbC, EC⟩ := proofErase_scoped_typeRecovery_replay
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓA hb
      (by simpa only [proofEraseCtx] using RC)
    obtain ⟨v, hC⟩ := hbC.isType henv hΓA
    exact ⟨A, C', u, v, hA, hC, RA, by simpa only [EC] using RP⟩
  | constant ht hx _ ih =>
    exact ih (static_structure_constant_beta_native_recovery heq hs hΓ ht hx RN)
  | identity ht HQ _ _ =>
    exact HQ.compute (static_structure_identity_native_origin heq hs hΓ ht RN)

/-- The stored histories read every later native eta domain from the initial
anchor; the currently wrapped payload need not recover the stored annotation. -/
theorem LambdaWrapperHistory.native_domain
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : LambdaWrapperHistory D Γ anchor e)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (.forallE X Y)) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ) anchor X :=
  (H.native_origin heq hs hΓ RN).domain heq hs hΓ

/-- Actual native recovery at frame creation supplies its historical
annotation certificate. The annotation need not be a literal Pi. -/
theorem LambdaWrapperHistory.native_identity
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : LambdaWrapperHistory D Γ anchor e)
    (ht : env.HasType univs Γ e Q)
    (RN : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ e) (proofErase Γ Q)) :
    LambdaWrapperHistory D Γ anchor (.app (.lam Q (.bvar 0)) e) :=
  .identity ht (H.native_origin heq hs hΓ RN) H

/-- A literal identity frame exposes its stored annotation origin separately
from its current argument history. A constant frame cannot have this syntax. -/
theorem LambdaWrapperHistory.identity_inv
    (H : LambdaWrapperHistory D Γ anchor (.app (.lam Q (.bvar 0)) e))
    : env.HasType univs Γ e Q ∧ NativePiHistory D Γ anchor (proofErase Γ Q) ∧
      LambdaWrapperHistory D Γ anchor e := by
  generalize HE : VExpr.app (.lam Q (.bvar 0)) e = source at H
  cases H with
  | payload => cases HE
  | @constant f T x A _ _ _ =>
    cases f <;> simp [VExpr.lift, VExpr.liftN, liftVar] at HE
    omega
  | identity ht HQ H => cases HE; exact ⟨ht, HQ, H⟩

/-- Replacing a frame's argument preserves the annotation's old history.
The new argument needs its payload history and ordinary typing only, not exact
native recovery at the old annotation. This isolates the useful provenance
information that the exact-cut development relation cannot retain universally. -/
theorem LambdaWrapperHistory.identity_argument
    (H : LambdaWrapperHistory D Γ anchor (.app (.lam Q (.bvar 0)) e))
    (ht' : env.HasType univs Γ e' Q) (H' : LambdaWrapperHistory D Γ anchor e') :
    LambdaWrapperHistory D Γ anchor (.app (.lam Q (.bvar 0)) e') :=
  .identity ht' H.identity_inv.2.1 H'

/-- Arbitrary computation of an identity control function's annotation
appends to the stored history. The actual new annotation is reconstructed from
the computation; no native recovery of the current argument is needed. -/
theorem LambdaWrapperHistory.identity_annotation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (H : LambdaWrapperHistory D Γ anchor (.app (.lam Q (.bvar 0)) e))
    (RQ : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ Q) out) :
    ∃ Q', proofErase Γ Q' = out ∧
      LambdaWrapperHistory D Γ anchor (.app (.lam Q' (.bvar 0)) e) := by
  obtain ⟨ht, HQ, HP⟩ := H.identity_inv
  obtain ⟨u, hQ⟩ := ht.isType henv hΓ
  obtain ⟨Q', HE, EQ⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ hQ rfl rfl RQ
  exact ⟨Q', EQ, .identity (HE.defeq ht) (EQ ▸ HQ.compute RQ) HP⟩

/-- Contracting a literal wrapper preserves its historical payload even if
the current argument no longer recovers the stored identity annotation. This
root-cut law asks for no native cut certificate. -/
theorem LambdaWrapperHistory.root_beta
    (H : LambdaWrapperHistory D Γ anchor (.app (.lam A b) x)) :
    LambdaWrapperHistory D Γ anchor (b.inst x) := by
  generalize HE : VExpr.app (.lam A b) x = source at H
  cases H with
  | payload => cases HE
  | constant _ _ H => cases HE; simpa only [VExpr.inst_lift] using H
  | identity _ _ H => cases HE; simpa only [VExpr.inst, VExpr.instVar_zero] using H

/-- Literal wrapper contraction exposes an actual lambda whose domain is
reached from the anchor. This is a finite beta path, with no normalization or
common-reduct premise. It deliberately does not assert a body history. -/
theorem LambdaWrapperHistory.readout (H : LambdaWrapperHistory D Γ anchor e) :
    ∃ A b, VExpr.BetaRed e (.lam A b) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        anchor (proofErase Γ A) := by
  induction H with
  | payload _ _ RA => exact ⟨_, _, .refl, RA⟩
  | @constant e T x A _ _ _ ih =>
    obtain ⟨L, b, R, RA⟩ := ih
    have RB : VExpr.BetaRed (.app (.lam A e.lift) x) e := by
      simpa only [VExpr.inst_lift] using (VExpr.BetaRed.beta (A := A) (b := e.lift) (a := x))
    exact ⟨L, b, RB.trans R, RA⟩
  | @identity e Q _ _ _ ih =>
    obtain ⟨L, b, R, RA⟩ := ih
    have RB : VExpr.BetaRed (.app (.lam Q (.bvar 0)) e) e := by
      simpa only [VExpr.inst, VExpr.instVar_zero] using
        (VExpr.BetaRed.beta (A := Q) (b := .bvar 0) (a := e))
    exact ⟨L, b, RB.trans R, RA⟩

/-- Root native eta reconstructs a new literal payload with a forward domain
history. This applies at every guard depth and through all nested stored frames,
without asking the frames' current arguments to recover old annotations. -/
theorem LambdaWrapperHistory.native_eta
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (H : LambdaWrapperHistory D Γ anchor e)
    (ht : env.HasType univs Γ e T)
    (RE : NativeEtaExpansion (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ e) out) :
    ∃ e', env.IsDefEq univs Γ e e' T ∧ proofErase Γ e' = out ∧
      LambdaWrapperHistory D Γ anchor e' := by
  cases RE with
  | intro RN SD =>
    obtain ⟨A, B, he, hA, EA, EB⟩ := proofErase_native_eta_domain_realize
      (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht RN SD
    have HE := IsDefEq.eta he
    obtain ⟨_, _, hb⟩ := HE.hasType.1.lam_inv henv hΓ
    have hn : ¬ IsProof Γ e := fun hp => RN.ne_proof (proofErase_eq_proof.2 hp)
    refine ⟨_, HE.symm.toU.of_l henv hΓ ht, ?_, .payload hA hb ?_⟩
    · rw [proofErase_nativeEtaExpansion hΓ hA he hn, EA]
    · rw [EA]
      exact H.native_domain heq hs hΓ RN

end Lean4Lean.VEnv.Strengthening
