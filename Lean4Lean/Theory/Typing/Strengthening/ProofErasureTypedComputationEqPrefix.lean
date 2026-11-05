import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationDeclarations

/-! # Canonical equality prefixes from computation chains

Move the final endpoint along its typed chain until the prefix check is
reflexive. The resulting guarded primitive computes directly. Ordinary lambda
reannotation then restores the requested proof domain. This avoids converting
an arbitrary data chain into a raw common reduct or native carrier certificate.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
open private equality_simAt from Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedReplay
variable [Params] {D : PureObservation.Definitions}

/-- A canonical Eq prefix with literally equal endpoints computes at stage
one: its carrier comparison is reflexive, regardless of the carrier's shape. -/
theorem TypedComputationEq.eq_prefix_refl
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m a) T) :
    TypedComputationEq D Γ (eqRecBeforeMajor v w α a M m a) (.lam (eqApp w α a a) m.lift) T := by
  obtain ⟨_, _, _, ha, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have R := proofErase_computed_joint_prefix_forward heq
    (erased_static_structure_eta_expansion_stage_descent heq hs 0) hΓ ht
    (.carrierChecked (.leaf .refl))
  exact .step (eqRecBeforeMajor_simAt henv heq hΓ ⟨_, ha⟩ T ht)
    (R.mono (fun H => ⟨1, .inr (.inr (.inl H))⟩))

/-- A typed chain of Eq endpoints suffices for prefix computation as a typed
chain. Arbitrary data endpoints are allowed. Neither a common raw reduct nor a
native certificate for either endpoint is required. -/
theorem TypedComputationEq.eq_prefix
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecBeforeMajor v w α a M m b) T)
    (H : TypedComputationEq D Γ a b α) :
    TypedComputationEq D Γ (eqRecBeforeMajor v w α a M m b) (.lam (eqApp w α a b) m.lift) T := by
  obtain ⟨hv, hw, hα, ha, hM, hm, _⟩ := eqRecBeforeMajor_typings henv heq hΓ ⟨_, ht⟩
  have HF := HasType.eqRec4 heq hv hw hα ha hM hm
  have HR : TypedComputationEq D Γ (eqRecBeforeMajor v w α a M m b)
      (eqRecBeforeMajor v w α a M m a) T :=
    (H.symm.app_arg hΓ HF).at_source_type hΓ ht
  have HC := TypedComputationEq.eq_prefix_refl heq hs hΓ HR.defeq.hasType.2
  have hE := HasType.eqApp heq hw hα ha ha
  have HA : env.IsDefEq univs Γ (eqApp w α a a) (eqApp w α a b) (.sort .zero) :=
    SimAt.app henv.orderedStrong hΓ .refl (equality_simAt hΓ H.defeq) _ hE
  obtain ⟨_, B, hb⟩ := HC.defeq.hasType.2.lam_inv henv hΓ
  have HL := TypedComputationEq.lam_ordinary_domain heq hs hΓ HA (TypedComputationEq.refl hb)
  exact (HR.trans HC).trans (HL.at_source_type hΓ HC.defeq.hasType.2)

/-- Applying the computed prefix to any actual proof major yields the minor.
The proof may be opaque and its endpoints arbitrary data related by a chain. -/
theorem TypedComputationEq.eq_rec
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ht : env.HasType univs Γ (eqRecApp v w α a M m b p) T)
    (H : TypedComputationEq D Γ a b α) :
    TypedComputationEq D Γ (eqRecApp v w α a M m b p) m T := by
  obtain ⟨_, _, hprefix, hp⟩ := ht.app_inv henv hΓ
  have R := (TypedComputationEq.eq_prefix (v := v) (w := w) (α := α) (a := a)
    (M := M) (m := m) (b := b) heq hs hΓ hprefix H).app_fn hΓ hp
  have R := R.at_source_type hΓ ht
  exact R.trans (TypedComputationEq.of_beta hΓ R.defeq.hasType.2
    (by simpa only [VExpr.inst_lift] using
      (VExpr.BetaRed.beta (A := eqApp w α a b) (b := m.lift) (a := p))))

end Lean4Lean.VEnv.Strengthening
