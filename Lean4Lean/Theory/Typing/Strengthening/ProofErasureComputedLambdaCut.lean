import Lean4Lean.Theory.Typing.Strengthening.ProofErasureLambdaDomainReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureNativeHeadBeta
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCommonNativeBinder

/-! # Native cuts exposed by computation of a lambda

An unchanged argument that recovers the original written domain also recovers
every domain exposed by computation of the function. The domain history supplies
the required conversion; it is not a new coverage premise. A finite beta readout
therefore ends in a certified application cut, even if its preceding control
beta steps have no native cut certificates.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params] {D : PureObservation.Definitions}

/-- Computing the function to a literal lambda supplies the exact certificate
for applying an unchanged native argument at the newly exposed domain. Only the
original argument certificate is assumed. No body-origin or fork join is used. -/
theorem computed_lambda_argument_recovery
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b)) (hm : ¬ IsProof Γ (.lam C d))
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam C d)))
    (RX : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      x (proofErase Γ A)) :
    ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      x (proofErase Γ C) := by
  rw [show proofErase Γ (.lam C d) = .lam _ _ from if_neg hm] at R
  exact RX.convert (proofErase_static_structure_lambda_domain_compute heq hs hΓ hA hb hn R)

/-- At any literal computed endpoint, the final application beta step is a
NativeHeadBeta cut. Computation of the function may use all expansion stages;
its intermediate cuts are not asserted to be certified. -/
theorem computed_lambda_native_cut
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b))
    (hC : env.HasType univs Γ C (.sort v)) (hd : env.HasType univs (C :: Γ) d E)
    (hm : ¬ IsProof Γ (.lam C d)) (hx : env.HasType univs Γ x C)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam C d)))
    (RX : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A)) :
    NativeHeadBeta D Γ (.app (.lam C d) x) (d.inst x) :=
  .beta hC hd hx (fun hp => computed_lambda_argument_recovery heq hs hΓ hA hb hn hm R (RX hp))

/-- Every computed function endpoint has a finite beta readout ending in an
actual typed lambda and a certified application cut for an unchanged argument
native at the original domain. The prefix is beta only, not certified head beta.
This distinction matters: control reductions can lose exact native types. -/
theorem computed_lambda_application_readout
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b)) (hx : env.HasType univs Γ x A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) out)
    (RX : ¬ IsProof Γ x → ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D)
      (proofEraseCtx Γ) (proofErase Γ x) (proofErase Γ A)) :
    ∃ C d v E, env.HasType univs Γ C (.sort v) ∧ env.HasType univs (C :: Γ) d E ∧
      env.HasType univs Γ x C ∧
      env.IsDefEq univs Γ (.lam A b) (.lam C d) (.forallE A B) ∧
      ProofShape.BetaRed out (proofErase Γ (.lam C d)) ∧
      ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
        (proofErase Γ A) (proofErase Γ C) ∧
      NativeHeadBeta D Γ (.app (.lam C d) x) (d.inst x) := by
  obtain ⟨C₀, _, d₀, _, RA, Rβ⟩ :=
    proofErase_static_structure_lambda_domain_readout heq hs hΓ hA hb hn R
  obtain ⟨f, HF, Ef⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs)
    hΓ (HasType.lam hA hb) rfl rfl (R.trans (.beta Rβ))
  obtain ⟨C, d, rfl, hm, EC, Ed⟩ := erase_lam_inv Ef
  obtain ⟨⟨v, hC⟩, E, hd⟩ := HF.hasType.2.lam_inv henv hΓ
  have hxC := argument_at_displayed_domain hΓ HF.hasType.2 (HasType.lam hC hd) hx
  have Rβ' : ProofShape.BetaRed out (proofErase Γ (.lam C d)) := Ef ▸ Rβ
  have RA' : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ C) := EC ▸ RA
  exact ⟨C, d, v, E, hC, hd, hxC, HF, Rβ', RA',
    .beta hC hd hxC (fun hp => (RX hp).convert RA')⟩

/-- Once the exposed cut is selected, arbitrary subsequent computation of its
body can be instantiated exactly. The unchanged argument's original certificate
suffices, because the computed function supplies the new domain path. This does
not compare that body with the initial lambda body. -/
theorem computed_lambda_body_instantiation
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) (hb : env.HasType univs (A :: Γ) b B)
    (hn : ¬ IsProof Γ (.lam A b)) (hm : ¬ IsProof Γ (.lam C d))
    (hx : env.HasType univs Γ x C) (hd : env.HasType univs (C :: Γ) d E)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (.lam A b)) (proofErase Γ (.lam C d)))
    (RX : ScopedTypeRecovery (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ x) (proofErase Γ A))
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx (C :: Γ))
      (proofErase (C :: Γ) d) out) :
    ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ (d.inst x)) (out.inst (proofErase Γ x)) :=
  static_structure_union_compute_inst_native heq hs hΓ hx
    (computed_lambda_argument_recovery heq hs hΓ hA hb hn hm R RX) hd RB

end Lean4Lean.VEnv.Strengthening
