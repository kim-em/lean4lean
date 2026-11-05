import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputationCore

/-! # Typed computation chains from common erased reducts

Replay realizes a raw endpoint at the original assignment. Two source-typed
paths to the same raw endpoint then give a typed chain by erasure reflection.
No confluence or ordinary-equality completeness premise is needed for this step.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params] {D : PureObservation.Definitions}

/-- Realize an arbitrary raw computation endpoint by an actual term, retaining
both its exact erasure and a typed chain from the original source. -/
theorem TypedComputationEq.realize_compute
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (ht : env.HasType univs Γ a A)
    (R : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ a) out) :
    ∃ b, TypedComputationEq D Γ a b A ∧ proofErase Γ b = out := by
  obtain ⟨b, HE, EB⟩ := proofErase_scoped_compute_realize
    (erased_static_structure_eta_expansion_union_descent heq hs) hΓ ht rfl rfl R
  exact ⟨b, .step HE (EB ▸ R), EB⟩

/-- Two terms at one actual assignment which compute to a common erased
endpoint have a typed chain. Ordinary equality of the sources is derived,
not assumed; the raw common endpoint need not carry an input typing witness. -/
theorem TypedComputationEq.of_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (RA : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ a) out)
    (RB : ScopedCompute (ErasedStaticStructureEtaExpansionUnion D) (proofEraseCtx Γ)
      (proofErase Γ b) out) : TypedComputationEq D Γ a b A := by
  obtain ⟨c, HC, EC⟩ := TypedComputationEq.realize_compute heq hs hΓ ha RA
  obtain ⟨d, HD, ED⟩ := TypedComputationEq.realize_compute heq hs hΓ hb RB
  have E : proofErase Γ c = proofErase Γ d := EC.trans ED.symm
  obtain ⟨u, hA⟩ := ha.isType henv hΓ
  obtain ⟨_, HN⟩ := (proofErase_reflect hΓ HC.defeq.hasType.2 HD.defeq.hasType.2 E).1 ⟨.sort u, hA⟩
  have Hcd := (HN.defeq hΓ).of_l henv hΓ HC.defeq.hasType.2
  exact HC.trans ((TypedComputationEq.of_erasure_eq Hcd E).trans HD.symm)

end Lean4Lean.VEnv.Strengthening
