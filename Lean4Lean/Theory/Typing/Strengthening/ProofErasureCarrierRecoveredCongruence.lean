import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierRecoveredCompare

/-! # Heterogeneous template instantiation with recovered carrier comparison

Compatible syntax can use the new inferred image comparison, including at a
variable occurrence. This supports nonjoining carrier-related images. It is
congruence of one shared typed template, not transport of arbitrary comparison
certificates or closure of the old computed checker.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- Interpreted renaming preserves every new comparison certificate, including
its two selected native recoveries and explicit carrier guard. -/
theorem ProofShape.CarrierRecoveredCompare.rename
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (H : CarrierRecoveredCompare Step Δ mode a b) (W : ContextRenaming Δ Δ' τ) :
    CarrierRecoveredCompare Target Δ' mode (a.subst τ) (b.subst τ) := by
  induction H generalizing Δ' τ with
  | base H => exact .base (H.rename hrename W)
  | recovered RA RB H => exact .recovered (RA.rename hrename W) (RB.rename hrename W) (H.rename hrename W)
  | app HF HX ihf ihx => exact .app (ihf W) (ihx W)
  | proj H ih => exact .proj (ih W)
  | lam HA HB ihA ihB => exact .lam (ihA W) (ihB W.cons)
  | forallE HA HB ihA ihB => exact .forallE (ihA W) (ihB W.cons)
  | compute RA RB H ih => exact .compute (RA.rename hrename W) (RB.rename hrename W) (ih W)
  | symm H ih => exact .symm (ih W)

/-- Pointwise inferred image comparison extends through any typed template.
Only the left image map needs an actual typed interpretation to build the
binder contexts used by renaming. No computation join is assumed. -/
theorem proofErase_carrier_recovered_subst_images
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (he : env.HasType univs Γ e T) (E : ErasedSubstAgreement Γ Γ₀ σ ρ)
    (H : ∀ i, CarrierRecoveredCompare Step (proofEraseCtx Γ₀) false (ρ i) (τ i)) :
    CarrierRecoveredCompare Step (proofEraseCtx Γ₀) false
      ((proofErase Γ e).subst ρ) ((proofErase Γ e).subst τ) := by
  classical
  induction e generalizing Γ Γ₀ σ ρ τ T with
  | bvar i =>
    by_cases hp : IsProof Γ (.bvar i)
    · rw [proofErase_eq_proof.2 hp]; exact .base (.leaf .refl)
    simpa only [proofErase, if_neg hp, ProofShape.subst] using H i
  | sort u => simp only [proofErase]; split <;> exact .base (.leaf .refl)
  | const c ls => simp only [proofErase]; split <;> exact .base (.leaf .refl)
  | app f a ihf iha =>
    by_cases hp : IsProof Γ (.app f a)
    · rw [proofErase_eq_proof.2 hp]; exact .base (.leaf .refl)
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv W.wf
    simp only [proofErase, if_neg hp, ProofShape.subst]
    exact .app (ihf hΓ₀ W hf E H) (iha hΓ₀ W ha E H).common
  | proj s i m ih =>
    by_cases hp : IsProof Γ (.proj s i m)
    · rw [proofErase_eq_proof.2 hp]; exact .base (.leaf .refl)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv W.wf
    simp only [proofErase, if_neg hp, ProofShape.subst]
    exact .proj (ih hΓ₀ W hm.hasType.2 E H)
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [proofErase]
    split
    · exact .base (.leaf .refl)
    obtain ⟨⟨u, hA⟩, _, hb⟩ := by
      first | exact he.lam_inv henv W.wf | exact he.forallE_inv henv
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have hΓA' : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hA'⟩
    have HH : ∀ i, CarrierRecoveredCompare Step (proofEraseCtx (A.subst σ :: Γ₀)) false
        (ρ.lift i) (τ.lift i) := by
      intro i
      cases i with
      | zero => exact .base (.leaf .refl)
      | succ i =>
        have HR := (H i).rename hrename (ContextRenaming.of_liftN hΓ₀ hΓA' Ctx.LiftN.one)
        simpa only [subst_bvar_liftN, ProofShape.Subst.lift] using HR
    have HB := ihb hΓA' (W.lift henv.ordered hA) hb (E.lift hΓ₀ W hA) HH
    rw [show proofEraseCtx (A.subst σ :: Γ₀) =
      (proofErase Γ A).subst ρ :: proofEraseCtx Γ₀ from
      congrArg (· :: proofEraseCtx Γ₀) (proofErase_subst_with hΓ₀ W hA E)] at HB
    simp only [ProofShape.subst]
    first | exact .lam (ihA hΓ₀ W hA E H) HB | exact .forallE (ihA hΓ₀ W hA E H) HB

/-- Distinct related arguments instantiate the same typed body in inferred
mode. The conclusion uses the enlarged comparison, including its recovered
carrier rule; it is not asserted in the original computed checker. -/
theorem proofErase_carrier_recovered_inst_images
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : CarrierRecoveredCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y)) :
    CarrierRecoveredCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (b.inst x)) (proofErase Γ (b.inst y)) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have HC := proofErase_carrier_recovered_subst_images hrename hΓA.1 W hb
    (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one (proofErase Γ y)) (fun i => by
      cases i with
      | zero => exact H
      | succ i => exact .base (.leaf .refl))
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb, proofErase_instN hΓA hy Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HC

/-- In particular, exact shared type recovery plus a carrier guard suffices
for heterogeneous instantiation of every typed body in the computed union. -/
theorem proofErase_computed_union_inst_shared_recovered_carrier
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (RX : ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ) (proofErase Γ x) U)
    (RY : ScopedTypeRecovery (ErasedComputedJointUnion D) (proofEraseCtx Γ) (proofErase Γ y) U)
    (H : ComputedJointCarrierGuard (ErasedComputedJointUnion D) (proofEraseCtx Γ) U
      (proofErase Γ x) (proofErase Γ y)) :
    CarrierRecoveredCompare (ErasedComputedJointUnion D) (proofEraseCtx Γ) false
      (proofErase Γ (b.inst x)) (proofErase Γ (b.inst y)) :=
  proofErase_carrier_recovered_inst_images (erased_computed_joint_union_rename heq hs)
    hΓA hb hx hy (.recovered RX RY H)

end Lean4Lean.VEnv.Strengthening
