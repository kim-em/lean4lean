import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedCompare

/-! # Heterogeneous template instantiation with recovered carrier comparison

Compatible syntax can use the new inferred image comparison, including recursive comparison of native types at a variable occurrence. This supports nonjoining carrier-related images. It is
congruence of one shared typed template, not transport of arbitrary comparison
certificates or closure of the old computed checker.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private subst_bvar_liftN from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRenaming
variable [Params]

/-- The old computed checker embeds through the exact-recovery checker. -/
theorem ProofShape.CarrierAlignedCompare.computed (H : ComputedJointCompare Step Δ mode a b) :
    CarrierAlignedCompare Step Δ mode a b := .base (.base H)

/-- Primitive inclusion retains both native outputs and their recursive comparison. -/
theorem ProofShape.CarrierAlignedCompare.mono
    (hstep : ∀ {Δ a b}, Step Δ a b → Target Δ a b)
    (H : CarrierAlignedCompare Step Δ mode a b) : CarrierAlignedCompare Target Δ mode a b := by
  induction H with
  | base H => exact .base (H.mono hstep)
  | commonCarrier RA H => exact .commonCarrier (RA.mono hstep) (H.mono hstep)
  | aligned RA RB HT H ihT => exact .aligned (RA.mono hstep) (RB.mono hstep) ihT (H.mono hstep)
  | app _ _ ihf ihx => exact .app ihf ihx
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | compute RA RB _ ih => exact .compute (RA.mono hstep) (RB.mono hstep) ih
  | symm _ ih => exact .symm ih

/-- Interpreted renaming preserves every new comparison certificate, including
its selected native recoveries, recursive type comparison and carrier guard. -/
theorem ProofShape.CarrierAlignedCompare.rename
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Target Δ' (a.subst τ) (b.subst τ))
    (H : CarrierAlignedCompare Step Δ mode a b) (W : ContextRenaming Δ Δ' τ) :
    CarrierAlignedCompare Target Δ' mode (a.subst τ) (b.subst τ) := by
  induction H generalizing Δ' τ with
  | base H => exact .base (H.rename hrename W)
  | commonCarrier RA H => exact .commonCarrier (RA.rename hrename W) (H.rename hrename W)
  | aligned RA RB HT H ihT =>
    exact .aligned (RA.rename hrename W) (RB.rename hrename W) (ihT W) (H.rename hrename W)
  | app HF HX ihf ihx => exact .app (ihf W) (ihx W)
  | proj H ih => exact .proj (ih W)
  | lam HA HB ihA ihB => exact .lam (ihA W) (ihB W.cons)
  | forallE HA HB ihA ihB => exact .forallE (ihA W) (ihB W.cons)
  | compute RA RB H ih => exact .compute (RA.rename hrename W) (RB.rename hrename W) (ih W)
  | symm H ih => exact .symm (ih W)

/-- Pointwise inferred image comparison extends through any typed template.
Only the left image map needs an actual typed interpretation to build the
binder contexts used by renaming. No computation join is assumed. -/
theorem proofErase_carrier_aligned_subst_images
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (he : env.HasType univs Γ e T) (E : ErasedSubstAgreement Γ Γ₀ σ ρ)
    (H : ∀ i, CarrierAlignedCompare Step (proofEraseCtx Γ₀) false (ρ i) (τ i)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ₀) false
      ((proofErase Γ e).subst ρ) ((proofErase Γ e).subst τ) := by
  classical
  induction e generalizing Γ Γ₀ σ ρ τ T with
  | bvar i =>
    by_cases hp : IsProof Γ (.bvar i)
    · rw [proofErase_eq_proof.2 hp]; exact .computed (.leaf .refl)
    simpa only [proofErase, if_neg hp, ProofShape.subst] using H i
  | sort u => simp only [proofErase]; split <;> exact .computed (.leaf .refl)
  | const c ls => simp only [proofErase]; split <;> exact .computed (.leaf .refl)
  | app f a ihf iha =>
    by_cases hp : IsProof Γ (.app f a)
    · rw [proofErase_eq_proof.2 hp]; exact .computed (.leaf .refl)
    obtain ⟨_, _, hf, ha⟩ := he.app_inv henv W.wf
    simp only [proofErase, if_neg hp, ProofShape.subst]
    exact .app (ihf hΓ₀ W hf E H) (iha hΓ₀ W ha E H).common
  | proj s i m ih =>
    by_cases hp : IsProof Γ (.proj s i m)
    · rw [proofErase_eq_proof.2 hp]; exact .computed (.leaf .refl)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := he.proj_inv henv W.wf
    simp only [proofErase, if_neg hp, ProofShape.subst]
    exact .proj (ih hΓ₀ W hm.hasType.2 E H)
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [proofErase]
    split
    · exact .computed (.leaf .refl)
    obtain ⟨⟨u, hA⟩, _, hb⟩ := by
      first | exact he.lam_inv henv W.wf | exact he.forallE_inv henv
    have hA' := hA.subst henv.orderedStrong W hΓ₀
    have hΓA' : OnCtx (A.subst σ :: Γ₀) (env.IsType univs) := ⟨hΓ₀, u, hA'⟩
    have HH : ∀ i, CarrierAlignedCompare Step (proofEraseCtx (A.subst σ :: Γ₀)) false
        (ρ.lift i) (τ.lift i) := by
      intro i
      cases i with
      | zero => exact .computed (.leaf .refl)
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
theorem proofErase_carrier_aligned_inst_images
    (hrename : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextRenaming Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (H : CarrierAlignedCompare Step (proofEraseCtx Γ) false (proofErase Γ x) (proofErase Γ y)) :
    CarrierAlignedCompare Step (proofEraseCtx Γ) false
      (proofErase Γ (b.inst x)) (proofErase Γ (b.inst y)) := by
  have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have HC := proofErase_carrier_aligned_subst_images hrename hΓA.1 W hb
    (erasedSubstAgreement_one hΓA hx)
    (τ := ProofShape.Subst.one (proofErase Γ y)) (fun i => by
      cases i with
      | zero => exact H
      | succ i => exact .computed (.leaf .refl))
  rw [proofErase_instN hΓA hx Ctx.InstN.zero hb, proofErase_instN hΓA hy Ctx.InstN.zero hb]
  simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN] using HC

end Lean4Lean.VEnv.Strengthening
