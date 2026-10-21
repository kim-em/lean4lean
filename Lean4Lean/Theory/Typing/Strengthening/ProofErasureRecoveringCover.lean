import Lean4Lean.Theory.Typing.Strengthening.ProofErasureIdentityRecoveryCover

/-! # Recoverable expansions of dependent simultaneous substitutions

Build the images from the oldest variable outward. Each new identity wrapper
uses the domain already instantiated by the expanded older images. Forward
substitution converts the original image to that domain. All wrappers beta
contract to the original images; exact recovery is asserted before contraction.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem cover (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) :
    ∃ ρ, Ctx.SubstEq env univs Γ₀ ρ σ Γ ∧
      (∀ i, ProofShape.BetaRed (proofErase Γ₀ (ρ i)) (proofErase Γ₀ (σ i))) ∧
      ∀ {i A}, Lookup Γ i A → ¬ IsProof Γ (.bvar i) →
        ScopedTypeRecovery Step (proofEraseCtx Γ₀) (proofErase Γ₀ (ρ i))
          (proofErase Γ₀ (A.subst ρ)) := by
  induction Γ generalizing σ with
  | nil => exact ⟨σ, .nil, fun _ => .refl, fun H => nomatch H⟩
  | cons A Γ ih =>
    cases W with
    | cons WT hA hx =>
      obtain ⟨ρ, WR, RB, HR⟩ := ih WT
      have HA := hA.substDF henv.orderedStrong WT.wf hΓ₀ WR
      have hx' := HA.symm.defeq hx.hasType.1
      obtain ⟨hy, HE, RY, HY⟩ := proofErase_identity_recovery_cover (Step := Step) hΓ₀ hx'
      let y := VExpr.app (.lam (A.subst ρ) (.bvar 0)) σ.head
      have hy : env.HasType univs Γ₀ y (A.subst ρ) := hy
      have WC : Ctx.SubstEq env univs Γ₀ (ρ.cons y) σ (A :: Γ) := .cons WR hA HE
      refine ⟨ρ.cons y, WC, ?_, ?_⟩
      · intro i
        cases i with
        | zero => exact RY
        | succ i => exact RB i
      · intro i T hl hn
        cases hl with
        | zero =>
          have hny : ¬ IsProof Γ₀ y := by
            intro hp
            exact hn ((isProof_subst hΓ₀ WC.left (HasType.bvar Lookup.zero)).1 hp)
          simpa only [VExpr.lift_subst, VExpr.Subst.cons_tail, VExpr.Subst.cons] using HY hny
        | @succ _ i T _ hl =>
          have hn' : ¬ IsProof Γ (.bvar i) :=
            fun hp => hn (IsProof.lift' (Ctx.Lift'.skip .refl) hp)
          simpa only [VExpr.lift_subst, VExpr.Subst.cons_tail, VExpr.Subst.cons] using HR hl hn'

/-- Every typed simultaneous substitution has a definitionally equal expansion
whose non-proof images recover their exact substituted oracle types. Each
expanded image beta contracts to the original image. No canonical Eq, recovery
completeness, or preservation of recovery by contraction is assumed. -/
theorem proofErase_recovering_substitution_cover
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ) :
    ∃ ρ, Ctx.SubstEq env univs Γ₀ ρ σ Γ ∧
      (∀ i, ProofShape.BetaRed (proofErase Γ₀ (ρ i)) (proofErase Γ₀ (σ i))) ∧
      RecoveringSubstitution Step (proofEraseCtx Γ) (proofEraseCtx Γ₀)
        (fun i => proofErase Γ₀ (ρ i)) := by
  obtain ⟨ρ, WR, RB, HR⟩ := cover (Step := Step) hΓ₀ W
  refine ⟨ρ, WR, RB, RecoveringSubstitution.of_typed hΓ₀ WR.left (fun _ _ => rfl) ?_⟩
  intro i A hl hn
  obtain ⟨u, hA⟩ := (show env.HasType univs Γ (.bvar i) A from .bvar hl).isType henv W.wf
  rw [proofEraseCtx_oracle, erasedTypeOracle_valid W.wf hl,
    ← proofErase_subst_with hΓ₀ WR.left hA (show ErasedSubstAgreement Γ Γ₀ ρ
      (fun i => proofErase Γ₀ (ρ i)) from fun _ _ => rfl)]
  exact HR hl hn

end Lean4Lean.VEnv.Strengthening
