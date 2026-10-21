import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointRecoverableSupply

/-! # Selected native recovery through full-union argument computation

Original argument recoveries suffice even when computation destroys exact
recovery of the output arguments. The native residual computes to every
selected recovery, including conversions between successive applications.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
variable [Params]

private theorem computed_app_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hB : env.HasType univs (A :: Γ) B (.sort v)) (ha : env.HasType univs Γ a A)
    (HR : ¬ IsProof Γ a → ScopedTypeRecovery (ErasedJointUnion D)
      (proofEraseCtx Γ) (proofErase Γ a) (proofErase Γ A))
    (HN : ∀ {T}, ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) f T →
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ (.forallE A B)) T)
    (RA : ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ a) argOut)
    (R : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (.app f argOut) out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ (B.inst a)) out := by
  generalize EΔ : proofEraseCtx Γ = Δ at R
  generalize E : ProofShape.app f argOut = e at R
  induction R with
  | app RF =>
    cases E
    rw [← EΔ] at RF ⊢
    exact proofErase_joint_union_computed_pi_inst heq hs hΓ hA hB ha HR (HN RF) RA
  | convert _ H ih => exact (ih EΔ E).trans H
  | bvar | sort | const | lam | forallE | proj => cases E

/-- Every selected type of a computed prefix is reachable from the original
native residual in the union. Each original argument retains its own exact
recovery; no recovery premise is imposed on any computed image. -/
theorem proofErase_joint_union_computed_telescope_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs)) (hT : env.HasType univs Γ T (.sort u))
    (HW : RecoverableNativeWalk D Γ T args residual)
    (HN : ∀ {U}, ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) f U →
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ T) U)
    (HA : List.Forall₂ (ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) args')
    (R : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ) (ProofShape.mkApps f args') out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ residual) out := by
  induction HW generalizing f u args' with
  | nil => cases HA; exact HN R
  | cons ha HR HW ih =>
    cases HA with | cons RA HA =>
    obtain ⟨⟨v, hA⟩, w, hB⟩ := hT.forallE_inv henv
    exact ih (hB.instN henv Ctx.InstN.zero ha)
      (fun R => computed_app_native heq hs hΓ hA hB ha HR HN RA R) HA R

/-- A constant's original recoverable telescope walk controls every selected
type of its computed argument spine. The declaration may itself compute; its
native residual remains a common ancestor of all selected recovery outputs. -/
theorem proofErase_joint_union_computed_const_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : RecoverableNativeWalk D Γ (ci.type.instL ls) args residual)
    (HA : List.Forall₂ (ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) args')
    (R : ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ)
      (ProofShape.mkApps (.const c ls) args') out) :
    ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ residual) out := by
  have hf := HasType.const (Γ := []) hc hw hl
  obtain ⟨u, hT⟩ := hf.isType henv (by trivial)
  apply proofErase_joint_union_computed_telescope_native heq hs hΓ
    (hT.weak0 henv.ordered) HW ?_ HA R
  intro U H
  rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ]
  exact H.const_compute hc

/-- Two constant spines supplied by recoverable native walks and joined
arguments have one recovered residual with paths from both original residuals.
The comparison is constructed in the full union, without global confluence,
primitive substitution closure or recovery of the shared arguments. -/
theorem proofErase_joint_union_joined_const_native
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓ : OnCtx Γ (env.IsType univs))
    (hc : env.constants c = some ci) (hw : ∀ l ∈ ls, l.WF univs)
    (hl : ls.length = ci.uvars)
    (HW : RecoverableNativeWalk D Γ (ci.type.instL ls) args T)
    (HW' : RecoverableNativeWalk D Γ (ci.type.instL ls) args' U)
    (HA : List.Forall₂ (ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ))
      (args.map (proofErase Γ)) sharedArgs)
    (HA' : List.Forall₂ (ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ))
      (args'.map (proofErase Γ)) sharedArgs) :
    ∃ out, ScopedTypeRecovery (ErasedJointUnion D) (proofEraseCtx Γ)
        (ProofShape.mkApps (.const c ls) sharedArgs) out ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ T) out ∧
      ScopedCompute (ErasedJointUnion D) (proofEraseCtx Γ) (proofErase Γ U) out ∧
      JointCompare (ErasedJointUnion D) (proofEraseCtx Γ) mode (proofErase Γ T) (proofErase Γ U) := by
  have hf := HasType.const (Γ := []) hc hw hl
  obtain ⟨u, hT⟩ := hf.isType henv (by trivial)
  obtain ⟨out, HS, R, R'⟩ := proofErase_joint_union_native_residuals_join heq hs hΓ
    (hT.weak0 henv.ordered) HW HW' HA HA'
  rw [proofErase_closed_context ((henv.ordered.closedC hc).instL) hT hΓ] at HS
  exact ⟨out, (ScopedTypeRecovery.const hc hw hl).supply HS, R, R', .compute R R' (.leaf .refl)⟩

end Lean4Lean.VEnv.Strengthening
