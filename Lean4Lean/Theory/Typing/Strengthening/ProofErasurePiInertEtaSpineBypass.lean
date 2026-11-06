import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCountedSpineComponents
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertLambdaCountReadout
import Lean4Lean.Theory.Typing.Strengthening.ProofErasurePiInertEtaBodyResidual

/-! # Bypass eta when its body retains the lifted function and fresh slot

The function portion of the body descends with its exact primitive count.
All pending argument and suffix computations are retained at a common finite
stage. Only typed instantiation of the unchanged eta slot is needed.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape PureObservation
open private typed_spine_head from Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSpineCut
open private erase_app_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

/-- Computation of the lifted function inside an eta body can be replayed
on the short application, retaining every argument and the exact suffix.
The body and outer paths may have different finite guard stages. -/
theorem pi_inert_retained_eta_body_count_bypass
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hguard : ErasedScopedPrimitiveDescent Guard)
    (HT : TypedSource Δ (ProofShape.mkApps f args))
    (RN : ScopedTypeRecovery Guard Δ f (.forallE A B)) (SD : DomainSort Δ A u)
    (RG : ScopedComputeCount (PiInertStage D m) cg (A :: Δ) (f.liftN 1) g)
    (RX : ScopedArgumentsCount (PiInertStage D n) Δ ca args (x' :: xs'))
    (RS : ScopedComputeCount (PiInertStage D n) cs Δ
      (ProofShape.mkApps ((ProofShape.app g (etaArgument u)).inst x') xs') out) :
    ScopedComputeCount (PiInertStage D (max m n)) (cg+ca+cs) Δ (ProofShape.mkApps f args) out := by
  cases RX with
  | cons RX RXS =>
    have HTapp : TypedSource Δ (.app f _) := typed_spine_head HT
    obtain ⟨Γ, e, T, hΓ, rfl, ht, Ee⟩ := HTapp
    obtain ⟨f₀, x₀, rfl, _, Ef, Ex⟩ := erase_app_inv Ee
    obtain ⟨A₀, B₀, hf, hx⟩ := ht.app_inv henv hΓ
    have W : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨A₁, B₁, hf₁, EA, _⟩ := proofErase_scoped_recovered_pi_descend hguard hΓ hΓ W hf
      (by simpa only [ProofShape.liftN_zero, Ef] using RN)
    obtain ⟨_, hPi⟩ := hf₁.isType henv hΓ
    obtain ⟨⟨_, hA⟩, _, _⟩ := hPi.forallE_inv henv
    have hA := (EA ▸ SD).descend hΓ hΓ W hA
    simp only [ProofShape.liftN_zero] at EA
    have hΓA : OnCtx (A₁ :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    obtain ⟨f₁, _, RF, EF⟩ := proofErase_scoped_compute_count_descend
      (pi_inert_stage_rule_descent heq hs) hΓ hΓA Ctx.LiftN.one hf₁
      (congrArg (fun rawA => rawA :: proofEraseCtx Γ) EA)
      (by simpa only [Ef] using RG)
    obtain ⟨x₁, HX, EX⟩ := proofErase_scoped_compute_realize
      (ErasedScopedPrimitiveCertificateDescent.descent (pi_inert_stage_certificate_descent heq hs n))
      hΓ hx rfl Ex RX.forget
    have hxA := argument_at_displayed_domain hΓ hf hf₁ HX.hasType.2
    have EB : (ProofShape.app g (etaArgument u)).inst x' = .app (proofErase Γ f₁) x' := by
      rw [← EF, ← EX]
      simp only [ProofShape.inst, proofErase_eta_argument_inst hΓ hA hxA]
      congr 1
      simp only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.Subst.one,
        ProofShape.lift_subst_cons, ProofShape.subst_id]
    have RF' := (Ef ▸ RF).mono (pi_inert_stage_mono (Nat.le_max_left m n))
    have RX' := (ScopedArgumentsCount.cons RX RXS).mono (pi_inert_stage_mono (Nat.le_max_right m n))
    exact (RF'.mkApps RX').trans (by
      simpa only [ProofShape.mkApps, EB] using RS.mono (pi_inert_stage_mono (Nat.le_max_right m n)))

end Lean4Lean.VEnv.Strengthening
