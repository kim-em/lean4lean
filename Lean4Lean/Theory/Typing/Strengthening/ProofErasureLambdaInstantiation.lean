import Lean4Lean.Theory.Typing.Strengthening.ProofErasureTypedComputeSubstitution
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedBinderComputation

/-! # Instantiating lambda computations without increasing the source stage

Instantiate each body segment in its own realized binder context. Forward
typing conversion gives the fixed argument that context's domain. This avoids
pulling all body segments back to one binder, which could increase the source
primitive stage before its substitution law was applied.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private erase_lam_inv from Lean4Lean.Theory.Typing.Strengthening.ProofErasureBeta
variable [Params]

private theorem lambda_inst_aux
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (R : ScopedCompute Step Δ source out)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b)) (EΓ : proofEraseCtx Γ = Δ)
    (Ee : ProofShape.lam (proofErase Γ A) (proofErase (A :: Γ) b) = source) :
    ∃ A' b', out = .lam A' b' ∧
      ScopedCompute Target (proofEraseCtx Γ) (proofErase Γ (b.inst x))
        (b'.inst (proofErase Γ x)) := by
  induction R generalizing Γ A u b B x with
  | base H => exact (Ee ▸ hhead H).elim
  | beta H =>
    cases Ee
    obtain ⟨A', b', HE, _, HB⟩ := H.lam_inv
    refine ⟨A', b', HE, ?_⟩
    rw [proofErase_instN (show OnCtx (A :: Γ) (env.IsType univs) from ⟨hΓ, u, hA⟩)
      hx Ctx.InstN.zero hb]
    apply ScopedCompute.beta
    simpa only [ProofShape.inst_eq_subst] using HB.subst (σ := (ProofShape.Subst.one (proofErase Γ x)).liftN 0)
  | lam RA RB =>
    cases Ee
    have hΓA : OnCtx (A :: Γ) (env.IsType univs) := ⟨hΓ, u, hA⟩
    have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
    have HR := proofErase_scoped_compute_subst_typed hstep hsubst hΓ W
      (erasedSubstAgreement_one hΓA hx) hb
      (by simpa only [proofEraseCtx, EΓ] using RB)
    refine ⟨_, _, rfl, ?_⟩
    simpa only [VExpr.Subst.liftN, ProofShape.Subst.liftN, VExpr.inst_eq,
      ProofShape.inst_eq_subst] using HR
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A₁, b₁, rfl, H₁⟩ := ih₁ hΓ hA hb hx hn EΓ Ee
    have EF := (show proofErase Γ (.lam A b) =
      .lam (proofErase Γ A) (proofErase (A :: Γ) b) from if_neg hn).trans Ee
    obtain ⟨f₁, HF, Ef₁⟩ := proofErase_scoped_compute_realize hstep hΓ (HasType.lam hA hb) EΓ EF R₁
    obtain ⟨A₀, b₀, rfl, hn₀, EA₀, Eb₀⟩ := erase_lam_inv Ef₁
    obtain ⟨⟨v, hA₀⟩, B₀, hb₀⟩ := HF.hasType.2.lam_inv henv hΓ
    have HPi := HF.hasType.2.uniqU henv hΓ (HasType.lam hA₀ hb₀)
    obtain ⟨⟨_, HAA⟩, _, _⟩ := HPi.forallE_inv henv hΓ
    have hx₀ := HAA.defeq hx
    obtain ⟨A₂, b₂, HE, H₂⟩ := ih₂ hΓ hA₀ hb₀ hx₀ hn₀ EΓ (by rw [EA₀, Eb₀])
    rw [proofErase_instN (show OnCtx (A₀ :: Γ) (env.IsType univs) from ⟨hΓ, v, hA₀⟩)
      hx₀ Ctx.InstN.zero hb₀, Eb₀] at H₂
    exact ⟨A₂, b₂, HE, H₁.trans H₂⟩
  | app | proj | forallE => cases Ee

/-- A typed lambda path supplies computation between its instantiated input
and output bodies using only substitution of the original source relation.
The argument needs no recovery certificate. Changing binder annotations and
arbitrarily many sequential segments do not enlarge the source relation. -/
theorem proofErase_scoped_lambda_inst_compute
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hb : env.HasType univs (A :: Γ) b B) (hx : env.HasType univs Γ x A)
    (hn : ¬ IsProof Γ (.lam A b))
    (R : ScopedCompute Step (proofEraseCtx Γ)
      (.lam (proofErase Γ A) (proofErase (A :: Γ) b)) out) :
    ∃ A' b', out = .lam A' b' ∧
      ScopedCompute Target (proofEraseCtx Γ) (proofErase Γ (b.inst x))
        (b'.inst (proofErase Γ x)) :=
  lambda_inst_aux hstep hhead hsubst R hΓ hA hb hx hn rfl rfl

end Lean4Lean.VEnv.Strengthening
