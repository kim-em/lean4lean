import Lean4Lean.Theory.Typing.Strengthening.ProofErasureFunctionCarrier
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedJoinedSubstitution

/-! # Joined paired substitution for recursive carrier guards

Both substituted endpoints compute to a shared raw substitution, and the left
result carrier computes along the same substitution. Typed replay realizes the
shared context interpretation. The result type is arbitrary and may depend on
the substituted arguments. Arbitrarily compared arguments without a literal
computational join remain outside this theorem.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]
variable {τ : ProofShape.Subst}

/-- Simultaneous paired substitution preserves carrier guards when the image
maps compute pointwise to a shared map. Computing the carrier is essential for
dependent result types; endpoint computation alone does not align its index. -/
theorem proofErase_carrier_subst_join_with
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs))
    (W₁ : Ctx.SubstEq env univs Γ₀ σ₁ σ₁ Γ) (W₂ : Ctx.SubstEq env univs Γ₀ σ₂ σ₂ Γ)
    (E₁ : ErasedSubstAgreement Γ Γ₀ σ₁ ρ₁) (E₂ : ErasedSubstAgreement Γ Γ₀ σ₂ ρ₂)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ A) (proofErase Γ a) (proofErase Γ b))
    (R₁ : ∀ i, ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (ρ₁ i) (τ i))
    (R₂ : ∀ i, ProofShape.ScopedCompute Step (proofEraseCtx Γ₀) (ρ₂ i) (τ i)) :
    ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ₀)
      (proofErase Γ₀ (A.subst σ₁))
      (proofErase Γ₀ (a.subst σ₁)) (proofErase Γ₀ (b.subst σ₂)) := by
  obtain ⟨_, hA⟩ := ha.isType henv W₁.wf
  rw [proofErase_subst_with hΓ₀ W₁ hA E₁, proofErase_subst_with hΓ₀ W₁ ha E₁,
    proofErase_subst_with hΓ₀ W₂ hb E₂]
  have WC : ProofShape.ContextSubstitution (proofEraseCtx Γ) (proofEraseCtx Γ₀) ρ₁ :=
    ProofShape.ContextSubstitution.of_typed hΓ₀ W₁ E₁
  exact .compute (proofErase_scoped_compute_subst_images hsubst hΓ₀ W₁ hA E₁ R₁)
    (.reduce (proofErase_scoped_compute_subst_images hsubst hΓ₀ W₁ ha E₁ R₁)
      (proofErase_scoped_compute_subst_images hsubst hΓ₀ W₂ hb E₂ R₂)
      (H.subst hsubst (WC.compute_images hstep R₁)))

/-- Single-binder paired instantiation closes for arbitrary dependent carriers
when the two argument erasures have a literal computational join. -/
theorem proofErase_carrier_inst_join
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hb' : env.HasType univs (A :: Γ) b' B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HB : ProofShape.StructureCarrierGuard Step (proofEraseCtx (A :: Γ))
      (proofErase (A :: Γ) B) (proofErase (A :: Γ) b) (proofErase (A :: Γ) b'))
    (RX : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : ProofShape.ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ y) shared) :
    ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (B.inst x)) (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y)) := by
  have W₁ := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := x) (A₀ := A)).substEq hΓA hx
  have W₂ := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := y) (A₀ := A)).substEq hΓA hy
  have H := proofErase_carrier_subst_join_with hstep hsubst hΓA.1 W₁ W₂
    (erasedSubstAgreement_one hΓA hx) (erasedSubstAgreement_one hΓA hy) hb hb' HB
    (τ := ProofShape.Subst.one shared)
    (fun i => by cases i with | zero => exact RX | succ => exact .refl)
    (fun i => by cases i with | zero => exact RY | succ => exact .refl)
  simpa only [instN_eq, VExpr.Subst.liftN] using H

/-- Distinct proofs of a common proposition satisfy the joined law without any
normalization premise: both argument erasures are the same proof marker. The
dependent result carrier and both body certificates remain arbitrary. -/
theorem proofErase_carrier_inst_proofs
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ProofShape.ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hP : env.HasType univs Γ P (.sort .zero))
    (hb : env.HasType univs (P :: Γ) b B) (hb' : env.HasType univs (P :: Γ) b' B)
    (hx : env.HasType univs Γ x P) (hy : env.HasType univs Γ y P)
    (HB : ProofShape.StructureCarrierGuard Step (proofEraseCtx (P :: Γ))
      (proofErase (P :: Γ) B) (proofErase (P :: Γ) b) (proofErase (P :: Γ) b')) :
    ProofShape.StructureCarrierGuard Step (proofEraseCtx Γ)
      (proofErase Γ (B.inst x)) (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y)) := by
  apply proofErase_carrier_inst_join hstep hsubst ⟨hΓ, _, hP⟩ hb hb' hx hy HB
    (shared := .proof)
  · rw [proofErase_eq_proof.2 ⟨P, hx, hP⟩]; exact .refl
  · rw [proofErase_eq_proof.2 ⟨P, hy, hP⟩]; exact .refl

/-- Every finite structure/function singleton stage preserves joined paired
instantiation at the same stage, with no subsingleton result restriction. -/
theorem proofErase_structure_singleton_carrier_inst_join
    (heq : env.HasCanonicalEq) (hs : D.Sound env univs)
    (hΓA : OnCtx (A :: Γ) (env.IsType univs))
    (hb : env.HasType univs (A :: Γ) b B) (hb' : env.HasType univs (A :: Γ) b' B)
    (hx : env.HasType univs Γ x A) (hy : env.HasType univs Γ y A)
    (HB : ProofShape.StructureCarrierGuard (ErasedStructureSingletonStage D stage)
      (proofEraseCtx (A :: Γ)) (proofErase (A :: Γ) B)
      (proofErase (A :: Γ) b) (proofErase (A :: Γ) b'))
    (RX : ProofShape.ScopedCompute (ErasedStructureSingletonStage D stage)
      (proofEraseCtx Γ) (proofErase Γ x) shared)
    (RY : ProofShape.ScopedCompute (ErasedStructureSingletonStage D stage)
      (proofEraseCtx Γ) (proofErase Γ y) shared) :
    ProofShape.StructureCarrierGuard (ErasedStructureSingletonStage D stage) (proofEraseCtx Γ)
      (proofErase Γ (B.inst x)) (proofErase Γ (b.inst x)) (proofErase Γ (b'.inst y)) :=
  proofErase_carrier_inst_join (erased_structure_singleton_stage_descent heq hs stage)
    (erased_structure_singleton_stage_subst heq hs stage) hΓA hb hb' hx hy HB RX RY

end Lean4Lean.VEnv.Strengthening
