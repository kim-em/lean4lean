import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport

/-! # Typed substitution of the full joint checking grammar

The shared transport induction specializes to arbitrary typed substitution
using source-typed primitive simulation and target domain re-synthesis.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private infer_raw from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointTransport
variable [Params]

private theorem joint_substitution
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (hinc : ∀ {Δ a b}, Step Δ a b → Target Δ a b)
    (hres : JointCarrierDomainResynthesis Target Target)
    (H : JointCheck Step Δ kind sa sb) :
    JointTransportResult ContextSubstitution Target Δ kind sa sb := by
  apply H.transport ContextSubstitution hstep
    (fun W => ContextSubstitution.cons W) (fun W S => ContextSubstitution.sort W S)
    (fun R hΓ ht EΓ Ee W => R.subst_typed hstep hsubst hΓ ht EΓ Ee W)
  intro Γ Δ' τ f x y D C A B hΓ hf hx hy R HX W _
  obtain ⟨Γ₀, σ, hΓ₀, EΓ₀, WS, ES⟩ := W hΓ rfl
  obtain ⟨A', B', R', HX'⟩ := hres hΓ₀ WS hf hx hy (R.mono hinc) (HX.mono hinc)
  rw [proofErase_subst_with hΓ₀ WS hf ES, EΓ₀] at R'
  rw [proofErase_subst_with hΓ₀ WS hx ES, proofErase_subst_with hΓ₀ WS hy ES, EΓ₀] at HX'
  exact ⟨A', B', R', HX'⟩

/-- Common-typed raw joint comparison transports under interpreted substitution.
Source primitives may simulate by computations in a larger target relation;
only the target joint domain re-synthesis law is additionally required. -/
theorem ProofShape.JointCompare.subst_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (hinc : ∀ {Δ a b}, Step Δ a b → Target Δ a b)
    (hres : JointCarrierDomainResynthesis Target Target)
    (H : JointCompare Step Δ mode sa sb)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : ContextSubstitution Δ Δ' τ) : JointCompare Target Δ' mode (sa.subst τ) (sb.subst τ) :=
  joint_substitution hstep hsubst hinc hres H hΓ ha hb EΓ Ea Eb W

/-- Typed joint carriers transport with their exact substituted carrier syntax.
Re-synthesis changes only domains selected inside recovered application rules. -/
theorem ProofShape.JointCarrierGuard.subst_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (hinc : ∀ {Δ a b}, Step Δ a b → Target Δ a b)
    (hres : JointCarrierDomainResynthesis Target Target)
    (H : JointCarrierGuard Step Δ α sa sb)
    (hΓ : OnCtx Γ (env.IsType univs)) (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (EΓ : proofEraseCtx Γ = Δ) (Eα : proofErase Γ A = α)
    (Ea : proofErase Γ a = sa) (Eb : proofErase Γ b = sb)
    (W : ContextSubstitution Δ Δ' τ) :
    JointCarrierGuard Target Δ' (α.subst τ) (sa.subst τ) (sb.subst τ) :=
  joint_substitution hstep hsubst hinc hres H hΓ ha hb EΓ Eα Ea Eb W

/-- Ordinary typed substitution of the full recursive checker, conditional on
source primitive simulation and target joint domain re-synthesis. Every binder,
eta, structure-field, carrier, and computation rule is covered. -/
theorem proofErase_joint_compare_subst_of_resynthesis
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (hinc : ∀ {Δ a b}, Step Δ a b → Target Δ a b)
    (hres : JointCarrierDomainResynthesis Target Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCompare Step (proofEraseCtx Γ) mode (proofErase Γ a) (proofErase Γ b)) :
    JointCompare Target (proofEraseCtx Γ₀) mode (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  let τ : ProofShape.Subst := fun i => proofErase Γ₀ (σ i)
  have E : ErasedSubstAgreement Γ Γ₀ σ τ := fun _ _ => rfl
  rw [proofErase_subst_with hΓ₀ W ha E, proofErase_subst_with hΓ₀ W hb E]
  exact H.subst_typed hstep hsubst hinc hres W.wf ha hb rfl rfl rfl
    (ContextSubstitution.of_typed hΓ₀ W E)

/-- Inferred checking also transports independently typed non-proof endpoints.
Source reflection first aligns their types, with no inverse weakening. -/
theorem proofErase_joint_inferred_subst_of_resynthesis
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (hinc : ∀ {Δ a b}, Step Δ a b → Target Δ a b)
    (hres : JointCarrierDomainResynthesis Target Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b B)
    (hna : ¬ IsProof Γ a) (hnb : ¬ IsProof Γ b)
    (H : JointCompare Step (proofEraseCtx Γ) false (proofErase Γ a) (proofErase Γ b)) :
    JointCompare Target (proofEraseCtx Γ₀) false (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) :=
  proofErase_joint_compare_subst_of_resynthesis hstep hsubst hinc hres hΓ₀ W ha
    (infer_raw hstep H W.wf ha hb rfl rfl rfl hna hnb).hasType.2 H

/-- Ordinary typed substitution preserves the supplied carrier and both
endpoints in the richer joint grammar, under the same two transport premises. -/
theorem proofErase_joint_carrier_subst_of_resynthesis
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ErasedPrimitiveSubstitutionTo Step Target)
    (hinc : ∀ {Δ a b}, Step Δ a b → Target Δ a b)
    (hres : JointCarrierDomainResynthesis Target Target)
    (hΓ₀ : OnCtx Γ₀ (env.IsType univs)) (W : Ctx.SubstEq env univs Γ₀ σ σ Γ)
    (ha : env.HasType univs Γ a A) (hb : env.HasType univs Γ b A)
    (H : JointCarrierGuard Step (proofEraseCtx Γ) (proofErase Γ A) (proofErase Γ a) (proofErase Γ b)) :
    JointCarrierGuard Target (proofEraseCtx Γ₀) (proofErase Γ₀ (A.subst σ))
      (proofErase Γ₀ (a.subst σ)) (proofErase Γ₀ (b.subst σ)) := by
  let τ : ProofShape.Subst := fun i => proofErase Γ₀ (σ i)
  have E : ErasedSubstAgreement Γ Γ₀ σ τ := fun _ _ => rfl
  obtain ⟨u, hA⟩ := ha.isType henv W.wf
  rw [proofErase_subst_with hΓ₀ W hA E, proofErase_subst_with hΓ₀ W ha E,
    proofErase_subst_with hΓ₀ W hb E]
  exact H.subst_typed hstep hsubst hinc hres W.wf ha hb rfl rfl rfl rfl
    (ContextSubstitution.of_typed hΓ₀ W E)

end Lean4Lean.VEnv.Strengthening
