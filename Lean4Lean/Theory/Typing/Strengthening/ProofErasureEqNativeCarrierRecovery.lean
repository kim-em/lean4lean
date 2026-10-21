import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqDecode
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointDomainExposure
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedBinderComputation
import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedSubstitutionImages

/-! # Native Eq recovery retains an arbitrary carrier computation

Unlike sort and variable carriers, a general Eq carrier can compute. Native
recovery of its last-argument domain is still reachable from that carrier.
The proof retains the computation instead of demanding an unchanged type.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params ProofShape
open private eq_recovery
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureJointEqDecode
open private beta_forallE_parts
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierDomainJoin
variable [Params]

namespace ProofShape
/-- Pi computation retains its codomain path in the original binder context.
Only the initial domain is required to have an original typing. -/
theorem ScopedCompute.forallE_inv_typed
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hroot : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hΓ : OnCtx Γ (env.IsType univs)) (hA : env.HasType univs Γ A (.sort u))
    (hΔ : proofEraseCtx Γ = Δ)
    (R : ScopedCompute Step Δ (.forallE (proofErase Γ A) body) out) :
    ∃ A' body', out = .forallE A' body' ∧
      ScopedCompute Step Δ (proofErase Γ A) A' ∧
      ScopedCompute Step (proofErase Γ A :: Δ) body body' := by
  generalize E : ProofShape.forallE (proofErase Γ A) body = source at R
  induction R generalizing Γ A u body with
  | base H => exact (E ▸ hroot H).elim
  | beta H =>
    cases E
    obtain ⟨A', body', HE, HA, HB⟩ := beta_forallE_parts H
    exact ⟨_, _, HE, .beta HA, .beta HB⟩
  | trans R₁ R₂ ih₁ ih₂ =>
    obtain ⟨A₁, body₁, rfl, RA, RB⟩ := ih₁ hΓ hA hΔ E
    have WI : Ctx.LiftN 0 0 Γ Γ := .zero []
    obtain ⟨A₀, HA, EA⟩ := proofErase_scoped_compute_descend hstep hΓ hΓ WI hA hΔ
      (by simpa only [liftN_zero] using RA)
    simp only [liftN_zero] at EA
    obtain ⟨A₂, body₂, HE, RA₂, RB₂⟩ := ih₂ hΓ HA.hasType.2 hΔ (congrArg (·.forallE body₁) EA)
    have HC : IsDefEqCtx env univs Γ (A₀ :: Γ) (A :: Γ) := .succ .zero HA.symm
    have RB₂' : ScopedCompute Step (proofEraseCtx (A₀ :: Γ)) body₁ body₂ := by
      simpa only [proofEraseCtx, hΔ] using RB₂
    have RB₂'' := RB₂'.defeqCtx hsubst hΓ HC
    refine ⟨_, _, HE, RA.trans (EA ▸ RA₂), RB.trans ?_⟩
    simpa only [proofEraseCtx, hΔ] using RB₂''
  | forallE RA RB => cases E; exact ⟨_, _, rfl, RA, RB⟩
  | app | proj | lam => cases E
end ProofShape

private theorem eq_carrier_recovery
    (heq : env.HasCanonicalEq)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (R : ScopedTypeRecovery Step Δ (.app (.const ``Eq [u]) α) T) :
    ScopedCompute Step Δ (.forallE α (.forallE (α.liftN 1) (.sort .zero))) T := by
  generalize E : ProofShape.app (.const ``Eq [u]) α = e at R
  induction R with
  | app R =>
    cases E
    cases eq_recovery heq hhead R
    simpa [ProofShape.inst, ProofShape.liftN_zero] using
      (ScopedCompute.refl (Step := Step)
        (e := .forallE α (.forallE (α.liftN 1) (.sort .zero))))
  | convert _ H ih => exact (ih E).trans H
  | bvar | sort | const | lam | forallE | proj => cases E

/-- Recovery of an actual Eq prefix computes from its native final Pi.
The retained carrier may be arbitrary syntax. Typed binder inversion and
forward substitution handle conversions before the fixed anchor is applied. -/
theorem proofErase_eq_prefix_native_compute
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (.app (.app (.const ``Eq [u]) (proofErase Γ α)) (proofErase Γ z)) T) :
    ScopedCompute Step (proofEraseCtx Γ) (.forallE (proofErase Γ α) (.sort .zero)) T := by
  generalize EΔ : proofEraseCtx Γ = Δ at R
  generalize E : ProofShape.app (.app (.const ``Eq [u]) (proofErase Γ α)) (proofErase Γ z) = e at R
  induction R with
  | app RF =>
    cases E
    have RC := eq_carrier_recovery heq hhead RF
    obtain ⟨A, B, HE, _, RB⟩ := RC.forallE_inv_typed hstep hsubst hhead hΓ hα EΔ
    cases HE
    have hΓα : OnCtx (α :: Γ) (env.IsType univs) := ⟨hΓ, _, hα⟩
    have W := (Ctx.InstN.zero (Γ₀ := Γ) (e₀ := z) (A₀ := α)).substEq hΓα hz
    rw [← EΔ] at RB
    change ScopedCompute Step (proofEraseCtx (α :: Γ)) _ _ at RB
    have RB := RB.subst hsubst (ContextSubstitution.of_typed hΓ W (erasedSubstAgreement_one hΓα hz))
    simpa only [ProofShape.inst_eq_subst, ProofShape.Subst.liftN, ProofShape.subst,
      ProofShape.Subst.one, ProofShape.lift_subst_cons, ProofShape.subst_id, EΔ] using RB
  | convert _ H ih => exact (ih EΔ E).trans H
  | bvar | sort | const | lam | forallE | proj => cases E

/-- The selected domain of an Eq prefix is reached by computation from the
original supplied carrier. No comparison or recovery completeness is assumed. -/
theorem proofErase_eq_prefix_domain_compute
    (heq : env.HasCanonicalEq)
    (hstep : ErasedScopedPrimitiveDescent Step)
    (hhead : ∀ {Δ a b}, Step Δ a b → PrimitiveHead a)
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (hΓ : OnCtx Γ (env.IsType univs)) (hα : env.HasType univs Γ α (.sort u))
    (hz : env.HasType univs Γ z α)
    (R : ScopedTypeRecovery Step (proofEraseCtx Γ)
      (.app (.app (.const ``Eq [u]) (proofErase Γ α)) (proofErase Γ z)) (.forallE A B)) :
    ScopedCompute Step (proofEraseCtx Γ) (proofErase Γ α) A := by
  obtain ⟨A', B', HE, RA⟩ :=
    (proofErase_eq_prefix_native_compute heq hstep hhead hsubst hΓ hα hz R).forallE_domain_inv hhead
  cases HE
  exact RA

end Lean4Lean.VEnv.Strengthening
