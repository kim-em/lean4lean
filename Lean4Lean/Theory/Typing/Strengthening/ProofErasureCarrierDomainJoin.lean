import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierFiniteStrength

/-! # Adapting subsingleton argument guards through domain joins

Structural subsingleton certificates survive beta computation. A recovered
domain that computes to the same reduct therefore supports the argument guard,
even if it differs from the old domain after substitution. This closes one
guard-adaptation case; general type exposure and arbitrary carrier guards remain
outside the result.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
namespace ProofShape

private theorem beta_forallE_parts (R : BetaRed (.forallE A B) out) :
    ∃ A' B', out = .forallE A' B' ∧ BetaRed A A' ∧ BetaRed B B' := by
  generalize E : ProofShape.forallE A B = source at R
  induction R generalizing A B with
  | refl => exact ⟨_, _, E.symm, .refl, .refl⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨A₁, B₁, rfl, RA, RB⟩ := ih₁ E
    obtain ⟨A₂, B₂, E₂, RA', RB'⟩ := ih₂ rfl
    exact ⟨A₂, B₂, E₂, RA.trans RA', RB.trans RB'⟩
  | forallE RA RB => cases E; exact ⟨_, _, rfl, RA, RB⟩
  | app | proj | lam | beta => cases E

variable [Params]

/-- Beta computation retains the empty-structure head and parameter arity, or
the recursive Pi codomain certificate. Domains may compute arbitrarily. -/
theorem SubsingletonCarrier.beta (H : SubsingletonCarrier A) (R : BetaRed A B) :
    SubsingletonCarrier B := by
  induction H generalizing B with
  | unit hi hx hf hp =>
    obtain ⟨ps', rfl, HR⟩ := R.const_spine
    exact .unit hi hx hf (HR.length_eq.symm.trans hp)
  | forallE H ih =>
    obtain ⟨A', B', rfl, _, RB⟩ := beta_forallE_parts R
    exact .forallE (ih RB)

/-- A beta-joined subsingleton domain transfers its argument guard to any
other carrier computing to that join. The new carrier need not have the old
syntax or itself belong to the structural grammar. -/
theorem SubsingletonCarrier.join_target
    (H : SubsingletonCarrier A) (RA : BetaRed A shared)
    (RB : ScopedCompute Step Δ B shared) : StructureCarrierGuard Step Δ B x y :=
  .compute RB (.subsingleton (H.beta RA))

/-- Joint re-synthesis at beta-joined subsingleton domains is constructive once
a new Pi recovery is supplied. The function comparison substitutes normally;
the new domain computes to a beta reduct of the substituted old certificate.
Neither the new domain nor its codomain is required to match old syntax. -/
theorem recovered_carrier_application_subst_subsingleton_join
    {x y : ProofShape}
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (W : ContextSubstitution Δ Δ' τ)
    (HF : ScopedCompare Step Δ false f g)
    (HS : SubsingletonCarrier A)
    (R : TypeRecovery Recovery (contextOracle Δ') (f.subst τ) (.forallE A' B'))
    (RA : BetaRed (A.subst τ) shared)
    (RA' : ScopedCompute Step Δ' A' shared) :
    RecoveredCarrierApplication Recovery Step Δ'
      ((ProofShape.app f x).subst τ) ((ProofShape.app g y).subst τ) :=
  .app R (HF.subst hsubst W) ((HS.subst τ).join_target RA RA')

end ProofShape
end Lean4Lean.VEnv.Strengthening
