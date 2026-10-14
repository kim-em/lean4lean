import Lean4Lean.Theory.Typing.Strengthening.ProofErasureScopedComparison

/-! # Transport and inclusion for scoped erased checking -/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
namespace ProofShape
variable [Params]

/-- Typed contextual substitution of primitives suffices for all computation,
including bodies under domains which themselves compute. -/
theorem ScopedCompute.subst
    (hstep : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : ScopedCompute Step Δ a b) (W : ContextSubstitution Δ Δ' τ) :
    ScopedCompute Step Δ' (a.subst τ) (b.subst τ) := by
  induction H generalizing Δ' τ with
  | base H => exact .base (hstep H W)
  | beta H => exact .beta H.subst
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ W) (ih₂ W)
  | app _ _ ih₁ ih₂ => exact .app (ih₁ W) (ih₂ W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ih₁ ih₂ => exact .lam (ih₁ W) (ih₂ W.cons)
  | forallE _ _ ih₁ ih₂ => exact .forallE (ih₁ W) (ih₂ W.cons)

omit [Params] in
/-- Context-independent computations embed whenever their roots are available
at every context. -/
theorem Compute.scoped
    (hstep : ∀ {Δ a b}, Step a b → ScopedCompute Step' Δ a b)
    (H : Compute Step a b) : ScopedCompute Step' Δ a b := by
  induction H generalizing Δ with
  | base H => exact hstep H
  | beta H => exact .beta H
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | proj _ ih => exact .proj ih
  | lam _ _ ih₁ ih₂ => exact .lam ih₁ ih₂
  | forallE _ _ ih₁ ih₂ => exact .forallE ih₁ ih₂

/-- Every erased term is reflexively scoped-compared. -/
theorem ScopedCompare.refl : ScopedCompare Step Δ mode a a := .base .refl

/-- Recursive sort witnesses and primitive computations substitute together
along a typed context interpretation. -/
theorem ScopedCompare.subst
    (hsubst : ∀ {Δ Δ' a b τ}, Step Δ a b → ContextSubstitution Δ Δ' τ →
      Step Δ' (a.subst τ) (b.subst τ))
    (H : ScopedCompare Step Δ mode a b) (W : ContextSubstitution Δ Δ' τ) :
    ScopedCompare Step Δ' mode (a.subst τ) (b.subst τ) := by
  induction H generalizing Δ' τ with
  | base H => exact .base (H.subst (by intros; contradiction) W)
  | app _ _ ihf iha => exact .app (ihf W) (iha W)
  | proj _ ih => exact .proj (ih W)
  | lam _ _ ihA ihb => exact .lam (ihA W) (ihb W.cons)
  | forallE _ _ ihA ihB => exact .forallE (ihA W) (ihB W.cons)
  | lamSorted SA SA' _ _ ihA ihb => exact .lamSorted (W.sort SA) (W.sort SA') (ihA W) (ihb W.cons)
  | forallSorted SA SA' _ SB SB' _ ihA ihB =>
    exact .forallSorted (W.sort SA) (W.sort SA') (ihA W) (ContextSubstitution.sort W.cons SB) (ContextSubstitution.sort W.cons SB') (ihB W.cons)
  | lamCommon _ ih => exact .lamCommon (ih W.cons)
  | etaBodyL S _ ih =>
    apply ScopedCompare.etaBodyL (W.sort S)
    simpa only [ProofShape.subst, etaArgument_subst, lift_subst_lift] using ih W.cons
  | etaBodyR S _ ih =>
    apply ScopedCompare.etaBodyR (W.sort S)
    simpa only [ProofShape.subst, etaArgument_subst, lift_subst_lift] using ih W.cons
  | etaLams _ H ih => exact .etaLams (ih W) (H.elim (fun H => .inl H.subst) (fun H => .inr H.subst))
  | compute Ra Rb _ ih => exact .compute (Ra.subst hsubst W) (Rb.subst hsubst W) (ih W)
  | symm _ ih => exact (ih W).symm
/-- Enlarging the contextual primitive relation preserves scoped guards. -/
theorem ScopedCompare.mono (hstep : ∀ {Δ a b}, Step Δ a b → Step' Δ a b)
    (H : ScopedCompare Step Δ mode a b) : ScopedCompare Step' Δ mode a b := by
  induction H with
  | base H => exact .base H
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | lamSorted SA SA' _ _ ihA ihb => exact .lamSorted SA SA' ihA ihb
  | forallSorted SA SA' _ SB SB' _ ihA ihB => exact .forallSorted SA SA' ihA SB SB' ihB
  | lamCommon _ ih => exact .lamCommon ih
  | etaBodyL SA _ ih => exact .etaBodyL SA ih
  | etaBodyR SA _ ih => exact .etaBodyR SA ih
  | etaLams _ H ih => exact .etaLams ih H
  | compute Ra Rb _ ih => exact .compute (Ra.mono hstep) (Rb.mono hstep) ih
  | symm _ ih => exact .symm ih
/-- Inferred scoped comparison also checks at common types. -/
theorem ScopedCompare.common (H : ScopedCompare Step Δ mode a b) :
    ScopedCompare Step Δ true a b := by
  induction H with
  | base H => exact .base H.common
  | app Hf Ha => exact .app Hf Ha
  | proj H => exact .proj H
  | lam HA _ _ ih => exact .lam HA ih
  | forallE HA HB => exact .forallE HA HB
  | lamSorted SA SA' HA _ _ ih => exact .lamSorted SA SA' HA ih
  | forallSorted SA SA' HA SB SB' HB => exact .forallSorted SA SA' HA SB SB' HB
  | lamCommon H => exact .lamCommon H
  | etaBodyL S H => exact .etaBodyL S H
  | etaBodyR S H => exact .etaBodyR S H
  | etaLams H E => exact .etaLams H E
  | compute Ra Rb _ ih => exact .compute Ra Rb ih
  | symm _ ih => exact ih.symm

/-- Earlier comparison certificates embed with identical endpoints and mode
when their primitive computations have contextual simulations. -/
theorem Compare.scoped (hstep : ∀ {Δ a b}, Step a b → ScopedCompute Step' Δ a b)
    (H : Compare Step mode a b) : ScopedCompare Step' Δ mode a b := by
  induction H generalizing Δ with
  | refl => exact .refl
  | sort h => exact .base (.base (.base (.sort h)))
  | const h => exact .base (.base (.base (.const h)))
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | etaL h => exact .base (.base (.base (.etaL h)))
  | etaR h => exact .base (.base (.base (.etaR h)))
  | structL h => exact .base (.base (.base (.structL h)))
  | structR h => exact .base (.base (.base (.structR h)))
  | etaLams _ h ih => exact .etaLams ih h
  | compute Ra Rb _ ih => exact .compute (Ra.scoped hstep) (Rb.scoped hstep) ih

/-- Earlier comparison certificates embed with identical endpoints and mode
when their primitive computations have contextual simulations. -/
theorem RawCheckedCompare.scoped (hstep : ∀ {Δ a b}, Step a b → ScopedCompute Step' Δ a b)
    (H : RawCheckedCompare Step mode a b) : ScopedCompare Step' Δ mode a b := by
  induction H generalizing Δ with
  | base H => exact H.scoped hstep
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | lamCommon _ ih => exact .lamCommon ih
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | compute Ra Rb _ ih => exact .compute (Ra.scoped hstep) (Rb.scoped hstep) ih

/-- Earlier comparison certificates embed with identical endpoints and mode
when their primitive computations have contextual simulations. -/
theorem ContextCompare.scoped (hstep : ∀ {Δ a b}, Step a b → ScopedCompute Step' Δ a b)
    (H : ContextCompare Step Δ mode a b) : ScopedCompare Step' Δ mode a b := by
  induction H with
  | base H => exact H.scoped hstep
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | lamSorted SA SA' _ _ ihA ihb => exact .lamSorted SA SA' ihA ihb
  | forallSorted SA SA' _ SB SB' _ ihA ihB => exact .forallSorted SA SA' ihA SB SB' ihB
  | lamCommon _ ih => exact .lamCommon ih
  | etaBodyL SA _ ih => exact .etaBodyL SA ih
  | etaBodyR SA _ ih => exact .etaBodyR SA ih
  | compute Ra Rb _ ih => exact .compute (Ra.scoped hstep) (Rb.scoped hstep) ih
  | symm _ ih => exact .symm ih

end ProofShape

end Lean4Lean.VEnv.Strengthening
