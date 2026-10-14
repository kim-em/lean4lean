import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextEta

/-! # Replacing erased primitives by finite computations

A simulation of primitive steps extends through compatible computation and each
comparison layer. The translation preserves endpoints, modes and erased contexts.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params

/-- Replacing each primitive by a finite path preserves every computation. -/
theorem Compute.simulate (hstep : ∀ {a b}, Step a b → Compute Step' a b)
    (H : Compute Step a b) : Compute Step' a b := by
  induction H with
  | base H => exact hstep H
  | beta H => exact .beta H
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | proj _ ih => exact .proj ih
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2

variable [Params]

/-- Raw comparison only observes the finite computations of its primitives. -/
theorem Compare.simulate (hstep : ∀ {a b}, Step a b → Compute Step' a b)
    (H : Compare Step mode a b) : Compare Step' mode a b := by
  induction H with
  | refl => exact .refl
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | etaL h => exact .etaL h
  | etaR h => exact .etaR h
  | structL h => exact .structL h
  | structR h => exact .structR h
  | etaLams _ h ih => exact .etaLams ih h
  | compute Ra Rb _ ih => exact .compute (Ra.simulate hstep) (Rb.simulate hstep) ih

/-- Raw common lambda checking is preserved by finite primitive simulation. -/
theorem RawCheckedCompare.simulate (hstep : ∀ {a b}, Step a b → Compute Step' a b)
    (H : RawCheckedCompare Step mode a b) : RawCheckedCompare Step' mode a b := by
  induction H with
  | base H => exact .base (H.simulate hstep)
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | lamCommon _ ih => exact .lamCommon ih
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | compute Ra Rb _ ih => exact .compute (Ra.simulate hstep) (Rb.simulate hstep) ih

/-- Contextual comparison survives primitive simulation without modifying any
of its domain-sort witnesses or binder contexts. -/
theorem ContextCompare.simulate (hstep : ∀ {a b}, Step a b → Compute Step' a b)
    (H : ContextCompare Step Δ mode a b) : ContextCompare Step' Δ mode a b := by
  induction H with
  | base H => exact .base (H.simulate hstep)
  | app _ _ ihf iha => exact .app ihf iha
  | proj _ ih => exact .proj ih
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | lamSorted SA SA' _ _ ihA ihb => exact .lamSorted SA SA' ihA ihb
  | forallSorted SA SA' _ SB SB' _ ihA ihB => exact .forallSorted SA SA' ihA SB SB' ihB
  | lamCommon _ ih => exact .lamCommon ih
  | etaBodyL SA _ ih => exact .etaBodyL SA ih
  | etaBodyR SA _ ih => exact .etaBodyR SA ih
  | compute Ra Rb _ ih => exact .compute (Ra.simulate hstep) (Rb.simulate hstep) ih
  | symm _ ih => exact .symm ih

end Lean4Lean.VEnv.Strengthening.ProofShape
