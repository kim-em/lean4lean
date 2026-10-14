import Lean4Lean.Theory.Typing.Strengthening.ProofErasureContextEta

/-! # Inverting contextual comparison at fixed application spines

When both application endpoints are fixed by computation and cannot be long
structure-eta endpoints, every comparison preserves their function and argument
positions. This includes recursive eta and symmetry in contextual comparison.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
namespace ProofShape

/-- A shape fixed by every finite compatible computation in the chosen fragment. -/
def ComputeFixed (Step : ProofShape → ProofShape → Prop) (a : ProofShape) : Prop :=
  ∀ {b}, Compute Step a b → b = a

/-- A fixed application has a fixed function subterm. -/
theorem ComputeFixed.fn (H : ComputeFixed Step (.app f a)) : ComputeFixed Step f := by
  intro g R
  exact (ProofShape.app.inj (H (.app R .refl))).1

/-- A fixed application has a fixed argument subterm. -/
theorem ComputeFixed.arg (H : ComputeFixed Step (.app f a)) : ComputeFixed Step a := by
  intro b R
  exact (ProofShape.app.inj (H (.app .refl R))).2

variable [Params]

/-- Fixed non-structure applications compared by the original raw relation have
inferred function certificates and common argument certificates. -/
theorem Compare.fixed_app_inv (H : Compare Step mode (.app f a) (.app g b))
    (hf : ComputeFixed Step (.app f a)) (hg : ComputeFixed Step (.app g b))
    (hfs : ∀ m, ¬ StructureEtaHead (.app f a) m)
    (hgs : ∀ m, ¬ StructureEtaHead (.app g b) m) :
    ContextCompare Step Δ false f g ∧ ContextCompare Step Δ true a b := by
  generalize Ef : ProofShape.app f a = sf at H
  generalize Eg : ProofShape.app g b = sg at H
  induction H generalizing f a g b with
  | refl =>
    obtain ⟨rfl, rfl⟩ := ProofShape.app.inj (Ef.trans Eg.symm)
    exact ⟨.refl, .refl⟩
  | app HF HA => cases Ef; cases Eg; exact ⟨.base (.base HF), .base (.base HA)⟩
  | etaL H => obtain ⟨_, _, HE, _⟩ := H.shape; cases Ef.trans HE
  | etaR H => obtain ⟨_, _, HE, _⟩ := H.shape; cases Eg.trans HE
  | structL H => exact (hfs _ (Ef ▸ H)).elim
  | structR H => exact (hgs _ (Eg ▸ H)).elim
  | compute Rf Rg HC ih =>
    have EF := hf (Ef ▸ Rf)
    have EG := hg (Eg ▸ Rg)
    exact ih hf hg hfs hgs EF.symm EG.symm
  | sort | const | proj | lam | forallE | etaLams => cases Ef

/-- The raw lambda-checking extension preserves inversion at fixed application
endpoints; its additional rule only compares lambda heads. -/
theorem RawCheckedCompare.fixed_app_inv (H : RawCheckedCompare Step mode (.app f a) (.app g b))
    (hf : ComputeFixed Step (.app f a)) (hg : ComputeFixed Step (.app g b))
    (hfs : ∀ m, ¬ StructureEtaHead (.app f a) m)
    (hgs : ∀ m, ¬ StructureEtaHead (.app g b) m) :
    ContextCompare Step Δ false f g ∧ ContextCompare Step Δ true a b := by
  generalize Ef : ProofShape.app f a = sf at H
  generalize Eg : ProofShape.app g b = sg at H
  induction H generalizing f a g b with
  | base H => exact (by rw [← Ef, ← Eg] at H; exact H.fixed_app_inv hf hg hfs hgs)
  | app HF HA => cases Ef; cases Eg; exact ⟨.base HF, .base HA⟩
  | compute Rf Rg HC ih =>
    have EF := hf (Ef ▸ Rf)
    have EG := hg (Eg ▸ Rg)
    exact ih hf hg hfs hgs EF.symm EG.symm
  | proj | lam | lamCommon | forallE => cases Ef

/-- Contextual sort witnesses and recursive eta do not alter fixed application
spine inversion. The explicit symmetry rule swaps the extracted certificates. -/
theorem ContextCompare.fixed_app_inv (H : ContextCompare Step Δ mode (.app f a) (.app g b))
    (hf : ComputeFixed Step (.app f a)) (hg : ComputeFixed Step (.app g b))
    (hfs : ∀ m, ¬ StructureEtaHead (.app f a) m)
    (hgs : ∀ m, ¬ StructureEtaHead (.app g b) m) :
    ContextCompare Step Δ false f g ∧ ContextCompare Step Δ true a b := by
  generalize Ef : ProofShape.app f a = sf at H
  generalize Eg : ProofShape.app g b = sg at H
  induction H generalizing f a g b with
  | base H => exact (by rw [← Ef, ← Eg] at H; exact H.fixed_app_inv hf hg hfs hgs)
  | app HF HA => cases Ef; cases Eg; exact ⟨HF, HA⟩
  | compute Rf Rg HC ih =>
    have EF := hf (Ef ▸ Rf)
    have EG := hg (Eg ▸ Rg)
    exact ih hf hg hfs hgs EF.symm EG.symm
  | symm H ih =>
    have HH := ih hg hf hgs hfs Eg Ef
    exact ⟨HH.1.symm, HH.2.symm⟩
  | etaBodyR => cases Eg
  | proj | lam | forallE | lamSorted | forallSorted | lamCommon | etaBodyL => cases Ef

end ProofShape
end Lean4Lean.VEnv.Strengthening
