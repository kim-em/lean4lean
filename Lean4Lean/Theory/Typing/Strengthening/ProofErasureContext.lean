import Lean4Lean.Theory.Typing.Strengthening.ProofErasureSortWitness

/-! # Typed realizations of erased contexts

An erased context retains each domain in the context of its older variables.
Two well-formed realizations of the same erased context are definitionally
convertible. This makes ambient domain-sort witnesses independent of the chosen
original realization, without computational type recovery.
-/
namespace Lean4Lean.VEnv.Strengthening
open _root_.Lean4Lean _root_.Lean4Lean.VExpr Params
variable [Params]

/-- Erase every context domain at its declaration scope. -/
noncomputable def proofEraseCtx : List VExpr → List ProofShape
  | [] => []
  | A :: Γ => proofErase Γ A :: proofEraseCtx Γ

namespace ProofShape
/-- Variable-type oracle determined by an erased context. -/
def contextOracle : List ProofShape → TypeOracle
  | [] => fun _ => .proof
  | A :: Δ => (contextOracle Δ).cons A
end ProofShape

/-- The erased context recovers the existing canonical type oracle exactly. -/
theorem proofEraseCtx_oracle : ProofShape.contextOracle (proofEraseCtx Γ) = erasedTypeOracle Γ := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => simp only [proofEraseCtx, ProofShape.contextOracle, erasedTypeOracle, ih]

/-- Equal erased contexts have convertible well-formed original realizations.
Domain comparison uses erasure reflection after converting the older context. -/
theorem proofEraseCtx_defeq (hΓ : OnCtx Γ (env.IsType univs))
    (hΔ : OnCtx Δ (env.IsType univs)) (E : proofEraseCtx Γ = proofEraseCtx Δ) :
    IsDefEqCtx env univs [] Γ Δ := by
  induction Γ generalizing Δ with
  | nil => cases Δ with
    | nil => exact .zero
    | cons => cases E
  | cons A Γ ih =>
    cases Δ with
    | nil => cases E
    | cons B Δ =>
      obtain ⟨hΓ, u, hA⟩ := hΓ
      obtain ⟨hΔ, v, hB⟩ := hΔ
      obtain ⟨EAB, EΓΔ⟩ := List.cons.inj E
      have W := ih hΓ hΔ EΓΔ
      have hB' := hB.defeqDFC henv (W.symm henv.ordered)
      have EB := proofErase_defeqCtx hΔ (W.symm henv.ordered) hB
      obtain ⟨_, H⟩ := (proofErase_reflect hΓ hA hB' (EAB.trans EB)).2
        (not_isProof_of_sort hΓ hA)
      exact .succ W ((H.defeq hΓ).of_l henv hΓ hA)

namespace ProofShape
/-- A domain's sort witnessed in any well-formed realization of the raw context.
No computed type or global recovery-completeness premise is part of the witness. -/
def DomainSort (Δ : List ProofShape) (A : ProofShape) (u : VLevel) : Prop :=
  ∃ Γ e, OnCtx Γ (env.IsType univs) ∧ proofEraseCtx Γ = Δ ∧
    env.HasType univs Γ e (.sort u) ∧ proofErase Γ e = A

/-- A typed original domain supplies its ambient sort witness directly. -/
theorem DomainSort.of_typed (hΓ : OnCtx Γ (env.IsType univs))
    (hA : env.HasType univs Γ A (.sort u)) :
    DomainSort (proofEraseCtx Γ) (proofErase Γ A) u := ⟨Γ, A, hΓ, rfl, hA, rfl⟩

/-- A domain-sort witness can be interpreted in every well-formed realization
of the same erased context. -/
theorem DomainSort.realize (H : DomainSort (proofEraseCtx Γ) A u)
    (hΓ : OnCtx Γ (env.IsType univs)) :
    ∃ e, env.HasType univs Γ e (.sort u) ∧ proofErase Γ e = A := by
  obtain ⟨Δ, e, hΔ, EΔ, he, Ee⟩ := H
  have W := proofEraseCtx_defeq hΔ hΓ EΔ
  exact ⟨e, he.defeqDFC henv W, (proofErase_defeqCtx hΔ W he).symm.trans Ee⟩

/-- Contextual domain-sort witnesses descend at an independently typed lower
domain. They determine its universe without computational sort exposure. -/
theorem DomainSort.descend (H : DomainSort (proofEraseCtx Γ') ((proofErase Γ A).liftN n k) u)
    (hΓ : OnCtx Γ (env.IsType univs)) (hΓ' : OnCtx Γ' (env.IsType univs))
    (W : Ctx.LiftN n k Γ Γ') (hA : env.HasType univs Γ A (.sort v)) :
    env.HasType univs Γ A (.sort u) := by
  obtain ⟨e, he, E⟩ := H.realize hΓ'
  exact proofErase_sort_witness_descend hΓ hΓ' W hA he E
end ProofShape
end Lean4Lean.VEnv.Strengthening
