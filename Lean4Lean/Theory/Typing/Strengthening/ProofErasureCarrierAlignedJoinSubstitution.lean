import Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedExpansionPiJoin

/-! # Substitution and context lookups for raw beta/universe joins

Join certificates substitute without requiring exact native type recovery.
Pointwise joined context entries induce joined lifted variable-type lookups.
-/
namespace Lean4Lean.VEnv.Strengthening.ProofShape
open _root_.Lean4Lean
open private beta_sort
  from Lean4Lean.Theory.Typing.Strengthening.ProofErasureCarrierAlignedSortRoot

/-- Raw joins survive arbitrary binder insertions. -/
theorem BetaLevelJoin.liftN (H : BetaLevelJoin a b) :
    BetaLevelJoin (a.liftN n k) (b.liftN n k) := by
  obtain ⟨a', b', RA, RB, V⟩ := H
  exact ⟨_, _, RA.liftN, RB.liftN, V.liftN⟩

/-- The same raw substitution can be applied to both sides of a join. -/
theorem BetaLevelJoin.subst (H : BetaLevelJoin a b) :
    BetaLevelJoin (a.subst σ) (b.subst σ) := by
  obtain ⟨a', b', RA, RB, V⟩ := H
  exact ⟨_, _, RA.subst, RB.subst, V.subst⟩

private theorem join_lift_images {σ τ : Subst} (H : ∀ i, BetaLevelJoin (σ i) (τ i)) :
    ∀ i, BetaLevelJoin (σ.lift i) (τ.lift i) := by
  intro i
  cases i with
  | zero => exact .refl
  | succ i => exact (H i).liftN

private theorem join_subst_same (a : ProofShape) (H : ∀ i, BetaLevelJoin (σ i) (τ i)) :
    BetaLevelJoin (a.subst σ) (a.subst τ) := by
  induction a generalizing σ τ with
  | proof | sort | const => exact .refl
  | bvar i => exact H i
  | app _ _ ihf ihx => exact .app (ihf H) (ihx H)
  | proj _ _ _ ih => exact .proj (ih H)
  | lam _ _ ihA ihb => exact .lam (ihA H) (ihb (join_lift_images H))
  | forallE _ _ ihA ihB => exact .forallE (ihA H) (ihB (join_lift_images H))

/-- Independently joined substitution images preserve raw joins of templates. -/
theorem BetaLevelJoin.subst_pair (H : BetaLevelJoin a b)
    (HS : ∀ i, BetaLevelJoin (σ i) (τ i)) :
    BetaLevelJoin (a.subst σ) (b.subst τ) :=
  H.subst.trans (join_subst_same b HS)

/-- Joined bodies instantiate at independently joined arguments. -/
theorem BetaLevelJoin.inst_pair (H : BetaLevelJoin a b) (HX : BetaLevelJoin x y) :
    BetaLevelJoin (a.inst x) (b.inst y) := by
  rw [inst_eq_subst, inst_eq_subst]
  apply H.subst_pair
  intro i
  cases i with
  | zero => exact HX
  | succ i => exact .refl

/-- A raw join to a sort exposes an equivalent sort by beta alone. Unlike exact
sort selection, this needs no target universe well-formedness or level steps. -/
theorem BetaLevelJoin.sort_exposure (H : BetaLevelJoin a (.sort u)) :
    ∃ v, BetaRed a (.sort v) ∧ v ≈ u := by
  obtain ⟨a', b', RA, RB, V⟩ := H
  obtain rfl := beta_sort RB rfl
  cases V with
  | refl => exact ⟨_, RA, by rfl⟩
  | sort H => exact ⟨_, RA, H⟩

/-- Declaration-scope context annotations related by raw joins. -/
def BetaLevelContext (Δ Δ' : List ProofShape) : Prop := List.Forall₂ BetaLevelJoin Δ Δ'

/-- Each raw context is joined to itself. -/
theorem BetaLevelContext.refl : BetaLevelContext Δ Δ :=
  List.Forall₂.rfl (fun _ _ => .refl)

/-- Independently joined domains extend joined contexts. -/
theorem BetaLevelContext.cons (H : BetaLevelContext Δ Δ') (HA : BetaLevelJoin A A') :
    BetaLevelContext (A :: Δ) (A' :: Δ') := List.Forall₂.cons HA H

/-- Joined declaration-scope annotations give joined variable-type lookups,
including all lifts and the default proof marker outside the context. -/
theorem BetaLevelContext.oracle (H : BetaLevelContext Δ Δ') :
    BetaLevelJoin (contextOracle Δ i) (contextOracle Δ' i) := by
  induction H generalizing i with
  | nil => exact .refl
  | cons HA _ ih =>
    cases i with
    | zero => exact HA.liftN
    | succ i => exact ih.liftN

end Lean4Lean.VEnv.Strengthening.ProofShape
